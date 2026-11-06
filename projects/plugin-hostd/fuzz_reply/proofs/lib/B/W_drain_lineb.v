(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10 (an internal work row): Section cx below adds dr_lineb_x : dr_lineb_stmt_x B PST ARx MT RP MMAX
   RG (lib/B/W_drain_lineb_cx.v Section cx), the ARx-generic twin of dr_lineb at the room texts; Section c is
   unchanged. *)
(* Modified by Theorem Labs, 2026-10: lib/B/W_drain_lineb.v, half B of the LINEA stage of the image-B
   (fuzz_reply.asan-ubsan) walk of fuzz_reply's drain.  Proves no function (kind: segment lemma):
   dr_lineb : dr_lineb_stmt B MT MMAX RG (lib/B/W_drain_lineb_cx.v), DLS 0x839f4 -> DLN (S q) 0x839d4 or DGS 0x83aa4.
   PORTED from lib/A/W_drain_lineb.v (a working branch e6b5f95b285, the same proof over image A), with image
   B's own code (objdump of fuzz_reply.asan-ubsan) and lib/B's interface (a working branch
   4c7c7ff2c10):
     0x839f4 .. 0x839fc  strrchr(line, ' ')            -> s3 (A: s9)
     0x83a04 .. 0x83a14  strncmp(line, .str.6, 13)      .str.6 = "param_gesture", A_OBJ 18 (A: 21)
     0x83a18             bnez a0 -> DLN
     0x83a1c / 0x83a24   UBSan traps (line non-null; line + 13 does not wrap): decided by the runner from atom 24's
                         fact [4096, 2^47 - 2^23] (the trap kit's recipe R1)
     0x83a28 .. 0x83a3c  ASan shadow check of line + 13, shadow base from the frame slot 240(sp) (A: s5)
     0x83a40 .. 0x83a4c  line[13]; reloads s5 = SA, s6 = SA + 24, s4 = SA + 16 from the frame (B only)
     0x83a54 .. 0x83a5c  line[13] == ' ', last != NULL, last != line + 13 -> else DLN
     0x83a64             UBSan trap (last + 1 does not wrap): refuted from last = line + j
     0x83a68 .. 0x83a78  strcmp(last + 1, .str.7 "begin") -> s9 (A: s3), A_OBJ 20 (A: 23); reloads again
     0x83a8c             beqz a0 -> DGS
     0x83a90 .. 0x83a9c  strcmp(last + 1, .str.8 "end"), A_OBJ 21 (A: 24); bnez a0 -> DLN; else DGS at 0x83aa4.
   STRUCTURE also cross-checked against a working branch 1c09e330abe
   lib/B/Prog/drain_p_seen_strrchr.v / drain_p_seen_strncmp.v / drain_p_seen_gtest.v / drain_p_seen_gbeg.v (the old
   h-lane framework's walk of the same bytes); nothing is copied from them. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_drain_cx W_drain_lineb_cx W_traps.
(* the ARx kit, read by Section cx only (after the AR imports above, which Section c reads unchanged) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).
#[local] Notation dnret := (RelayRunT.nret YO0i.sptr).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c SEGS B MT MMAX CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.

Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

Definition lb_line (rd : Z -> option Z) (x : Z) (l : list Z) : Prop :=
(forall i, (i < length l)%nat -> rd (x + Z.of_nat i) = Some (nth i l 0)) /\
rd (x + Z.of_nat (length l)) = Some 0 /\
(forall i, (i < length l)%nat -> nth i l 0 <> 0).

Definition lb_lit (rd : Z -> option Z) (y : Z) (w : list Z) : Prop :=
forall i, (i <= length w)%nat -> rd (y + Z.of_nat i) = Some (nth i (w ++ [0]) 0).

Lemma lbA_aview_garr8 : forall (W : world SEGS) m base l j,
garr8 SEGS (arm W m) base l -> (j < length l)%nat ->
aview SEGS (w_H W) m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m base l j Hg Hj. destruct (Hg j Hj) as (_ & Hr).
unfold aview. change (mrestrict (w_H W) m) with (arm W m).
rewrite (garr8_mbyte SEGS (arm W m) base l j Hg Hj). cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact Hr.
Qed.

Lemma lbA_nth_bound : forall (w : list Z) i, (i <= length w)%nat ->
Forall (fun b => 0 <= b < 256) w -> 0 <= nth i (w ++ [0]) 0 < 256.
Proof.
intros w i Hi HF. destruct (Nat.eq_dec i (length w)) as [->|Hne].
- rewrite nth_middle. lia.
- rewrite app_nth1 by lia. rewrite Forall_forall in HF. apply HF. apply nth_In. lia.
Qed.

Lemma lbA_kg_len : length K_GESTURE = 13%nat.
Proof. reflexivity. Qed.

Lemma lbA_kg_nz : forall i, (i < 13)%nat -> nth i K_GESTURE 0 <> 0.
Proof.
unfold K_GESTURE. intros i Hi.
do 13 (destruct i as [|i]; [cbn; lia|]). exfalso. lia.
Qed.

Lemma lb_line_of_garr8 : forall (W : world SEGS) m base (L : list Z) p q,
garr8 SEGS (arm W m) base L -> (p <= q < length L)%nat -> nth_error L q = Some 0 ->
(forall i, (p <= i < q)%nat -> nth_error L i <> Some 0) ->
lb_line (aview SEGS (w_H W) m) (base + Z.of_nat p) (firstn (q - p) (skipn p L)).
Proof.
intros W m base L p q Hg Hpq Hq Hno.
assert (HL : length (firstn (q - p) (skipn p L)) = (q - p)%nat).
{ rewrite length_firstn, length_skipn. lia. }
assert (HN : forall i, (i < q - p)%nat -> nth i (firstn (q - p) (skipn p L)) 0 = nth (p + i) L 0).
{ intros i Hi. rewrite nth_firstn, (proj2 (Nat.ltb_lt i (q - p)) Hi), nth_skipn. reflexivity. }
split; [|split].
- intros i Hi. rewrite HL in Hi. rewrite (HN i Hi).
  replace (base + Z.of_nat p + Z.of_nat i) with (base + Z.of_nat (p + i)) by lia.
  apply (lbA_aview_garr8 W m base L (p + i)%nat Hg). lia.
- rewrite HL. replace (base + Z.of_nat p + Z.of_nat (q - p)) with (base + Z.of_nat q) by lia.
  rewrite (lbA_aview_garr8 W m base L q Hg ltac:(lia)). f_equal.
  rewrite (nth_error_nth' L 0) in Hq by lia. injection Hq as Hq. exact Hq.
- intros i Hi. rewrite HL in Hi. rewrite (HN i Hi).
  intros E. apply (Hno (p + i)%nat ltac:(lia)).
  rewrite (nth_error_nth' L 0) by lia. rewrite E. reflexivity.
Qed.

Lemma lb_line_ext : forall rd rd' x l, lb_line rd x l ->
(forall a, x <= a <= x + Z.of_nat (length l) -> rd' a = rd a) -> lb_line rd' x l.
Proof.
intros rd rd' x l (H1 & H2 & H3) HE. split; [|split].
- intros i Hi. rewrite (HE (x + Z.of_nat i) ltac:(lia)). exact (H1 i Hi).
- rewrite (HE (x + Z.of_nat (length l)) ltac:(lia)). exact H2.
- exact H3.
Qed.

Lemma lb_lit_ext : forall rd rd' y w, lb_lit rd y w ->
(forall a, y <= a <= y + Z.of_nat (length w) -> rd' a = rd a) -> lb_lit rd' y w.
Proof.
intros rd rd' y w H HE i Hi. rewrite (HE (y + Z.of_nat i) ltac:(lia)). exact (H i Hi).
Qed.

Lemma lb_lit_of_dlit : forall i w (W : world SEGS) m, dlit_at B i (w ++ [0]) -> rom_view SEGS W m ->
Forall (fun b => 0 <= b < 256) w -> lb_lit (aview SEGS (w_H W) m) (VAL (A_OBJ i)) w.
Proof.
intros i w W m (HR & HI & _) HRV HF k Hk.
assert (HLen : length (w ++ [0]) = S (length w)) by (rewrite length_app; cbn [length]; lia).
assert (HinR : YG0d.in_rom SEGS (VAL (A_OBJ i) + Z.of_nat k)) by (apply HI; lia).
rewrite (HRV _ HinR), (HR k ltac:(lia)).
rewrite (nth_error_nth' (w ++ [0]) 0) by lia.
cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. apply lbA_nth_bound; assumption.
Qed.

Lemma lb_line_first_byte : forall (W : world SEGS) m x l n, lb_line (aview SEGS (w_H W) m) x l -> 0 <= n ->
first_byte SEGS W m x n 0 (Z.min n (Z.of_nat (length l))).
Proof.
intros W m x l n (H1 & H2 & H3) Hn. split; [lia|split].
- intros i Hi. exists (nth (Z.to_nat i) l 0). split.
  + replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia. apply H1. lia.
  + apply H3. lia.
- intros Hlt. replace (Z.min n (Z.of_nat (length l))) with (Z.of_nat (length l)) by lia. exact H2.
Qed.

Lemma lb_lit_first_byte : forall (W : world SEGS) m y w n, lb_lit (aview SEGS (w_H W) m) y w ->
(forall i, (i < length w)%nat -> nth i w 0 <> 0) -> 0 <= n ->
first_byte SEGS W m y n 0 (Z.min n (Z.of_nat (length w))).
Proof.
intros W m y w n H Hnz Hn. split; [lia|split].
- intros i Hi. exists (nth (Z.to_nat i) w 0). split.
  + replace (y + i) with (y + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (H (Z.to_nat i) ltac:(lia)). f_equal. apply app_nth1. lia.
  + apply Hnz. lia.
- intros Hlt. replace (Z.min n (Z.of_nat (length w))) with (Z.of_nat (length w)) by lia.
  rewrite (H (length w) ltac:(lia)). f_equal. apply nth_middle.
Qed.

Lemma lb_line_skipn : forall rd x l j, lb_line rd x l -> (j < length l)%nat ->
lb_line rd (x + Z.of_nat j + 1) (skipn (S j) l).
Proof.
intros rd x l j (H1 & H2 & H3) Hj.
assert (HL : length (skipn (S j) l) = (length l - S j)%nat) by apply length_skipn.
split; [|split].
- intros i Hi. rewrite HL in Hi. rewrite nth_skipn.
  replace (x + Z.of_nat j + 1 + Z.of_nat i) with (x + Z.of_nat (S j + i)) by lia.
  apply H1. lia.
- rewrite HL. replace (x + Z.of_nat j + 1 + Z.of_nat (length l - S j)) with (x + Z.of_nat (length l)) by lia.
  exact H2.
- intros i Hi. rewrite HL in Hi. rewrite nth_skipn. apply H3. lia.
Qed.

Lemma lb_line_vis : forall rd x l a, lb_line rd x l -> x <= a <= x + Z.of_nat (length l) -> rd a <> None.
Proof.
intros rd x l a (H1 & H2 & _) Ha.
destruct (Z.eq_dec a (x + Z.of_nat (length l))) as [Heq|Hne].
- rewrite Heq, H2. discriminate.
- assert (Hk : (Z.to_nat (a - x) < length l)%nat) by lia.
  assert (Ha' : a = x + Z.of_nat (Z.to_nat (a - x))) by lia.
  rewrite Ha', (H1 _ Hk). discriminate.
Qed.

Lemma lb_lit_vis : forall rd y w a, lb_lit rd y w -> y <= a <= y + Z.of_nat (length w) -> rd a <> None.
Proof.
intros rd y w a H Ha.
assert (Hk : (Z.to_nat (a - y) <= length w)%nat) by lia.
assert (Ha' : a = y + Z.of_nat (Z.to_nat (a - y))) by lia.
rewrite Ha', (H _ Hk). discriminate.
Qed.

Lemma lb_strncmp_iff : forall rd x y l, lb_line rd x l -> lb_lit rd y K_GESTURE ->
((forall i, 0 <= i < 13 -> (forall j, 0 <= j < i -> rd (x + j) <> Some 0) -> rd (x + i) = rd (y + i)) <->
 firstn 13 l = K_GESTURE).
Proof.
intros rd x y l (H1 & H2 & H3) HK.
assert (HY : forall k, (k < 13)%nat -> rd (y + Z.of_nat k) = Some (nth k K_GESTURE 0)).
{ intros k Hk. rewrite (HK k ltac:(rewrite lbA_kg_len; lia)). f_equal.
  apply app_nth1. rewrite lbA_kg_len. lia. }
split.
- intros HA.
  assert (MAIN : forall k, (k <= 13)%nat -> (k <= length l)%nat /\
    (forall t, (t < k)%nat -> nth t l 0 = nth t K_GESTURE 0)).
  { intros k. induction k as [|k IHk]; intros Hk.
    - split; [lia|intros t Ht; exfalso; lia].
    - destruct (IHk ltac:(lia)) as (Hlen & Hagr).
      assert (HNZ : forall j, 0 <= j < Z.of_nat k -> rd (x + j) <> Some 0).
      { intros j Hj. assert (Hj' : (Z.to_nat j < length l)%nat) by lia.
        replace (x + j) with (x + Z.of_nat (Z.to_nat j)) by lia.
        rewrite (H1 _ Hj'). intros E. injection E as E. exact (H3 _ Hj' E). }
      assert (HEQ : rd (x + Z.of_nat k) = Some (nth k K_GESTURE 0)).
      { rewrite (HA (Z.of_nat k) ltac:(lia) HNZ). apply HY. lia. }
      assert (HlenS : (S k <= length l)%nat).
      { destruct (Nat.ltb k (length l)) eqn:Eb; [apply Nat.ltb_lt in Eb; lia|].
        apply Nat.ltb_ge in Eb. exfalso.
        assert (Ek : k = length l) by lia. subst k.
        rewrite H2 in HEQ. injection HEQ as HEQ.
        apply (lbA_kg_nz (length l) ltac:(lia)). symmetry. exact HEQ. }
      split; [exact HlenS|].
      intros t Ht. destruct (Nat.eq_dec t k) as [->|Hne].
      + rewrite (H1 k ltac:(lia)) in HEQ. injection HEQ as HEQ. exact HEQ.
      + apply Hagr. lia. }
  destruct (MAIN 13%nat ltac:(lia)) as (Hlen13 & Hagr13).
  apply (nth_ext _ _ 0 0).
  { rewrite length_firstn, lbA_kg_len. lia. }
  intros t Ht. rewrite length_firstn in Ht.
  rewrite nth_firstn, (proj2 (Nat.ltb_lt t 13) ltac:(lia)).
  apply Hagr13. lia.
- intros HF i Hi _.
  assert (HLL : length (firstn 13 l) = length K_GESTURE) by (rewrite HF; reflexivity).
  rewrite length_firstn, lbA_kg_len in HLL.
  assert (Hik : (Z.to_nat i < 13)%nat) by lia.
  replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia.
  replace (y + i) with (y + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (H1 (Z.to_nat i) ltac:(lia)), (HY (Z.to_nat i) Hik). f_equal.
  rewrite <- HF, nth_firstn, (proj2 (Nat.ltb_lt (Z.to_nat i) 13) Hik). reflexivity.
Qed.

Lemma lbA_lsf_none : forall l i, (forall k, (k < length l)%nat -> nth k l 0 <> SPACE) ->
last_space_from i l = None.
Proof.
induction l as [|b l IH]; intros i H; [reflexivity|].
cbn [last_space_from].
rewrite (IH (S i) ltac:(intros k Hk; apply (H (S k)); cbn [length]; lia)).
cbv beta iota.
destruct (Z.eqb b SPACE) eqn:E; [|reflexivity].
exfalso. apply (H 0%nat ltac:(cbn [length]; lia)). cbn [nth].
exact (proj1 (Z.eqb_eq b SPACE) E).
Qed.

Lemma lbA_lsf_none_inv : forall l i, last_space_from i l = None ->
forall k, (k < length l)%nat -> nth k l 0 <> SPACE.
Proof.
induction l as [|b l IH]; intros i H k Hk; [cbn [length] in Hk; exfalso; lia|].
cbn [last_space_from] in H.
destruct (last_space_from (S i) l) eqn:E; cbv beta iota in H; [discriminate|].
destruct (Z.eqb b SPACE) eqn:Eb; cbv beta iota in H; [discriminate|].
destruct k as [|k].
- cbn [nth]. intros Hb. rewrite Hb, Z.eqb_refl in Eb. discriminate.
- cbn [nth]. apply (IH (S i) E k). cbn [length] in Hk. lia.
Qed.

Lemma lbA_lsf_some : forall l i k, (k < length l)%nat -> nth k l 0 = SPACE ->
(forall m, (k < m < length l)%nat -> nth m l 0 <> SPACE) ->
last_space_from i l = Some (i + k)%nat.
Proof.
induction l as [|b l IH]; intros i k Hk Hnth Hmax; [cbn [length] in Hk; exfalso; lia|].
cbn [last_space_from].
destruct k as [|k].
- rewrite (lbA_lsf_none l (S i) ltac:(intros m Hm; apply (Hmax (S m)); cbn [length]; lia)).
  cbn [nth] in Hnth. rewrite Hnth, Z.eqb_refl. cbv beta iota. f_equal. lia.
- rewrite (IH (S i) k ltac:(cbn [length] in Hk; lia) Hnth
    ltac:(intros m Hm; apply (Hmax (S m)); cbn [length]; lia)).
  cbv beta iota. f_equal. lia.
Qed.

Lemma lbA_lsf_spec : forall l i j, last_space_from i l = Some j ->
(i <= j < i + length l)%nat /\ nth (j - i) l 0 = SPACE /\
(forall m, (j - i < m < length l)%nat -> nth m l 0 <> SPACE).
Proof.
induction l as [|b l IH]; intros i j H; [cbn [last_space_from] in H; discriminate|].
cbn [last_space_from] in H.
destruct (last_space_from (S i) l) as [k|] eqn:E; cbv beta iota in H.
- injection H as <-.
  destruct (IH (S i) k E) as (Hr & Hn & Hm).
  split; [cbn [length]; lia|]. split.
  + replace (k - i)%nat with (S (k - S i)) by lia. cbn [nth]. exact Hn.
  + intros m Hm'. destruct m as [|m]; [exfalso; lia|].
    cbn [nth]. apply Hm. cbn [length] in Hm'. lia.
- destruct (Z.eqb b SPACE) eqn:Eb; cbv beta iota in H; [|discriminate].
  injection H as <-.
  split; [cbn [length]; lia|]. split.
  + replace (i - i)%nat with 0%nat by lia. cbn [nth]. exact (proj1 (Z.eqb_eq b SPACE) Eb).
  + intros m Hm'. destruct m as [|m]; [exfalso; lia|].
    cbn [nth]. apply (lbA_lsf_none_inv l (S i) E m). cbn [length] in Hm'. lia.
Qed.

Lemma lb_strrchr : forall rd x l (r : bv 64), lb_line rd x l -> 0 < x -> x + Z.of_nat (length l) < 2 ^ 63 ->
(((forall i, 0 <= i <= Z.of_nat (length l) -> rd (x + i) <> Some 32) /\ r = w64 0) \/
 (exists i, 0 <= i <= Z.of_nat (length l) /\ rd (x + i) = Some 32 /\
   (forall j, i < j <= Z.of_nat (length l) -> rd (x + j) <> Some 32) /\ r = w64 (x + i))) ->
(r = w64 0 /\ last_space_from 0 l = None) \/
(exists j, (j < length l)%nat /\ r = w64 (x + Z.of_nat j) /\ last_space_from 0 l = Some j).
Proof.
intros rd x l r (H1 & H2 & H3) Hx Hub [[HNo Hr]|[i (Hi & Hsp & Hmax & Hr)]].
- left. split; [exact Hr|]. apply lbA_lsf_none. intros k Hk Ek.
  apply (HNo (Z.of_nat k) ltac:(lia)). rewrite (H1 k Hk), Ek. reflexivity.
- right.
  assert (Hne : i <> Z.of_nat (length l)).
  { intros E. rewrite E, H2 in Hsp. discriminate. }
  assert (Hk : (Z.to_nat i < length l)%nat) by lia.
  assert (HthS : nth (Z.to_nat i) l 0 = SPACE).
  { assert (E := H1 (Z.to_nat i) Hk).
    replace (x + Z.of_nat (Z.to_nat i)) with (x + i) in E by lia.
    rewrite Hsp in E. injection E as E. symmetry. exact E. }
  assert (Hmx : forall m, (Z.to_nat i < m < length l)%nat -> nth m l 0 <> SPACE).
  { intros m Hm Em. apply (Hmax (Z.of_nat m) ltac:(lia)).
    rewrite (H1 m ltac:(lia)), Em. reflexivity. }
  exists (Z.to_nat i). split; [exact Hk|]. split.
  + rewrite Hr. f_equal. lia.
  + rewrite (lbA_lsf_some l 0%nat (Z.to_nat i) Hk HthS Hmx). reflexivity.
Qed.

Lemma lb_strcmp_iff : forall rd x y l w j, lb_line rd x l -> lb_lit rd y w -> (j < length l)%nat ->
((Z.of_nat (length l) - Z.of_nat j - 1 = Z.of_nat (length w) /\
  forall i, 0 <= i < Z.of_nat (length l) - Z.of_nat j - 1 -> rd (x + Z.of_nat j + 1 + i) = rd (y + i)) <->
 skipn (S j) l = w).
Proof.
intros rd x y l w j (H1 & H2 & H3) HW Hj.
assert (HSL : length (skipn (S j) l) = (length l - S j)%nat) by apply length_skipn.
split.
- intros (HLen & HA).
  apply (nth_ext _ _ 0 0).
  { rewrite HSL. lia. }
  intros t Ht. rewrite HSL in Ht. rewrite nth_skipn.
  assert (HT : rd (x + Z.of_nat j + 1 + Z.of_nat t) = rd (y + Z.of_nat t)) by (apply HA; lia).
  replace (x + Z.of_nat j + 1 + Z.of_nat t) with (x + Z.of_nat (S j + t)) in HT by lia.
  rewrite (H1 (S j + t)%nat ltac:(lia)), (HW t ltac:(lia)) in HT.
  injection HT as HT. transitivity (nth t (w ++ [0]) 0); [exact HT|].
  apply app_nth1. lia.
- intros HS.
  assert (HLw : length w = (length l - S j)%nat) by (rewrite <- HS; exact HSL).
  split; [lia|].
  intros i Hi.
  assert (Hti : (Z.to_nat i < length w)%nat) by lia.
  replace (x + Z.of_nat j + 1 + i) with (x + Z.of_nat (S j + Z.to_nat i)) by lia.
  replace (y + i) with (y + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (H1 (S j + Z.to_nat i)%nat ltac:(lia)), (HW (Z.to_nat i) ltac:(lia)).
  f_equal. rewrite app_nth1 by lia. rewrite <- HS, nth_skipn. reflexivity.
Qed.

Lemma lb_g_nok : forall l, firstn 13 l <> K_GESTURE -> gesture l = None.
Proof.
intros l H. unfold gesture.
destruct (list_eqb (firstn 13 l) K_GESTURE) eqn:E; [|reflexivity].
exfalso. apply H. exact (list_eqb_true _ _ E).
Qed.

Lemma lb_g_nsp : forall l, nth 13 l 0 <> SPACE -> gesture l = None.
Proof.
intros l H. unfold gesture.
destruct (Z.eqb (nth 13 l 0) SPACE) eqn:E.
- exfalso. apply H. exact (proj1 (Z.eqb_eq (nth 13 l 0) SPACE) E).
- destruct (list_eqb (firstn 13 l) K_GESTURE); reflexivity.
Qed.

Lemma lb_g_nolast : forall l, last_space_from 0 l = None -> gesture l = None.
Proof.
intros l H. unfold gesture. rewrite H.
match goal with |- (if ?c then _ else _) = None => destruct c end; reflexivity.
Qed.

Lemma lb_g_13 : forall l, last_space_from 0 l = Some 13%nat -> gesture l = None.
Proof.
intros l H. unfold gesture. rewrite H.
match goal with |- (if ?c then _ else _) = None => destruct c end; reflexivity.
Qed.

Lemma lb_g_last : forall l j, nth 13 l 0 = SPACE -> last_space_from 0 l = Some j ->
(13 <= j < length l)%nat /\ nth j l 0 = SPACE.
Proof.
intros l j HS HL.
destruct (lbA_lsf_spec l 0%nat j HL) as (Hr & Hn & Hm).
rewrite Nat.sub_0_r in Hn. rewrite Nat.sub_0_r in Hm.
assert (H13 : (13 < length l)%nat).
{ destruct (Nat.ltb 13 (length l)) eqn:E; [exact (proj1 (Nat.ltb_lt 13 (length l)) E)|].
  pose proof (proj1 (Nat.ltb_ge 13 (length l)) E) as E'. exfalso.
  rewrite nth_overflow in HS by lia. unfold SPACE in HS. lia. }
assert (Hge : (13 <= j)%nat).
{ destruct (Nat.leb 13 j) eqn:E; [exact (proj1 (Nat.leb_le 13 j) E)|].
  pose proof (proj1 (Nat.leb_gt 13 j) E) as E'. exfalso. apply (Hm 13%nat ltac:(lia)). exact HS. }
split; [lia|]. exact Hn.
Qed.

Lemma lb_g_some : forall l j, firstn 13 l = K_GESTURE -> nth 13 l 0 = SPACE -> last_space_from 0 l = Some j ->
(13 < j)%nat ->
gesture l = if list_eqb (skipn (S j) l) W_BEGIN then Some (GBegin, firstn j l)
            else if list_eqb (skipn (S j) l) W_END then Some (GEnd, firstn j l) else None.
Proof.
intros l j HK HS HL HJ.
destruct (lb_g_last l j HS HL) as ((Hge & Hlt) & _).
unfold gesture. rewrite HK, HS, HL, list_eqb_refl, Z.eqb_refl. cbv beta iota.
rewrite (proj2 (Nat.ltb_lt 13 (length l))) by lia.
rewrite (proj2 (Nat.ltb_lt 13 j)) by lia. reflexivity.
Qed.

Lemma lb_list_eqb : forall a b, list_eqb a b = true <-> a = b.
Proof.
intros a b. unfold list_eqb. destruct (list_eq_dec Z.eq_dec a b); split; congruence.
Qed.


Definition lb_keep (cx : dcx) (W1 : world SEGS) (m1 m2 : word -> option byte) : Prop :=
(forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - 2 * ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x) /\
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m2 x).

Definition lbB_low (a : Z) : Prop := 0 <= a < alloc_ceiling + 8.

Ltac lbB_in := repeat (first [left; reflexivity | right]).

Lemma lbB_blk_low : forall ly S (W : world SEGS) mem md q n a,
AR SEGS B ly S W mem md -> In (q, n) (ablocks B ly S) -> q <= a -> a < q + req_size n + 8 -> lbB_low a.
Proof.
intros ly S W mem md q n a HAR Hin H1 H2.
destruct (al_blocks SEGS B LAWS ly S W mem md q n HAR Hin) as (_ & H4096 & Hceil & _).
unfold lbB_low. lia.
Qed.

Lemma lbB_img_low : forall a lo hi, 0x10000 <= lo -> lo <= a -> a < hi -> hi <= IMG_TOP -> lbB_low a.
Proof. intros a lo hi H1 H2 H3 H4. pose proof asan_consts as (C1 & _). unfold lbB_low, IMG_TOP in *. lia. Qed.

Lemma lbB_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma lbB_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|].
unfold key_ptrs in *. cbn [map concat length]. rewrite length_app, Mem.length_le8, IH. lia.
Qed.

Lemma lbB_eb_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
length (entry_bytes e) = 56%nat.
Proof.
intros e H1 H2. unfold entry_bytes.
rewrite !length_app, !Mem.length_le4, !Mem.length_le8, H1, H2. reflexivity.
Qed.

Lemma lbB_alist_fp_low : forall ly S (W : world SEGS) mem md LA l lns lo hi,
AR SEGS B ly S W mem md -> alist_at B ly S W mem LA l lns ->
0x10000 <= lo -> lo <= LA -> LA + 16 <= hi -> hi <= IMG_TOP ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> lbB_low a.
Proof.
intros ly S W mem md LA l lns lo hi HAR HL Hlo1 Hlo2 Hhi1 Hhi2 r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (lbB_img_low a lo hi); unfold IMG_TOP in *; lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, lbB_recs_len in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (lbB_blk_low ly S W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin); [lia|].
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as (_ & Hrq).
    unfold hl_n in Hn, Hj. unfold AREC in *. lia.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs q Hq) as (Hin & _).
    apply (lbB_blk_low ly S W mem md (fst q) (Z.of_nat (length (snd q)) + 1) a HAR Hin); [lia|].
    pose proof (req_size_pos (Z.of_nat (length (snd q)) + 1) ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma lbB_asrc_fp_low : forall ly S (W : world SEGS) mem md HA h,
AR SEGS B ly S W mem md -> asrc_at B ly S W mem HA h ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> lbB_low a.
Proof.
intros ly S W mem md HA h HAR HS Hlo Hhi r Hr a Ha.
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (lbB_img_low a (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  apply (lbB_blk_low ly S W mem md (hs_partial h) APARTIAL a HAR Hpb); [lia|].
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + refine (lbB_alist_fp_low ly S W mem md (HA + 16) (hs_pending h) false (rg_s RG) (rg_s RG + 4 * ASRC)
      HAR Hpend _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * refine (lbB_alist_fp_low ly S W mem md (HA + 64) (hs_expected h) true (rg_s RG) (rg_s RG + 4 * ASRC)
        HAR Hexp _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
    * refine (lbB_alist_fp_low ly S W mem md (HA + 80) (hs_held h) true (rg_s RG) (rg_s RG + 4 * ASRC)
        HAR Hheld _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
Qed.

Lemma lbB_aout_fp_low : forall ly S (W : world SEGS) mem md c O mx no cap out,
AR SEGS B ly S W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> lbB_low a.
Proof.
intros ly S W mem md c O mx no cap out HAR HOUT r Hr a Ha.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (GL : forall x l, In (x, l) (G_DR B RG) -> x <= a < x + l -> lbB_low a).
{ intros x l Hin Hx.
  assert (HI : inG (G_DR B RG) a)
    by (unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low SEGS B pa_segs_low _ a HG HI). unfold lbB_low. lia. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- pose proof HSM as (Hs1 & Hs2). apply (lbB_img_low a (rg_send_max RG) (rg_send_max RG + 8)); unfold IMG_TOP in *; lia.
- apply (GL (rg_nout RG) 8); [unfold G_DR, G_SL; lbB_in | lia].
- apply (GL (rg_capout RG) 8); [unfold G_DR, G_SL; lbB_in | lia].
- apply (GL (rg_out RG) 8); [unfold G_DR, G_SL; lbB_in | lia].
- pose proof (pa_obj_img 9 ltac:(lia)) as H9. rewrite HV9 in H9.
  apply (lbB_img_low a (rg_client RG) (rg_client RG + 4)); unfold IMG_TOP in *; lia.
- apply (GL (rg_client_broken RG) 1); [unfold G_DR, G_SL; lbB_in | lia].
- pose proof HSD as (Hd1 & Hd2). apply (lbB_img_low a (rg_send_dead RG) (rg_send_dead RG + 1)); unfold IMG_TOP in *; lia.
- apply (GL (rg_send_eintr RG) 1); [unfold G_DR, G_SL; lbB_in | lia].
- apply (GL (as_errno B) 4); [unfold G_DR, G_SL; lbB_in | lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  apply (lbB_blk_low ly S W mem md out cap a HAR Hin); [lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma lbB_eokx : forall ly S (W : world SEGS) mem md mem' e,
AR SEGS B ly S W mem md -> aentry_okx B ly S W mem e ->
(forall a, lbB_low a -> abyte_kept W mem W mem' a) -> aentry_okx B ly S W mem' e.
Proof.
intros ly S W mem md mem' e HAR HE KL.
destruct HE as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14).
do 8 (split; [assumption|]).
split.
{ destruct H9 as [H9 | (Hc & Hin & Hj & Hg)]; [left; exact H9|right].
  split; [exact Hc|]. split; [exact Hin|]. split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. apply KL. apply (lbB_blk_low ly S W mem md (re_buf e) (re_cap e) x HAR Hin); [lia|].
  unfold bzs in Hx. rewrite length_map, length_app in Hx.
  pose proof (req_size_pos (re_cap e) ltac:(lia)) as (_ & Hrq). lia. }
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H11|right].
  split; [exact Hz|]. split; [exact Hin|]. split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. apply KL. apply (lbB_blk_low ly S W mem md (re_hp e) (re_kh e) x HAR Hin); [lia|].
  unfold bzs in Hx. rewrite length_map, lbB_key_ptrs_len in Hx. unfold re_nheld in Hk1.
  pose proof (req_size_pos (re_kh e) ltac:(lia)) as (_ & Hrq). lia. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3 & K4).
split; [exact K1|]. split; [|split; [exact K3 | exact K4]].
apply (akept_garr8 W mem); [|exact K2].
intros x Hx. apply KL.
apply (lbB_blk_low ly S W mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) x HAR K1); [lia|].
unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx.
pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma lbB_rom : forall (W : world SEGS) mem m',
(forall a, lbB_low a -> abyte_kept W mem W m' a) -> rom_view SEGS W mem -> rom_view SEGS W m'.
Proof.
intros W mem m' KL HR a Ha. pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (Hl : 0 <= a < kLowMemEnd).
{ destruct Ha as (sg & Hsg & _ & Hr). exact (pa_segs_low a ltac:(exists sg; split; [exact Hsg | exact Hr])). }
rewrite (proj1 (KL a ltac:(unfold lbB_low; lia))). exact (HR a Ha).
Qed.

Lemma lbB_stk : forall cx, DBASE B MT MMAX RG cx -> alloc_ceiling + DRAIN_STK <= dsp0 cx /\ dsp0 cx <= 2 ^ 47.
Proof.
intros cx HB. unfold DBASE in HB. destruct HB as (Hafn & _).
destruct Hafn as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
unfold dsp0. lia.
Qed.

Lemma lbB_kept : forall cx (W1 : world SEGS) m1 m2 a, lb_keep cx W1 m1 m2 -> 0 <= a < 2 ^ 64 ->
~ (dsp0 cx - DRAIN_FRAME - 2 * ESTACK <= a < dsp0 cx - DRAIN_FRAME) -> abyte_kept W1 m1 W1 m2 a.
Proof.
intros cx W1 m1 m2 a (HV & HP) Ha Hw. split; [exact (HV a Ha Hw)|].
unfold arm. apply writable_kept. intros Hp. exact (HP a Hp).
Qed.

Lemma lbB_low_kept : forall cx (W1 : world SEGS) m1 m2,
DBASE B MT MMAX RG cx -> lb_keep cx W1 m1 m2 -> forall a, lbB_low a -> abyte_kept W1 m1 W1 m2 a.
Proof.
intros cx W1 m1 m2 HB HK a Ha.
pose proof (lbB_stk cx HB) as (H1 & H2). pose proof asan_consts as (C1 & _).
assert (EF : DRAIN_FRAME = 352) by reflexivity. assert (ES : DRAIN_STK = 16880) by reflexivity.
assert (EE : ESTACK = 4096) by reflexivity.
unfold lbB_low in Ha. apply (lbB_kept cx W1 m1 m2 a HK); lia.
Qed.

Lemma lbB_hi_kept : forall cx (W1 : world SEGS) m1 m2,
DBASE B MT MMAX RG cx -> lb_keep cx W1 m1 m2 ->
forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W1 m1 W1 m2 a.
Proof.
intros cx W1 m1 m2 HB HK a Ha.
pose proof (lbB_stk cx HB) as (H1 & H2). pose proof asan_consts as (C1 & _).
assert (EF : DRAIN_FRAME = 352) by reflexivity. assert (ES : DRAIN_STK = 16880) by reflexivity.
assert (EE : ESTACK = 4096) by reflexivity.
apply (lbB_kept cx W1 m1 m2 a HK); lia.
Qed.

Lemma lbB_vm_hi : forall cx (W1 : world SEGS) m1 m2 a n v,
DBASE B MT MMAX RG cx -> lb_keep cx W1 m1 m2 ->
dsp0 cx - DRAIN_FRAME <= a -> a + Z.of_nat n <= dsp0 cx ->
val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W1 m2) a n v.
Proof.
intros cx W1 m1 m2 a n v HB HK H1 H2 Hv.
apply (akept_vm W1 m1); [|exact Hv].
intros x Hx. apply (lbB_hi_kept cx W1 m1 m2 HB HK). lia.
Qed.

Lemma lbB_frame : forall cx (W1 : world SEGS) m1 m2,
DBASE B MT MMAX RG cx -> lb_keep cx W1 m1 m2 -> dr_frame RG cx W1 m1 -> dr_frame RG cx W1 m2.
Proof.
intros cx W1 m1 m2 HB HK HF.
assert (EF : DRAIN_FRAME = 352) by reflexivity.
assert (V : forall a n v, dsp0 cx - DRAIN_FRAME <= a -> a + Z.of_nat n <= dsp0 cx ->
  val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W1 m2) a n v)
  by (intros a n v H1 H2 Hv; exact (lbB_vm_hi cx W1 m1 m2 a n v HB HK H1 H2 Hv)).
unfold dr_frame in HF |- *. cbv zeta in HF |- *.
destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 &
  F19 & F20 & F21 & F22 & F23 & FS).
repeat match goal with |- _ /\ _ => split end;
  try (apply V; [lia | lia | assumption]).
unfold dr_saved in FS |- *. intros i Hi. apply V; [unfold DR_SAVE_OFF; lia | unfold DR_SAVE_OFF; lia | exact (FS i Hi)].
Qed.

(* the four frame slots this path reads, after any change of memory that keeps drain's frame *)
Lemma lb_frame_slots : forall cx (W1 : world SEGS) m1 m2,
DBASE B MT MMAX RG cx -> lb_keep cx W1 m1 m2 -> dr_frame RG cx W1 m1 ->
val_mem SEGS (arm W1 m2) (dsp0 cx - DRAIN_FRAME + 128) 8 (dxSA cx + 16) /\
val_mem SEGS (arm W1 m2) (dsp0 cx - DRAIN_FRAME + 136) 8 (dxSA cx + 24) /\
val_mem SEGS (arm W1 m2) (dsp0 cx - DRAIN_FRAME + 144) 8 (dxSA cx) /\
val_mem SEGS (arm W1 m2) (dsp0 cx - DRAIN_FRAME + 240) 8 SHADOW_OFF.
Proof.
intros cx W1 m1 m2 HB HK HF. pose proof (lbB_frame cx W1 m1 m2 HB HK HF) as HF2.
unfold dr_frame in HF2. cbv zeta in HF2.
destruct HF2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F128 & F136 & F144 & _ & _ & _ & _ & _ & _ & _ & _ &
  F240 & _).
exact (conj F128 (conj F136 (conj F144 F240))).
Qed.

Lemma lb_lcore_keep : forall cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2,
DBASE B MT MMAX RG cx ->
LCORE B MT MMAX RG cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
lb_keep cx W1 m1 m2 ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k1 ->
LCORE B MT MMAX RG cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m2 md2 k1 e1 h1 out1 ev1 LB1 spent tl.
Proof.
intros cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2 HB HL HK HJ2.
unfold LCORE in HL |- *. cbv zeta in HL |- *.
destruct HL as (HMEM & HLINK & HSAME & HHIST & HRST & HBUD).
refine (conj _ (conj HLINK (conj HSAME (conj HHIST (conj HRST HBUD))))).
unfold DMEM in HMEM |- *.
destruct HMEM as (HJ & HROM & HPRES & HFRAMES & HFR & HGARR & HAWR & HEOK & HSRC & HOTH & HKEPT & HOUT & HLIVE & HPERM).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof (lbB_low_kept cx W1 m1 m2 HB HK) as KL.
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof HB as HB'. unfold DBASE in HB'.
destruct HB' as (_ & _ & _ & HSAlo & HSAhi & _ & _ & _ & _ & Hj4 & _).
assert (Htbl : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
assert (KSA : forall x, dxSA cx <= x < dxSA cx + AENT -> abyte_kept W1 m1 W1 m2 x).
{ intros x Hx. apply KL. apply (lbB_blk_low ly1 S1 W1 m1 md1 (dxG cx) ATABLE x HAR Htbl); [lia|].
  pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as (_ & Hrq). lia. }
assert (KGS : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W1 m2 x).
{ intros x Hx. apply KL. apply (lbB_img_low x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold IMG_TOP in *; lia. }
split; [exact HJ2|].
split; [exact (lbB_rom W1 m1 m2 KL HROM)|].
split; [intros a Ha1 Ha2 Ha3 Hp; apply (proj2 HK); exact (HPRES a Ha1 Ha2 Ha3 Hp)|].
split; [exact HFRAMES|].
split; [exact (lbB_frame cx W1 m1 m2 HB HK HFR)|].
split.
{ apply (akept_garr8 W1 m1); [|exact HGARR]. intros x Hx. apply KSA.
  pose proof HEOK as (_ & _ & Hp1 & Hp2 & _).
  unfold bzs in Hx. rewrite length_map, (lbB_eb_len e1 Hp1 Hp2) in Hx. unfold AENT. lia. }
split; [exact (akept_awr W1 m1 W1 m2 (dxSA cx) AENT KSA HAWR)|].
split; [exact (lbB_eokx ly1 S1 W1 m1 md1 m2 e1 HAR HEOK KL)|].
split.
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 (dHA RG cx) h1 HSRC).
  - intros r Hr x Hx. apply KL.
    refine (lbB_asrc_fp_low ly1 S1 W1 m1 md1 (dHA RG cx) h1 HAR HSRC _ _ r Hr x Hx); unfold dHA, ASRC; lia.
  - intros b Hb. apply (Permutation_in _ (Permutation_sym HPERM)).
    right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
split.
{ intros i Hi Hne. destruct (HOTH i Hi Hne) as (f & o' & Hf & Ho & Hfo). exists f, o'.
  split; [|split; [|exact Hfo]].
  - apply (akept_vm W1 m1); [|exact Hf]. intros x Hx. apply KGS. unfold ASRC in *. lia.
  - apply (akept_vm W1 m1); [|exact Ho]. intros x Hx. apply KGS. unfold ASRC in *. lia. }
split.
{ intros x Hx Hn. pose proof (HKEPT x Hx Hn) as K1. pose proof (KGS x Hx) as K2.
  split; [rewrite (proj1 K2); exact (proj1 K1)|].
  intros Hw. apply (proj2 K2). apply (proj2 K1). exact Hw. }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2 _ _ _ _ _ _ HOUT).
  - intros r Hr x Hx. apply KL. exact (lbB_aout_fp_low ly1 S1 W1 m1 md1 _ _ _ _ _ _ HAR HOUT r Hr x Hx).
  - intros b Hb. apply (Permutation_in _ (Permutation_sym HPERM)).
    right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
split; [exact HLIVE | exact HPERM].
Qed.

Lemma lb_dregs_keep : forall cx regs1 regs2 W1 m1 m2,
DBASE B MT MMAX RG cx -> dregs_line RG cx regs1 W1 m1 ->
spZ regs2 = spZ regs1 ->
getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 -> getr regs2 21 = getr regs1 21 ->
getr regs2 20 = getr regs1 20 -> getr regs2 22 = getr regs1 22 -> getr regs2 27 = getr regs1 27 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
lb_keep cx W1 m1 m2 ->
dregs_line RG cx regs2 W1 m2.
Proof.
intros cx regs1 regs2 W1 m1 m2 HB HR Hsp H3 H4 H21 H20 H22 H27 H8 H9 H18 HK.
unfold dregs_line in HR |- *.
destruct HR as (R0 & R3 & R4 & R21 & R20 & R22 & R27 & R8 & R9 & R18 & RF).
rewrite Hsp, H3, H4, H21, H20, H22, H27, H8, H9, H18.
exact (conj R0 (conj R3 (conj R4 (conj R21 (conj R20 (conj R22 (conj R27 (conj R8 (conj R9 (conj R18
  (lbB_frame cx W1 m1 m2 HB HK RF))))))))))).
Qed.

Lemma lbB_scan_zero_fst : forall sk acc d, fst (scan sk acc (0 :: d)) = fst (scan false [] d).
Proof. intros sk acc d. rewrite scan_zero. destruct (scan false [] d) as [[a b] c]. reflexivity. Qed.

Lemma lbB_scan_zero_snd : forall sk acc d, snd (scan sk acc (0 :: d)) =
  if (sk || Nat.ltb LINE_LIMIT (length acc))%bool then snd (scan false [] d) else acc :: snd (scan false [] d).
Proof. intros sk acc d. rewrite scan_zero. destruct (scan false [] d) as [[a b] c]. reflexivity. Qed.

Lemma lbB_scan_nz_app : forall u sk acc d, nozero u -> scan sk acc (u ++ d) = scan sk (acc ++ u) d.
Proof.
induction u as [|b u IH]; intros sk acc d Hz.
- rewrite app_nil_r. reflexivity.
- pose proof (Forall_inv Hz) as Hb. pose proof (Forall_inv_tail Hz) as Hu. cbn [app].
  rewrite (scan_nz sk acc b (u ++ d) Hb), (IH sk (acc ++ [b]) d Hu), <- app_assoc. reflexivity.
Qed.

Lemma lbB_nth_skipn_cons : forall (l : list Z) n x, nth_error l n = Some x -> skipn n l = x :: skipn (S n) l.
Proof.
induction l as [|a l IH]; intros n x Hn; [rewrite nth_error_nil in Hn; discriminate|].
destruct n as [|n].
- change (Some a = Some x) in Hn. injection Hn as ->. reflexivity.
- exact (IH n x Hn).
Qed.

Lemma lbB_firstn_nth_app : forall (l : list Z) n x, nth_error l n = Some x -> firstn (S n) l = firstn n l ++ [x].
Proof.
induction l as [|a l IH]; intros n x Hn; [rewrite nth_error_nil in Hn; discriminate|].
destruct n as [|n].
- change (Some a = Some x) in Hn. injection Hn as ->. reflexivity.
- change (firstn (S (S n)) (a :: l)) with (a :: firstn (S n) l). rewrite (IH n x Hn). reflexivity.
Qed.

Lemma lbB_firstn_split : forall P Q (l : list Z), (P <= Q)%nat -> firstn Q l = firstn P l ++ firstn (Q - P) (skipn P l).
Proof.
induction P as [|P IH]; intros Q l HPQ.
- rewrite Nat.sub_0_r. reflexivity.
- destruct Q as [|Q]; [lia|]. destruct l as [|a l].
  + rewrite skipn_nil, !firstn_nil. reflexivity.
  + change (a :: firstn Q l = a :: firstn P l ++ firstn (Q - P) (skipn P l)).
    rewrite (IH Q l) by lia. reflexivity.
Qed.

Lemma lbB_nth_skipn : forall (l : list Z) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
induction l as [|a l IH]; intros n i.
- rewrite skipn_nil, !nth_error_nil. reflexivity.
- destruct n as [|n]; [reflexivity|]. change (nth_error (skipn n l) i = nth_error l (n + i)). apply IH.
Qed.

Lemma lbB_nz_firstn : forall (l : list Z) k, (forall i, (i < k)%nat -> nth_error l i <> Some 0) -> nozero (firstn k l).
Proof.
unfold nozero. induction l as [|a l IH]; intros k H.
- rewrite firstn_nil. constructor.
- destruct k as [|k]; [change (Forall (fun b => b <> 0) (@nil Z)); constructor|].
  change (Forall (fun b => b <> 0) (a :: firstn k l)). constructor.
  + intro E. apply (H 0%nat); [lia|]. rewrite E. reflexivity.
  + apply IH. intros i Hi. exact (H (S i) ltac:(lia)).
Qed.

Lemma lbB_scan_app_z : forall p sk acc q,
  fst (scan sk acc (p ++ 0 :: q)) = fst (scan false [] q) /\
  snd (scan sk acc (p ++ 0 :: q)) = snd (scan sk acc (p ++ [0])) ++ snd (scan false [] q).
Proof.
induction p as [|b p IH]; intros sk acc q.
- cbn [app]. rewrite lbB_scan_zero_fst, !lbB_scan_zero_snd. cbn [scan snd]. split; [reflexivity|].
  destruct (sk || Nat.ltb LINE_LIMIT (length acc))%bool; reflexivity.
- cbn [app]. destruct (Z.eq_dec b 0) as [->|Hb].
  + rewrite lbB_scan_zero_fst, !lbB_scan_zero_snd. destruct (IH false [] q) as [I1 I2].
    split; [exact I1|]. rewrite I2. destruct (sk || Nat.ltb LINE_LIMIT (length acc))%bool; reflexivity.
  + rewrite (scan_nz sk acc b (p ++ 0 :: q) Hb), (scan_nz sk acc b (p ++ [0]) Hb). apply IH.
Qed.

Lemma lbB_dline_len : forall s1 p q, (p <= q < length (dW s1))%nat -> length (dline s1 p q) = (q - p)%nat.
Proof. intros s1 p q H. unfold dline. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. Qed.

Lemma lbB_dline_nz : forall s1 p q,
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) -> nozero (dline s1 p q).
Proof.
intros s1 p q H. unfold dline. apply lbB_nz_firstn. intros i Hi. rewrite lbB_nth_skipn. apply H. lia.
Qed.

Lemma lbB_dW_split : forall s1 p q, (p <= q)%nat -> nth_error (dW s1) q = Some 0 ->
  skipn p (dW s1) = dline s1 p q ++ 0 :: skipn (S q) (dW s1).
Proof.
intros s1 p q HPQ HQ. unfold dline. rewrite <- (lbB_nth_skipn_cons _ _ _ HQ).
rewrite <- (firstn_skipn (q - p) (skipn p (dW s1))) at 1.
rewrite skipn_skipn. replace (q - p + p)%nat with q by lia. reflexivity.
Qed.

Lemma lbB_dW_pre_line : forall s1 p q, (p <= q)%nat -> nth_error (dW s1) q = Some 0 ->
  firstn (S q) (dW s1) = firstn p (dW s1) ++ dline s1 p q ++ [0].
Proof.
intros s1 p q HPQ HQ. rewrite (lbB_firstn_nth_app _ _ _ HQ), (lbB_firstn_split p q _ HPQ), <- app_assoc.
reflexivity.
Qed.

Lemma lbB_scan_pre : forall s1 p r, dbound s1 p ->
  fst (scan (drain_b_c.ds_skip s1) [] (firstn p (dW s1) ++ r)) = fst (scan (dskp s1 p) [] r) /\
  snd (scan (drain_b_c.ds_skip s1) [] (firstn p (dW s1) ++ r)) = drlp s1 p ++ snd (scan (dskp s1 p) [] r).
Proof.
intros s1 p r (HP & HN). destruct p as [|p]; [split; reflexivity|].
assert (HN' : nth_error (dW s1) p = Some 0).
{ destruct HN as [H0|H0]; [discriminate|]. replace p with (S p - 1)%nat by lia. exact H0. }
unfold drlp, dskp. cbn [Nat.eqb]. rewrite (lbB_firstn_nth_app _ _ _ HN'), <- app_assoc. cbn [app].
exact (lbB_scan_app_z (firstn p (dW s1)) (drain_b_c.ds_skip s1) [] r).
Qed.

Lemma lbB_scan_line : forall sk ln r, nozero ln ->
  fst (scan sk [] (ln ++ 0 :: r)) = fst (scan false [] r) /\
  snd (scan sk [] (ln ++ 0 :: r)) =
    (if (sk || Nat.ltb LINE_LIMIT (length ln))%bool then [] else [ln]) ++ snd (scan false [] r).
Proof.
intros sk ln r Hz. rewrite (lbB_scan_nz_app ln sk [] _ Hz). cbn [app].
rewrite lbB_scan_zero_fst, lbB_scan_zero_snd.
split; [reflexivity|]. destruct (sk || Nat.ltb LINE_LIMIT (length ln))%bool; reflexivity.
Qed.

Lemma lbB_drl_line : forall s1 p q, dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
  (forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) ->
  drlp s1 (S q) = drlp s1 p ++ (if (dskp s1 p || Nat.ltb LINE_LIMIT (q - p))%bool then [] else [dline s1 p q]) /\
  drlq s1 p = (if (dskp s1 p || Nat.ltb LINE_LIMIT (q - p))%bool then [] else [dline s1 p q]) ++ drlq s1 (S q).
Proof.
intros s1 p q HB HPQ HQ HNZ.
pose proof (lbB_dline_nz s1 p q HNZ) as Hz. rewrite <- (lbB_dline_len s1 p q HPQ). split.
- unfold drlp at 1. rewrite (lbB_dW_pre_line s1 p q (proj1 HPQ) HQ), (proj2 (lbB_scan_pre s1 p _ HB)).
  rewrite (proj2 (lbB_scan_line (dskp s1 p) (dline s1 p q) [] Hz)). cbn [scan snd]. rewrite app_nil_r.
  reflexivity.
- unfold drlq at 1. rewrite (lbB_dW_split s1 p q (proj1 HPQ) HQ).
  rewrite (proj2 (lbB_scan_line (dskp s1 p) (dline s1 p q) _ Hz)). reflexivity.
Qed.

Lemma lbB_drl : forall s1 p q,
dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) -> dskp s1 p = false ->
(q - p <= LINE_LIMIT)%nat ->
drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] /\
drlq s1 p = dline s1 p q :: drlq s1 (S q) /\
dskp s1 (S q) = false.
Proof.
intros s1 p q HB HPQ HQ HNZ HK HL.
destruct (lbB_drl_line s1 p q HB HPQ HQ HNZ) as [E1 E2].
rewrite HK, (proj2 (Nat.ltb_ge LINE_LIMIT (q - p)) HL) in E1, E2. cbn [orb app] in E1, E2.
split; [exact E1|]. split; [exact E2|reflexivity].
Qed.

Lemma lbB_with_nul_cons : forall l r, with_nul (l :: r) = (l ++ [0]) ++ with_nul r.
Proof. reflexivity. Qed.

Lemma lbB_lrun_one : forall lv mx0 no0 cp0 H0 ka0 l,
  lrun lv mx0 no0 cp0 H0 ka0 [l] =
  (send_line_b_c.send_line_cap lv mx0 no0 cp0 (Z.of_nat (length l) + 1), seen_arr H0 l, seen_ka H0 ka0 l).
Proof.
intros lv mx0 no0 cp0 H0 ka0 l. unfold lrun. cbn [drain_b_c.lines_run fst snd]. rewrite seen_tr_m. reflexivity.
Qed.

Lemma lbB_lrun_app : forall lv mx0 l1 l2 no0 cp0 H0 ka0,
  lrun lv mx0 no0 cp0 H0 ka0 (l1 ++ l2) =
  lrun lv mx0 (no0 + Z.of_nat (length (with_nul l1))) (fst (fst (lrun lv mx0 no0 cp0 H0 ka0 l1)))
    (snd (fst (lrun lv mx0 no0 cp0 H0 ka0 l1))) (snd (lrun lv mx0 no0 cp0 H0 ka0 l1)) l2.
Proof.
intros lv mx0 l1. induction l1 as [|l r IH]; intros l2 no0 cp0 H0 ka0.
- rewrite app_nil_l. change (with_nul []) with (@nil Z). cbn [length Z.of_nat]. rewrite Z.add_0_r. reflexivity.
- assert (C : forall nb cb Hb kb ls, lrun lv mx0 nb cb Hb kb (l :: ls) =
               lrun lv mx0 (nb + (Z.of_nat (length l) + 1))
                 (send_line_b_c.send_line_cap lv mx0 nb cb (Z.of_nat (length l) + 1))
                 (seen_arr Hb l) (seen_ka Hb kb l) ls).
  { intros nb cb Hb kb ls. unfold lrun at 1. cbn [drain_b_c.lines_run fst snd]. rewrite lines_run_m, seen_tr_m.
    reflexivity. }
  rewrite <- app_comm_cons, !C, IH.
  replace (no0 + (Z.of_nat (length l) + 1) + Z.of_nat (length (with_nul r)))
    with (no0 + Z.of_nat (length (with_nul (l :: r))))
    by (rewrite lbB_with_nul_cons, !length_app; cbn [length]; lia).
  reflexivity.
Qed.

Lemma lbB_dlno : forall s1 p q, drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] ->
dlno s1 (S q) = dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1.
Proof.
intros s1 p q E. unfold dlno. rewrite E. unfold with_nul. rewrite map_app, concat_app. cbn [map concat].
rewrite app_nil_r, !length_app. cbn [length]. lia.
Qed.

Lemma lbB_dlrun : forall (cx : dcx) s1 p q, drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] ->
dlrun cx s1 (S q) =
(send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
   (Z.of_nat (length (dline s1 p q)) + 1),
 seen_arr (dlH cx s1 p) (dline s1 p q),
 seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)).
Proof.
intros cx s1 p q E. unfold dlrun at 1. rewrite E, lbB_lrun_app, lbB_lrun_one.
unfold dlno, dloc, dlH, dlka, dlrun. reflexivity.
Qed.

Lemma lbB_dloc : forall (cx : dcx) s1 p q, drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] ->
dloc cx s1 (S q) = send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
  (Z.of_nat (length (dline s1 p q)) + 1).
Proof.
intros cx s1 p q E. change (dloc cx s1 (S q)) with (fst (fst (dlrun cx s1 (S q)))).
rewrite (lbB_dlrun cx s1 p q E). reflexivity.
Qed.

Lemma lbB_dlH : forall (cx : dcx) s1 p q, drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] ->
dlH cx s1 (S q) = seen_arr (dlH cx s1 p) (dline s1 p q).
Proof.
intros cx s1 p q E. change (dlH cx s1 (S q)) with (snd (fst (dlrun cx s1 (S q)))).
rewrite (lbB_dlrun cx s1 p q E). reflexivity.
Qed.

Lemma lbB_dlka : forall (cx : dcx) s1 p q, drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] ->
dlka cx s1 (S q) = seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q).
Proof.
intros cx s1 p q E. change (dlka cx s1 (S q)) with (snd (dlrun cx s1 (S q))).
rewrite (lbB_dlrun cx s1 p q E). reflexivity.
Qed.

Lemma lbB_seen_tr_none : forall H ka l j ha ks, gesture l = None ->
drain_b_c.seen_tr H ka l j ha ks = ([], ka, (ha, ks)).
Proof. intros H ka l j ha ks Hg. unfold drain_b_c.seen_tr. rewrite Hg. reflexivity. Qed.

Lemma lbB_seen_arr_none : forall H l, gesture l = None -> seen_arr H l = H.
Proof. intros H l Hg. unfold seen_arr. rewrite Hg. reflexivity. Qed.

Lemma lbB_seen_ka_none : forall H ka l, gesture l = None -> seen_ka H ka l = ka.
Proof. intros H ka l Hg. unfold seen_ka. rewrite (lbB_seen_tr_none H ka l _ _ _ Hg). reflexivity. Qed.

Lemma lbB_upds_none : forall G ls l, gesture l = None -> upds G (ls ++ [l]) = upds G ls.
Proof.
intros G ls l Hg. unfold upds. rewrite fold_left_app. cbn [fold_left]. unfold RelayModel.upd. rewrite Hg.
reflexivity.
Qed.

Lemma lbB_lcore_none : forall cx s1 D sent kl kl' l H ka no oc n sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl,
gesture l = None -> kl' = kl ++ [l] ->
LCORE B MT MMAX RG cx s1 D sent kl H ka no oc (Z.of_nat (S n)) sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
LCORE B MT MMAX RG cx s1 D sent kl' H ka no oc (Z.of_nat n) sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.
Proof.
intros cx s1 D sent kl kl' l H ka no oc n sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl Hg Ekl HL.
subst kl'.
unfold LCORE in HL |- *. cbv zeta in HL |- *.
destruct HL as (HMEM & HLINK & HSAME & HHIST & HRST & HBUD).
refine (conj HMEM (conj HLINK (conj HSAME (conj _ (conj HRST HBUD))))).
unfold DHIST in HHIST |- *.
destruct HHIST as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11).
rewrite (lbB_upds_none _ kl l Hg).
refine (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj X8 (conj X9 (conj _ X11)))))))))).
lia.
Qed.

Lemma lb_mk_dln : forall cx s1 D p q regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl W1 regs2 m2 md2,
DBASE B MT MMAX RG cx ->
dregs_line RG cx regs1 W1 m1 ->
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) ->
dinband (re_buf e1) (re_cap e1) -> 0 < re_cap e1 ->
dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) ->
dskp s1 p = false -> (q - p <= LINE_LIMIT)%nat ->
LCORE B MT MMAX RG cx s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
dsfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (drlq s1 (S q)) jb o ha ks tl ->
gesture (dline s1 p q) = None ->
spZ regs2 = spZ regs1 ->
getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 -> getr regs2 21 = getr regs1 21 ->
getr regs2 20 = getr regs1 20 -> getr regs2 22 = getr regs1 22 -> getr regs2 27 = getr regs1 27 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 23 = getr regs1 23 ->
lb_keep cx W1 m1 m2 ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k1 ->
DLN B MT MMAX RG cx s1 D (S q) W1 (cfg_at SEGS (BASE + A_dr_next) regs2 m2 md2).
Proof.
intros cx s1 D p q regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl W1 regs2 m2 md2
  HB HR H23 Hdin Hcap0 Hbnd Hpq Hnul Hnoz Hskp Hlim HL HF Hg Hsp H3 H4 H21 H20 H22 H27 H8 H9 H18 H23' HK HJ2.
pose proof (lb_lcore_keep cx s1 D _ _ _ _ _ _ _ _ ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2
  HB HL HK HJ2) as HL2.
destruct (lbB_drl s1 p q Hbnd Hpq Hnul Hnoz Hskp Hlim) as (E1 & E2 & E3).
pose proof (lbB_dlno s1 p q E1) as Edlno.
pose proof (lbB_dloc cx s1 p q E1) as Edloc.
assert (EdlH : dlH cx s1 (S q) = dlH cx s1 p)
  by (rewrite (lbB_dlH cx s1 p q E1); exact (lbB_seen_arr_none _ _ Hg)).
assert (Edlka : dlka cx s1 (S q) = dlka cx s1 p)
  by (rewrite (lbB_dlka cx s1 p q E1); exact (lbB_seen_ka_none _ _ _ Hg)).
unfold dsfut in HF. cbv zeta in HF. destruct HF as (tl2 & HF1 & HF2).
rewrite (lbB_seen_tr_none _ _ _ _ _ _ Hg) in HF1, HF2.
rewrite (lbB_seen_arr_none _ _ Hg), (lbB_seen_ka_none _ _ _ Hg) in HF1.
cbn [fst snd app] in HF1, HF2.
change (RelayRunT.nret YO0i.sptr []) with 0%nat in HF1. rewrite Nat.add_0_r in HF1.
subst tl2.
exists regs2, ly1, S1, m2, md2, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
split; [reflexivity|].
split; [exact (lb_dregs_keep cx regs1 regs2 W1 m1 m2 HB HR Hsp H3 H4 H21 H20 H22 H27 H8 H9 H18 HK)|].
split; [rewrite H23', H23; f_equal; lia|].
split; [exact Hdin|]. split; [exact Hcap0|].
split; [split; [lia | right; replace (S q - 1)%nat with q by lia; exact Hnul]|].
split; [lia|].
split.
{ unfold DLC. rewrite EdlH, Edlka, Edlno, Edloc, E3, E1.
  apply (lbB_lcore_none cx s1 D _ (lines (dSTR cx) D ++ drlp s1 p) _ (dline s1 p q));
    [exact Hg | apply app_assoc | exact HL2]. }
rewrite Edlno, Edloc, EdlH, Edlka. exact HF1.
Qed.

Lemma lb_mk_dgs : forall cx s1 D p q regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl W1 regs2 m2 md2
  (kd : gkind) (jj : nat) (bg : Z),
DBASE B MT MMAX RG cx ->
dregs_line RG cx regs1 W1 m1 ->
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) -> getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) ->
dinband (re_buf e1) (re_cap e1) -> 0 < re_cap e1 ->
dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) ->
dskp s1 p = false -> (q - p <= LINE_LIMIT)%nat ->
LCORE B MT MMAX RG cx s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
dsfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (drlq s1 (S q)) jb o ha ks tl ->
spZ regs2 = spZ regs1 ->
getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 -> getr regs2 21 = getr regs1 21 ->
getr regs2 20 = getr regs1 20 -> getr regs2 22 = getr regs1 22 -> getr regs2 27 = getr regs1 27 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 ->
getr regs2 19 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj) ->
getr regs2 26 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj + 1) -> getr regs2 25 = w64 bg ->
0 <= bg < 2 ^ 64 -> (bg = 0 <-> kd = GBegin) ->
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) -> (13 < jj < q - p)%nat ->
lb_keep cx W1 m1 m2 ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k1 ->
DGS B MT MMAX RG cx s1 D p q W1 (cfg_at SEGS (BASE + A_dr_seen) regs2 m2 md2).
Proof.
intros cx s1 D p q regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl W1 regs2 m2 md2 kd jj bg
  HB HR H23 H24 Hdin Hcap0 Hbnd Hpq Hnul Hnoz Hskp Hlim HL HF Hsp H3 H4 H21 H20 H22 H27 H8 H9 H18 H23' H24'
  H19 H26 H25 Hbg Hbgk Hges Hjj HK HJ2.
pose proof (lb_lcore_keep cx s1 D _ _ _ _ _ _ _ _ ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2
  HB HL HK HJ2) as HL2.
exists regs2, ly1, S1, m2, md2, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl, kd, jj, bg.
split; [reflexivity|].
split; [exact (lb_dregs_keep cx regs1 regs2 W1 m1 m2 HB HR Hsp H3 H4 H21 H20 H22 H27 H8 H9 H18 HK)|].
split; [rewrite H23'; exact H23|].
split; [rewrite H24'; exact H24|].
split; [exact H19|]. split; [exact H26|]. split; [exact H25|]. split; [exact Hbg|]. split; [exact Hbgk|].
split; [exact Hdin|]. split; [exact Hcap0|].
split; [exact Hges|]. split; [exact Hjj|].
split; [exact Hbnd|]. split; [exact Hpq|]. split; [exact Hnul|]. split; [exact Hnoz|].
split; [exact Hskp|]. split; [exact Hlim|].
split; [exact HL2 | exact HF].
Qed.

Lemma lb_scr_lo : forall cx, DBASE B MT MMAX RG cx ->
alloc_ceiling + 8 <= dsp0 cx - DRAIN_FRAME - 2 * ESTACK /\ dsp0 cx <= 2 ^ 47 /\ dsp0 cx mod 16 = 0.
Proof.
intros cx HB. pose proof HB as (Hafn & _). pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (DRAIN_STK = 16880) by reflexivity. unfold dsp0, DRAIN_FRAME, ESTACK. lia.
Qed.

Lemma lb_keep_refl : forall cx W m, lb_keep cx W m m.
Proof. intros cx W m. split; [intros; reflexivity | intros x H; exact H]. Qed.

Lemma lb_keep_run : forall cx W m1 m2 m3 E rs, lb_keep cx W m1 m2 ->
frame_of E rs (mrestrict (w_H W) m2) (mrestrict (w_H W) m3) ->
mem_grows (mrestrict (w_H W) m2) (mrestrict (w_H W) m3) ->
(forall a, ~ in_wrange E rs a) -> lb_keep cx W m1 m3.
Proof.
intros cx W m1 m2 m3 E rs [K1 P1] HF HGr HW. split.
- intros x Hx Hs. rewrite (aview_kept_out E rs (w_H W) m2 m3 HF x Hx (HW x)). exact (K1 x Hx Hs).
- intros x Hp. apply (apresent_grows _ _ _ _ HGr). exact (P1 x Hp).
Qed.

Lemma lb_keep_call : forall cx W m1 m2 m3, lb_keep cx W m1 m2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ False -> ~ (dsp0 cx + - DRAIN_FRAME - 2 * ESTACK <= a < dsp0 cx + - DRAIN_FRAME) ->
  aview SEGS (w_H W) m3 a = aview SEGS (w_H W) m2 a) ->
(forall a, apresent (w_H W) m2 a -> apresent (w_H W) m3 a) -> lb_keep cx W m1 m3.
Proof.
intros cx W m1 m2 m3 [K1 P1] K2 P2. split.
- intros x Hx Hs. rewrite (K2 x Hx (fun f => f) ltac:(intros Hs'; apply Hs; lia)). exact (K1 x Hx Hs).
- intros x Hp. exact (P2 x (P1 x Hp)).
Qed.

Lemma lb_keep_low : forall cx W m1 m2 a, DBASE B MT MMAX RG cx -> lb_keep cx W m1 m2 -> 0 <= a < alloc_ceiling + 8 ->
aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a.
Proof.
intros cx W m1 m2 a HB [K _] Ha. pose proof (lb_scr_lo cx HB) as (L & _). pose proof asan_consts as (C1 & _).
apply K; lia.
Qed.

Lemma lb_keep_rom : forall cx W m1 m2, DBASE B MT MMAX RG cx -> lb_keep cx W m1 m2 ->
rom_view SEGS W m1 -> rom_view SEGS W m2.
Proof.
intros cx W m1 m2 HB HK HR a Ha. pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (Hl : 0 <= a < kLowMemEnd).
{ destruct Ha as (sg & Hsg & _ & Hr). exact (pa_segs_low a ltac:(exists sg; split; [exact Hsg | exact Hr])). }
rewrite (lb_keep_low cx W m1 m2 a HB HK ltac:(lia)). exact (HR a Ha).
Qed.

Lemma lb_garr8_vis : forall (W : world SEGS) m base l a, garr8 SEGS (arm W m) base l ->
base <= a < base + Z.of_nat (length l) -> aview SEGS (w_H W) m a <> None.
Proof.
intros W m base l a Hg Ha.
replace a with (base + Z.of_nat (Z.to_nat (a - base))) by lia.
unfold aview. change (mrestrict (w_H W) m) with (arm W m).
rewrite (garr8_mbyte SEGS (arm W m) base l (Z.to_nat (a - base)) Hg ltac:(lia)). cbn [option_map]. discriminate.
Qed.

Lemma lb_tail_arith : forall b c t a, b mod 16 = 0 -> (c = 8192 \/ c = 16384) -> b <= t < b + c ->
t < a < t - t mod 8 + 8 -> a < b + c.
Proof.
intros b c t a Hb Hc Ht Ha.
pose proof (Z.div_mod t 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound t 8 ltac:(lia)) as M1.
pose proof (Z.div_mod b 16 ltac:(lia)) as D2. rewrite Hb in D2. lia.
Qed.

Lemma lb_keep_byte : forall cx W m1 m2 a, DBASE B MT MMAX RG cx -> lb_keep cx W m1 m2 -> 0 <= a < alloc_ceiling + 8 ->
abyte_kept W m1 W m2 a.
Proof.
intros cx W m1 m2 a HB HK Ha. split; [exact (lb_keep_low cx W m1 m2 a HB HK Ha)|].
unfold arm. apply writable_kept. intros Hp. exact (proj2 HK a Hp).
Qed.

Lemma lb_hull_sub : forall rd y n n', shadow_hull_vis rd y n -> 0 < n' <= n -> shadow_hull_vis rd y n'.
Proof.
intros rd y n n' H Hn s Hs. apply H.
assert (shadow_addr (y + n' - 1) / 8 <= shadow_addr (y + n - 1) / 8)
  by (apply Z.div_le_mono; [lia | apply shadow_mono; lia]).
lia.
Qed.
(* range_addressable of a literal's prefix, from ashp's range_addressable over its whole bytes (dlit_at's third
   conjunct, W_drain_cx.v; it replaced a false zero-shadow conjunct the three sites below used to go through) *)
Lemma lb_ra_sub : forall rd o a n n', range_addressable rd o a n -> 0 <= n' <= n -> range_addressable rd o a n'.
Proof. intros rd o a n n' H Hn x Hx. apply H. lia. Qed.

Lemma lb_amr_img : forall a n, 0x10000 <= a -> 0 <= n -> a + n <= IMG_TOP -> amem_range a n.
Proof. intros a n H1 H2 H3. unfold amem_range, kLowMemEnd, IMG_TOP in *. left. lia. Qed.

Lemma lb_lit_bytes : Forall (fun b => 0 <= b < 256) K_GESTURE /\ Forall (fun b => 0 <= b < 256) W_BEGIN /\
Forall (fun b => 0 <= b < 256) W_END.
Proof. unfold K_GESTURE, W_BEGIN, W_END. repeat split; repeat (apply Forall_cons; [lia|]); apply Forall_nil. Qed.

Lemma lb_lit_nz : (forall i, (i < length K_GESTURE)%nat -> nth i K_GESTURE 0 <> 0) /\
(forall i, (i < length W_BEGIN)%nat -> nth i W_BEGIN 0 <> 0) /\ (forall i, (i < length W_END)%nat -> nth i W_END 0 <> 0).
Proof.
unfold K_GESTURE, W_BEGIN, W_END. cbn [length].
repeat split; intros i Hi; (do 13 (destruct i as [|i]; [cbn; lia|])); cbn [length] in Hi; lia.
Qed.

Lemma lb_lit_range : forall i l, dlit_at B i l -> (0 < length l)%nat ->
0x10000 <= VAL (A_OBJ i) /\ VAL (A_OBJ i) + Z.of_nat (length l) <= IMG_TOP.
Proof.
intros i l (_ & HR & _) Hl.
assert (I1 : in_img SEGS (VAL (A_OBJ i))).
{ destruct (HR (VAL (A_OBJ i)) ltac:(lia)) as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr]. }
assert (I2 : in_img SEGS (VAL (A_OBJ i) + Z.of_nat (length l) - 1)).
{ destruct (HR (VAL (A_OBJ i) + Z.of_nat (length l) - 1) ltac:(lia)) as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr]. }
pose proof (pa_img_range _ I1). pose proof (pa_img_range _ I2). unfold IMG_TOP. lia.
Qed.

Lemma lb_br_ne0 : forall E n w, ew E n = w ->
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = negb (bv_unsigned w =? 0).
Proof.
intros E n w H. rewrite branch_ne_U. pose proof (bv_unsigned_in_range 64 w) as R.
change (bv_modulus 64) with (2 ^ 64) in R.
rewrite (U_atom E n (bv_unsigned w)); [rewrite U_lit by lia; reflexivity | rewrite H; symmetry; apply Z_to_bv_bv_unsigned | exact R].
Qed.

Lemma lb_br_eq0 : forall E n w, ew E n = w ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (bv_unsigned w =? 0).
Proof.
intros E n w H. rewrite branch_eq_U. pose proof (bv_unsigned_in_range 64 w) as R.
change (bv_modulus 64) with (2 ^ 64) in R.
rewrite (U_atom E n (bv_unsigned w)); [rewrite U_lit by lia; reflexivity | rewrite H; symmetry; apply Z_to_bv_bv_unsigned | exact R].
Qed.

Lemma lb_br_eq_lit : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = (v =? c).
Proof.
intros E n v c H Hv Hc. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit by lia. reflexivity.
Qed.

Lemma lb_w0 : forall w : bv 64, bv_unsigned w = 0 <-> w = w64 0.
Proof.
intros w. split.
- intros H. apply bv_eq. rewrite H. reflexivity.
- intros ->. reflexivity.
Qed.

Lemma lb_br_ne_byte : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> 0 <= c < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SExt false 8 (SOff n 0))) (sv_denot E (SLit c)) = negb (v =? c).
Proof.
intros E n v c H Hv Hc. rewrite branch_ne_U, U_zext, (U_atom E n v H) by lia. rewrite U_lit by lia.
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma lb_br_eq_ao : forall E n m v u c, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 u ->
0 <= v < 2 ^ 64 -> 0 <= u < 2 ^ 64 -> 0 <= u + c < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SOff m c)) = (v =? u + c).
Proof.
intros E n m v u c H1 H2 R1 R2 R3. rewrite branch_eq_U, (U_atom E n v H1 R1), (U_atom_off E m u c H2 R2 R3).
reflexivity.
Qed.

Lemma lb_ae_ewset : forall k E0 E n v, (k <= n)%nat -> env_agree k E0 E -> env_agree k E0 (ewset E n v).
Proof.
intros k E0 E n v Hk [HA HD]. split; [|exact HD].
intros m Hm. rewrite ew_ewset_other by lia. apply HA. exact Hm.
Qed.

Lemma lb_nth13 : forall s1 p q, (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
(13 <= q - p)%nat -> nth 13 (dline s1 p q) 0 = nth (p + 13) (dW s1) 0.
Proof.
intros s1 p q Hpq Hq H13. unfold dline.
destruct (Nat.eq_dec (q - p) 13) as [E|E].
- rewrite E. rewrite nth_overflow by (rewrite firstn_length_le by (rewrite length_skipn; lia); lia).
  replace (p + 13)%nat with q by lia. symmetry. apply nth_error_nth. exact Hq.
- rewrite nth_firstn, (proj2 (Nat.ltb_lt 13 (q - p))) by lia. rewrite nth_skipn. reflexivity.
Qed.


Definition lb_Bx : sv := SOff 33 0.
Definition lb_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition lb_CEIL : Z := 140737479966720.
Definition lb_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (33%nat, mkAF SB SB 0); (24%nat, mkAF 4096 lb_CEIL 0) ] [] [].
Definition ss_lb : sstate := mkSS A_dr_send sr_atoms [] None lb_facts.
Definition lb_extra (v13 : Z) : list word := map (Z_to_bv 64) [v13; SHADOW_OFF].

Lemma lb_entry : forall (W : world SEGS) regs m v13 sp x,
spZ regs = sp -> 2 ^ 46 <= sp -> sp <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs 24 = w64 x -> 4096 <= x <= lb_CEIL ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (lb_extra v13))) ss_lb
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_send)) m (seg_rom SEGS))).
Proof.
intros W regs m v13 sp x Hsp H1 H2 H3 R24 Hx.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (lb_extra v13))).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n r Hr)).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (U33 : bv_unsigned (ew E 33) = SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ 1); cbn [lb_extra map nth];
      rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity).
assert (U24 : bv_unsigned (ew E 24) = x)
  by (rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); rewrite R24; apply unsigned_lit_small; unfold lb_CEIL in *; lia).
unfold ss_lb. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [lb_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U33, U24. unfold SB, lb_CEIL in *.
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.


Ltac lbin := cbn; repeat (first [left; reflexivity | right]).
Ltac lb_regs HS HAEx :=
  let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    lazymatch type of HAEx with env_agree _ (Ereg ?R0 ?X0) _ =>
      let HAEz := fresh "HAEz" in
      assert (HAEz : env_agree 32 (Ereg R0 X0) Ev)
        by (first [exact HAEx | repeat (first [apply lb_ae_ewset; [lia|] | apply env_agree_havoc_ge; [cbv; lia|]]);
                   first [exact HAEx | eassumption]]);
      exact (regs_kept_of_st_ok_pi Ev _ _ R0 X0 [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 27]%bv HS HAEz
        ltac:(vm_compute; reflexivity) r Hr)
    end end.
Ltac lb_ewg := repeat (first [rewrite ew_ewset_other by lia | rewrite YN3v.ew_havoc_old by (cbv; lia)]).
(* ---- drain's frame, seated as a region (B reloads s5 / s6 / s4 from it and reads the shadow base 240(sp)) ---- *)
Definition lb_frame_region : YP09.region := YP09.mkRegion (Some 2%nat) 128 248 128 128
  [ YP09.mkChunk 128 (CVal 8 (SOff 20 0)); YP09.mkChunk 136 (CVal 8 (SOff 22 0));
    YP09.mkChunk 144 (CVal 8 (SOff 21 0)); YP09.mkChunk 240 (CVal 8 (SOff 33 0)) ].

Ltac lb_awr1 := apply awr_ok_x_cons; [|apply awr_ok_x_nil];
  cbn [lb_frame_region YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; exfalso; clear - Ha; lia.
Ltac lb_nowr := let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [lb_frame_region YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia|]); destruct Hin.

Lemma lb_frame_region_ok : forall cx E m, DBASE B MT MMAX RG cx ->
bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME ->
ew E 20 = Z_to_bv 64 (dxSA cx + 16) -> ew E 21 = Z_to_bv 64 (dxSA cx) -> ew E 22 = Z_to_bv 64 (dxSA cx + 24) ->
ew E 33 = Z_to_bv 64 SHADOW_OFF ->
0 <= dxSA cx /\ dxSA cx + 24 < 2 ^ 64 ->
val_mem SEGS m (dsp0 cx - DRAIN_FRAME + 128) 8 (dxSA cx + 16) ->
val_mem SEGS m (dsp0 cx - DRAIN_FRAME + 136) 8 (dxSA cx + 24) ->
val_mem SEGS m (dsp0 cx - DRAIN_FRAME + 144) 8 (dxSA cx) ->
val_mem SEGS m (dsp0 cx - DRAIN_FRAME + 240) 8 SHADOW_OFF ->
region_ok SEGS E m lb_frame_region.
Proof.
intros cx E m HB Usp E20 E21 E22 E33 HSA V128 V136 V144 V240.
pose proof (lb_scr_lo cx HB) as (SL & SH47 & SAL). pose proof asan_consts as (C1 & _).
assert (EF : DRAIN_FRAME = 352) by reflexivity. assert (EE : ESTACK = 4096) by reflexivity.
unfold region_ok, lb_frame_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val SEGS E m (dsp0 cx - DRAIN_FRAME) 128 8 (SOff 20 0) (dxSA cx + 16));
    [exact (den_atom0 E 20 _ E20 ltac:(lia)) | cbn; lia | cbn; lia | exact V128].
- apply (chunk_ok_val SEGS E m (dsp0 cx - DRAIN_FRAME) 136 8 (SOff 22 0) (dxSA cx + 24));
    [exact (den_atom0 E 22 _ E22 ltac:(lia)) | cbn; lia | cbn; lia | exact V136].
- apply (chunk_ok_val SEGS E m (dsp0 cx - DRAIN_FRAME) 144 8 (SOff 21 0) (dxSA cx));
    [exact (den_atom0 E 21 _ E21 ltac:(lia)) | cbn; lia | cbn; lia | exact V144].
- apply (chunk_ok_val SEGS E m (dsp0 cx - DRAIN_FRAME) 240 8 (SOff 33 0) SHADOW_OFF);
    [exact (den_atom0 E 33 _ E33 ltac:(unfold SHADOW_OFF; lia)) | cbn; unfold SHADOW_OFF; lia
    | cbn; lia | exact V240].
Qed.

Lemma lb_frame_disj : forall cx E X, bv_unsigned (ew E 24) = X -> bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME ->
X + 14 <= dsp0 cx - DRAIN_FRAME + 128 ->
all_disjoint E lb_frame_region [YP09.mkRegion (Some 24%nat) 13 14 0 0 [YP09.mkChunk 13 (CVal 1 (SOff 32 0))]].
Proof.
intros cx E X H24 Hsp Hlt. cbn [all_disjoint]. split; [|exact I].
unfold extent_disjoint, extent_of_region, lb_frame_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd]. rewrite H24, Hsp. lia.
Qed.

Ltac lb_awr2 := apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]];
  cbn [lb_frame_region YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; exfalso; clear - Ha; lia.

Theorem dr_lineb_of :
(forall ly S W mem md, AR SEGS B ly S W mem md -> shadow_hull_vis (aview SEGS (w_H W) mem) (VAL (A_OBJ 18)) 14) ->
(forall ly S W mem md, AR SEGS B ly S W mem md -> shadow_hull_vis (aview SEGS (w_H W) mem) (VAL (A_OBJ 20)) 6) ->
(forall ly S W mem md, AR SEGS B ly S W mem md -> shadow_hull_vis (aview SEGS (w_H W) mem) (VAL (A_OBJ 21)) 4) ->
dr_lineb_stmt B MT MMAX RG.
Proof.
intros HV21 HV23 HV24 cx s1 D p q W1 c1 HB HLS KDLN KDGS.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HLS as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & oo & ha & ks & tl
  & Hc1 & Hregs & H23 & H24 & Hdin & Hcap0 & Hbnd & Hpq & Hnulq & Hnoq & Hskp & Hlim & HLC & Hfut).
pose proof Hregs as (Hsp & Hr3 & Hr4 & Hr21 & Hr20 & Hr22 & Hr27 & Hr8 & Hr9 & Hr18 & HFRM).
pose proof HLC as (HMEM & HLINK & HSAME & HHIST & HRST & HBUD).
pose proof HMEM as (HJ & HROM & HPRES & HFRAMES & HFR2 & HGARR & HAWR & HEOK & HSRC & HOTH & HKEPT & HOUT & HLIVE & HPERM).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HB as (Hafn & HBa0 & Htbl & HSAlo & HSAhi & _).
pose proof Hafn as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : DRAIN_STK = 16880) by reflexivity.
assert (HFRAME : DRAIN_FRAME = 352) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HEOK as (Heof & Hskip & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedr & Hbufc & Hnheld & Hheld & HND1 & HND2 & Hkeys).
assert (HUeq : bzs (re_U e1) = dW s1) by (destruct HLINK as (_ & Hu & _); exact Hu).
assert (Hdwlen : Z.of_nat (length (dW s1)) = re_used e1)
  by (rewrite <- HUeq; unfold bzs; rewrite length_map; exact HUlen).
destruct Hbufc as [(Hc0 & _) | (_ & Hbufin & Hjunk & Hbg)]; [lia|].
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hbufin)
  as (HB16 & HB4096 & HBceil & HBia & HBpres & _).
assert (RQB : req_size (re_cap e1) = re_cap e1)
  by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQB in HBceil, HBia.
set (v13 := nth (p + 13) (dW s1) 0).
pose proof (lb_scr_lo cx HB) as (SL & SH47 & SAL).
assert (HSAr : 0 <= dxSA cx /\ dxSA cx + 24 < 2 ^ 64).
{ assert (Htbl1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
    by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
  pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as (_ & Hrq).
  pose proof (lbB_blk_low ly1 S1 W1 m1 md1 (dxG cx) ATABLE (dxSA cx) HAR Htbl1 ltac:(lia)
    ltac:(unfold AENT in *; lia)) as Hl0.
  pose proof (lbB_blk_low ly1 S1 W1 m1 md1 (dxG cx) ATABLE (dxSA cx + 24) HAR Htbl1 ltac:(lia)
    ltac:(unfold AENT in *; lia)) as Hl1.
  pose proof asan_consts as (C1' & _). unfold lbB_low in Hl0, Hl1. split; lia. }
assert (HLl : length (bzs (re_U e1 ++ re_junk e1)) = Z.to_nat (re_cap e1))
  by (unfold bzs; rewrite length_map, length_app; lia).
assert (HLapp : bzs (re_U e1 ++ re_junk e1) = dW s1 ++ bzs (re_junk e1))
  by (unfold bzs in *; rewrite map_app, HUeq; reflexivity).
assert (HLEN : length (dline s1 p q) = (q - p)%nat)
  by (unfold dline; rewrite firstn_length_le; [reflexivity|]; rewrite length_skipn; lia).
assert (LN0 : lb_line (aview SEGS (w_H W1) m1) (re_buf e1 + Z.of_nat p) (dline s1 p q)).
{ pose proof (lb_line_of_garr8 W1 m1 (re_buf e1) (bzs (re_U e1 ++ re_junk e1)) p q Hbg) as LN.
  rewrite HLapp in LN.
  replace (firstn (q - p) (skipn p (dW s1 ++ bzs (re_junk e1)))) with (dline s1 p q) in LN.
  - apply LN; [rewrite length_app; lia | rewrite nth_error_app1 by lia; exact Hnulq |].
    intros i Hi. rewrite nth_error_app1 by lia. exact (Hnoq i Hi).
  - unfold dline. rewrite skipn_app, firstn_app, length_skipn.
    replace (q - p - (length (dW s1) - p))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. reflexivity. }
assert (KN : forall regsF mF mdF, gesture (dline s1 p q) = None ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 27]%bv -> getr regsF r = getr regs1 r) ->
  lb_keep cx W1 m1 mF ->
  @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 mF mdF k1 ->
  SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_next) regsF mF mdF) (dPOST B MT RG cx)).
{ intros regsF mF mdF GN HR KF HJF. apply KDLN.
  pose proof (HR 2%bv ltac:(lbin)) as R2. pose proof (HR 3%bv ltac:(lbin)) as R3.
  pose proof (HR 4%bv ltac:(lbin)) as R4. pose proof (HR 8%bv ltac:(lbin)) as R8.
  pose proof (HR 9%bv ltac:(lbin)) as R9. pose proof (HR 18%bv ltac:(lbin)) as R18.
  pose proof (HR 20%bv ltac:(lbin)) as R20. pose proof (HR 21%bv ltac:(lbin)) as R21.
  pose proof (HR 22%bv ltac:(lbin)) as R22.
  pose proof (HR 23%bv ltac:(lbin)) as R23. pose proof (HR 27%bv ltac:(lbin)) as R27.
  exact (lb_mk_dln cx s1 D p q regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl W1 regsF mF mdF
    HB Hregs H23 Hdin Hcap0 Hbnd Hpq Hnulq Hnoq Hskp Hlim HLC Hfut GN ltac:(unfold spZ; rewrite R2; reflexivity)
    R3 R4 R21 R20 R22 R27 R8 R9 R18 R23 KF HJF). }
assert (KG : forall regsF mF mdF (kd : gkind) (jj : nat) (bg : Z),
  gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) -> (13 < jj < q - p)%nat ->
  getr regsF 19 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj) ->
  getr regsF 26 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj + 1) -> getr regsF 25 = w64 bg ->
  0 <= bg < 2 ^ 64 -> (bg = 0 <-> kd = GBegin) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 27]%bv -> getr regsF r = getr regs1 r) ->
  lb_keep cx W1 m1 mF ->
  @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 mF mdF k1 ->
  SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_seen) regsF mF mdF) (dPOST B MT RG cx)).
{ intros regsF mF mdF kd jj bg GS Hjj H19 H26 H25 Hbgr Hbk HR KF HJF. apply KDGS.
  pose proof (HR 2%bv ltac:(lbin)) as R2. pose proof (HR 3%bv ltac:(lbin)) as R3.
  pose proof (HR 4%bv ltac:(lbin)) as R4. pose proof (HR 8%bv ltac:(lbin)) as R8.
  pose proof (HR 9%bv ltac:(lbin)) as R9. pose proof (HR 18%bv ltac:(lbin)) as R18.
  pose proof (HR 20%bv ltac:(lbin)) as R20. pose proof (HR 21%bv ltac:(lbin)) as R21.
  pose proof (HR 22%bv ltac:(lbin)) as R22.
  pose proof (HR 23%bv ltac:(lbin)) as R23. pose proof (HR 24%bv ltac:(lbin)) as R24.
  pose proof (HR 27%bv ltac:(lbin)) as R27.
  exact (lb_mk_dgs cx s1 D p q regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl W1 regsF mF mdF
    kd jj bg HB Hregs H23 H24 Hdin Hcap0 Hbnd Hpq Hnulq Hnoq Hskp Hlim HLC Hfut ltac:(unfold spZ; rewrite R2; reflexivity)
    R3 R4 R21 R20 R22 R27 R8 R9 R18 R23 R24 H19 H26 H25 Hbgr Hbk GS Hjj KF HJF). }
set (X := re_buf e1 + Z.of_nat p) in *.
pose proof (lb_entry W1 regs1 m1 v13 (dsp0 cx - DRAIN_FRAME) X Hsp
  ltac:(unfold DRAIN_FRAME, ESTACK in *; lia) ltac:(unfold DRAIN_FRAME in *; lia)
  ltac:(unfold DRAIN_FRAME in *; rewrite Zminus_mod, SAL; reflexivity)
  H24 ltac:(unfold lb_CEIL, X in *; lia)) as HS.
remember (Eimg (Ereg regs1 (lb_extra v13))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (lb_extra v13)) E)
  by (rewrite HE; split; [intros mm Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 v13)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (SHOK : sh_ok SEGS lb_Bx [] E (mrestrict (w_H W1) m1)) by constructor.
clear HE.
rewrite Hc1. unfold cfg_at. change (w64 (BASE + A_dr_send)) with (Z_to_bv 64 (BASE + A_dr_send)).
paj_run_tok RUN HS HJ SHOK lb_Bspan; [apply awr_ok_x_nil|].
rename HFr into FR0; rename HG0 into GR0; clear HF.
assert (KP0 : lb_keep cx W1 m1 (ms_mem ms)).
{ apply (lb_keep_run cx W1 m1 m1 (ms_mem ms) E []); [apply lb_keep_refl | exact FR0 | exact GR0 |].
  intros a (r & Hin & _). destruct Hin. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
pose proof (lb_line_ext _ _ X (dline s1 p q) LN0
  (fun a Ha => lb_keep_low cx W1 m1 (ms_mem ms) a HB KP0 ltac:(rewrite HLEN in Ha; unfold X in *; lia))) as LN1.
assert (HQC : re_buf e1 + Z.of_nat q < re_buf e1 + re_cap e1) by lia.
eapply SRr_bind.
{ eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 ([] : list (Z * Z)) (2 * ESTACK) (SIGMA WS_strrchr)
      (fun _ => False) _ W1 (ms_regs ms) (ms_mem ms) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx)
      (dxmem cx) (dxmd cx) ([] : list (Z * Z)) ly1 S1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ);
  [ unfold spZ at 1; rewrite Q2, Usp; lia
  | reflexivity
  | unfold DRAIN_FRAME; lia
  | unfold ESTACK; lia
  | unfold ESTACK, DRAIN_FRAME; rewrite WS; lia
  | rewrite Q3, (EREG 3%nat 3%bv), Hr3 by (first [lia | reflexivity]); exact Hgp
  | rewrite Q4, (EREG 4%nat 4%bv), Hr4 by (first [lia | reflexivity]); exact Htp
  | exact Q1
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | intros _; right; intros []
  | intros a []
  | intros a []
  | ].
  intros HPRE HSC.
  eapply (ASTRRCHR ly1 S1 W1 (ms_regs ms) (ms_mem ms) _ X 32 (Z.of_nat (q - p)) HPRE HSC).
  - rewrite Q10, (EREG 24%nat 24%bv), H24 by (first [lia | reflexivity]). reflexivity.
  - rewrite Q11. reflexivity.
  - lia.
  - unfold X; lia.
  - lia.
  - unfold X; lia.
  - unfold LINE_LIMIT in *; lia.
  - pose proof (lb_line_first_byte W1 (ms_mem ms) X (dline s1 p q) (Z.of_nat (q - p) + 1) LN1 ltac:(lia)) as FB.
    rewrite HLEN in FB. replace (Z.min (Z.of_nat (q - p) + 1) (Z.of_nat (q - p))) with (Z.of_nat (q - p)) in FB by lia.
    exact FB.
  - intros a Ha. split.
    + apply (lb_line_vis _ X (dline s1 p q) a LN1). rewrite HLEN. lia.
    + unfold spZ. rewrite Q2, Usp. unfold X in *. lia.
  - intros a Ha. rewrite (lb_keep_low cx W1 m1 (ms_mem ms) a HB KP0) by (unfold X in *; lia).
    apply (lb_garr8_vis W1 m1 (re_buf e1) (bzs (re_U e1 ++ re_junk e1)) a Hbg). rewrite HLl.
    pose proof (lb_tail_arith (re_buf e1) (re_cap e1) (X + Z.of_nat (q - p)) a HB16
      ltac:(destruct Hcapr as [Hc|[Hc|Hc]]; [lia | left; exact Hc | right; exact Hc]) ltac:(unfold X in *; lia) Ha).
    unfold X in *. lia.
  - exact (lb_keep_rom cx W1 m1 (ms_mem ms) HB KP0 HROM).
  - split; [|split].
    + apply (amem_range_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) X _ HAR1 Hbufin);
        rewrite ?RQB; unfold X in *; lia.
    + apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) X _ HAR1 Hbufin);
        rewrite ?RQB; unfold X in *; lia.
    + intros Hpos. apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) X _ HAR1 Hbufin);
        rewrite ?RQB; unfold X in *; lia.
  - apply (amem_range_near_block B RG LAWS HGSB ly1 S1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) X HAR1 Hbufin);
      rewrite ?RQB; unfold X in *; lia. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrr & Hfr2 & Hpres2).
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W1) mem2) HP2 ([] : list nat) HS2.
specialize (HS2 (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 34 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 34)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs1 (lb_extra v13)) Ea)
  by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
pose proof (lb_keep_call cx W1 m1 (ms_mem ms) mem2 KP0 Hfr2 Hpres2) as KP1.
prreg HS (10%bv : bv 5) R10a.
assert (SR : (getr regs2 10 = w64 0 /\ last_space_from 0 (dline s1 p q) = None) \/
  (exists j, (j < length (dline s1 p q))%nat /\ getr regs2 10 = w64 (X + Z.of_nat j) /\
     last_space_from 0 (dline s1 p q) = Some j)).
{ apply (lb_strrchr _ X (dline s1 p q) (getr regs2 10) LN1); [unfold X in *; lia | rewrite HLEN; unfold X in *; lia |].
  rewrite HLEN. exact Hrr. }
assert (F38 : ew Ea 38 = getr regs2 10) by (rewrite R10a; reflexivity).
clear Hrr LN1 KP0 FR0 GR0 Q1 Q2 Q3 Q4 Q10 Q11 HAR1 R10a Hfr2 Hpres2 HP2.
clear dependent ms.
pose proof (lb_line_ext _ _ X (dline s1 p q) LN0
  (fun a Ha => lb_keep_low cx W1 m1 mem2 a HB KP1 ltac:(rewrite HLEN in Ha; unfold X in *; lia))) as LN2.
assert (SHOK1 : sh_ok SEGS lb_Bx [] Ea (mrestrict (w_H W1) mem2)) by constructor.
paj_run_tok RUN HS HJ2 SHOK1 lb_Bspan; [apply awr_ok_x_nil|].
rename HFr into FR1; rename HG0 into GR1; clear HF.
assert (KP2 : lb_keep cx W1 m1 (ms_mem ms)).
{ apply (lb_keep_run cx W1 m1 mem2 (ms_mem ms) Ea []); [exact KP1 | exact FR1 | exact GR1 |].
  intros a (r & Hin & _). destruct Hin. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
pose proof (lb_line_ext _ _ X (dline s1 p q) LN0
  (fun a Ha => lb_keep_low cx W1 m1 (ms_mem ms) a HB KP2 ltac:(rewrite HLEN in Ha; unfold X in *; lia))) as LN3.
pose proof (lb_keep_rom cx W1 m1 (ms_mem ms) HB KP2 HROM) as ROM2.
pose proof lb_lit_bytes as (LBK & LBB & LBE).
pose proof lb_lit_nz as (NZK & NZB & NZE).
pose proof (lb_lit_of_dlit 18 K_GESTURE W1 (ms_mem ms) HLIT5 ROM2 LBK) as LIT21.
pose proof (lb_lit_range 18 _ HLIT5 ltac:(cbv; lia)) as (Y21a & Y21b). unfold IMG_TOP in Y21b.
change (Z.of_nat (length (K_GESTURE ++ [0]))) with 14 in Y21b.
assert (V262 : getr (ms_regs ms) 11 = w64 (VAL (A_OBJ 18))).
{ rewrite Q11. apply bv_eq. unfold w64. rewrite unsigned_lit_small by lia.
  exact (HEIa (A_OBJ 18) ltac:(cbv; lia)). }
assert (SP2 : spZ (ms_regs ms) = dsp0 cx - DRAIN_FRAME) by (unfold spZ; rewrite Q2, OLDa, Usp by lia; reflexivity).
eapply SRr_bind.
{ eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 ([] : list (Z * Z)) (2 * ESTACK) (SIGMA WS_strncmp)
      (fun _ => False) _ W1 (ms_regs ms) (ms_mem ms) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx)
      (dxmem cx) (dxmd cx) ([] : list (Z * Z)) ly1 S1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ2);
  [ rewrite SP2; lia
  | reflexivity
  | unfold DRAIN_FRAME; lia
  | unfold ESTACK; lia
  | unfold ESTACK, DRAIN_FRAME; rewrite WS; lia
  | rewrite Q3, OLDa, (EREG 3%nat 3%bv), Hr3 by (first [lia | reflexivity]); exact Hgp
  | rewrite Q4, OLDa, (EREG 4%nat 4%bv), Hr4 by (first [lia | reflexivity]); exact Htp
  | exact Q1
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | intros _; right; intros []
  | intros a []
  | intros a []
  | ].
  intros HPRE HSC.
  eapply (ASTRNCMP ly1 S1 W1 (ms_regs ms) (ms_mem ms) _ X (VAL (A_OBJ 18)) 13 (Z.min 13 (Z.of_nat (q - p))) 13
    HPRE HSC).
  - rewrite Q10, OLDa, (EREG 24%nat 24%bv), H24 by (first [lia | reflexivity]). reflexivity.
  - exact V262.
  - rewrite Q12. reflexivity.
  - lia.
  - lia.
  - unfold X in *; lia.
  - lia.
  - pose proof (lb_line_first_byte W1 (ms_mem ms) X (dline s1 p q) 13 LN3 ltac:(lia)) as FB. rewrite HLEN in FB.
    exact FB.
  - pose proof (lb_lit_first_byte W1 (ms_mem ms) (VAL (A_OBJ 18)) K_GESTURE 13 LIT21 NZK ltac:(lia)) as FB.
    change (Z.min 13 (Z.of_nat (length K_GESTURE))) with 13 in FB. exact FB.
  - unfold X in *; lia.
  - lia.
  - intros a Ha. split.
    + apply (lb_line_vis _ X (dline s1 p q) a LN3). rewrite HLEN. lia.
    + rewrite SP2. unfold X in *. lia.
  - intros a Ha. split.
    + apply (lb_lit_vis _ (VAL (A_OBJ 18)) K_GESTURE a LIT21). cbn [length K_GESTURE]. lia.
    + rewrite SP2. lia.
  - split; [|split].
    + apply (amem_range_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) X _ HAR2 Hbufin);
        rewrite ?RQB; unfold X in *; lia.
    + apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) X _ HAR2 Hbufin);
        rewrite ?RQB; unfold X in *; lia.
    + intros Hpos. apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) X _ HAR2 Hbufin);
        rewrite ?RQB; unfold X in *; lia.
  - split; [|split].
    + apply lb_amr_img; unfold IMG_TOP; lia.
    + apply (lb_ra_sub _ _ _ 14); [exact (proj1 (proj2 (proj2 HLIT5) ly1 S1 W1 (ms_mem ms) _ HAR2)) | lia].
    + intros _. apply (lb_hull_sub _ _ 14); [exact (HV21 _ _ _ _ _ HAR2) | lia].
  - exact ROM2.
  - split.
    + apply (amem_range_near_block B RG LAWS HGSB ly1 S1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) X HAR2 Hbufin);
        rewrite ?RQB; unfold X in *; lia.
    + apply lb_amr_img; unfold IMG_TOP; lia. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hnc & Hfr3 & Hpres3).
jafter_call_keep_pi HS 50%nat regs3 (mrestrict (w_H W1) mem3) HP3 ([] : list nat) HS3.
specialize (HS3 (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 50 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 50)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEb : env_agree 32 (Ereg regs1 (lb_extra v13)) Eb)
  by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
pose proof (lb_keep_call cx W1 m1 (ms_mem ms) mem3 KP2 Hfr3 Hpres3) as KP3.
prreg HS (10%bv : bv 5) R10b.
assert (NC : getr regs3 10 = w64 0 <-> firstn 13 (dline s1 p q) = K_GESTURE).
{ rewrite Hnc. unfold astrn_agree. exact (lb_strncmp_iff _ X (VAL (A_OBJ 18)) (dline s1 p q) LN3 LIT21). }
clear Hnc LN3 LIT21 ROM2 KP2 FR1 GR1 Q1 Q2 Q3 Q4 Q10 Q11 Q12 V262 HAR2 Hfr3 Hpres3 HP3 SP2.
clear dependent ms.
assert (SHOK2 : sh_ok SEGS lb_Bx [] Eb (mrestrict (w_H W1) mem3)) by constructor.
assert (A54 : ew Eb 54 = getr regs3 10) by (rewrite R10b; reflexivity).
assert (B24 : bv_unsigned (ew Eb 24) = X)
  by (rewrite OLDb, OLDa, (EREG 24%nat 24%bv), H24 by (first [lia | reflexivity]);
      apply unsigned_lit_small; unfold X in *; lia).
psrr_branch_tok RUN BR HS SHOK2 lb_Bspan.
- rewrite (lb_br_ne0 Eb 54 _ A54) in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  assert (GN : gesture (dline s1 p q) = None).
  { apply lb_g_nok. intros Hk. apply Hc. apply lb_w0. exact (proj2 NC Hk). }
  paj_run_to_tok RUNTO HS HJ3 SHOK2 lb_Bspan A_dr_next; [apply awr_ok_x_nil|].
  rename HFr into FRn; rename HG0 into GRn; clear HF.
  assert (KPn : lb_keep cx W1 m1 (ms_mem ms)).
  { apply (lb_keep_run cx W1 m1 mem3 (ms_mem ms) _ _ KP3 FRn GRn). intros a (r & Hin & _). destruct Hin. }
  pmkst HS.
  apply (KN (ms_regs ms) (ms_mem ms) _ GN); [| exact KPn | exact HJ3].
  intros r Hr.
  exact (regs_kept_of_st_ok_pi _ _ _ regs1 (lb_extra v13) [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 27]%bv HS HAEb
    ltac:(vm_compute; reflexivity) r Hr).
- rewrite (lb_br_ne0 Eb 54 _ A54) in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  assert (HK13 : firstn 13 (dline s1 p q) = K_GESTURE) by (apply NC; apply lb_w0; exact Hc).
  clear Hc.
  assert (HL13 : (13 <= q - p)%nat).
  { pose proof (f_equal (@length Z) HK13) as HLk. rewrite length_firstn, HLEN in HLk. cbn [length K_GESTURE] in HLk. lia. }
  pose proof (Hbg (p + 13)%nat ltac:(rewrite HLl; lia)) as (HV13 & V13R).
  rewrite HLapp, app_nth1 in HV13, V13R by lia. fold v13 in HV13, V13R.
  assert (HB13 : val_mem SEGS (arm W1 mem3) (X + 13) 1 v13).
  { apply (akept_vm W1 m1 W1 mem3 (X + 13) 1 v13).
    - intros x Hx. apply (lb_keep_byte cx W1 m1 mem3 x HB KP3). unfold X in *; lia.
    - replace (X + 13) with (re_buf e1 + Z.of_nat (p + 13)) by (unfold X; lia). exact HV13. }
  assert (E32b : ew Eb 32 = Z_to_bv 64 v13) by (rewrite OLDb, OLDa by lia; exact E32).
  apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 24%nat) 13 14 0 0 [YP09.mkChunk 13 (CVal 1 (SOff 32 0))])) in HS;
  [ | vm_compute; reflexivity
    | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite B24; split; [unfold X in *; lia|]; split; [unfold X in *; lia|]; split; [intros o Ho; lia|];
      apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val SEGS Eb _ X 13 1 (SOff 32 0) v13);
      [ exact (den_atom0 Eb 32 v13 E32b ltac:(lia)) | cbn; lia | cbn; lia | exact HB13 ]
    | cbn; exact I ].
  (* B reads four slots of drain's frame on this path (0x83a30 the shadow base, 0x83a44 .. 0x83a4c and 0x83a80 ..
     0x83a88 the reloads of s5 / s6 / s4), so the frame is seated as a region whose chunks are dr_frame's values. *)
  assert (USPb : bv_unsigned (ew Eb 2) = dsp0 cx - DRAIN_FRAME) by (rewrite OLDb, OLDa by lia; exact Usp).
  assert (E20b : ew Eb 20 = Z_to_bv 64 (dxSA cx + 16))
    by (rewrite OLDb, OLDa, (EREG 20%nat 20%bv), Hr20 by (first [lia | reflexivity]); reflexivity).
  assert (E21b : ew Eb 21 = Z_to_bv 64 (dxSA cx))
    by (rewrite OLDb, OLDa, (EREG 21%nat 21%bv), Hr21 by (first [lia | reflexivity]); reflexivity).
  assert (E22b : ew Eb 22 = Z_to_bv 64 (dxSA cx + 24))
    by (rewrite OLDb, OLDa, (EREG 22%nat 22%bv), Hr22 by (first [lia | reflexivity]); reflexivity).
  assert (E33b : ew Eb 33 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDb, OLDa by lia; exact E33).
  pose proof (lb_frame_slots cx W1 m1 mem3 HB KP3 HFRM) as (VM128 & VM136 & VM144 & VM240).
  apply (st_ok_pi_add_region _ _ _ lb_frame_region) in HS;
  [ | vm_compute; reflexivity
    | apply (lb_frame_region_ok cx Eb _ HB USPb E20b E21b E22b E33b HSAr VM128 VM136 VM144 VM240)
    | apply (lb_frame_disj cx Eb X B24 USPb); unfold X in *; lia ].
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
  assert (SHOK3 : sh_ok SEGS lb_Bx [mkSHE 24 13 14] Eb (mrestrict (w_H W1) mem3)).
  { unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
    eapply (shent_ok_of_range SEGS (w_H W1) mem3 Eb lb_Bx 24%nat (X + 13) 1 X 13 14).
    - apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 mem3 _ (re_buf e1) (re_cap e1) (X + 13) 1 HAR3 Hbufin);
        rewrite ?RQB; unfold X in *; lia.
    - unfold lb_Bx. apply U_atom; [|unfold SHADOW_OFF; lia]. exact E33b.
    - apply U_atom; [|unfold X in *; lia].
      rewrite OLDb, OLDa, (EREG 24%nat 24%bv), H24 by (first [lia | reflexivity]). reflexivity.
    - lia.
    - lia.
    - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, X in *. cbn [Z.min Z.max] in Hx. lia. }
  paj_run_tok RUN HS HJ3 SHOK3 lb_Bspan; [lb_awr2|].
  rename HFr into FR4; rename HG0 into GR4; clear HF.
  assert (KP4 : lb_keep cx W1 m1 (ms_mem ms)) by (apply (lb_keep_run cx W1 m1 mem3 (ms_mem ms) _ _ KP3 FR4 GR4); lb_nowr).
  assert (HAEc : env_agree 32 (Ereg regs1 (lb_extra v13)) (ewset (ewset Eb 512 w) 513 w0))
    by (repeat (apply lb_ae_ewset; [lia|]); exact HAEb).
  assert (C32 : ew (ewset (ewset Eb 512 w) 513 w0) 32 = Z_to_bv 64 v13) by (rewrite !ew_ewset_other by lia; exact E32b).
  assert (C38 : ew (ewset (ewset Eb 512 w) 513 w0) 38 = getr regs2 10)
    by (rewrite !ew_ewset_other, OLDb, F38 by lia; reflexivity).
  assert (C24 : ew (ewset (ewset Eb 512 w) 513 w0) 24 = Z_to_bv 64 X)
    by (rewrite !ew_ewset_other, OLDb, OLDa, (EREG 24%nat 24%bv), H24 by (first [lia | reflexivity]); reflexivity).
  assert (N13 : nth 13 (dline s1 p q) 0 = v13) by (rewrite (lb_nth13 s1 p q Hpq Hnulq HL13); reflexivity).
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR4.
  assert (SHOK4 : sh_ok SEGS lb_Bx [] (ewset (ewset Eb 512 w) 513 w0) (mrestrict (w_H W1) (ms_mem ms))) by constructor.
  psrr_branch_tok RUN BR HS SHOK4 lb_Bspan.
  + rewrite (lb_br_ne_byte _ 32 v13 32 C32 V13R ltac:(lia)) in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    assert (GN : gesture (dline s1 p q) = None) by (apply lb_g_nsp; rewrite N13; unfold SPACE; exact Hc).
    paj_run_to_tok RUNTO HS HJ3 SHOK4 lb_Bspan A_dr_next; [lb_awr2|].
    rename HFr into FRn; rename HG0 into GRn; clear HF.
    assert (KPn : lb_keep cx W1 m1 (ms_mem ms0)) by (apply (lb_keep_run cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP4 FRn GRn); lb_nowr).
    pmkst HS. apply (KN _ _ _ GN); [lb_regs HS HAEc | exact KPn | exact HJ3].
  + rewrite (lb_br_ne_byte _ 32 v13 32 C32 V13R ltac:(lia)) in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    assert (HSP : nth 13 (dline s1 p q) 0 = SPACE) by (rewrite N13; unfold SPACE; exact Hc).
    clear Hc.
    paj_run_tok RUN HS HJ3 SHOK4 lb_Bspan; [lb_awr2|].
    rename HFr into FR5; rename HG0 into GR5; clear HF.
    assert (KP5 : lb_keep cx W1 m1 (ms_mem ms0))
      by (apply (lb_keep_run cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP4 FR5 GR5); lb_nowr).
    clear dependent ms. rename ms0 into ms.
    psrr_branch_tok RUN BR HS SHOK4 lb_Bspan.
    * rewrite (lb_br_eq0 _ 38 _ C38) in Hc. apply Z.eqb_eq in Hc.
      assert (GN : gesture (dline s1 p q) = None).
      { destruct SR as [(_ & HN) | (j & Hj & Hr10 & _)]; [exact (lb_g_nolast _ HN)|].
        exfalso. rewrite HLEN in Hj. rewrite Hr10 in Hc. unfold w64 in Hc.
        rewrite unsigned_lit_small in Hc by (unfold X in *; lia). unfold X in *. lia. }
      paj_run_to_tok RUNTO HS HJ3 SHOK4 lb_Bspan A_dr_next; [lb_awr2|].
      rename HFr into FRn; rename HG0 into GRn; clear HF.
      assert (KPn : lb_keep cx W1 m1 (ms_mem ms0))
        by (apply (lb_keep_run cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP5 FRn GRn); lb_nowr).
      pmkst HS. apply (KN _ _ _ GN); [lb_regs HS HAEc | exact KPn | exact HJ3].
    * rewrite (lb_br_eq0 _ 38 _ C38) in Hc. apply Z.eqb_neq in Hc.
      destruct SR as [(Hr10 & _) | (j & Hj & Hr10 & HLS)]; [exfalso; apply Hc; rewrite Hr10; reflexivity|].
      clear Hc. rewrite HLEN in Hj.
      assert (C38j : ew (ewset (ewset Eb 512 w) 513 w0) 38 = Z_to_bv 64 (X + Z.of_nat j)) by (rewrite C38, Hr10; reflexivity).
      paj_run_tok RUN HS HJ3 SHOK4 lb_Bspan; [lb_awr2|].
      rename HFr into FR6; rename HG0 into GR6; clear HF.
      assert (KP6 : lb_keep cx W1 m1 (ms_mem ms0))
        by (apply (lb_keep_run cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP5 FR6 GR6); lb_nowr).
      clear dependent ms. rename ms0 into ms.
      psrr_branch_tok RUN BR HS SHOK4 lb_Bspan.
      -- rewrite (lb_br_eq_ao _ 38 24 (X + Z.of_nat j) X 13 C38j C24) in Hc by (unfold X in *; lia).
         apply Z.eqb_eq in Hc.
         assert (GN : gesture (dline s1 p q) = None) by (apply lb_g_13; replace 13%nat with j by lia; exact HLS).
         paj_run_to_tok RUNTO HS HJ3 SHOK4 lb_Bspan A_dr_next; [lb_awr2|].
         rename HFr into FRn; rename HG0 into GRn; clear HF.
         assert (KPn : lb_keep cx W1 m1 (ms_mem ms0))
           by (apply (lb_keep_run cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP6 FRn GRn); lb_nowr).
         pmkst HS. apply (KN _ _ _ GN); [lb_regs HS HAEc | exact KPn | exact HJ3].
      -- rewrite (lb_br_eq_ao _ 38 24 (X + Z.of_nat j) X 13 C38j C24) in Hc by (unfold X in *; lia).
         apply Z.eqb_neq in Hc.
         destruct (lb_g_last _ j HSP HLS) as (Hj13 & _).
         assert (Hjg : (13 < j)%nat) by lia.
         clear Hc.
         (* 0x83a60 li a0,-1; 0x83a64 beq s3,a0 -> 0x84004: UBSan's check that s3 + 1 does not wrap (the trap kit's
            census row WRAP p+1).  s3 = line + j, so the taken edge is refuted by its value. *)
         paj_run_tok RUN HS HJ3 SHOK4 lb_Bspan; [lb_awr2|].
         rename HFr into FR6t; rename HG0 into GR6t; clear HF.
         assert (KP6t : lb_keep cx W1 m1 (ms_mem ms0))
           by (apply (lb_keep_run cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP6 FR6t GR6t); lb_nowr).
         clear dependent ms. rename ms0 into ms.
         psrr_branch_tok RUN BR HS SHOK4 lb_Bspan.
         { exfalso. rewrite (lb_br_eq_lit _ 38 (X + Z.of_nat j) 18446744073709551615 C38j) in Hc
             by (unfold X in *; lia).
           apply Z.eqb_eq in Hc. unfold X in *. lia. }
         clear Hc.
         paj_run_tok RUN HS HJ3 SHOK4 lb_Bspan; [lb_awr2|].
         rename HFr into FR7; rename HG0 into GR7; clear HF.
         assert (KP7 : lb_keep cx W1 m1 (ms_mem ms0))
           by (apply (lb_keep_run cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP6t FR7 GR7); lb_nowr).
         clear dependent ms. rename ms0 into ms.
         pmkst HS.
         prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
         prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.

         pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HARc3.
         pose proof (lb_line_ext _ _ X (dline s1 p q) LN0
           (fun a Ha => lb_keep_low cx W1 m1 (ms_mem ms) a HB KP7 ltac:(rewrite HLEN in Ha; unfold X in *; lia))) as LNc3.
         pose proof (lb_line_skipn _ X (dline s1 p q) j LNc3 ltac:(rewrite HLEN; lia)) as LSc3.
         assert (HLSc3 : length (skipn (S j) (dline s1 p q)) = (q - p - S j)%nat) by (rewrite length_skipn, HLEN; reflexivity).
         pose proof (lb_keep_rom cx W1 m1 (ms_mem ms) HB KP7 HROM) as ROMc3.
         pose proof (lb_lit_of_dlit 20 W_BEGIN W1 (ms_mem ms) HLIT6 ROMc3 LBB) as LITc3.
         pose proof (lb_lit_range 20 _ HLIT6 ltac:(cbv; lia)) as (Yc3a & Yc3b). unfold IMG_TOP in Yc3b.
         change (Z.of_nat (length (W_BEGIN ++ [0]))) with 6 in Yc3b.
         pose proof (pa_obj_img 20 ltac:(lia)) as (Yo3a & Yo3b).
         assert (Vc3 : getr (ms_regs ms) 11 = w64 (VAL (A_OBJ 20))).
         { rewrite Q11. apply bv_eq. unfold w64. rewrite unsigned_lit_small by lia.
           first [ match goal with HI : img_env _ _ ?Ev |- bv_unsigned (ew ?Ev _) = _ => exact (HI (A_OBJ 20) ltac:(cbv; lia)) end
                 | rewrite nth_overflow by (rewrite length_map; cbv; lia);
                   match goal with HI : img_env _ _ ?Ev |- bv_unsigned (ew ?Ev _) = _ =>
                     exact (HI (A_OBJ 20) ltac:(cbv; lia)) end]. }
         assert (Ac3 : getr (ms_regs ms) 10 = w64 (X + Z.of_nat j + 1)).
         { rewrite Q10. lb_ewg. rewrite OLDb, F38, Hr10 by lia. unfold w64.
           rewrite unsigned_lit_small by (unfold X in *; lia). reflexivity. }
         assert (SPc3 : spZ (ms_regs ms) = dsp0 cx - DRAIN_FRAME)
           by (unfold spZ; rewrite Q2; lb_ewg; rewrite OLDb, OLDa, Usp by lia; reflexivity).
         eapply SRr_bind.
         { eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 ([] : list (Z * Z)) (2 * ESTACK) (SIGMA WS_strcmp)
               (fun _ => False) _ W1 (ms_regs ms) (ms_mem ms) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx)
               (dxmem cx) (dxmd cx) ([] : list (Z * Z)) ly1 S1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ3);
           [ rewrite SPc3; lia
           | reflexivity
           | unfold DRAIN_FRAME; lia
           | unfold ESTACK; lia
           | unfold ESTACK, DRAIN_FRAME; rewrite WS; lia
           | rewrite Q3; lb_ewg; rewrite OLDb, OLDa, (EREG 3%nat 3%bv), Hr3 by (first [lia | reflexivity]); exact Hgp
           | rewrite Q4; lb_ewg; rewrite OLDb, OLDa, (EREG 4%nat 4%bv), Hr4 by (first [lia | reflexivity]); exact Htp
           | exact Q1
           | apply ret_ok_codeptr_v; [lia | reflexivity]
           | intros _; right; intros []
           | intros a []
           | intros a []
           | ].
           intros HPRE HSC.
           eapply (ASTRCMP ly1 S1 W1 (ms_regs ms) (ms_mem ms) _ (X + Z.of_nat j + 1) (VAL (A_OBJ 20))
             (Z.of_nat (q - p) - Z.of_nat j - 1) 5 HPRE HSC).
           - exact Ac3.
           - exact Vc3.
           - unfold X in *; lia.
           - lia.
           - lia.
           - lia.
           - unfold X in *; lia.
           - lia.
           - unfold LINE_LIMIT in *; lia.
           - pose proof (lb_line_first_byte W1 (ms_mem ms) _ _ (Z.of_nat (q - p) - Z.of_nat j - 1 + 1) LSc3 ltac:(lia)) as FB.
             rewrite HLSc3 in FB.
             replace (Z.min (Z.of_nat (q - p) - Z.of_nat j - 1 + 1) (Z.of_nat (q - p - S j)))
               with (Z.of_nat (q - p) - Z.of_nat j - 1) in FB by lia.
             exact FB.
           - pose proof (lb_lit_first_byte W1 (ms_mem ms) (VAL (A_OBJ 20)) W_BEGIN (5 + 1) LITc3 NZB ltac:(lia)) as FB.
             change (Z.min (5 + 1) (Z.of_nat (length W_BEGIN))) with 5 in FB. exact FB.
           - intros a Ha. split.
             + apply (lb_line_vis _ _ _ a LSc3). rewrite HLSc3. lia.
             + rewrite SPc3. unfold X in *. lia.
           - intros a Ha. split.
             + apply (lb_lit_vis _ _ W_BEGIN a LITc3). cbn [length W_BEGIN]. lia.
             + rewrite SPc3. lia.
           - split; [|split].
             + apply (amem_range_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) _ _ HARc3 Hbufin);
                 rewrite ?RQB; unfold X in *; lia.
             + apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) _ _ HARc3 Hbufin);
                 rewrite ?RQB; unfold X in *; lia.
             + intros Hpos. apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) _ _
                 HARc3 Hbufin); rewrite ?RQB; unfold X in *; lia.
           - split; [|split].
             + apply lb_amr_img; unfold IMG_TOP; lia.
             + apply (lb_ra_sub _ _ _ 6); [exact (proj1 (proj2 (proj2 HLIT6) ly1 S1 W1 (ms_mem ms) _ HARc3)) | lia].
             + intros _. apply (lb_hull_sub _ _ 6); [exact (HV23 _ _ _ _ _ HARc3) | lia].
           - exact ROMc3.
           - split.
             + apply (amem_range_near_block B RG LAWS HGSB ly1 S1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) _ HARc3 Hbufin);
                 rewrite ?RQB; unfold X in *; lia.
             + apply lb_amr_img; unfold IMG_TOP; lia. }
         cbv beta. intros W3x c3x Hwle3x (-> & regs4 & mem4 & md3x & -> & HJ4 & HP3x & Hbc & Hfr3x & Hpres3x).
         jafter_call_keep_pi HS 66%nat regs4 (mrestrict (w_H W1) mem4) HP3x ([] : list nat) HS3x.
         specialize (HS3x (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS3x. rename HS3x into HS.
         lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
           assert (HEIc3 : img_env VAL A_LIM Ev) by (apply img_env_havoc; [assumption | cbv; lia]) end.
         pose proof (lb_keep_call cx W1 m1 (ms_mem ms) mem4 KP7 Hfr3x Hpres3x) as KP8.
         prreg HS (10%bv : bv 5) R10c.
         lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
           assert (A70 : ew Ev 70 = getr regs4 10) by (rewrite R10c; reflexivity) end.
         assert (BC : getr regs4 10 = w64 0 <-> skipn (S j) (dline s1 p q) = W_BEGIN).
         { rewrite Hbc. pose proof (lb_strcmp_iff _ X (VAL (A_OBJ 20)) (dline s1 p q) W_BEGIN j LNc3 LITc3
             ltac:(rewrite HLEN; lia)) as I.
           rewrite HLEN in I. change (Z.of_nat (length W_BEGIN)) with 5 in I. exact I. }
         clear Hbc. clear dependent ms.
         (* 0x83a7c mv s9,a0 and the reloads of s5 / s6 / s4 from the frame (0x83a80 .. 0x83a88): seat the frame again *)
         lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
           assert (SHOK5 : sh_ok SEGS lb_Bx [] Ev (mrestrict (w_H W1) mem4)) by constructor;
           assert (USPc : bv_unsigned (ew Ev 2) = dsp0 cx - DRAIN_FRAME) by (lb_ewg; exact USPb);
           assert (E20c : ew Ev 20 = Z_to_bv 64 (dxSA cx + 16)) by (lb_ewg; exact E20b);
           assert (E21c : ew Ev 21 = Z_to_bv 64 (dxSA cx)) by (lb_ewg; exact E21b);
           assert (E22c : ew Ev 22 = Z_to_bv 64 (dxSA cx + 24)) by (lb_ewg; exact E22b);
           assert (E33c : ew Ev 33 = Z_to_bv 64 SHADOW_OFF) by (lb_ewg; exact E33b) end.
         pose proof (lb_frame_slots cx W1 m1 mem4 HB KP8 HFRM) as (VM128c & VM136c & VM144c & VM240c).
         apply (st_ok_pi_add_region _ _ _ lb_frame_region) in HS;
         [ | vm_compute; reflexivity
           | exact (lb_frame_region_ok cx _ _ HB USPc E20c E21c E22c E33c HSAr VM128c VM136c VM144c VM240c)
           | cbn; exact I ].
         paj_run_tok RUN HS HJ4 SHOK5 lb_Bspan; [lb_awr1|].
         rename HFr into FR9; rename HG0 into GR9; clear HF.
         assert (KP9 : lb_keep cx W1 m1 (ms_mem ms))
           by (apply (lb_keep_run cx W1 m1 mem4 (ms_mem ms) _ _ KP8 FR9 GR9); lb_nowr).
         psrr_branch_tok RUN BR HS SHOK5 lb_Bspan.
         ++ rewrite (lb_br_eq0 _ _ _ A70) in Hc. apply Z.eqb_eq in Hc.
            assert (HBEG : skipn (S j) (dline s1 p q) = W_BEGIN) by (apply BC; apply lb_w0; exact Hc).
            assert (GS : gesture (dline s1 p q) = Some (GBegin, firstn j (dline s1 p q))).
            { rewrite (lb_g_some _ j HK13 HSP HLS Hjg). rewrite (proj2 (lb_list_eqb _ _) HBEG). reflexivity. }
            paj_run_to_tok RUNTO HS HJ4 SHOK5 lb_Bspan A_dr_seen; [lb_awr1|].
            rename HFr into FRg; rename HG0 into GRg; clear HF.
            assert (KPg : lb_keep cx W1 m1 (ms_mem ms0))
              by (apply (lb_keep_run cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP9 FRg GRg); lb_nowr).
            pmkst HS. prreg HS (19%bv : bv 5) R19. prreg HS (26%bv : bv 5) R26. prreg HS (25%bv : bv 5) R25.
            apply (KG _ _ _ GBegin j 0 GS ltac:(lia));
              [ | | | lia | split; intros _; reflexivity | lb_regs HS HAEb | exact KPg | exact HJ4 ].
            ** rewrite R19. lb_ewg. rewrite OLDb, F38, Hr10 by lia. reflexivity.
            ** rewrite R26. lb_ewg. rewrite OLDb, F38, Hr10 by lia. unfold w64.
               rewrite unsigned_lit_small by (unfold X in *; lia). reflexivity.
            ** rewrite R25, <- R10c. apply lb_w0. exact Hc.
         ++ rewrite (lb_br_eq0 _ _ _ A70) in Hc. apply Z.eqb_neq in Hc.
            assert (HNB : skipn (S j) (dline s1 p q) <> W_BEGIN)
              by (intros E0; apply Hc; apply lb_w0; exact (proj2 BC E0)).
            rename Hc into R4nz.
            paj_run_tok RUN HS HJ4 SHOK5 lb_Bspan; [lb_awr1|].
            rename HFr into FR10; rename HG0 into GR10; clear HF.
            assert (KP10 : lb_keep cx W1 m1 (ms_mem ms0))
              by (apply (lb_keep_run cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP9 FR10 GR10); lb_nowr).
            clear dependent ms. rename ms0 into ms.
            pmkst HS.
            prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
            prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.

         pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HARc4.
         pose proof (lb_line_ext _ _ X (dline s1 p q) LN0
           (fun a Ha => lb_keep_low cx W1 m1 (ms_mem ms) a HB KP10 ltac:(rewrite HLEN in Ha; unfold X in *; lia))) as LNc4.
         pose proof (lb_line_skipn _ X (dline s1 p q) j LNc4 ltac:(rewrite HLEN; lia)) as LSc4.
         assert (HLSc4 : length (skipn (S j) (dline s1 p q)) = (q - p - S j)%nat) by (rewrite length_skipn, HLEN; reflexivity).
         pose proof (lb_keep_rom cx W1 m1 (ms_mem ms) HB KP10 HROM) as ROMc4.
         pose proof (lb_lit_of_dlit 21 W_END W1 (ms_mem ms) HLIT7 ROMc4 LBE) as LITc4.
         pose proof (lb_lit_range 21 _ HLIT7 ltac:(cbv; lia)) as (Yc4a & Yc4b). unfold IMG_TOP in Yc4b.
         change (Z.of_nat (length (W_END ++ [0]))) with 4 in Yc4b.
         pose proof (pa_obj_img 21 ltac:(lia)) as (Yo4a & Yo4b).
         assert (Vc4 : getr (ms_regs ms) 11 = w64 (VAL (A_OBJ 21))).
         { rewrite Q11. apply bv_eq. unfold w64. rewrite unsigned_lit_small by lia.
           first [ match goal with HI : img_env _ _ ?Ev |- bv_unsigned (ew ?Ev _) = _ => exact (HI (A_OBJ 21) ltac:(cbv; lia)) end
                 | rewrite nth_overflow by (rewrite length_map; cbv; lia);
                   match goal with HI : img_env _ _ ?Ev |- bv_unsigned (ew ?Ev _) = _ =>
                     exact (HI (A_OBJ 21) ltac:(cbv; lia)) end]. }
         assert (Ac4 : getr (ms_regs ms) 10 = w64 (X + Z.of_nat j + 1)).
         { rewrite Q10. lb_ewg. rewrite OLDb, F38, Hr10 by lia. unfold w64.
           rewrite unsigned_lit_small by (unfold X in *; lia). reflexivity. }
         assert (SPc4 : spZ (ms_regs ms) = dsp0 cx - DRAIN_FRAME)
           by (unfold spZ; rewrite Q2; lb_ewg; rewrite OLDb, OLDa, Usp by lia; reflexivity).
         eapply SRr_bind.
         { eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 ([] : list (Z * Z)) (2 * ESTACK) (SIGMA WS_strcmp)
               (fun _ => False) _ W1 (ms_regs ms) (ms_mem ms) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx)
               (dxmem cx) (dxmd cx) ([] : list (Z * Z)) ly1 S1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ4);
           [ rewrite SPc4; lia
           | reflexivity
           | unfold DRAIN_FRAME; lia
           | unfold ESTACK; lia
           | unfold ESTACK, DRAIN_FRAME; rewrite WS; lia
           | rewrite Q3; lb_ewg; rewrite OLDb, OLDa, (EREG 3%nat 3%bv), Hr3 by (first [lia | reflexivity]); exact Hgp
           | rewrite Q4; lb_ewg; rewrite OLDb, OLDa, (EREG 4%nat 4%bv), Hr4 by (first [lia | reflexivity]); exact Htp
           | exact Q1
           | apply ret_ok_codeptr_v; [lia | reflexivity]
           | intros _; right; intros []
           | intros a []
           | intros a []
           | ].
           intros HPRE HSC.
           eapply (ASTRCMP ly1 S1 W1 (ms_regs ms) (ms_mem ms) _ (X + Z.of_nat j + 1) (VAL (A_OBJ 21))
             (Z.of_nat (q - p) - Z.of_nat j - 1) 3 HPRE HSC).
           - exact Ac4.
           - exact Vc4.
           - unfold X in *; lia.
           - lia.
           - lia.
           - lia.
           - unfold X in *; lia.
           - lia.
           - unfold LINE_LIMIT in *; lia.
           - pose proof (lb_line_first_byte W1 (ms_mem ms) _ _ (Z.of_nat (q - p) - Z.of_nat j - 1 + 1) LSc4 ltac:(lia)) as FB.
             rewrite HLSc4 in FB.
             replace (Z.min (Z.of_nat (q - p) - Z.of_nat j - 1 + 1) (Z.of_nat (q - p - S j)))
               with (Z.of_nat (q - p) - Z.of_nat j - 1) in FB by lia.
             exact FB.
           - pose proof (lb_lit_first_byte W1 (ms_mem ms) (VAL (A_OBJ 21)) W_END (3 + 1) LITc4 NZE ltac:(lia)) as FB.
             change (Z.min (3 + 1) (Z.of_nat (length W_END))) with 3 in FB. exact FB.
           - intros a Ha. split.
             + apply (lb_line_vis _ _ _ a LSc4). rewrite HLSc4. lia.
             + rewrite SPc4. unfold X in *. lia.
           - intros a Ha. split.
             + apply (lb_lit_vis _ _ W_END a LITc4). cbn [length W_END]. lia.
             + rewrite SPc4. lia.
           - split; [|split].
             + apply (amem_range_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) _ _ HARc4 Hbufin);
                 rewrite ?RQB; unfold X in *; lia.
             + apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) _ _ HARc4 Hbufin);
                 rewrite ?RQB; unfold X in *; lia.
             + intros Hpos. apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) _ _
                 HARc4 Hbufin); rewrite ?RQB; unfold X in *; lia.
           - split; [|split].
             + apply lb_amr_img; unfold IMG_TOP; lia.
             + apply (lb_ra_sub _ _ _ 4); [exact (proj1 (proj2 (proj2 HLIT7) ly1 S1 W1 (ms_mem ms) _ HARc4)) | lia].
             + intros _. apply (lb_hull_sub _ _ 4); [exact (HV24 _ _ _ _ _ HARc4) | lia].
           - exact ROMc4.
           - split.
             + apply (amem_range_near_block B RG LAWS HGSB ly1 S1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) _ HARc4 Hbufin);
                 rewrite ?RQB; unfold X in *; lia.
             + apply lb_amr_img; unfold IMG_TOP; lia. }
         cbv beta. intros W4x c4x Hwle4x (-> & regs5 & mem5 & md4x & -> & HJ5 & HP4x & Hbe & Hfr4x & Hpres4x).
         jafter_call_keep_pi HS 82%nat regs5 (mrestrict (w_H W1) mem5) HP4x ([] : list nat) HS4x.
         specialize (HS4x (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS4x. rename HS4x into HS.
         lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
           assert (HEIc4 : img_env VAL A_LIM Ev) by (apply img_env_havoc; [assumption | cbv; lia]) end.
         pose proof (lb_keep_call cx W1 m1 (ms_mem ms) mem5 KP10 Hfr4x Hpres4x) as KP11.

            prreg HS (10%bv : bv 5) R10d.
            lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
              assert (A86 : ew Ev 86 = getr regs5 10) by (rewrite R10d; reflexivity) end.
            assert (BE : getr regs5 10 = w64 0 <-> skipn (S j) (dline s1 p q) = W_END).
            { rewrite Hbe. pose proof (lb_strcmp_iff _ X (VAL (A_OBJ 21)) (dline s1 p q) W_END j LNc4 LITc4
                ltac:(rewrite HLEN; lia)) as I.
              rewrite HLEN in I. change (Z.of_nat (length W_END)) with 3 in I. exact I. }
            clear Hbe. clear dependent ms.
            lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
              assert (SHOK6 : sh_ok SEGS lb_Bx [] Ev (mrestrict (w_H W1) mem5)) by constructor end.
            psrr_branch_tok RUN BR HS SHOK6 lb_Bspan.
            ** rewrite (lb_br_ne0 _ _ _ A86) in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
               assert (GN : gesture (dline s1 p q) = None).
               { rewrite (lb_g_some _ j HK13 HSP HLS Hjg).
                 destruct (list_eqb (skipn (S j) (dline s1 p q)) W_BEGIN) eqn:EB;
                   [exfalso; apply HNB; apply lb_list_eqb; exact EB|].
                 destruct (list_eqb (skipn (S j) (dline s1 p q)) W_END) eqn:EE;
                   [exfalso; apply Hc; apply lb_w0; apply BE; apply lb_list_eqb; exact EE|].
                 reflexivity. }
               paj_run_to_tok RUNTO HS HJ5 SHOK6 lb_Bspan A_dr_next; [apply awr_ok_x_nil|].
               rename HFr into FRn; rename HG0 into GRn; clear HF.
               assert (KPn : lb_keep cx W1 m1 (ms_mem ms))
                 by (apply (lb_keep_run cx W1 m1 mem5 (ms_mem ms) _ _ KP11 FRn GRn); lb_nowr).
               pmkst HS. apply (KN _ _ _ GN); [lb_regs HS HAEb | exact KPn | exact HJ5].
            ** rewrite (lb_br_ne0 _ _ _ A86) in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
               assert (HEND : skipn (S j) (dline s1 p q) = W_END) by (apply BE; apply lb_w0; exact Hc).
               assert (GS : gesture (dline s1 p q) = Some (GEnd, firstn j (dline s1 p q))).
               { rewrite (lb_g_some _ j HK13 HSP HLS Hjg).
                 destruct (list_eqb (skipn (S j) (dline s1 p q)) W_BEGIN) eqn:EB;
                   [exfalso; apply HNB; apply lb_list_eqb; exact EB|].
                 rewrite (proj2 (lb_list_eqb _ _) HEND). reflexivity. }
               paj_run_to_tok RUNTO HS HJ5 SHOK6 lb_Bspan A_dr_seen; [apply awr_ok_x_nil|].
               rename HFr into FRg; rename HG0 into GRg; clear HF.
               assert (KPg : lb_keep cx W1 m1 (ms_mem ms))
                 by (apply (lb_keep_run cx W1 m1 mem5 (ms_mem ms) _ _ KP11 FRg GRg); lb_nowr).
               pmkst HS. prreg HS (19%bv : bv 5) R19. prreg HS (26%bv : bv 5) R26. prreg HS (25%bv : bv 5) R25.
               pose proof (bv_unsigned_in_range 64 (getr regs4 10)) as RR4. change (bv_modulus 64) with (2 ^ 64) in RR4.
               apply (KG _ _ _ GEnd j (bv_unsigned (getr regs4 10)) GS ltac:(lia));
                 [ | | | exact RR4 | split; [intros E0; contradiction | intros E0; discriminate]
                 | lb_regs HS HAEb | exact KPg | exact HJ5 ].
               --- rewrite R19. lb_ewg. rewrite OLDb, F38, Hr10 by lia. reflexivity.
               --- rewrite R26. lb_ewg. rewrite OLDb, F38, Hr10 by lia. unfold w64.
                   rewrite unsigned_lit_small by (unfold X in *; lia). reflexivity.
               --- rewrite R25, <- R10c. unfold w64. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Theorem dr_lineb : dr_lineb_stmt B MT MMAX RG.
Proof.
apply dr_lineb_of.
- intros ly S W mem md HAR. exact (proj2 (proj2 (proj2 HLIT5) ly S W mem md HAR) ltac:(vm_compute; reflexivity)).
- intros ly S W mem md HAR. exact (proj2 (proj2 (proj2 HLIT6) ly S W mem md HAR) ltac:(vm_compute; reflexivity)).
- intros ly S W mem md HAR. exact (proj2 (proj2 (proj2 HLIT7) ly S W mem md HAR) ltac:(vm_compute; reflexivity)).
Qed.

End c.

(* ---- THE GENERIC WALK (an internal work row, step 3): LINEB over any allocator relation ARx with its laws, at the room texts
   (lib/B/W_drain_lineb_cx.v Section cx: dr_lineb_stmt_x, the entry's ghost list Hp and budget kr after cx, the cut's
   ghost list Hp1 an existential after S1).  The Section is lib/B/W_drain_cx_x.v's Section c - its variables
   B PST ARx MT RP MMAX RG in that order, each hypothesis that file's text - with the three allocator rules in their
   caller-context forms (this segment calls no allocator, so no call-site fact HCTX_* is stated), and after LAWS the
   one generic-relation fact the walk reads:
     HP0 (no hidden head in any ARx state: the line buffer's shadow facts are W_journal_x.v's
     range_addressable_of_block_hp0_x / shadow_hull_vis_of_block_hp0_x).
   The runtime sites strrchr / strncmp / strcmp keep the allocator state (W_sites_x.v aentry_post_x: ARx at the same
   ly S Hp), so the cut's LCORE_x - its dbud_x included - passes from DLS_x to DLN_x / DGS_x unchanged: no request is
   charged in this segment.  The AR walk above (Section c) is unchanged.  Its Definitions are cited; its lemmas are
   restated here with an _x suffix (each over ARx where it reads the relation), so no lemma's Section generalization
   is relied on. ---- *)
Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM_x SEGS B ARx 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes_x B ARx (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes_x B ARx (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
Hypothesis ALLOC_TAIL : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_list_push).
Hypothesis RMM : forall S k k', (k' <= k)%nat -> rp_RM RP S k -> rp_RM RP S k'.
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at_x ARx 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at_x ARx 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at_x ARx 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.

Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- the line and the literals (lb_line / lb_lit, cited) ---- *)
Lemma lbA_aview_garr8_x : forall (W : world SEGS) m base l j,
garr8 SEGS (arm W m) base l -> (j < length l)%nat ->
aview SEGS (w_H W) m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m base l j Hg Hj. destruct (Hg j Hj) as (_ & Hr).
unfold aview. change (mrestrict (w_H W) m) with (arm W m).
rewrite (garr8_mbyte SEGS (arm W m) base l j Hg Hj). cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact Hr.
Qed.

Lemma lbA_nth_bound_x : forall (w : list Z) i, (i <= length w)%nat ->
Forall (fun b => 0 <= b < 256) w -> 0 <= nth i (w ++ [0]) 0 < 256.
Proof.
intros w i Hi HF. destruct (Nat.eq_dec i (length w)) as [->|Hne].
- rewrite nth_middle. lia.
- rewrite app_nth1 by lia. rewrite Forall_forall in HF. apply HF. apply nth_In. lia.
Qed.

Lemma lbA_kg_len_x : length K_GESTURE = 13%nat.
Proof. reflexivity. Qed.

Lemma lbA_kg_nz_x : forall i, (i < 13)%nat -> nth i K_GESTURE 0 <> 0.
Proof.
unfold K_GESTURE. intros i Hi.
do 13 (destruct i as [|i]; [cbn; lia|]). exfalso. lia.
Qed.

Lemma lb_line_of_garr8_x : forall (W : world SEGS) m base (L : list Z) p q,
garr8 SEGS (arm W m) base L -> (p <= q < length L)%nat -> nth_error L q = Some 0 ->
(forall i, (p <= i < q)%nat -> nth_error L i <> Some 0) ->
lb_line (aview SEGS (w_H W) m) (base + Z.of_nat p) (firstn (q - p) (skipn p L)).
Proof.
intros W m base L p q Hg Hpq Hq Hno.
assert (HL : length (firstn (q - p) (skipn p L)) = (q - p)%nat).
{ rewrite length_firstn, length_skipn. lia. }
assert (HN : forall i, (i < q - p)%nat -> nth i (firstn (q - p) (skipn p L)) 0 = nth (p + i) L 0).
{ intros i Hi. rewrite nth_firstn, (proj2 (Nat.ltb_lt i (q - p)) Hi), nth_skipn. reflexivity. }
split; [|split].
- intros i Hi. rewrite HL in Hi. rewrite (HN i Hi).
  replace (base + Z.of_nat p + Z.of_nat i) with (base + Z.of_nat (p + i)) by lia.
  apply (lbA_aview_garr8_x W m base L (p + i)%nat Hg). lia.
- rewrite HL. replace (base + Z.of_nat p + Z.of_nat (q - p)) with (base + Z.of_nat q) by lia.
  rewrite (lbA_aview_garr8_x W m base L q Hg ltac:(lia)). f_equal.
  rewrite (nth_error_nth' L 0) in Hq by lia. injection Hq as Hq. exact Hq.
- intros i Hi. rewrite HL in Hi. rewrite (HN i Hi).
  intros E. apply (Hno (p + i)%nat ltac:(lia)).
  rewrite (nth_error_nth' L 0) by lia. rewrite E. reflexivity.
Qed.

Lemma lb_line_ext_x : forall rd rd' x l, lb_line rd x l ->
(forall a, x <= a <= x + Z.of_nat (length l) -> rd' a = rd a) -> lb_line rd' x l.
Proof.
intros rd rd' x l (H1 & H2 & H3) HE. split; [|split].
- intros i Hi. rewrite (HE (x + Z.of_nat i) ltac:(lia)). exact (H1 i Hi).
- rewrite (HE (x + Z.of_nat (length l)) ltac:(lia)). exact H2.
- exact H3.
Qed.

(* lb_lit_of_dlit over dlit_at_x (its first two conjuncts are dlit_at's) *)
Lemma lb_lit_of_dlit_x : forall i w (W : world SEGS) m, dlit_at_x ARx i (w ++ [0]) -> rom_view SEGS W m ->
Forall (fun b => 0 <= b < 256) w -> lb_lit (aview SEGS (w_H W) m) (VAL (A_OBJ i)) w.
Proof.
intros i w W m (HR & HI & _) HRV HF k Hk.
assert (HLen : length (w ++ [0]) = S (length w)) by (rewrite length_app; cbn [length]; lia).
assert (HinR : YG0d.in_rom SEGS (VAL (A_OBJ i) + Z.of_nat k)) by (apply HI; lia).
rewrite (HRV _ HinR), (HR k ltac:(lia)).
rewrite (nth_error_nth' (w ++ [0]) 0) by lia.
cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. apply lbA_nth_bound_x; assumption.
Qed.

Lemma lb_line_first_byte_x : forall (W : world SEGS) m x l n, lb_line (aview SEGS (w_H W) m) x l -> 0 <= n ->
first_byte SEGS W m x n 0 (Z.min n (Z.of_nat (length l))).
Proof.
intros W m x l n (H1 & H2 & H3) Hn. split; [lia|split].
- intros i Hi. exists (nth (Z.to_nat i) l 0). split.
  + replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia. apply H1. lia.
  + apply H3. lia.
- intros Hlt. replace (Z.min n (Z.of_nat (length l))) with (Z.of_nat (length l)) by lia. exact H2.
Qed.

Lemma lb_lit_first_byte_x : forall (W : world SEGS) m y w n, lb_lit (aview SEGS (w_H W) m) y w ->
(forall i, (i < length w)%nat -> nth i w 0 <> 0) -> 0 <= n ->
first_byte SEGS W m y n 0 (Z.min n (Z.of_nat (length w))).
Proof.
intros W m y w n H Hnz Hn. split; [lia|split].
- intros i Hi. exists (nth (Z.to_nat i) w 0). split.
  + replace (y + i) with (y + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (H (Z.to_nat i) ltac:(lia)). f_equal. apply app_nth1. lia.
  + apply Hnz. lia.
- intros Hlt. replace (Z.min n (Z.of_nat (length w))) with (Z.of_nat (length w)) by lia.
  rewrite (H (length w) ltac:(lia)). f_equal. apply nth_middle.
Qed.

Lemma lb_line_skipn_x : forall rd x l j, lb_line rd x l -> (j < length l)%nat ->
lb_line rd (x + Z.of_nat j + 1) (skipn (S j) l).
Proof.
intros rd x l j (H1 & H2 & H3) Hj.
assert (HL : length (skipn (S j) l) = (length l - S j)%nat) by apply length_skipn.
split; [|split].
- intros i Hi. rewrite HL in Hi. rewrite nth_skipn.
  replace (x + Z.of_nat j + 1 + Z.of_nat i) with (x + Z.of_nat (S j + i)) by lia.
  apply H1. lia.
- rewrite HL. replace (x + Z.of_nat j + 1 + Z.of_nat (length l - S j)) with (x + Z.of_nat (length l)) by lia.
  exact H2.
- intros i Hi. rewrite HL in Hi. rewrite nth_skipn. apply H3. lia.
Qed.

Lemma lb_line_vis_x : forall rd x l a, lb_line rd x l -> x <= a <= x + Z.of_nat (length l) -> rd a <> None.
Proof.
intros rd x l a (H1 & H2 & _) Ha.
destruct (Z.eq_dec a (x + Z.of_nat (length l))) as [Heq|Hne].
- rewrite Heq, H2. discriminate.
- assert (Hk : (Z.to_nat (a - x) < length l)%nat) by lia.
  assert (Ha' : a = x + Z.of_nat (Z.to_nat (a - x))) by lia.
  rewrite Ha', (H1 _ Hk). discriminate.
Qed.

Lemma lb_lit_vis_x : forall rd y w a, lb_lit rd y w -> y <= a <= y + Z.of_nat (length w) -> rd a <> None.
Proof.
intros rd y w a H Ha.
assert (Hk : (Z.to_nat (a - y) <= length w)%nat) by lia.
assert (Ha' : a = y + Z.of_nat (Z.to_nat (a - y))) by lia.
rewrite Ha', (H _ Hk). discriminate.
Qed.

Lemma lb_strncmp_iff_x : forall rd x y l, lb_line rd x l -> lb_lit rd y K_GESTURE ->
((forall i, 0 <= i < 13 -> (forall j, 0 <= j < i -> rd (x + j) <> Some 0) -> rd (x + i) = rd (y + i)) <->
 firstn 13 l = K_GESTURE).
Proof.
intros rd x y l (H1 & H2 & H3) HK.
assert (HY : forall k, (k < 13)%nat -> rd (y + Z.of_nat k) = Some (nth k K_GESTURE 0)).
{ intros k Hk. rewrite (HK k ltac:(rewrite lbA_kg_len_x; lia)). f_equal.
  apply app_nth1. rewrite lbA_kg_len_x. lia. }
split.
- intros HA.
  assert (MAIN : forall k, (k <= 13)%nat -> (k <= length l)%nat /\
    (forall t, (t < k)%nat -> nth t l 0 = nth t K_GESTURE 0)).
  { intros k. induction k as [|k IHk]; intros Hk.
    - split; [lia|intros t Ht; exfalso; lia].
    - destruct (IHk ltac:(lia)) as (Hlen & Hagr).
      assert (HNZ : forall j, 0 <= j < Z.of_nat k -> rd (x + j) <> Some 0).
      { intros j Hj. assert (Hj' : (Z.to_nat j < length l)%nat) by lia.
        replace (x + j) with (x + Z.of_nat (Z.to_nat j)) by lia.
        rewrite (H1 _ Hj'). intros E. injection E as E. exact (H3 _ Hj' E). }
      assert (HEQ : rd (x + Z.of_nat k) = Some (nth k K_GESTURE 0)).
      { rewrite (HA (Z.of_nat k) ltac:(lia) HNZ). apply HY. lia. }
      assert (HlenS : (S k <= length l)%nat).
      { destruct (Nat.ltb k (length l)) eqn:Eb; [apply Nat.ltb_lt in Eb; lia|].
        apply Nat.ltb_ge in Eb. exfalso.
        assert (Ek : k = length l) by lia. subst k.
        rewrite H2 in HEQ. injection HEQ as HEQ.
        apply (lbA_kg_nz_x (length l) ltac:(lia)). symmetry. exact HEQ. }
      split; [exact HlenS|].
      intros t Ht. destruct (Nat.eq_dec t k) as [->|Hne].
      + rewrite (H1 k ltac:(lia)) in HEQ. injection HEQ as HEQ. exact HEQ.
      + apply Hagr. lia. }
  destruct (MAIN 13%nat ltac:(lia)) as (Hlen13 & Hagr13).
  apply (nth_ext _ _ 0 0).
  { rewrite length_firstn, lbA_kg_len_x. lia. }
  intros t Ht. rewrite length_firstn in Ht.
  rewrite nth_firstn, (proj2 (Nat.ltb_lt t 13) ltac:(lia)).
  apply Hagr13. lia.
- intros HF i Hi _.
  assert (HLL : length (firstn 13 l) = length K_GESTURE) by (rewrite HF; reflexivity).
  rewrite length_firstn, lbA_kg_len_x in HLL.
  assert (Hik : (Z.to_nat i < 13)%nat) by lia.
  replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia.
  replace (y + i) with (y + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (H1 (Z.to_nat i) ltac:(lia)), (HY (Z.to_nat i) Hik). f_equal.
  rewrite <- HF, nth_firstn, (proj2 (Nat.ltb_lt (Z.to_nat i) 13) Hik). reflexivity.
Qed.

Lemma lbA_lsf_none_x : forall l i, (forall k, (k < length l)%nat -> nth k l 0 <> SPACE) ->
last_space_from i l = None.
Proof.
induction l as [|b l IH]; intros i H; [reflexivity|].
cbn [last_space_from].
rewrite (IH (S i) ltac:(intros k Hk; apply (H (S k)); cbn [length]; lia)).
cbv beta iota.
destruct (Z.eqb b SPACE) eqn:E; [|reflexivity].
exfalso. apply (H 0%nat ltac:(cbn [length]; lia)). cbn [nth].
exact (proj1 (Z.eqb_eq b SPACE) E).
Qed.

Lemma lbA_lsf_none_inv_x : forall l i, last_space_from i l = None ->
forall k, (k < length l)%nat -> nth k l 0 <> SPACE.
Proof.
induction l as [|b l IH]; intros i H k Hk; [cbn [length] in Hk; exfalso; lia|].
cbn [last_space_from] in H.
destruct (last_space_from (S i) l) eqn:E; cbv beta iota in H; [discriminate|].
destruct (Z.eqb b SPACE) eqn:Eb; cbv beta iota in H; [discriminate|].
destruct k as [|k].
- cbn [nth]. intros Hb. rewrite Hb, Z.eqb_refl in Eb. discriminate.
- cbn [nth]. apply (IH (S i) E k). cbn [length] in Hk. lia.
Qed.

Lemma lbA_lsf_some_x : forall l i k, (k < length l)%nat -> nth k l 0 = SPACE ->
(forall m, (k < m < length l)%nat -> nth m l 0 <> SPACE) ->
last_space_from i l = Some (i + k)%nat.
Proof.
induction l as [|b l IH]; intros i k Hk Hnth Hmax; [cbn [length] in Hk; exfalso; lia|].
cbn [last_space_from].
destruct k as [|k].
- rewrite (lbA_lsf_none_x l (S i) ltac:(intros m Hm; apply (Hmax (S m)); cbn [length]; lia)).
  cbn [nth] in Hnth. rewrite Hnth, Z.eqb_refl. cbv beta iota. f_equal. lia.
- rewrite (IH (S i) k ltac:(cbn [length] in Hk; lia) Hnth
    ltac:(intros m Hm; apply (Hmax (S m)); cbn [length]; lia)).
  cbv beta iota. f_equal. lia.
Qed.

Lemma lbA_lsf_spec_x : forall l i j, last_space_from i l = Some j ->
(i <= j < i + length l)%nat /\ nth (j - i) l 0 = SPACE /\
(forall m, (j - i < m < length l)%nat -> nth m l 0 <> SPACE).
Proof.
induction l as [|b l IH]; intros i j H; [cbn [last_space_from] in H; discriminate|].
cbn [last_space_from] in H.
destruct (last_space_from (S i) l) as [k|] eqn:E; cbv beta iota in H.
- injection H as <-.
  destruct (IH (S i) k E) as (Hr & Hn & Hm).
  split; [cbn [length]; lia|]. split.
  + replace (k - i)%nat with (S (k - S i)) by lia. cbn [nth]. exact Hn.
  + intros m Hm'. destruct m as [|m]; [exfalso; lia|].
    cbn [nth]. apply Hm. cbn [length] in Hm'. lia.
- destruct (Z.eqb b SPACE) eqn:Eb; cbv beta iota in H; [|discriminate].
  injection H as <-.
  split; [cbn [length]; lia|]. split.
  + replace (i - i)%nat with 0%nat by lia. cbn [nth]. exact (proj1 (Z.eqb_eq b SPACE) Eb).
  + intros m Hm'. destruct m as [|m]; [exfalso; lia|].
    cbn [nth]. apply (lbA_lsf_none_inv_x l (S i) E m). cbn [length] in Hm'. lia.
Qed.

Lemma lb_strrchr_x : forall rd x l (r : bv 64), lb_line rd x l -> 0 < x -> x + Z.of_nat (length l) < 2 ^ 63 ->
(((forall i, 0 <= i <= Z.of_nat (length l) -> rd (x + i) <> Some 32) /\ r = w64 0) \/
 (exists i, 0 <= i <= Z.of_nat (length l) /\ rd (x + i) = Some 32 /\
   (forall j, i < j <= Z.of_nat (length l) -> rd (x + j) <> Some 32) /\ r = w64 (x + i))) ->
(r = w64 0 /\ last_space_from 0 l = None) \/
(exists j, (j < length l)%nat /\ r = w64 (x + Z.of_nat j) /\ last_space_from 0 l = Some j).
Proof.
intros rd x l r (H1 & H2 & H3) Hx Hub [[HNo Hr]|[i (Hi & Hsp & Hmax & Hr)]].
- left. split; [exact Hr|]. apply lbA_lsf_none_x. intros k Hk Ek.
  apply (HNo (Z.of_nat k) ltac:(lia)). rewrite (H1 k Hk), Ek. reflexivity.
- right.
  assert (Hne : i <> Z.of_nat (length l)).
  { intros E. rewrite E, H2 in Hsp. discriminate. }
  assert (Hk : (Z.to_nat i < length l)%nat) by lia.
  assert (HthS : nth (Z.to_nat i) l 0 = SPACE).
  { assert (E := H1 (Z.to_nat i) Hk).
    replace (x + Z.of_nat (Z.to_nat i)) with (x + i) in E by lia.
    rewrite Hsp in E. injection E as E. symmetry. exact E. }
  assert (Hmx : forall m, (Z.to_nat i < m < length l)%nat -> nth m l 0 <> SPACE).
  { intros m Hm Em. apply (Hmax (Z.of_nat m) ltac:(lia)).
    rewrite (H1 m ltac:(lia)), Em. reflexivity. }
  exists (Z.to_nat i). split; [exact Hk|]. split.
  + rewrite Hr. f_equal. lia.
  + rewrite (lbA_lsf_some_x l 0%nat (Z.to_nat i) Hk HthS Hmx). reflexivity.
Qed.

Lemma lb_strcmp_iff_x : forall rd x y l w j, lb_line rd x l -> lb_lit rd y w -> (j < length l)%nat ->
((Z.of_nat (length l) - Z.of_nat j - 1 = Z.of_nat (length w) /\
  forall i, 0 <= i < Z.of_nat (length l) - Z.of_nat j - 1 -> rd (x + Z.of_nat j + 1 + i) = rd (y + i)) <->
 skipn (S j) l = w).
Proof.
intros rd x y l w j (H1 & H2 & H3) HW Hj.
assert (HSL : length (skipn (S j) l) = (length l - S j)%nat) by apply length_skipn.
split.
- intros (HLen & HA).
  apply (nth_ext _ _ 0 0).
  { rewrite HSL. lia. }
  intros t Ht. rewrite HSL in Ht. rewrite nth_skipn.
  assert (HT : rd (x + Z.of_nat j + 1 + Z.of_nat t) = rd (y + Z.of_nat t)) by (apply HA; lia).
  replace (x + Z.of_nat j + 1 + Z.of_nat t) with (x + Z.of_nat (S j + t)) in HT by lia.
  rewrite (H1 (S j + t)%nat ltac:(lia)), (HW t ltac:(lia)) in HT.
  injection HT as HT. transitivity (nth t (w ++ [0]) 0); [exact HT|].
  apply app_nth1. lia.
- intros HS.
  assert (HLw : length w = (length l - S j)%nat) by (rewrite <- HS; exact HSL).
  split; [lia|].
  intros i Hi.
  assert (Hti : (Z.to_nat i < length w)%nat) by lia.
  replace (x + Z.of_nat j + 1 + i) with (x + Z.of_nat (S j + Z.to_nat i)) by lia.
  replace (y + i) with (y + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (H1 (S j + Z.to_nat i)%nat ltac:(lia)), (HW (Z.to_nat i) ltac:(lia)).
  f_equal. rewrite app_nth1 by lia. rewrite <- HS, nth_skipn. reflexivity.
Qed.

Lemma lb_g_nok_x : forall l, firstn 13 l <> K_GESTURE -> gesture l = None.
Proof.
intros l H. unfold gesture.
destruct (list_eqb (firstn 13 l) K_GESTURE) eqn:E; [|reflexivity].
exfalso. apply H. exact (list_eqb_true _ _ E).
Qed.

Lemma lb_g_nsp_x : forall l, nth 13 l 0 <> SPACE -> gesture l = None.
Proof.
intros l H. unfold gesture.
destruct (Z.eqb (nth 13 l 0) SPACE) eqn:E.
- exfalso. apply H. exact (proj1 (Z.eqb_eq (nth 13 l 0) SPACE) E).
- destruct (list_eqb (firstn 13 l) K_GESTURE); reflexivity.
Qed.

Lemma lb_g_nolast_x : forall l, last_space_from 0 l = None -> gesture l = None.
Proof.
intros l H. unfold gesture. rewrite H.
match goal with |- (if ?c then _ else _) = None => destruct c end; reflexivity.
Qed.

Lemma lb_g_13_x : forall l, last_space_from 0 l = Some 13%nat -> gesture l = None.
Proof.
intros l H. unfold gesture. rewrite H.
match goal with |- (if ?c then _ else _) = None => destruct c end; reflexivity.
Qed.

Lemma lb_g_last_x : forall l j, nth 13 l 0 = SPACE -> last_space_from 0 l = Some j ->
(13 <= j < length l)%nat /\ nth j l 0 = SPACE.
Proof.
intros l j HS HL.
destruct (lbA_lsf_spec_x l 0%nat j HL) as (Hr & Hn & Hm).
rewrite Nat.sub_0_r in Hn. rewrite Nat.sub_0_r in Hm.
assert (H13 : (13 < length l)%nat).
{ destruct (Nat.ltb 13 (length l)) eqn:E; [exact (proj1 (Nat.ltb_lt 13 (length l)) E)|].
  pose proof (proj1 (Nat.ltb_ge 13 (length l)) E) as E'. exfalso.
  rewrite nth_overflow in HS by lia. unfold SPACE in HS. lia. }
assert (Hge : (13 <= j)%nat).
{ destruct (Nat.leb 13 j) eqn:E; [exact (proj1 (Nat.leb_le 13 j) E)|].
  pose proof (proj1 (Nat.leb_gt 13 j) E) as E'. exfalso. apply (Hm 13%nat ltac:(lia)). exact HS. }
split; [lia|]. exact Hn.
Qed.

Lemma lb_g_some_x : forall l j, firstn 13 l = K_GESTURE -> nth 13 l 0 = SPACE -> last_space_from 0 l = Some j ->
(13 < j)%nat ->
gesture l = if list_eqb (skipn (S j) l) W_BEGIN then Some (GBegin, firstn j l)
            else if list_eqb (skipn (S j) l) W_END then Some (GEnd, firstn j l) else None.
Proof.
intros l j HK HS HL HJ.
destruct (lb_g_last_x l j HS HL) as ((Hge & Hlt) & _).
unfold gesture. rewrite HK, HS, HL, list_eqb_refl, Z.eqb_refl. cbv beta iota.
rewrite (proj2 (Nat.ltb_lt 13 (length l))) by lia.
rewrite (proj2 (Nat.ltb_lt 13 j)) by lia. reflexivity.
Qed.

Lemma lb_list_eqb_x : forall a b, list_eqb a b = true <-> a = b.
Proof.
intros a b. unfold list_eqb. destruct (list_eq_dec Z.eq_dec a b); split; congruence.
Qed.

(* ---- what the calls leave: every byte the cut's representations read lies below alloc_ceiling + 8 (a live block of
   the ARx state, the image) or in drain's frame (lb_keep / lbB_low, cited) ---- *)
Ltac lbB_in_x := repeat (first [left; reflexivity | right]).

Lemma lbB_blk_low_x : forall ly S Hp (W : world SEGS) mem md q n a,
ARx ly S Hp W mem md -> In (q, n) (ablocks B ly S) -> q <= a -> a < q + req_size n + 8 -> lbB_low a.
Proof.
intros ly S Hp W mem md q n a HAR Hin H1 H2.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md q n HAR Hin) as (_ & H4096 & Hceil & _).
unfold lbB_low. lia.
Qed.

Lemma lbB_img_low_x : forall a lo hi, 0x10000 <= lo -> lo <= a -> a < hi -> hi <= IMG_TOP -> lbB_low a.
Proof. intros a lo hi H1 H2 H3 H4. pose proof asan_consts as (C1 & _). unfold lbB_low, IMG_TOP in *. lia. Qed.

Lemma lbB_recs_len_x : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma lbB_key_ptrs_len_x : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|].
unfold key_ptrs in *. cbn [map concat length]. rewrite length_app, Mem.length_le8, IH. lia.
Qed.

Lemma lbB_eb_len_x : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
length (entry_bytes e) = 56%nat.
Proof.
intros e H1 H2. unfold entry_bytes.
rewrite !length_app, !Mem.length_le4, !Mem.length_le8, H1, H2. reflexivity.
Qed.

Lemma lbB_alist_fp_low_x : forall ly S Hp (W : world SEGS) mem md LA l lns lo hi,
ARx ly S Hp W mem md -> alist_at B ly S W mem LA l lns ->
0x10000 <= lo -> lo <= LA -> LA + 16 <= hi -> hi <= IMG_TOP ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> lbB_low a.
Proof.
intros ly S Hp W mem md LA l lns lo hi HAR HL Hlo1 Hlo2 Hhi1 Hhi2 r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (lbB_img_low_x a lo hi); unfold IMG_TOP in *; lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, lbB_recs_len_x in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (lbB_blk_low_x ly S Hp W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin); [lia|].
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as (_ & Hrq).
    unfold hl_n in Hn, Hj. unfold AREC in *. lia.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs q Hq) as (Hin & _).
    apply (lbB_blk_low_x ly S Hp W mem md (fst q) (Z.of_nat (length (snd q)) + 1) a HAR Hin); [lia|].
    pose proof (req_size_pos (Z.of_nat (length (snd q)) + 1) ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma lbB_asrc_fp_low_x : forall ly S Hp (W : world SEGS) mem md HA h,
ARx ly S Hp W mem md -> asrc_at B ly S W mem HA h ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> lbB_low a.
Proof.
intros ly S Hp W mem md HA h HAR HS Hlo Hhi r Hr a Ha.
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (lbB_img_low_x a (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  apply (lbB_blk_low_x ly S Hp W mem md (hs_partial h) APARTIAL a HAR Hpb); [lia|].
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + refine (lbB_alist_fp_low_x ly S Hp W mem md (HA + 16) (hs_pending h) false (rg_s RG) (rg_s RG + 4 * ASRC)
      HAR Hpend _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * refine (lbB_alist_fp_low_x ly S Hp W mem md (HA + 64) (hs_expected h) true (rg_s RG) (rg_s RG + 4 * ASRC)
        HAR Hexp _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
    * refine (lbB_alist_fp_low_x ly S Hp W mem md (HA + 80) (hs_held h) true (rg_s RG) (rg_s RG + 4 * ASRC)
        HAR Hheld _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
Qed.

Lemma lbB_aout_fp_low_x : forall ly S Hp (W : world SEGS) mem md c O mx no cap out,
ARx ly S Hp W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> lbB_low a.
Proof.
intros ly S Hp W mem md c O mx no cap out HAR HOUT r Hr a Ha.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (GL : forall x l, In (x, l) (G_DR B RG) -> x <= a < x + l -> lbB_low a).
{ intros x l Hin Hx.
  assert (HI : inG (G_DR B RG) a)
    by (unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low SEGS B pa_segs_low _ a HG HI). unfold lbB_low. lia. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- pose proof HSM as (Hs1 & Hs2). apply (lbB_img_low_x a (rg_send_max RG) (rg_send_max RG + 8)); unfold IMG_TOP in *; lia.
- apply (GL (rg_nout RG) 8); [unfold G_DR, G_SL; lbB_in_x | lia].
- apply (GL (rg_capout RG) 8); [unfold G_DR, G_SL; lbB_in_x | lia].
- apply (GL (rg_out RG) 8); [unfold G_DR, G_SL; lbB_in_x | lia].
- pose proof (pa_obj_img 9 ltac:(lia)) as H9. rewrite HV9 in H9.
  apply (lbB_img_low_x a (rg_client RG) (rg_client RG + 4)); unfold IMG_TOP in *; lia.
- apply (GL (rg_client_broken RG) 1); [unfold G_DR, G_SL; lbB_in_x | lia].
- pose proof HSD as (Hd1 & Hd2). apply (lbB_img_low_x a (rg_send_dead RG) (rg_send_dead RG + 1)); unfold IMG_TOP in *; lia.
- apply (GL (rg_send_eintr RG) 1); [unfold G_DR, G_SL; lbB_in_x | lia].
- apply (GL (as_errno B) 4); [unfold G_DR, G_SL; lbB_in_x | lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  apply (lbB_blk_low_x ly S Hp W mem md out cap a HAR Hin); [lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma lbB_eokx_x : forall ly S Hp (W : world SEGS) mem md mem' e,
ARx ly S Hp W mem md -> aentry_okx B ly S W mem e ->
(forall a, lbB_low a -> abyte_kept W mem W mem' a) -> aentry_okx B ly S W mem' e.
Proof.
intros ly S Hp W mem md mem' e HAR HE KL.
destruct HE as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14).
do 8 (split; [assumption|]).
split.
{ destruct H9 as [H9 | (Hc & Hin & Hj & Hg)]; [left; exact H9|right].
  split; [exact Hc|]. split; [exact Hin|]. split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. apply KL. apply (lbB_blk_low_x ly S Hp W mem md (re_buf e) (re_cap e) x HAR Hin); [lia|].
  unfold bzs in Hx. rewrite length_map, length_app in Hx.
  pose proof (req_size_pos (re_cap e) ltac:(lia)) as (_ & Hrq). lia. }
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H11|right].
  split; [exact Hz|]. split; [exact Hin|]. split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. apply KL. apply (lbB_blk_low_x ly S Hp W mem md (re_hp e) (re_kh e) x HAR Hin); [lia|].
  unfold bzs in Hx. rewrite length_map, lbB_key_ptrs_len_x in Hx. unfold re_nheld in Hk1.
  pose proof (req_size_pos (re_kh e) ltac:(lia)) as (_ & Hrq). lia. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3 & K4).
split; [exact K1|]. split; [|split; [exact K3 | exact K4]].
apply (akept_garr8 W mem); [|exact K2].
intros x Hx. apply KL.
apply (lbB_blk_low_x ly S Hp W mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) x HAR K1); [lia|].
unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx.
pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma lbB_rom_x : forall (W : world SEGS) mem m',
(forall a, lbB_low a -> abyte_kept W mem W m' a) -> rom_view SEGS W mem -> rom_view SEGS W m'.
Proof.
intros W mem m' KL HR a Ha. pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (Hl : 0 <= a < kLowMemEnd).
{ destruct Ha as (sg & Hsg & _ & Hr). exact (pa_segs_low a ltac:(exists sg; split; [exact Hsg | exact Hr])). }
rewrite (proj1 (KL a ltac:(unfold lbB_low; lia))). exact (HR a Ha).
Qed.

Lemma lbB_stk_x : forall cx Hp kr, DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
alloc_ceiling + DRAIN_STK <= dsp0 cx /\ dsp0 cx <= 2 ^ 47.
Proof.
intros cx Hp kr HB. unfold DBASE_x in HB. destruct HB as (Hafn & _).
destruct Hafn as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
unfold dsp0. unfold DRAIN_STK_x in *. lia.
Qed.

Lemma lbB_kept_x : forall cx (W1 : world SEGS) m1 m2 a, lb_keep cx W1 m1 m2 -> 0 <= a < 2 ^ 64 ->
~ (dsp0 cx - DRAIN_FRAME - 2 * ESTACK <= a < dsp0 cx - DRAIN_FRAME) -> abyte_kept W1 m1 W1 m2 a.
Proof.
intros cx W1 m1 m2 a (HV & HP) Ha Hw. split; [exact (HV a Ha Hw)|].
unfold arm. apply writable_kept. intros Hpa. exact (HP a Hpa).
Qed.

Lemma lbB_low_kept_x : forall cx Hp kr (W1 : world SEGS) m1 m2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> lb_keep cx W1 m1 m2 -> forall a, lbB_low a -> abyte_kept W1 m1 W1 m2 a.
Proof.
intros cx Hp kr W1 m1 m2 HB HK a Ha.
pose proof (lbB_stk_x cx Hp kr HB) as (H1 & H2). pose proof asan_consts as (C1 & _).
assert (EF : DRAIN_FRAME = 352) by reflexivity. assert (ES : DRAIN_STK = 16880) by reflexivity.
assert (EE : ESTACK = 4096) by reflexivity.
unfold lbB_low in Ha. apply (lbB_kept_x cx W1 m1 m2 a HK); lia.
Qed.

Lemma lbB_hi_kept_x : forall cx Hp kr (W1 : world SEGS) m1 m2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> lb_keep cx W1 m1 m2 ->
forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W1 m1 W1 m2 a.
Proof.
intros cx Hp kr W1 m1 m2 HB HK a Ha.
pose proof (lbB_stk_x cx Hp kr HB) as (H1 & H2). pose proof asan_consts as (C1 & _).
assert (EF : DRAIN_FRAME = 352) by reflexivity. assert (ES : DRAIN_STK = 16880) by reflexivity.
assert (EE : ESTACK = 4096) by reflexivity.
apply (lbB_kept_x cx W1 m1 m2 a HK); lia.
Qed.

Lemma lbB_vm_hi_x : forall cx Hp kr (W1 : world SEGS) m1 m2 a n v,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> lb_keep cx W1 m1 m2 ->
dsp0 cx - DRAIN_FRAME <= a -> a + Z.of_nat n <= dsp0 cx ->
val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W1 m2) a n v.
Proof.
intros cx Hp kr W1 m1 m2 a n v HB HK H1 H2 Hv.
apply (akept_vm W1 m1); [|exact Hv].
intros x Hx. apply (lbB_hi_kept_x cx Hp kr W1 m1 m2 HB HK). lia.
Qed.

Lemma lbB_frame_x : forall cx Hp kr (W1 : world SEGS) m1 m2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> lb_keep cx W1 m1 m2 -> dr_frame RG cx W1 m1 -> dr_frame RG cx W1 m2.
Proof.
intros cx Hp kr W1 m1 m2 HB HK HF.
assert (EF : DRAIN_FRAME = 352) by reflexivity.
assert (V : forall a n v, dsp0 cx - DRAIN_FRAME <= a -> a + Z.of_nat n <= dsp0 cx ->
  val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W1 m2) a n v)
  by (intros a n v H1 H2 Hv; exact (lbB_vm_hi_x cx Hp kr W1 m1 m2 a n v HB HK H1 H2 Hv)).
unfold dr_frame in HF |- *. cbv zeta in HF |- *.
destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 &
  F19 & F20 & F21 & F22 & F23 & FS).
repeat match goal with |- _ /\ _ => split end;
  try (apply V; [lia | lia | assumption]).
unfold dr_saved in FS |- *. intros i Hi. apply V; [unfold DR_SAVE_OFF; lia | unfold DR_SAVE_OFF; lia | exact (FS i Hi)].
Qed.

(* the four frame slots this path reads, after any change of memory that keeps drain's frame *)
Lemma lb_frame_slots_x : forall cx Hp kr (W1 : world SEGS) m1 m2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> lb_keep cx W1 m1 m2 -> dr_frame RG cx W1 m1 ->
val_mem SEGS (arm W1 m2) (dsp0 cx - DRAIN_FRAME + 128) 8 (dxSA cx + 16) /\
val_mem SEGS (arm W1 m2) (dsp0 cx - DRAIN_FRAME + 136) 8 (dxSA cx + 24) /\
val_mem SEGS (arm W1 m2) (dsp0 cx - DRAIN_FRAME + 144) 8 (dxSA cx) /\
val_mem SEGS (arm W1 m2) (dsp0 cx - DRAIN_FRAME + 240) 8 SHADOW_OFF.
Proof.
intros cx Hp kr W1 m1 m2 HB HK HF. pose proof (lbB_frame_x cx Hp kr W1 m1 m2 HB HK HF) as HF2.
unfold dr_frame in HF2. cbv zeta in HF2.
destruct HF2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F128 & F136 & F144 & _ & _ & _ & _ & _ & _ & _ & _ &
  F240 & _).
exact (conj F128 (conj F136 (conj F144 F240))).
Qed.


Lemma lb_dregs_keep_x : forall cx Hp kr regs1 regs2 W1 m1 m2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> dregs_line RG cx regs1 W1 m1 ->
spZ regs2 = spZ regs1 ->
getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 -> getr regs2 21 = getr regs1 21 ->
getr regs2 20 = getr regs1 20 -> getr regs2 22 = getr regs1 22 -> getr regs2 27 = getr regs1 27 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
lb_keep cx W1 m1 m2 ->
dregs_line RG cx regs2 W1 m2.
Proof.
intros cx Hp kr regs1 regs2 W1 m1 m2 HB HR Hsp H3 H4 H21 H20 H22 H27 H8 H9 H18 HK.
unfold dregs_line in HR |- *.
destruct HR as (R0 & R3 & R4 & R21 & R20 & R22 & R27 & R8 & R9 & R18 & RF).
rewrite Hsp, H3, H4, H21, H20, H22, H27, H8, H9, H18.
exact (conj R0 (conj R3 (conj R4 (conj R21 (conj R20 (conj R22 (conj R27 (conj R8 (conj R9 (conj R18
  (lbB_frame_x cx Hp kr W1 m1 m2 HB HK RF))))))))))).
Qed.

(* ---- the model: the line [p, q) is the next one drain's scan keeps; a non-gesture line updates nothing ---- *)
Lemma lbB_scan_zero_fst_x : forall sk acc d, fst (scan sk acc (0 :: d)) = fst (scan false [] d).
Proof. intros sk acc d. rewrite scan_zero. destruct (scan false [] d) as [[a b] c]. reflexivity. Qed.

Lemma lbB_scan_zero_snd_x : forall sk acc d, snd (scan sk acc (0 :: d)) =
  if (sk || Nat.ltb LINE_LIMIT (length acc))%bool then snd (scan false [] d) else acc :: snd (scan false [] d).
Proof. intros sk acc d. rewrite scan_zero. destruct (scan false [] d) as [[a b] c]. reflexivity. Qed.

Lemma lbB_scan_nz_app_x : forall u sk acc d, nozero u -> scan sk acc (u ++ d) = scan sk (acc ++ u) d.
Proof.
induction u as [|b u IH]; intros sk acc d Hz.
- rewrite app_nil_r. reflexivity.
- pose proof (Forall_inv Hz) as Hb. pose proof (Forall_inv_tail Hz) as Hu. cbn [app].
  rewrite (scan_nz sk acc b (u ++ d) Hb), (IH sk (acc ++ [b]) d Hu), <- app_assoc. reflexivity.
Qed.

Lemma lbB_nth_skipn_cons_x : forall (l : list Z) n x, nth_error l n = Some x -> skipn n l = x :: skipn (S n) l.
Proof.
induction l as [|a l IH]; intros n x Hn; [rewrite nth_error_nil in Hn; discriminate|].
destruct n as [|n].
- change (Some a = Some x) in Hn. injection Hn as ->. reflexivity.
- exact (IH n x Hn).
Qed.

Lemma lbB_firstn_nth_app_x : forall (l : list Z) n x, nth_error l n = Some x -> firstn (S n) l = firstn n l ++ [x].
Proof.
induction l as [|a l IH]; intros n x Hn; [rewrite nth_error_nil in Hn; discriminate|].
destruct n as [|n].
- change (Some a = Some x) in Hn. injection Hn as ->. reflexivity.
- change (firstn (S (S n)) (a :: l)) with (a :: firstn (S n) l). rewrite (IH n x Hn). reflexivity.
Qed.

Lemma lbB_firstn_split_x : forall P Q (l : list Z), (P <= Q)%nat -> firstn Q l = firstn P l ++ firstn (Q - P) (skipn P l).
Proof.
induction P as [|P IH]; intros Q l HPQ.
- rewrite Nat.sub_0_r. reflexivity.
- destruct Q as [|Q]; [lia|]. destruct l as [|a l].
  + rewrite skipn_nil, !firstn_nil. reflexivity.
  + change (a :: firstn Q l = a :: firstn P l ++ firstn (Q - P) (skipn P l)).
    rewrite (IH Q l) by lia. reflexivity.
Qed.

Lemma lbB_nth_skipn_x : forall (l : list Z) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
induction l as [|a l IH]; intros n i.
- rewrite skipn_nil, !nth_error_nil. reflexivity.
- destruct n as [|n]; [reflexivity|]. change (nth_error (skipn n l) i = nth_error l (n + i)). apply IH.
Qed.

Lemma lbB_nz_firstn_x : forall (l : list Z) k, (forall i, (i < k)%nat -> nth_error l i <> Some 0) -> nozero (firstn k l).
Proof.
unfold nozero. induction l as [|a l IH]; intros k H.
- rewrite firstn_nil. constructor.
- destruct k as [|k]; [change (Forall (fun b => b <> 0) (@nil Z)); constructor|].
  change (Forall (fun b => b <> 0) (a :: firstn k l)). constructor.
  + intro E. apply (H 0%nat); [lia|]. rewrite E. reflexivity.
  + apply IH. intros i Hi. exact (H (S i) ltac:(lia)).
Qed.

Lemma lbB_scan_app_z_x : forall p sk acc q,
  fst (scan sk acc (p ++ 0 :: q)) = fst (scan false [] q) /\
  snd (scan sk acc (p ++ 0 :: q)) = snd (scan sk acc (p ++ [0])) ++ snd (scan false [] q).
Proof.
induction p as [|b p IH]; intros sk acc q.
- cbn [app]. rewrite lbB_scan_zero_fst_x, !lbB_scan_zero_snd_x. cbn [scan snd]. split; [reflexivity|].
  destruct (sk || Nat.ltb LINE_LIMIT (length acc))%bool; reflexivity.
- cbn [app]. destruct (Z.eq_dec b 0) as [->|Hb].
  + rewrite lbB_scan_zero_fst_x, !lbB_scan_zero_snd_x. destruct (IH false [] q) as [I1 I2].
    split; [exact I1|]. rewrite I2. destruct (sk || Nat.ltb LINE_LIMIT (length acc))%bool; reflexivity.
  + rewrite (scan_nz sk acc b (p ++ 0 :: q) Hb), (scan_nz sk acc b (p ++ [0]) Hb). apply IH.
Qed.

Lemma lbB_dline_len_x : forall s1 p q, (p <= q < length (dW s1))%nat -> length (dline s1 p q) = (q - p)%nat.
Proof. intros s1 p q H. unfold dline. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. Qed.

Lemma lbB_dline_nz_x : forall s1 p q,
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) -> nozero (dline s1 p q).
Proof.
intros s1 p q H. unfold dline. apply lbB_nz_firstn_x. intros i Hi. rewrite lbB_nth_skipn_x. apply H. lia.
Qed.

Lemma lbB_dW_split_x : forall s1 p q, (p <= q)%nat -> nth_error (dW s1) q = Some 0 ->
  skipn p (dW s1) = dline s1 p q ++ 0 :: skipn (S q) (dW s1).
Proof.
intros s1 p q HPQ HQ. unfold dline. rewrite <- (lbB_nth_skipn_cons_x _ _ _ HQ).
rewrite <- (firstn_skipn (q - p) (skipn p (dW s1))) at 1.
rewrite skipn_skipn. replace (q - p + p)%nat with q by lia. reflexivity.
Qed.

Lemma lbB_dW_pre_line_x : forall s1 p q, (p <= q)%nat -> nth_error (dW s1) q = Some 0 ->
  firstn (S q) (dW s1) = firstn p (dW s1) ++ dline s1 p q ++ [0].
Proof.
intros s1 p q HPQ HQ. rewrite (lbB_firstn_nth_app_x _ _ _ HQ), (lbB_firstn_split_x p q _ HPQ), <- app_assoc.
reflexivity.
Qed.

Lemma lbB_scan_pre_x : forall s1 p r, dbound s1 p ->
  fst (scan (drain_b_c.ds_skip s1) [] (firstn p (dW s1) ++ r)) = fst (scan (dskp s1 p) [] r) /\
  snd (scan (drain_b_c.ds_skip s1) [] (firstn p (dW s1) ++ r)) = drlp s1 p ++ snd (scan (dskp s1 p) [] r).
Proof.
intros s1 p r (HP & HN). destruct p as [|p]; [split; reflexivity|].
assert (HN' : nth_error (dW s1) p = Some 0).
{ destruct HN as [H0|H0]; [discriminate|]. replace p with (S p - 1)%nat by lia. exact H0. }
unfold drlp, dskp. cbn [Nat.eqb]. rewrite (lbB_firstn_nth_app_x _ _ _ HN'), <- app_assoc. cbn [app].
exact (lbB_scan_app_z_x (firstn p (dW s1)) (drain_b_c.ds_skip s1) [] r).
Qed.

Lemma lbB_scan_line_x : forall sk ln r, nozero ln ->
  fst (scan sk [] (ln ++ 0 :: r)) = fst (scan false [] r) /\
  snd (scan sk [] (ln ++ 0 :: r)) =
    (if (sk || Nat.ltb LINE_LIMIT (length ln))%bool then [] else [ln]) ++ snd (scan false [] r).
Proof.
intros sk ln r Hz. rewrite (lbB_scan_nz_app_x ln sk [] _ Hz). cbn [app].
rewrite lbB_scan_zero_fst_x, lbB_scan_zero_snd_x.
split; [reflexivity|]. destruct (sk || Nat.ltb LINE_LIMIT (length ln))%bool; reflexivity.
Qed.

Lemma lbB_drl_line_x : forall s1 p q, dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
  (forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) ->
  drlp s1 (S q) = drlp s1 p ++ (if (dskp s1 p || Nat.ltb LINE_LIMIT (q - p))%bool then [] else [dline s1 p q]) /\
  drlq s1 p = (if (dskp s1 p || Nat.ltb LINE_LIMIT (q - p))%bool then [] else [dline s1 p q]) ++ drlq s1 (S q).
Proof.
intros s1 p q HB HPQ HQ HNZ.
pose proof (lbB_dline_nz_x s1 p q HNZ) as Hz. rewrite <- (lbB_dline_len_x s1 p q HPQ). split.
- unfold drlp at 1. rewrite (lbB_dW_pre_line_x s1 p q (proj1 HPQ) HQ), (proj2 (lbB_scan_pre_x s1 p _ HB)).
  rewrite (proj2 (lbB_scan_line_x (dskp s1 p) (dline s1 p q) [] Hz)). cbn [scan snd]. rewrite app_nil_r.
  reflexivity.
- unfold drlq at 1. rewrite (lbB_dW_split_x s1 p q (proj1 HPQ) HQ).
  rewrite (proj2 (lbB_scan_line_x (dskp s1 p) (dline s1 p q) _ Hz)). reflexivity.
Qed.

Lemma lbB_drl_x : forall s1 p q,
dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) -> dskp s1 p = false ->
(q - p <= LINE_LIMIT)%nat ->
drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] /\
drlq s1 p = dline s1 p q :: drlq s1 (S q) /\
dskp s1 (S q) = false.
Proof.
intros s1 p q HB HPQ HQ HNZ HK HL.
destruct (lbB_drl_line_x s1 p q HB HPQ HQ HNZ) as [E1 E2].
rewrite HK, (proj2 (Nat.ltb_ge LINE_LIMIT (q - p)) HL) in E1, E2. cbn [orb app] in E1, E2.
split; [exact E1|]. split; [exact E2|reflexivity].
Qed.

Lemma lbB_with_nul_cons_x : forall l r, with_nul (l :: r) = (l ++ [0]) ++ with_nul r.
Proof. reflexivity. Qed.

Lemma lbB_lrun_one_x : forall lv mx0 no0 cp0 H0 ka0 l,
  lrun lv mx0 no0 cp0 H0 ka0 [l] =
  (send_line_b_c.send_line_cap lv mx0 no0 cp0 (Z.of_nat (length l) + 1), seen_arr H0 l, seen_ka H0 ka0 l).
Proof.
intros lv mx0 no0 cp0 H0 ka0 l. unfold lrun. cbn [drain_b_c.lines_run fst snd]. rewrite seen_tr_m. reflexivity.
Qed.

Lemma lbB_lrun_app_x : forall lv mx0 l1 l2 no0 cp0 H0 ka0,
  lrun lv mx0 no0 cp0 H0 ka0 (l1 ++ l2) =
  lrun lv mx0 (no0 + Z.of_nat (length (with_nul l1))) (fst (fst (lrun lv mx0 no0 cp0 H0 ka0 l1)))
    (snd (fst (lrun lv mx0 no0 cp0 H0 ka0 l1))) (snd (lrun lv mx0 no0 cp0 H0 ka0 l1)) l2.
Proof.
intros lv mx0 l1. induction l1 as [|l r IH]; intros l2 no0 cp0 H0 ka0.
- rewrite app_nil_l. change (with_nul []) with (@nil Z). cbn [length Z.of_nat]. rewrite Z.add_0_r. reflexivity.
- assert (C : forall nb cb Hb kb ls, lrun lv mx0 nb cb Hb kb (l :: ls) =
               lrun lv mx0 (nb + (Z.of_nat (length l) + 1))
                 (send_line_b_c.send_line_cap lv mx0 nb cb (Z.of_nat (length l) + 1))
                 (seen_arr Hb l) (seen_ka Hb kb l) ls).
  { intros nb cb Hb kb ls. unfold lrun at 1. cbn [drain_b_c.lines_run fst snd]. rewrite lines_run_m, seen_tr_m.
    reflexivity. }
  rewrite <- app_comm_cons, !C, IH.
  replace (no0 + (Z.of_nat (length l) + 1) + Z.of_nat (length (with_nul r)))
    with (no0 + Z.of_nat (length (with_nul (l :: r))))
    by (rewrite lbB_with_nul_cons_x, !length_app; cbn [length]; lia).
  reflexivity.
Qed.

Lemma lbB_dlno_x : forall s1 p q, drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] ->
dlno s1 (S q) = dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1.
Proof.
intros s1 p q E. unfold dlno. rewrite E. unfold with_nul. rewrite map_app, concat_app. cbn [map concat].
rewrite app_nil_r, !length_app. cbn [length]. lia.
Qed.

Lemma lbB_dlrun_x : forall (cx : dcx) s1 p q, drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] ->
dlrun cx s1 (S q) =
(send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
   (Z.of_nat (length (dline s1 p q)) + 1),
 seen_arr (dlH cx s1 p) (dline s1 p q),
 seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)).
Proof.
intros cx s1 p q E. unfold dlrun at 1. rewrite E, lbB_lrun_app_x, lbB_lrun_one_x.
unfold dlno, dloc, dlH, dlka, dlrun. reflexivity.
Qed.

Lemma lbB_dloc_x : forall (cx : dcx) s1 p q, drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] ->
dloc cx s1 (S q) = send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
  (Z.of_nat (length (dline s1 p q)) + 1).
Proof.
intros cx s1 p q E. change (dloc cx s1 (S q)) with (fst (fst (dlrun cx s1 (S q)))).
rewrite (lbB_dlrun_x cx s1 p q E). reflexivity.
Qed.

Lemma lbB_dlH_x : forall (cx : dcx) s1 p q, drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] ->
dlH cx s1 (S q) = seen_arr (dlH cx s1 p) (dline s1 p q).
Proof.
intros cx s1 p q E. change (dlH cx s1 (S q)) with (snd (fst (dlrun cx s1 (S q)))).
rewrite (lbB_dlrun_x cx s1 p q E). reflexivity.
Qed.

Lemma lbB_dlka_x : forall (cx : dcx) s1 p q, drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] ->
dlka cx s1 (S q) = seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q).
Proof.
intros cx s1 p q E. change (dlka cx s1 (S q)) with (snd (dlrun cx s1 (S q))).
rewrite (lbB_dlrun_x cx s1 p q E). reflexivity.
Qed.

Lemma lbB_seen_tr_none_x : forall H ka l j ha ks, gesture l = None ->
drain_b_c.seen_tr H ka l j ha ks = ([], ka, (ha, ks)).
Proof. intros H ka l j ha ks Hg. unfold drain_b_c.seen_tr. rewrite Hg. reflexivity. Qed.

Lemma lbB_seen_arr_none_x : forall H l, gesture l = None -> seen_arr H l = H.
Proof. intros H l Hg. unfold seen_arr. rewrite Hg. reflexivity. Qed.

Lemma lbB_seen_ka_none_x : forall H ka l, gesture l = None -> seen_ka H ka l = ka.
Proof. intros H ka l Hg. unfold seen_ka. rewrite (lbB_seen_tr_none_x H ka l _ _ _ Hg). reflexivity. Qed.

Lemma lbB_upds_none_x : forall G ls l, gesture l = None -> upds G (ls ++ [l]) = upds G ls.
Proof.
intros G ls l Hg. unfold upds. rewrite fold_left_app. cbn [fold_left]. unfold RelayModel.upd. rewrite Hg.
reflexivity.
Qed.




(* ---- the keep of drain's frame and of the low bytes across the walk's runs and calls ---- *)
Lemma lb_scr_lo_x : forall cx Hp kr, DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
alloc_ceiling + 8 <= dsp0 cx - DRAIN_FRAME - 2 * ESTACK /\ dsp0 cx <= 2 ^ 47 /\ dsp0 cx mod 16 = 0.
Proof.
intros cx Hp kr HB. pose proof HB as (Hafn & _). pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (DRAIN_STK_x = 17008) by reflexivity. unfold dsp0, DRAIN_FRAME, ESTACK. lia.
Qed.

Lemma lb_keep_refl_x : forall cx W m, lb_keep cx W m m.
Proof. intros cx W m. split; [intros; reflexivity | intros x H; exact H]. Qed.

Lemma lb_keep_run_x : forall cx W m1 m2 m3 E rs, lb_keep cx W m1 m2 ->
frame_of E rs (mrestrict (w_H W) m2) (mrestrict (w_H W) m3) ->
mem_grows (mrestrict (w_H W) m2) (mrestrict (w_H W) m3) ->
(forall a, ~ in_wrange E rs a) -> lb_keep cx W m1 m3.
Proof.
intros cx W m1 m2 m3 E rs [K1 P1] HF HGr HW. split.
- intros x Hx Hs. rewrite (aview_kept_out E rs (w_H W) m2 m3 HF x Hx (HW x)). exact (K1 x Hx Hs).
- intros x Hpa. apply (apresent_grows _ _ _ _ HGr). exact (P1 x Hpa).
Qed.

Lemma lb_keep_call_x : forall cx W m1 m2 m3, lb_keep cx W m1 m2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ False -> ~ (dsp0 cx + - DRAIN_FRAME - 2 * ESTACK <= a < dsp0 cx + - DRAIN_FRAME) ->
  aview SEGS (w_H W) m3 a = aview SEGS (w_H W) m2 a) ->
(forall a, apresent (w_H W) m2 a -> apresent (w_H W) m3 a) -> lb_keep cx W m1 m3.
Proof.
intros cx W m1 m2 m3 [K1 P1] K2 P2. split.
- intros x Hx Hs. rewrite (K2 x Hx (fun f => f) ltac:(intros Hs'; apply Hs; lia)). exact (K1 x Hx Hs).
- intros x Hpa. exact (P2 x (P1 x Hpa)).
Qed.

Lemma lb_keep_low_x : forall cx Hp kr W m1 m2 a, DBASE_x B ARx MT RP MMAX RG cx Hp kr -> lb_keep cx W m1 m2 ->
0 <= a < alloc_ceiling + 8 -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a.
Proof.
intros cx Hp kr W m1 m2 a HB [K _] Ha. pose proof (lb_scr_lo_x cx Hp kr HB) as (L & _).
pose proof asan_consts as (C1 & _).
apply K; lia.
Qed.

Lemma lb_keep_rom_x : forall cx Hp kr W m1 m2, DBASE_x B ARx MT RP MMAX RG cx Hp kr -> lb_keep cx W m1 m2 ->
rom_view SEGS W m1 -> rom_view SEGS W m2.
Proof.
intros cx Hp kr W m1 m2 HB HK HR a Ha. pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (Hl : 0 <= a < kLowMemEnd).
{ destruct Ha as (sg & Hsg & _ & Hr). exact (pa_segs_low a ltac:(exists sg; split; [exact Hsg | exact Hr])). }
rewrite (lb_keep_low_x cx Hp kr W m1 m2 a HB HK ltac:(lia)). exact (HR a Ha).
Qed.

Lemma lb_garr8_vis_x : forall (W : world SEGS) m base l a, garr8 SEGS (arm W m) base l ->
base <= a < base + Z.of_nat (length l) -> aview SEGS (w_H W) m a <> None.
Proof.
intros W m base l a Hg Ha.
replace a with (base + Z.of_nat (Z.to_nat (a - base))) by lia.
unfold aview. change (mrestrict (w_H W) m) with (arm W m).
rewrite (garr8_mbyte SEGS (arm W m) base l (Z.to_nat (a - base)) Hg ltac:(lia)). cbn [option_map]. discriminate.
Qed.

Lemma lb_tail_arith_x : forall b c t a, b mod 16 = 0 -> (c = 8192 \/ c = 16384) -> b <= t < b + c ->
t < a < t - t mod 8 + 8 -> a < b + c.
Proof.
intros b c t a Hb Hc Ht Ha.
pose proof (Z.div_mod t 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound t 8 ltac:(lia)) as M1.
pose proof (Z.div_mod b 16 ltac:(lia)) as D2. rewrite Hb in D2. lia.
Qed.

Lemma lb_keep_byte_x : forall cx Hp kr W m1 m2 a, DBASE_x B ARx MT RP MMAX RG cx Hp kr -> lb_keep cx W m1 m2 ->
0 <= a < alloc_ceiling + 8 -> abyte_kept W m1 W m2 a.
Proof.
intros cx Hp kr W m1 m2 a HB HK Ha. split; [exact (lb_keep_low_x cx Hp kr W m1 m2 a HB HK Ha)|].
unfold arm. apply writable_kept. intros Hpa. exact (proj2 HK a Hpa).
Qed.

(* ---- the string sites' achecked / amem_range premises ---- *)
Lemma lb_hull_sub_x : forall rd y n n', shadow_hull_vis rd y n -> 0 < n' <= n -> shadow_hull_vis rd y n'.
Proof.
intros rd y n n' H Hn s Hs. apply H.
assert (shadow_addr (y + n' - 1) / 8 <= shadow_addr (y + n - 1) / 8)
  by (apply Z.div_le_mono; [lia | apply shadow_mono; lia]).
lia.
Qed.

Lemma lb_ra_sub_x : forall rd o a n n', range_addressable rd o a n -> 0 <= n' <= n -> range_addressable rd o a n'.
Proof. intros rd o a n n' H Hn x Hx. apply H. lia. Qed.

Lemma lb_amr_img_x : forall a n, 0x10000 <= a -> 0 <= n -> a + n <= IMG_TOP -> amem_range a n.
Proof. intros a n H1 H2 H3. unfold amem_range, kLowMemEnd, IMG_TOP in *. left. lia. Qed.

(* YCbq.v amem_range_of_block, over ARx (AR_laws_x's blocks law alx_blocks) *)
Lemma lb_amr_blk_x : forall ly S Hp W mem md p m a n,
ARx ly S Hp W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> a + n <= p + req_size m -> amem_range a n.
Proof.
intros ly S Hp W mem md p m a n HAR Hin H1 H2.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p m HAR Hin) as (_ & _ & Hc & [Hh Hh2] & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). zlia.
Qed.

(* W_drain_cx.v amem_range_near_block, over ARx (W_drain_cx_x.v amem_range_near_block_x's proof) *)
Lemma lb_amr_near_x : forall ly S Hp W mem md q n a,
ARx ly S Hp W mem md -> In (q, n) (ablocks B ly S) -> q <= a -> a <= q + req_size n -> amem_range a 8.
Proof.
intros ly S Hp W mem md q n a HAR Hin H1 H2.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md q n HAR Hin) as (_ & H4096 & Hceil & Hap & _).
pose proof (@ASAN_CEIL_range rc) as (Hc & _).
destruct Hap as (Ha0 & [HL | [HH1 HH2]]);
unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
[left; lia | right; lia].
Qed.

Lemma lb_lit_bytes_x : Forall (fun b => 0 <= b < 256) K_GESTURE /\ Forall (fun b => 0 <= b < 256) W_BEGIN /\
Forall (fun b => 0 <= b < 256) W_END.
Proof. unfold K_GESTURE, W_BEGIN, W_END. repeat split; repeat (apply Forall_cons; [lia|]); apply Forall_nil. Qed.

Lemma lb_lit_nz_x : (forall i, (i < length K_GESTURE)%nat -> nth i K_GESTURE 0 <> 0) /\
(forall i, (i < length W_BEGIN)%nat -> nth i W_BEGIN 0 <> 0) /\ (forall i, (i < length W_END)%nat -> nth i W_END 0 <> 0).
Proof.
unfold K_GESTURE, W_BEGIN, W_END. cbn [length].
repeat split; intros i Hi; (do 13 (destruct i as [|i]; [cbn; lia|])); cbn [length] in Hi; lia.
Qed.

(* lb_lit_range over dlit_at_x (its second conjunct is dlit_at's) *)
Lemma lb_lit_range_x : forall i l, dlit_at_x ARx i l -> (0 < length l)%nat ->
0x10000 <= VAL (A_OBJ i) /\ VAL (A_OBJ i) + Z.of_nat (length l) <= IMG_TOP.
Proof.
intros i l (_ & HR & _) Hl.
assert (I1 : in_img SEGS (VAL (A_OBJ i))).
{ destruct (HR (VAL (A_OBJ i)) ltac:(lia)) as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr]. }
assert (I2 : in_img SEGS (VAL (A_OBJ i) + Z.of_nat (length l) - 1)).
{ destruct (HR (VAL (A_OBJ i) + Z.of_nat (length l) - 1) ltac:(lia)) as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr]. }
pose proof (pa_img_range _ I1). pose proof (pa_img_range _ I2). unfold IMG_TOP. lia.
Qed.

(* ---- the branch decisions ---- *)
Lemma lb_br_ne0_x : forall E n w, ew E n = w ->
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = negb (bv_unsigned w =? 0).
Proof.
intros E n w H. rewrite branch_ne_U. pose proof (bv_unsigned_in_range 64 w) as R.
change (bv_modulus 64) with (2 ^ 64) in R.
rewrite (U_atom E n (bv_unsigned w)); [rewrite U_lit by lia; reflexivity | rewrite H; symmetry; apply Z_to_bv_bv_unsigned | exact R].
Qed.

Lemma lb_br_eq0_x : forall E n w, ew E n = w ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (bv_unsigned w =? 0).
Proof.
intros E n w H. rewrite branch_eq_U. pose proof (bv_unsigned_in_range 64 w) as R.
change (bv_modulus 64) with (2 ^ 64) in R.
rewrite (U_atom E n (bv_unsigned w)); [rewrite U_lit by lia; reflexivity | rewrite H; symmetry; apply Z_to_bv_bv_unsigned | exact R].
Qed.

Lemma lb_br_eq_lit_x : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = (v =? c).
Proof.
intros E n v c H Hv Hc. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit by lia. reflexivity.
Qed.

Lemma lb_w0_x : forall w : bv 64, bv_unsigned w = 0 <-> w = w64 0.
Proof.
intros w. split.
- intros H. apply bv_eq. rewrite H. reflexivity.
- intros ->. reflexivity.
Qed.

Lemma lb_br_ne_byte_x : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> 0 <= c < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SExt false 8 (SOff n 0))) (sv_denot E (SLit c)) = negb (v =? c).
Proof.
intros E n v c H Hv Hc. rewrite branch_ne_U, U_zext, (U_atom E n v H) by lia. rewrite U_lit by lia.
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma lb_br_eq_ao_x : forall E n m v u c, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 u ->
0 <= v < 2 ^ 64 -> 0 <= u < 2 ^ 64 -> 0 <= u + c < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SOff m c)) = (v =? u + c).
Proof.
intros E n m v u c H1 H2 R1 R2 R3. rewrite branch_eq_U, (U_atom E n v H1 R1), (U_atom_off E m u c H2 R2 R3).
reflexivity.
Qed.

Lemma lb_ae_ewset_x : forall k E0 E n v, (k <= n)%nat -> env_agree k E0 E -> env_agree k E0 (ewset E n v).
Proof.
intros k E0 E n v Hk [HA HD]. split; [|exact HD].
intros m Hm. rewrite ew_ewset_other by lia. apply HA. exact Hm.
Qed.

Lemma lb_nth13_x : forall s1 p q, (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
(13 <= q - p)%nat -> nth 13 (dline s1 p q) 0 = nth (p + 13) (dW s1) 0.
Proof.
intros s1 p q Hpq Hq H13. unfold dline.
destruct (Nat.eq_dec (q - p) 13) as [E|E].
- rewrite E. rewrite nth_overflow by (rewrite firstn_length_le by (rewrite length_skipn; lia); lia).
  replace (p + 13)%nat with q by lia. symmetry. apply nth_error_nth. exact Hq.
- rewrite nth_firstn, (proj2 (Nat.ltb_lt 13 (q - p))) by lia. rewrite nth_skipn. reflexivity.
Qed.

(* ---- the symbolic entry at 0x839f4 (lb_Bx / lb_Bspan / lb_CEIL / lb_facts / ss_lb / lb_extra, cited) ---- *)
Lemma lb_entry_x : forall (W : world SEGS) regs m v13 sp x,
spZ regs = sp -> 2 ^ 46 <= sp -> sp <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs 24 = w64 x -> 4096 <= x <= lb_CEIL ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (lb_extra v13))) ss_lb
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_send)) m (seg_rom SEGS))).
Proof.
intros W regs m v13 sp x Hsp H1 H2 H3 R24 Hx.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (lb_extra v13))).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n r Hr)).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (U33 : bv_unsigned (ew E 33) = SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ 1); cbn [lb_extra map nth];
      rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity).
assert (U24 : bv_unsigned (ew E 24) = x)
  by (rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); rewrite R24; apply unsigned_lit_small; unfold lb_CEIL in *; lia).
unfold ss_lb. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [lb_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U33, U24. unfold SB, lb_CEIL in *.
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Ltac lbin_x := cbn; repeat (first [left; reflexivity | right]).
Ltac lb_regs_x HS HAEx :=
  let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    lazymatch type of HAEx with env_agree _ (Ereg ?R0 ?X0) _ =>
      let HAEz := fresh "HAEz" in
      assert (HAEz : env_agree 32 (Ereg R0 X0) Ev)
        by (first [exact HAEx | repeat (first [apply lb_ae_ewset_x; [lia|] | apply env_agree_havoc_ge; [cbv; lia|]]);
                   first [exact HAEx | eassumption]]);
      exact (regs_kept_of_st_ok_pi Ev _ _ R0 X0 [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 27]%bv HS HAEz
        ltac:(vm_compute; reflexivity) r Hr)
    end end.
Ltac lb_ewg_x := repeat (first [rewrite ew_ewset_other by lia | rewrite YN3v.ew_havoc_old by (cbv; lia)]).
(* drain's frame, seated as a region (lb_frame_region, cited) *)
Ltac lb_awr1_x := apply awr_ok_x_cons; [|apply awr_ok_x_nil];
  cbn [lb_frame_region YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; exfalso; clear - Ha; lia.
Ltac lb_nowr_x := let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [lb_frame_region YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia|]); destruct Hin.

Lemma lb_frame_region_ok_x : forall cx Hp kr E m, DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME ->
ew E 20 = Z_to_bv 64 (dxSA cx + 16) -> ew E 21 = Z_to_bv 64 (dxSA cx) -> ew E 22 = Z_to_bv 64 (dxSA cx + 24) ->
ew E 33 = Z_to_bv 64 SHADOW_OFF ->
0 <= dxSA cx /\ dxSA cx + 24 < 2 ^ 64 ->
val_mem SEGS m (dsp0 cx - DRAIN_FRAME + 128) 8 (dxSA cx + 16) ->
val_mem SEGS m (dsp0 cx - DRAIN_FRAME + 136) 8 (dxSA cx + 24) ->
val_mem SEGS m (dsp0 cx - DRAIN_FRAME + 144) 8 (dxSA cx) ->
val_mem SEGS m (dsp0 cx - DRAIN_FRAME + 240) 8 SHADOW_OFF ->
region_ok SEGS E m lb_frame_region.
Proof.
intros cx Hp kr E m HB Usp E20 E21 E22 E33 HSA V128 V136 V144 V240.
pose proof (lb_scr_lo_x cx Hp kr HB) as (SL & SH47 & SAL). pose proof asan_consts as (C1 & _).
assert (EF : DRAIN_FRAME = 352) by reflexivity. assert (EE : ESTACK = 4096) by reflexivity.
unfold region_ok, lb_frame_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val SEGS E m (dsp0 cx - DRAIN_FRAME) 128 8 (SOff 20 0) (dxSA cx + 16));
    [exact (den_atom0 E 20 _ E20 ltac:(lia)) | cbn; lia | cbn; lia | exact V128].
- apply (chunk_ok_val SEGS E m (dsp0 cx - DRAIN_FRAME) 136 8 (SOff 22 0) (dxSA cx + 24));
    [exact (den_atom0 E 22 _ E22 ltac:(lia)) | cbn; lia | cbn; lia | exact V136].
- apply (chunk_ok_val SEGS E m (dsp0 cx - DRAIN_FRAME) 144 8 (SOff 21 0) (dxSA cx));
    [exact (den_atom0 E 21 _ E21 ltac:(lia)) | cbn; lia | cbn; lia | exact V144].
- apply (chunk_ok_val SEGS E m (dsp0 cx - DRAIN_FRAME) 240 8 (SOff 33 0) SHADOW_OFF);
    [exact (den_atom0 E 33 _ E33 ltac:(unfold SHADOW_OFF; lia)) | cbn; unfold SHADOW_OFF; lia
    | cbn; lia | exact V240].
Qed.

Lemma lb_frame_disj_x : forall cx E X, bv_unsigned (ew E 24) = X -> bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME ->
X + 14 <= dsp0 cx - DRAIN_FRAME + 128 ->
all_disjoint E lb_frame_region [YP09.mkRegion (Some 24%nat) 13 14 0 0 [YP09.mkChunk 13 (CVal 1 (SOff 32 0))]].
Proof.
intros cx E X H24 Hsp Hlt. cbn [all_disjoint]. split; [|exact I].
unfold extent_disjoint, extent_of_region, lb_frame_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd]. rewrite H24, Hsp. lia.
Qed.

Ltac lb_awr2_x := apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]];
  cbn [lb_frame_region YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; exfalso; clear - Ha; lia.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0): LINEB at a world relation R.  dr_lineb_stmt_x / DLS_x / DLN_x / DGS_x /
   DLC_x / LCORE_x / DMEM_x / dPOST_x -> their R twins (W_drain_cx_x.v, W_drain_lineb_cx.v), ajournal_gx_x ->
   ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the runs and the branch -> their SRrG forms (W_journal_x.v
   paj_run_x_xG / paj_run_to_x_xG, W_kit.v paj_branch_xR), the three string sites -> W_sites_x.v aj_gx_entry_at_xR (the
   string contracts stay strict), and the cut helpers below -> their R twins.  dr_lineb_of_x and dr_lineb_x below are
   these at R := wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNR := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (R := R) (PI := PI).

(* R twin of lb_lcore_keep_x *)
Lemma lb_lcore_keep_xR : forall cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  m2 md2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl ->
lb_keep cx W1 m1 m2 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m2 md2 k1 e1 h1 out1 ev1 LB1
  spent tl.
Proof.
intros cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2 HB HL HK HJ2.
unfold LCORE_xR in HL |- *. cbv zeta in HL |- *.
destruct HL as (HMEM & HLINK & HSAME & HHIST & HRST & HBUD).
refine (conj _ (conj HLINK (conj HSAME (conj HHIST (conj HRST HBUD))))).
unfold DMEM_xR in HMEM |- *.
destruct HMEM as (HJ & HROM & HPRES & HFRAMES & HFR & HGARR & HAWR & HEOK & HSRC & HOTH & HKEPT & HOUT & HLIVE & HPERM).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof (lbB_low_kept_x cx Hp kr W1 m1 m2 HB HK) as KL.
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof HB as HB'. unfold DBASE_x in HB'.
destruct HB' as (_ & _ & _ & HSAlo & HSAhi & _ & _ & _ & _ & Hj4 & _).
assert (Htbl : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
assert (KSA : forall x, dxSA cx <= x < dxSA cx + AENT -> abyte_kept W1 m1 W1 m2 x).
{ intros x Hx. apply KL. apply (lbB_blk_low_x ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE x HAR Htbl); [lia|].
  pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as (_ & Hrq). lia. }
assert (KGS : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W1 m2 x).
{ intros x Hx. apply KL. apply (lbB_img_low_x x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold IMG_TOP in *; lia. }
split; [exact HJ2|].
split; [exact (lbB_rom_x W1 m1 m2 KL HROM)|].
split; [intros a Ha1 Ha2 Ha3 Hpa; apply (proj2 HK); exact (HPRES a Ha1 Ha2 Ha3 Hpa)|].
split; [exact HFRAMES|].
split; [exact (lbB_frame_x cx Hp kr W1 m1 m2 HB HK HFR)|].
split.
{ apply (akept_garr8 W1 m1); [|exact HGARR]. intros x Hx. apply KSA.
  pose proof HEOK as (_ & _ & Hpd1 & Hpd2 & _).
  unfold bzs in Hx. rewrite length_map, (lbB_eb_len_x e1 Hpd1 Hpd2) in Hx. unfold AENT. lia. }
split; [exact (akept_awr W1 m1 W1 m2 (dxSA cx) AENT KSA HAWR)|].
split; [exact (lbB_eokx_x ly1 S1 Hp1 W1 m1 md1 m2 e1 HAR HEOK KL)|].
split.
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 (dHA RG cx) h1 HSRC).
  - intros r Hr x Hx. apply KL.
    refine (lbB_asrc_fp_low_x ly1 S1 Hp1 W1 m1 md1 (dHA RG cx) h1 HAR HSRC _ _ r Hr x Hx); unfold dHA, ASRC; lia.
  - intros b Hb. apply (Permutation_in _ (Permutation_sym HPERM)).
    right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
split.
{ intros i Hi Hne. destruct (HOTH i Hi Hne) as (f & o' & Hf & Ho & Hfo). exists f, o'.
  split; [|split; [|exact Hfo]].
  - apply (akept_vm W1 m1); [|exact Hf]. intros x Hx. apply KGS. unfold ASRC in *. lia.
  - apply (akept_vm W1 m1); [|exact Ho]. intros x Hx. apply KGS. unfold ASRC in *. lia. }
split.
{ intros x Hx Hn. pose proof (HKEPT x Hx Hn) as K1. pose proof (KGS x Hx) as K2.
  split; [rewrite (proj1 K2); exact (proj1 K1)|].
  intros Hw. apply (proj2 K2). apply (proj2 K1). exact Hw. }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2 _ _ _ _ _ _ HOUT).
  - intros r Hr x Hx. apply KL. exact (lbB_aout_fp_low_x ly1 S1 Hp1 W1 m1 md1 _ _ _ _ _ _ HAR HOUT r Hr x Hx).
  - intros b Hb. apply (Permutation_in _ (Permutation_sym HPERM)).
    right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
split; [exact HLIVE | exact HPERM].
Qed.
(* R twin of lbB_lcore_none_x *)
Lemma lbB_lcore_none_xR : forall cx Hp kr s1 D sent kl kl' l H ka no oc n sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl,
gesture l = None -> kl' = kl ++ [l] ->
LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D sent kl H ka no oc (Z.of_nat (S n)) sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1
  ev1 LB1 spent tl ->
LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D sent kl' H ka no oc (Z.of_nat n) sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1
  ev1 LB1 spent tl.
Proof.
intros cx Hp kr s1 D sent kl kl' l H ka no oc n sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl Hg Ekl HL.
subst kl'.
unfold LCORE_xR in HL |- *. cbv zeta in HL |- *.
destruct HL as (HMEM & HLINK & HSAME & HHIST & HRST & HBUD).
refine (conj HMEM (conj HLINK (conj HSAME (conj _ (conj HRST HBUD))))).
unfold DHIST in HHIST |- *.
destruct HHIST as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11).
rewrite (lbB_upds_none_x _ kl l Hg).
refine (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj X8 (conj X9 (conj _ X11)))))))))).
lia.
Qed.
(* R twin of lb_mk_dln_x *)
Lemma lb_mk_dln_xR : forall cx Hp kr s1 D p q regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl W1
  regs2 m2 md2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
dregs_line RG cx regs1 W1 m1 ->
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) ->
dinband (re_buf e1) (re_cap e1) -> 0 < re_cap e1 ->
dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) ->
dskp s1 p = false -> (q - p <= LINE_LIMIT)%nat ->
LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q])
  (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
dsfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (drlq s1 (S q)) jb o ha ks tl ->
gesture (dline s1 p q) = None ->
spZ regs2 = spZ regs1 ->
getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 -> getr regs2 21 = getr regs1 21 ->
getr regs2 20 = getr regs1 20 -> getr regs2 22 = getr regs1 22 -> getr regs2 27 = getr regs1 27 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 23 = getr regs1 23 ->
lb_keep cx W1 m1 m2 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
DLN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S q) W1 (cfg_at SEGS (BASE + A_dr_next) regs2 m2 md2).
Proof.
intros cx Hp kr s1 D p q regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl W1 regs2 m2 md2
  HB HR H23 Hdin Hcap0 Hbnd Hpq Hnul Hnoz Hskp Hlim HL HF Hg Hsp H3 H4 H21 H20 H22 H27 H8 H9 H18 H23' HK HJ2.
pose proof (lb_lcore_keep_xR cx Hp kr s1 D _ _ _ _ _ _ _ _ ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2
  HB HL HK HJ2) as HL2.
destruct (lbB_drl_x s1 p q Hbnd Hpq Hnul Hnoz Hskp Hlim) as (E1 & E2 & E3).
pose proof (lbB_dlno_x s1 p q E1) as Edlno.
pose proof (lbB_dloc_x cx s1 p q E1) as Edloc.
assert (EdlH : dlH cx s1 (S q) = dlH cx s1 p)
  by (rewrite (lbB_dlH_x cx s1 p q E1); exact (lbB_seen_arr_none_x _ _ Hg)).
assert (Edlka : dlka cx s1 (S q) = dlka cx s1 p)
  by (rewrite (lbB_dlka_x cx s1 p q E1); exact (lbB_seen_ka_none_x _ _ _ Hg)).
unfold dsfut in HF. cbv zeta in HF. destruct HF as (tl2 & HF1 & HF2).
rewrite (lbB_seen_tr_none_x _ _ _ _ _ _ Hg) in HF1, HF2.
rewrite (lbB_seen_arr_none_x _ _ Hg), (lbB_seen_ka_none_x _ _ _ Hg) in HF1.
cbn [fst snd app] in HF1, HF2.
change (RelayRunT.nret YO0i.sptr []) with 0%nat in HF1. rewrite Nat.add_0_r in HF1.
subst tl2.
exists regs2, ly1, S1, Hp1, m2, md2, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
split; [reflexivity|].
split; [exact (lb_dregs_keep_x cx Hp kr regs1 regs2 W1 m1 m2 HB HR Hsp H3 H4 H21 H20 H22 H27 H8 H9 H18 HK)|].
split; [rewrite H23', H23; f_equal; lia|].
split; [exact Hdin|]. split; [exact Hcap0|].
split; [split; [lia | right; replace (S q - 1)%nat with q by lia; exact Hnul]|].
split; [lia|].
split.
{ unfold DLC_xR. rewrite EdlH, Edlka, Edlno, Edloc, E3, E1.
  apply (lbB_lcore_none_xR cx Hp kr s1 D _ (lines (dSTR cx) D ++ drlp s1 p) _ (dline s1 p q));
    [exact Hg | apply app_assoc | exact HL2]. }
rewrite Edlno, Edloc, EdlH, Edlka. exact HF1.
Qed.
(* R twin of lb_mk_dgs_x *)
Lemma lb_mk_dgs_xR : forall cx Hp kr s1 D p q regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl W1
  regs2 m2 md2 (kd : gkind) (jj : nat) (bg : Z),
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
dregs_line RG cx regs1 W1 m1 ->
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) -> getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) ->
dinband (re_buf e1) (re_cap e1) -> 0 < re_cap e1 ->
dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) ->
dskp s1 p = false -> (q - p <= LINE_LIMIT)%nat ->
LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q])
  (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
dsfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (drlq s1 (S q)) jb o ha ks tl ->
spZ regs2 = spZ regs1 ->
getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 -> getr regs2 21 = getr regs1 21 ->
getr regs2 20 = getr regs1 20 -> getr regs2 22 = getr regs1 22 -> getr regs2 27 = getr regs1 27 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 ->
getr regs2 19 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj) ->
getr regs2 26 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj + 1) -> getr regs2 25 = w64 bg ->
0 <= bg < 2 ^ 64 -> (bg = 0 <-> kd = GBegin) ->
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) -> (13 < jj < q - p)%nat ->
lb_keep cx W1 m1 m2 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
DGS_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W1 (cfg_at SEGS (BASE + A_dr_seen) regs2 m2 md2).
Proof.
intros cx Hp kr s1 D p q regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl W1 regs2 m2 md2 kd jj bg
  HB HR H23 H24 Hdin Hcap0 Hbnd Hpq Hnul Hnoz Hskp Hlim HL HF Hsp H3 H4 H21 H20 H22 H27 H8 H9 H18 H23' H24'
  H19 H26 H25 Hbg Hbgk Hges Hjj HK HJ2.
pose proof (lb_lcore_keep_xR cx Hp kr s1 D _ _ _ _ _ _ _ _ ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2
  HB HL HK HJ2) as HL2.
exists regs2, ly1, S1, Hp1, m2, md2, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl, kd, jj, bg.
split; [reflexivity|].
split; [exact (lb_dregs_keep_x cx Hp kr regs1 regs2 W1 m1 m2 HB HR Hsp H3 H4 H21 H20 H22 H27 H8 H9 H18 HK)|].
split; [rewrite H23'; exact H23|].
split; [rewrite H24'; exact H24|].
split; [exact H19|]. split; [exact H26|]. split; [exact H25|]. split; [exact Hbg|]. split; [exact Hbgk|].
split; [exact Hdin|]. split; [exact Hcap0|].
split; [exact Hges|]. split; [exact Hjj|].
split; [exact Hbnd|]. split; [exact Hpq|]. split; [exact Hnul|]. split; [exact Hnoz|].
split; [exact Hskp|]. split; [exact Hlim|].
split; [exact HL2 | exact HF].
Qed.

(* R twin of dr_lineb_of_x *)
Theorem dr_lineb_of_xR :
(forall ly S Hp W mem md, ARx ly S Hp W mem md -> shadow_hull_vis (aview SEGS (w_H W) mem) (VAL (A_OBJ 18)) 14) ->
(forall ly S Hp W mem md, ARx ly S Hp W mem md -> shadow_hull_vis (aview SEGS (w_H W) mem) (VAL (A_OBJ 20)) 6) ->
(forall ly S Hp W mem md, ARx ly S Hp W mem md -> shadow_hull_vis (aview SEGS (w_H W) mem) (VAL (A_OBJ 21)) 4) ->
dr_lineb_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros HV21 HV23 HV24 cx Hpe kr s1 D p q W1 c1 HB HLS KDLN KDGS.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HLS as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & oo & ha & ks & tl
  & Hc1 & Hregs & H23 & H24 & Hdin & Hcap0 & Hbnd & Hpq & Hnulq & Hnoq & Hskp & Hlim & HLC & Hfut).
pose proof Hregs as (Hsp & Hr3 & Hr4 & Hr21 & Hr20 & Hr22 & Hr27 & Hr8 & Hr9 & Hr18 & HFRM).
pose proof HLC as (HMEM & HLINK & HSAME & HHIST & HRST & HBUD).
pose proof HMEM as (HJ & HROM & HPRES & HFRAMES & HFR2 & HGARR & HAWR & HEOK & HSRC & HOTH & HKEPT & HOUT & HLIVE & HPERM).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HB as (Hafn & HBa0 & Htbl & HSAlo & HSAhi & _).
pose proof Hafn as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : DRAIN_STK_x = 17008) by reflexivity.
assert (HFRAME : DRAIN_FRAME = 352) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HEOK as (Heof & Hskip & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedr & Hbufc & Hnheld & Hheld & HND1 & HND2 & Hkeys).
assert (HUeq : bzs (re_U e1) = dW s1) by (destruct HLINK as (_ & Hu & _); exact Hu).
assert (Hdwlen : Z.of_nat (length (dW s1)) = re_used e1)
  by (rewrite <- HUeq; unfold bzs; rewrite length_map; exact HUlen).
destruct Hbufc as [(Hc0 & _) | (_ & Hbufin & Hjunk & Hbg)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hbufin)
  as (HB16 & HB4096 & HBceil & HBia & HBpres & _).
assert (RQB : req_size (re_cap e1) = re_cap e1)
  by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQB in HBceil, HBia.
set (v13 := nth (p + 13) (dW s1) 0).
pose proof (lb_scr_lo_x cx Hpe kr HB) as (SL & SH47 & SAL).
assert (HSAr : 0 <= dxSA cx /\ dxSA cx + 24 < 2 ^ 64).
{ assert (Htbl1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
    by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
  pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as (_ & Hrq).
  pose proof (lbB_blk_low_x ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE (dxSA cx) HAR Htbl1 ltac:(lia)
    ltac:(unfold AENT in *; lia)) as Hl0.
  pose proof (lbB_blk_low_x ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE (dxSA cx + 24) HAR Htbl1 ltac:(lia)
    ltac:(unfold AENT in *; lia)) as Hl1.
  pose proof asan_consts as (C1' & _). unfold lbB_low in Hl0, Hl1. split; lia. }
assert (HLl : length (bzs (re_U e1 ++ re_junk e1)) = Z.to_nat (re_cap e1))
  by (unfold bzs; rewrite length_map, length_app; lia).
assert (HLapp : bzs (re_U e1 ++ re_junk e1) = dW s1 ++ bzs (re_junk e1))
  by (unfold bzs in *; rewrite map_app, HUeq; reflexivity).
assert (HLEN : length (dline s1 p q) = (q - p)%nat)
  by (unfold dline; rewrite firstn_length_le; [reflexivity|]; rewrite length_skipn; lia).
assert (LN0 : lb_line (aview SEGS (w_H W1) m1) (re_buf e1 + Z.of_nat p) (dline s1 p q)).
{ pose proof (lb_line_of_garr8_x W1 m1 (re_buf e1) (bzs (re_U e1 ++ re_junk e1)) p q Hbg) as LN.
  rewrite HLapp in LN.
  replace (firstn (q - p) (skipn p (dW s1 ++ bzs (re_junk e1)))) with (dline s1 p q) in LN.
  - apply LN; [rewrite length_app; lia | rewrite nth_error_app1 by lia; exact Hnulq |].
    intros i Hi. rewrite nth_error_app1 by lia. exact (Hnoq i Hi).
  - unfold dline. rewrite skipn_app, firstn_app, length_skipn.
    replace (q - p - (length (dW s1) - p))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. reflexivity. }
assert (KN : forall regsF mF mdF, gesture (dline s1 p q) = None ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 27]%bv -> getr regsF r = getr regs1 r) ->
  lb_keep cx W1 m1 mF ->
  @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 mF mdF k1 ->
  YA0nH.SRrG SEGS R W1 (cfg_at SEGS (BASE + A_dr_next) regsF mF mdF) (dPOST_xR B PST ARx MT RP RG R cx Hpe kr)).
{ intros regsF mF mdF GN HR KF HJF. apply KDLN.
  pose proof (HR 2%bv ltac:(lbin_x)) as R2. pose proof (HR 3%bv ltac:(lbin_x)) as R3.
  pose proof (HR 4%bv ltac:(lbin_x)) as R4. pose proof (HR 8%bv ltac:(lbin_x)) as R8.
  pose proof (HR 9%bv ltac:(lbin_x)) as R9. pose proof (HR 18%bv ltac:(lbin_x)) as R18.
  pose proof (HR 20%bv ltac:(lbin_x)) as R20. pose proof (HR 21%bv ltac:(lbin_x)) as R21.
  pose proof (HR 22%bv ltac:(lbin_x)) as R22.
  pose proof (HR 23%bv ltac:(lbin_x)) as R23. pose proof (HR 27%bv ltac:(lbin_x)) as R27.
  exact (lb_mk_dln_xR cx Hpe kr s1 D p q regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl W1
    regsF mF mdF
    HB Hregs H23 Hdin Hcap0 Hbnd Hpq Hnulq Hnoq Hskp Hlim HLC Hfut GN ltac:(unfold spZ; rewrite R2; reflexivity)
    R3 R4 R21 R20 R22 R27 R8 R9 R18 R23 KF HJF). }
assert (KG : forall regsF mF mdF (kd : gkind) (jj : nat) (bg : Z),
  gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) -> (13 < jj < q - p)%nat ->
  getr regsF 19 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj) ->
  getr regsF 26 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj + 1) -> getr regsF 25 = w64 bg ->
  0 <= bg < 2 ^ 64 -> (bg = 0 <-> kd = GBegin) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 27]%bv -> getr regsF r = getr regs1 r) ->
  lb_keep cx W1 m1 mF ->
  @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 mF mdF k1 ->
  YA0nH.SRrG SEGS R W1 (cfg_at SEGS (BASE + A_dr_seen) regsF mF mdF) (dPOST_xR B PST ARx MT RP RG R cx Hpe kr)).
{ intros regsF mF mdF kd jj bg GS Hjj H19 H26 H25 Hbgr Hbk HR KF HJF. apply KDGS.
  pose proof (HR 2%bv ltac:(lbin_x)) as R2. pose proof (HR 3%bv ltac:(lbin_x)) as R3.
  pose proof (HR 4%bv ltac:(lbin_x)) as R4. pose proof (HR 8%bv ltac:(lbin_x)) as R8.
  pose proof (HR 9%bv ltac:(lbin_x)) as R9. pose proof (HR 18%bv ltac:(lbin_x)) as R18.
  pose proof (HR 20%bv ltac:(lbin_x)) as R20. pose proof (HR 21%bv ltac:(lbin_x)) as R21.
  pose proof (HR 22%bv ltac:(lbin_x)) as R22.
  pose proof (HR 23%bv ltac:(lbin_x)) as R23. pose proof (HR 24%bv ltac:(lbin_x)) as R24.
  pose proof (HR 27%bv ltac:(lbin_x)) as R27.
  exact (lb_mk_dgs_xR cx Hpe kr s1 D p q regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl W1
    regsF mF mdF
    kd jj bg HB Hregs H23 H24 Hdin Hcap0 Hbnd Hpq Hnulq Hnoq Hskp Hlim HLC Hfut ltac:(unfold spZ; rewrite R2; reflexivity)
    R3 R4 R21 R20 R22 R27 R8 R9 R18 R23 R24 H19 H26 H25 Hbgr Hbk GS Hjj KF HJF). }
set (X := re_buf e1 + Z.of_nat p) in *.
pose proof (lb_entry_x W1 regs1 m1 v13 (dsp0 cx - DRAIN_FRAME) X Hsp
  ltac:(unfold DRAIN_FRAME, ESTACK in *; lia) ltac:(unfold DRAIN_FRAME in *; lia)
  ltac:(unfold DRAIN_FRAME in *; rewrite Zminus_mod, SAL; reflexivity)
  H24 ltac:(unfold lb_CEIL, X in *; lia)) as HS.
remember (Eimg (Ereg regs1 (lb_extra v13))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (lb_extra v13)) E)
  by (rewrite HE; split; [intros mm Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 v13)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (SHOK : sh_ok SEGS lb_Bx [] E (mrestrict (w_H W1) m1)) by constructor.
clear HE.
rewrite Hc1. unfold cfg_at. change (w64 (BASE + A_dr_send)) with (Z_to_bv 64 (BASE + A_dr_send)).
paj_run_tok_xR RUNR HS HJ SHOK lb_Bspan; [apply awr_ok_x_nil|].
rename HFr into FR0; rename HG0 into GR0; clear HF.
assert (KP0 : lb_keep cx W1 m1 (ms_mem ms)).
{ apply (lb_keep_run_x cx W1 m1 m1 (ms_mem ms) E []); [apply lb_keep_refl_x | exact FR0 | exact GR0 |].
  intros a (r & Hin & _). destruct Hin. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
pose proof HJ as HAR1. apply ajournal_gx_AR_xR in HAR1.
pose proof (lb_line_ext_x _ _ X (dline s1 p q) LN0
  (fun a Ha => lb_keep_low_x cx Hpe kr W1 m1 (ms_mem ms) a HB KP0 ltac:(rewrite HLEN in Ha; unfold X in *; lia))) as LN1.
assert (HQC : re_buf e1 + Z.of_nat q < re_buf e1 + re_cap e1) by lia.
eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_DR B RG) 0 ([] : list (Z * Z)) (2 * ESTACK) (SIGMA WS_strrchr)
      (fun _ => False) _ W1 (ms_regs ms) (ms_mem ms) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hpe (dxW cx)
      (dxmem cx) (dxmd cx) ([] : list (Z * Z)) ly1 S1 Hp1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ);
  [ unfold spZ at 1; rewrite Q2, Usp; lia
  | reflexivity
  | unfold DRAIN_FRAME; lia
  | unfold ESTACK; lia
  | unfold ESTACK, DRAIN_FRAME; rewrite WS; lia
  | rewrite Q3, (EREG 3%nat 3%bv), Hr3 by (first [lia | reflexivity]); exact Hgp
  | rewrite Q4, (EREG 4%nat 4%bv), Hr4 by (first [lia | reflexivity]); exact Htp
  | exact Q1
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | intros _; right; intros []
  | intros a []
  | intros a []
  | ].
  intros HPRE HSC.
  eapply (ASTRRCHR ly1 S1 Hp1 W1 (ms_regs ms) (ms_mem ms) _ X 32 (Z.of_nat (q - p)) HPRE HSC).
  - rewrite Q10, (EREG 24%nat 24%bv), H24 by (first [lia | reflexivity]). reflexivity.
  - rewrite Q11. reflexivity.
  - lia.
  - unfold X; lia.
  - lia.
  - unfold X; lia.
  - unfold LINE_LIMIT in *; lia.
  - pose proof (lb_line_first_byte_x W1 (ms_mem ms) X (dline s1 p q) (Z.of_nat (q - p) + 1) LN1 ltac:(lia)) as FB.
    rewrite HLEN in FB. replace (Z.min (Z.of_nat (q - p) + 1) (Z.of_nat (q - p))) with (Z.of_nat (q - p)) in FB by lia.
    exact FB.
  - intros a Ha. split.
    + apply (lb_line_vis_x _ X (dline s1 p q) a LN1). rewrite HLEN. lia.
    + unfold spZ. rewrite Q2, Usp. unfold X in *. lia.
  - intros a Ha. rewrite (lb_keep_low_x cx Hpe kr W1 m1 (ms_mem ms) a HB KP0) by (unfold X in *; lia).
    apply (lb_garr8_vis_x W1 m1 (re_buf e1) (bzs (re_U e1 ++ re_junk e1)) a Hbg). rewrite HLl.
    pose proof (lb_tail_arith_x (re_buf e1) (re_cap e1) (X + Z.of_nat (q - p)) a HB16
      ltac:(destruct Hcapr as [Hc|[Hc|Hc]]; [lia | left; exact Hc | right; exact Hc]) ltac:(unfold X in *; lia) Ha).
    unfold X in *. lia.
  - exact (lb_keep_rom_x cx Hpe kr W1 m1 (ms_mem ms) HB KP0 HROM).
  - split; [|split].
    + apply (lb_amr_blk_x ly1 S1 Hp1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) X _ HAR1 Hbufin);
        rewrite ?RQB; unfold X in *; lia.
    + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) X _
        HAR1 Hbufin); rewrite ?RQB; unfold X in *; lia.
    + intros Hpos. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms) _ (re_buf e1)
        (re_cap e1) X _ HAR1 Hbufin); rewrite ?RQB; unfold X in *; lia.
  - apply (lb_amr_near_x ly1 S1 Hp1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) X HAR1 Hbufin);
      rewrite ?RQB; unfold X in *; lia. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrr & Hfr2 & Hpres2).
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W1) mem2) HP2 ([] : list nat) HS2.
specialize (HS2 (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 34 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 34)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs1 (lb_extra v13)) Ea)
  by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
pose proof (lb_keep_call_x cx W1 m1 (ms_mem ms) mem2 KP0 Hfr2 Hpres2) as KP1.
prreg HS (10%bv : bv 5) R10a.
assert (SR : (getr regs2 10 = w64 0 /\ last_space_from 0 (dline s1 p q) = None) \/
  (exists j, (j < length (dline s1 p q))%nat /\ getr regs2 10 = w64 (X + Z.of_nat j) /\
     last_space_from 0 (dline s1 p q) = Some j)).
{ apply (lb_strrchr_x _ X (dline s1 p q) (getr regs2 10) LN1); [unfold X in *; lia | rewrite HLEN; unfold X in *; lia |].
  rewrite HLEN. exact Hrr. }
assert (F38 : ew Ea 38 = getr regs2 10) by (rewrite R10a; reflexivity).
clear Hrr LN1 KP0 FR0 GR0 Q1 Q2 Q3 Q4 Q10 Q11 HAR1 R10a Hfr2 Hpres2 HP2.
clear dependent ms.
pose proof (lb_line_ext_x _ _ X (dline s1 p q) LN0
  (fun a Ha => lb_keep_low_x cx Hpe kr W1 m1 mem2 a HB KP1 ltac:(rewrite HLEN in Ha; unfold X in *; lia))) as LN2.
assert (SHOK1 : sh_ok SEGS lb_Bx [] Ea (mrestrict (w_H W1) mem2)) by constructor.
paj_run_tok_xR RUNR HS HJ2 SHOK1 lb_Bspan; [apply awr_ok_x_nil|].
rename HFr into FR1; rename HG0 into GR1; clear HF.
assert (KP2 : lb_keep cx W1 m1 (ms_mem ms)).
{ apply (lb_keep_run_x cx W1 m1 mem2 (ms_mem ms) Ea []); [exact KP1 | exact FR1 | exact GR1 |].
  intros a (r & Hin & _). destruct Hin. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
pose proof HJ2 as HAR2. apply ajournal_gx_AR_xR in HAR2.
pose proof (lb_line_ext_x _ _ X (dline s1 p q) LN0
  (fun a Ha => lb_keep_low_x cx Hpe kr W1 m1 (ms_mem ms) a HB KP2 ltac:(rewrite HLEN in Ha; unfold X in *; lia))) as LN3.
pose proof (lb_keep_rom_x cx Hpe kr W1 m1 (ms_mem ms) HB KP2 HROM) as ROM2.
pose proof lb_lit_bytes_x as (LBK & LBB & LBE).
pose proof lb_lit_nz_x as (NZK & NZB & NZE).
pose proof (lb_lit_of_dlit_x 18 K_GESTURE W1 (ms_mem ms) HLIT5 ROM2 LBK) as LIT21.
pose proof (lb_lit_range_x 18 _ HLIT5 ltac:(cbv; lia)) as (Y21a & Y21b). unfold IMG_TOP in Y21b.
change (Z.of_nat (length (K_GESTURE ++ [0]))) with 14 in Y21b.
assert (V262 : getr (ms_regs ms) 11 = w64 (VAL (A_OBJ 18))).
{ rewrite Q11. apply bv_eq. unfold w64. rewrite unsigned_lit_small by lia.
  exact (HEIa (A_OBJ 18) ltac:(cbv; lia)). }
assert (SP2 : spZ (ms_regs ms) = dsp0 cx - DRAIN_FRAME) by (unfold spZ; rewrite Q2, OLDa, Usp by lia; reflexivity).
eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_DR B RG) 0 ([] : list (Z * Z)) (2 * ESTACK) (SIGMA WS_strncmp)
      (fun _ => False) _ W1 (ms_regs ms) (ms_mem ms) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hpe (dxW cx)
      (dxmem cx) (dxmd cx) ([] : list (Z * Z)) ly1 S1 Hp1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ2);
  [ rewrite SP2; lia
  | reflexivity
  | unfold DRAIN_FRAME; lia
  | unfold ESTACK; lia
  | unfold ESTACK, DRAIN_FRAME; rewrite WS; lia
  | rewrite Q3, OLDa, (EREG 3%nat 3%bv), Hr3 by (first [lia | reflexivity]); exact Hgp
  | rewrite Q4, OLDa, (EREG 4%nat 4%bv), Hr4 by (first [lia | reflexivity]); exact Htp
  | exact Q1
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | intros _; right; intros []
  | intros a []
  | intros a []
  | ].
  intros HPRE HSC.
  eapply (ASTRNCMP ly1 S1 Hp1 W1 (ms_regs ms) (ms_mem ms) _ X (VAL (A_OBJ 18)) 13 (Z.min 13 (Z.of_nat (q - p))) 13
    HPRE HSC).
  - rewrite Q10, OLDa, (EREG 24%nat 24%bv), H24 by (first [lia | reflexivity]). reflexivity.
  - exact V262.
  - rewrite Q12. reflexivity.
  - lia.
  - lia.
  - unfold X in *; lia.
  - lia.
  - pose proof (lb_line_first_byte_x W1 (ms_mem ms) X (dline s1 p q) 13 LN3 ltac:(lia)) as FB. rewrite HLEN in FB.
    exact FB.
  - pose proof (lb_lit_first_byte_x W1 (ms_mem ms) (VAL (A_OBJ 18)) K_GESTURE 13 LIT21 NZK ltac:(lia)) as FB.
    change (Z.min 13 (Z.of_nat (length K_GESTURE))) with 13 in FB. exact FB.
  - unfold X in *; lia.
  - lia.
  - intros a Ha. split.
    + apply (lb_line_vis_x _ X (dline s1 p q) a LN3). rewrite HLEN. lia.
    + rewrite SP2. unfold X in *. lia.
  - intros a Ha. split.
    + apply (lb_lit_vis_x _ (VAL (A_OBJ 18)) K_GESTURE a LIT21). cbn [length K_GESTURE]. lia.
    + rewrite SP2. lia.
  - split; [|split].
    + apply (lb_amr_blk_x ly1 S1 Hp1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) X _ HAR2 Hbufin);
        rewrite ?RQB; unfold X in *; lia.
    + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) X _
        HAR2 Hbufin); rewrite ?RQB; unfold X in *; lia.
    + intros Hpos. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms) _ (re_buf e1)
        (re_cap e1) X _ HAR2 Hbufin); rewrite ?RQB; unfold X in *; lia.
  - split; [|split].
    + apply lb_amr_img_x; unfold IMG_TOP; lia.
    + apply (lb_ra_sub_x _ _ _ 14); [exact (proj1 (proj2 (proj2 HLIT5) ly1 S1 Hp1 W1 (ms_mem ms) _ HAR2)) | lia].
    + intros _. apply (lb_hull_sub_x _ _ 14); [exact (HV21 _ _ _ _ _ _ HAR2) | lia].
  - exact ROM2.
  - split.
    + apply (lb_amr_near_x ly1 S1 Hp1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) X HAR2 Hbufin);
        rewrite ?RQB; unfold X in *; lia.
    + apply lb_amr_img_x; unfold IMG_TOP; lia. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hnc & Hfr3 & Hpres3).
jafter_call_keep_pi HS 50%nat regs3 (mrestrict (w_H W1) mem3) HP3 ([] : list nat) HS3.
specialize (HS3 (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 50 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 50)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEb : env_agree 32 (Ereg regs1 (lb_extra v13)) Eb)
  by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
pose proof (lb_keep_call_x cx W1 m1 (ms_mem ms) mem3 KP2 Hfr3 Hpres3) as KP3.
prreg HS (10%bv : bv 5) R10b.
assert (NC : getr regs3 10 = w64 0 <-> firstn 13 (dline s1 p q) = K_GESTURE).
{ rewrite Hnc. unfold astrn_agree. exact (lb_strncmp_iff_x _ X (VAL (A_OBJ 18)) (dline s1 p q) LN3 LIT21). }
clear Hnc LN3 LIT21 ROM2 KP2 FR1 GR1 Q1 Q2 Q3 Q4 Q10 Q11 Q12 V262 HAR2 Hfr3 Hpres3 HP3 SP2.
clear dependent ms.
assert (SHOK2 : sh_ok SEGS lb_Bx [] Eb (mrestrict (w_H W1) mem3)) by constructor.
assert (A54 : ew Eb 54 = getr regs3 10) by (rewrite R10b; reflexivity).
assert (B24 : bv_unsigned (ew Eb 24) = X)
  by (rewrite OLDb, OLDa, (EREG 24%nat 24%bv), H24 by (first [lia | reflexivity]);
      apply unsigned_lit_small; unfold X in *; lia).
psrr_branch_tok RUNR BRR HS SHOK2 lb_Bspan.
- rewrite (lb_br_ne0_x Eb 54 _ A54) in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  assert (GN : gesture (dline s1 p q) = None).
  { apply lb_g_nok_x. intros Hk. apply Hc. apply lb_w0_x. exact (proj2 NC Hk). }
  paj_run_to_tok_xR RUNTOR HS HJ3 SHOK2 lb_Bspan A_dr_next; [apply awr_ok_x_nil|].
  rename HFr into FRn; rename HG0 into GRn; clear HF.
  assert (KPn : lb_keep cx W1 m1 (ms_mem ms)).
  { apply (lb_keep_run_x cx W1 m1 mem3 (ms_mem ms) _ _ KP3 FRn GRn). intros a (r & Hin & _). destruct Hin. }
  pmkst HS.
  apply (KN (ms_regs ms) (ms_mem ms) _ GN); [| exact KPn | exact HJ3].
  intros r Hr.
  exact (regs_kept_of_st_ok_pi _ _ _ regs1 (lb_extra v13) [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 27]%bv HS HAEb
    ltac:(vm_compute; reflexivity) r Hr).
- rewrite (lb_br_ne0_x Eb 54 _ A54) in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  assert (HK13 : firstn 13 (dline s1 p q) = K_GESTURE) by (apply NC; apply lb_w0_x; exact Hc).
  clear Hc.
  assert (HL13 : (13 <= q - p)%nat).
  { pose proof (f_equal (@length Z) HK13) as HLk. rewrite length_firstn, HLEN in HLk. cbn [length K_GESTURE] in HLk. lia. }
  pose proof (Hbg (p + 13)%nat ltac:(rewrite HLl; lia)) as (HV13 & V13R).
  rewrite HLapp, app_nth1 in HV13, V13R by lia. fold v13 in HV13, V13R.
  assert (HB13 : val_mem SEGS (arm W1 mem3) (X + 13) 1 v13).
  { apply (akept_vm W1 m1 W1 mem3 (X + 13) 1 v13).
    - intros x Hx. apply (lb_keep_byte_x cx Hpe kr W1 m1 mem3 x HB KP3). unfold X in *; lia.
    - replace (X + 13) with (re_buf e1 + Z.of_nat (p + 13)) by (unfold X; lia). exact HV13. }
  assert (E32b : ew Eb 32 = Z_to_bv 64 v13) by (rewrite OLDb, OLDa by lia; exact E32).
  apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 24%nat) 13 14 0 0 [YP09.mkChunk 13 (CVal 1 (SOff 32 0))])) in HS;
  [ | vm_compute; reflexivity
    | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite B24; split; [unfold X in *; lia|]; split; [unfold X in *; lia|]; split; [intros o Ho; lia|];
      apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val SEGS Eb _ X 13 1 (SOff 32 0) v13);
      [ exact (den_atom0 Eb 32 v13 E32b ltac:(lia)) | cbn; lia | cbn; lia | exact HB13 ]
    | cbn; exact I ].
  (* the frame seated as a region (Section c's walk, lb_frame_region) *)
  assert (USPb : bv_unsigned (ew Eb 2) = dsp0 cx - DRAIN_FRAME) by (rewrite OLDb, OLDa by lia; exact Usp).
  assert (E20b : ew Eb 20 = Z_to_bv 64 (dxSA cx + 16))
    by (rewrite OLDb, OLDa, (EREG 20%nat 20%bv), Hr20 by (first [lia | reflexivity]); reflexivity).
  assert (E21b : ew Eb 21 = Z_to_bv 64 (dxSA cx))
    by (rewrite OLDb, OLDa, (EREG 21%nat 21%bv), Hr21 by (first [lia | reflexivity]); reflexivity).
  assert (E22b : ew Eb 22 = Z_to_bv 64 (dxSA cx + 24))
    by (rewrite OLDb, OLDa, (EREG 22%nat 22%bv), Hr22 by (first [lia | reflexivity]); reflexivity).
  assert (E33b : ew Eb 33 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDb, OLDa by lia; exact E33).
  pose proof (lb_frame_slots_x cx Hpe kr W1 m1 mem3 HB KP3 HFRM) as (VM128 & VM136 & VM144 & VM240).
  apply (st_ok_pi_add_region _ _ _ lb_frame_region) in HS;
  [ | vm_compute; reflexivity
    | apply (lb_frame_region_ok_x cx Hpe kr Eb _ HB USPb E20b E21b E22b E33b HSAr VM128 VM136 VM144 VM240)
    | apply (lb_frame_disj_x cx Eb X B24 USPb); unfold X in *; lia ].
  pose proof HJ3 as HAR3. apply ajournal_gx_AR_xR in HAR3.
  assert (SHOK3 : sh_ok SEGS lb_Bx [mkSHE 24 13 14] Eb (mrestrict (w_H W1) mem3)).
  { unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
    eapply (shent_ok_of_range SEGS (w_H W1) mem3 Eb lb_Bx 24%nat (X + 13) 1 X 13 14).
    - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 mem3 _ (re_buf e1) (re_cap e1) (X + 13) 1
        HAR3 Hbufin); rewrite ?RQB; unfold X in *; lia.
    - unfold lb_Bx. apply U_atom; [|unfold SHADOW_OFF; lia]. exact E33b.
    - apply U_atom; [|unfold X in *; lia].
      rewrite OLDb, OLDa, (EREG 24%nat 24%bv), H24 by (first [lia | reflexivity]). reflexivity.
    - lia.
    - lia.
    - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, X in *. cbn [Z.min Z.max] in Hx. lia. }
  paj_run_tok_xR RUNR HS HJ3 SHOK3 lb_Bspan; [lb_awr2_x|].
  rename HFr into FR4; rename HG0 into GR4; clear HF.
  assert (KP4 : lb_keep cx W1 m1 (ms_mem ms)) by (apply (lb_keep_run_x cx W1 m1 mem3 (ms_mem ms) _ _ KP3 FR4 GR4); lb_nowr_x).
  assert (HAEc : env_agree 32 (Ereg regs1 (lb_extra v13)) (ewset (ewset Eb 512 w) 513 w0))
    by (repeat (apply lb_ae_ewset_x; [lia|]); exact HAEb).
  assert (C32 : ew (ewset (ewset Eb 512 w) 513 w0) 32 = Z_to_bv 64 v13) by (rewrite !ew_ewset_other by lia; exact E32b).
  assert (C38 : ew (ewset (ewset Eb 512 w) 513 w0) 38 = getr regs2 10)
    by (rewrite !ew_ewset_other, OLDb, F38 by lia; reflexivity).
  assert (C24 : ew (ewset (ewset Eb 512 w) 513 w0) 24 = Z_to_bv 64 X)
    by (rewrite !ew_ewset_other, OLDb, OLDa, (EREG 24%nat 24%bv), H24 by (first [lia | reflexivity]); reflexivity).
  assert (N13 : nth 13 (dline s1 p q) 0 = v13) by (rewrite (lb_nth13_x s1 p q Hpq Hnulq HL13); reflexivity).
  pose proof HJ3 as HAR4. apply ajournal_gx_AR_xR in HAR4.
  assert (SHOK4 : sh_ok SEGS lb_Bx [] (ewset (ewset Eb 512 w) 513 w0) (mrestrict (w_H W1) (ms_mem ms))) by constructor.
  psrr_branch_tok RUNR BRR HS SHOK4 lb_Bspan.
  + rewrite (lb_br_ne_byte_x _ 32 v13 32 C32 V13R ltac:(lia)) in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    assert (GN : gesture (dline s1 p q) = None) by (apply lb_g_nsp_x; rewrite N13; unfold SPACE; exact Hc).
    paj_run_to_tok_xR RUNTOR HS HJ3 SHOK4 lb_Bspan A_dr_next; [lb_awr2_x|].
    rename HFr into FRn; rename HG0 into GRn; clear HF.
    assert (KPn : lb_keep cx W1 m1 (ms_mem ms0))
      by (apply (lb_keep_run_x cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP4 FRn GRn); lb_nowr_x).
    pmkst HS. apply (KN _ _ _ GN); [lb_regs_x HS HAEc | exact KPn | exact HJ3].
  + rewrite (lb_br_ne_byte_x _ 32 v13 32 C32 V13R ltac:(lia)) in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    assert (HSP : nth 13 (dline s1 p q) 0 = SPACE) by (rewrite N13; unfold SPACE; exact Hc).
    clear Hc.
    paj_run_tok_xR RUNR HS HJ3 SHOK4 lb_Bspan; [lb_awr2_x|].
    rename HFr into FR5; rename HG0 into GR5; clear HF.
    assert (KP5 : lb_keep cx W1 m1 (ms_mem ms0))
      by (apply (lb_keep_run_x cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP4 FR5 GR5); lb_nowr_x).
    clear dependent ms. rename ms0 into ms.
    psrr_branch_tok RUNR BRR HS SHOK4 lb_Bspan.
    * rewrite (lb_br_eq0_x _ 38 _ C38) in Hc. apply Z.eqb_eq in Hc.
      assert (GN : gesture (dline s1 p q) = None).
      { destruct SR as [(_ & HN) | (j & Hj & Hr10 & _)]; [exact (lb_g_nolast_x _ HN)|].
        exfalso. rewrite HLEN in Hj. rewrite Hr10 in Hc. unfold w64 in Hc.
        rewrite unsigned_lit_small in Hc by (unfold X in *; lia). unfold X in *. lia. }
      paj_run_to_tok_xR RUNTOR HS HJ3 SHOK4 lb_Bspan A_dr_next; [lb_awr2_x|].
      rename HFr into FRn; rename HG0 into GRn; clear HF.
      assert (KPn : lb_keep cx W1 m1 (ms_mem ms0))
        by (apply (lb_keep_run_x cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP5 FRn GRn); lb_nowr_x).
      pmkst HS. apply (KN _ _ _ GN); [lb_regs_x HS HAEc | exact KPn | exact HJ3].
    * rewrite (lb_br_eq0_x _ 38 _ C38) in Hc. apply Z.eqb_neq in Hc.
      destruct SR as [(Hr10 & _) | (j & Hj & Hr10 & HLS)]; [exfalso; apply Hc; rewrite Hr10; reflexivity|].
      clear Hc. rewrite HLEN in Hj.
      assert (C38j : ew (ewset (ewset Eb 512 w) 513 w0) 38 = Z_to_bv 64 (X + Z.of_nat j)) by (rewrite C38, Hr10; reflexivity).
      paj_run_tok_xR RUNR HS HJ3 SHOK4 lb_Bspan; [lb_awr2_x|].
      rename HFr into FR6; rename HG0 into GR6; clear HF.
      assert (KP6 : lb_keep cx W1 m1 (ms_mem ms0))
        by (apply (lb_keep_run_x cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP5 FR6 GR6); lb_nowr_x).
      clear dependent ms. rename ms0 into ms.
      psrr_branch_tok RUNR BRR HS SHOK4 lb_Bspan.
      -- rewrite (lb_br_eq_ao_x _ 38 24 (X + Z.of_nat j) X 13 C38j C24) in Hc by (unfold X in *; lia).
         apply Z.eqb_eq in Hc.
         assert (GN : gesture (dline s1 p q) = None) by (apply lb_g_13_x; replace 13%nat with j by lia; exact HLS).
         paj_run_to_tok_xR RUNTOR HS HJ3 SHOK4 lb_Bspan A_dr_next; [lb_awr2_x|].
         rename HFr into FRn; rename HG0 into GRn; clear HF.
         assert (KPn : lb_keep cx W1 m1 (ms_mem ms0))
           by (apply (lb_keep_run_x cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP6 FRn GRn); lb_nowr_x).
         pmkst HS. apply (KN _ _ _ GN); [lb_regs_x HS HAEc | exact KPn | exact HJ3].
      -- rewrite (lb_br_eq_ao_x _ 38 24 (X + Z.of_nat j) X 13 C38j C24) in Hc by (unfold X in *; lia).
         apply Z.eqb_neq in Hc.
         destruct (lb_g_last_x _ j HSP HLS) as (Hj13 & _).
         assert (Hjg : (13 < j)%nat) by lia.
         clear Hc.
         (* 0x83a60 li a0,-1; 0x83a64 beq s3,a0 -> 0x84004: the UBSan wrap check, refuted by s3 = line + j *)
         paj_run_tok_xR RUNR HS HJ3 SHOK4 lb_Bspan; [lb_awr2_x|].
         rename HFr into FR6t; rename HG0 into GR6t; clear HF.
         assert (KP6t : lb_keep cx W1 m1 (ms_mem ms0))
           by (apply (lb_keep_run_x cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP6 FR6t GR6t); lb_nowr_x).
         clear dependent ms. rename ms0 into ms.
         psrr_branch_tok RUNR BRR HS SHOK4 lb_Bspan.
         { exfalso. rewrite (lb_br_eq_lit_x _ 38 (X + Z.of_nat j) 18446744073709551615 C38j) in Hc
             by (unfold X in *; lia).
           apply Z.eqb_eq in Hc. unfold X in *. lia. }
         clear Hc.
         paj_run_tok_xR RUNR HS HJ3 SHOK4 lb_Bspan; [lb_awr2_x|].
         rename HFr into FR7; rename HG0 into GR7; clear HF.
         assert (KP7 : lb_keep cx W1 m1 (ms_mem ms0))
           by (apply (lb_keep_run_x cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP6t FR7 GR7); lb_nowr_x).
         clear dependent ms. rename ms0 into ms.
         pmkst HS.
         prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
         prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.

         pose proof HJ3 as HARc3. apply ajournal_gx_AR_xR in HARc3.
         pose proof (lb_line_ext_x _ _ X (dline s1 p q) LN0
           (fun a Ha => lb_keep_low_x cx Hpe kr W1 m1 (ms_mem ms) a HB KP7 ltac:(rewrite HLEN in Ha; unfold X in *; lia)))
           as LNc3.
         pose proof (lb_line_skipn_x _ X (dline s1 p q) j LNc3 ltac:(rewrite HLEN; lia)) as LSc3.
         assert (HLSc3 : length (skipn (S j) (dline s1 p q)) = (q - p - S j)%nat) by (rewrite length_skipn, HLEN; reflexivity).
         pose proof (lb_keep_rom_x cx Hpe kr W1 m1 (ms_mem ms) HB KP7 HROM) as ROMc3.
         pose proof (lb_lit_of_dlit_x 20 W_BEGIN W1 (ms_mem ms) HLIT6 ROMc3 LBB) as LITc3.
         pose proof (lb_lit_range_x 20 _ HLIT6 ltac:(cbv; lia)) as (Yc3a & Yc3b). unfold IMG_TOP in Yc3b.
         change (Z.of_nat (length (W_BEGIN ++ [0]))) with 6 in Yc3b.
         pose proof (pa_obj_img 20 ltac:(lia)) as (Yo3a & Yo3b).
         assert (Vc3 : getr (ms_regs ms) 11 = w64 (VAL (A_OBJ 20))).
         { rewrite Q11. apply bv_eq. unfold w64. rewrite unsigned_lit_small by lia.
           first [ match goal with HI : img_env _ _ ?Ev |- bv_unsigned (ew ?Ev _) = _ => exact (HI (A_OBJ 20) ltac:(cbv; lia)) end
                 | rewrite nth_overflow by (rewrite length_map; cbv; lia);
                   match goal with HI : img_env _ _ ?Ev |- bv_unsigned (ew ?Ev _) = _ =>
                     exact (HI (A_OBJ 20) ltac:(cbv; lia)) end]. }
         assert (Ac3 : getr (ms_regs ms) 10 = w64 (X + Z.of_nat j + 1)).
         { rewrite Q10. lb_ewg_x. rewrite OLDb, F38, Hr10 by lia. unfold w64.
           rewrite unsigned_lit_small by (unfold X in *; lia). reflexivity. }
         assert (SPc3 : spZ (ms_regs ms) = dsp0 cx - DRAIN_FRAME)
           by (unfold spZ; rewrite Q2; lb_ewg_x; rewrite OLDb, OLDa, Usp by lia; reflexivity).
         eapply (YA0nH.SRrG_bind SEGS R R_trans).
         { eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_DR B RG) 0 ([] : list (Z * Z)) (2 * ESTACK) (SIGMA WS_strcmp)
               (fun _ => False) _ W1 (ms_regs ms) (ms_mem ms) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hpe
               (dxW cx) (dxmem cx) (dxmd cx) ([] : list (Z * Z)) ly1 S1 Hp1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ3);
           [ rewrite SPc3; lia
           | reflexivity
           | unfold DRAIN_FRAME; lia
           | unfold ESTACK; lia
           | unfold ESTACK, DRAIN_FRAME; rewrite WS; lia
           | rewrite Q3; lb_ewg_x; rewrite OLDb, OLDa, (EREG 3%nat 3%bv), Hr3 by (first [lia | reflexivity]); exact Hgp
           | rewrite Q4; lb_ewg_x; rewrite OLDb, OLDa, (EREG 4%nat 4%bv), Hr4 by (first [lia | reflexivity]); exact Htp
           | exact Q1
           | apply ret_ok_codeptr_v; [lia | reflexivity]
           | intros _; right; intros []
           | intros a []
           | intros a []
           | ].
           intros HPRE HSC.
           eapply (ASTRCMP ly1 S1 Hp1 W1 (ms_regs ms) (ms_mem ms) _ (X + Z.of_nat j + 1) (VAL (A_OBJ 20))
             (Z.of_nat (q - p) - Z.of_nat j - 1) 5 HPRE HSC).
           - exact Ac3.
           - exact Vc3.
           - unfold X in *; lia.
           - lia.
           - lia.
           - lia.
           - unfold X in *; lia.
           - lia.
           - unfold LINE_LIMIT in *; lia.
           - pose proof (lb_line_first_byte_x W1 (ms_mem ms) _ _ (Z.of_nat (q - p) - Z.of_nat j - 1 + 1) LSc3 ltac:(lia))
               as FB.
             rewrite HLSc3 in FB.
             replace (Z.min (Z.of_nat (q - p) - Z.of_nat j - 1 + 1) (Z.of_nat (q - p - S j)))
               with (Z.of_nat (q - p) - Z.of_nat j - 1) in FB by lia.
             exact FB.
           - pose proof (lb_lit_first_byte_x W1 (ms_mem ms) (VAL (A_OBJ 20)) W_BEGIN (5 + 1) LITc3 NZB ltac:(lia)) as FB.
             change (Z.min (5 + 1) (Z.of_nat (length W_BEGIN))) with 5 in FB. exact FB.
           - intros a Ha. split.
             + apply (lb_line_vis_x _ _ _ a LSc3). rewrite HLSc3. lia.
             + rewrite SPc3. unfold X in *. lia.
           - intros a Ha. split.
             + apply (lb_lit_vis_x _ _ W_BEGIN a LITc3). cbn [length W_BEGIN]. lia.
             + rewrite SPc3. lia.
           - split; [|split].
             + apply (lb_amr_blk_x ly1 S1 Hp1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) _ _ HARc3 Hbufin);
                 rewrite ?RQB; unfold X in *; lia.
             + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms) _ (re_buf e1)
                 (re_cap e1) _ _ HARc3 Hbufin); rewrite ?RQB; unfold X in *; lia.
             + intros Hpos. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms) _
                 (re_buf e1) (re_cap e1) _ _ HARc3 Hbufin); rewrite ?RQB; unfold X in *; lia.
           - split; [|split].
             + apply lb_amr_img_x; unfold IMG_TOP; lia.
             + apply (lb_ra_sub_x _ _ _ 6); [exact (proj1 (proj2 (proj2 HLIT6) ly1 S1 Hp1 W1 (ms_mem ms) _ HARc3)) | lia].
             + intros _. apply (lb_hull_sub_x _ _ 6); [exact (HV23 _ _ _ _ _ _ HARc3) | lia].
           - exact ROMc3.
           - split.
             + apply (lb_amr_near_x ly1 S1 Hp1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) _ HARc3 Hbufin);
                 rewrite ?RQB; unfold X in *; lia.
             + apply lb_amr_img_x; unfold IMG_TOP; lia. }
         cbv beta. intros W3x c3x Hwle3x (-> & regs4 & mem4 & md3x & -> & HJ4 & HP3x & Hbc & Hfr3x & Hpres3x).
         jafter_call_keep_pi HS 66%nat regs4 (mrestrict (w_H W1) mem4) HP3x ([] : list nat) HS3x.
         specialize (HS3x (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS3x. rename HS3x into HS.
         lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
           assert (HEIc3 : img_env VAL A_LIM Ev) by (apply img_env_havoc; [assumption | cbv; lia]) end.
         pose proof (lb_keep_call_x cx W1 m1 (ms_mem ms) mem4 KP7 Hfr3x Hpres3x) as KP8.
         prreg HS (10%bv : bv 5) R10c.
         lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
           assert (A70 : ew Ev 70 = getr regs4 10) by (rewrite R10c; reflexivity) end.
         assert (BC : getr regs4 10 = w64 0 <-> skipn (S j) (dline s1 p q) = W_BEGIN).
         { rewrite Hbc. pose proof (lb_strcmp_iff_x _ X (VAL (A_OBJ 20)) (dline s1 p q) W_BEGIN j LNc3 LITc3
             ltac:(rewrite HLEN; lia)) as I.
           rewrite HLEN in I. change (Z.of_nat (length W_BEGIN)) with 5 in I. exact I. }
         clear Hbc. clear dependent ms.
         (* the reloads of s5 / s6 / s4 from the frame (0x83a80 .. 0x83a88): seat the frame again *)
         lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
           assert (SHOK5 : sh_ok SEGS lb_Bx [] Ev (mrestrict (w_H W1) mem4)) by constructor;
           assert (USPc : bv_unsigned (ew Ev 2) = dsp0 cx - DRAIN_FRAME) by (lb_ewg_x; exact USPb);
           assert (E20c : ew Ev 20 = Z_to_bv 64 (dxSA cx + 16)) by (lb_ewg_x; exact E20b);
           assert (E21c : ew Ev 21 = Z_to_bv 64 (dxSA cx)) by (lb_ewg_x; exact E21b);
           assert (E22c : ew Ev 22 = Z_to_bv 64 (dxSA cx + 24)) by (lb_ewg_x; exact E22b);
           assert (E33c : ew Ev 33 = Z_to_bv 64 SHADOW_OFF) by (lb_ewg_x; exact E33b) end.
         pose proof (lb_frame_slots_x cx Hpe kr W1 m1 mem4 HB KP8 HFRM) as (VM128c & VM136c & VM144c & VM240c).
         apply (st_ok_pi_add_region _ _ _ lb_frame_region) in HS;
         [ | vm_compute; reflexivity
           | exact (lb_frame_region_ok_x cx Hpe kr _ _ HB USPc E20c E21c E22c E33c HSAr VM128c VM136c VM144c VM240c)
           | cbn; exact I ].
         paj_run_tok_xR RUNR HS HJ4 SHOK5 lb_Bspan; [lb_awr1_x|].
         rename HFr into FR9; rename HG0 into GR9; clear HF.
         assert (KP9 : lb_keep cx W1 m1 (ms_mem ms))
           by (apply (lb_keep_run_x cx W1 m1 mem4 (ms_mem ms) _ _ KP8 FR9 GR9); lb_nowr_x).
         psrr_branch_tok RUNR BRR HS SHOK5 lb_Bspan.
         ++ rewrite (lb_br_eq0_x _ _ _ A70) in Hc. apply Z.eqb_eq in Hc.
            assert (HBEG : skipn (S j) (dline s1 p q) = W_BEGIN) by (apply BC; apply lb_w0_x; exact Hc).
            assert (GS : gesture (dline s1 p q) = Some (GBegin, firstn j (dline s1 p q))).
            { rewrite (lb_g_some_x _ j HK13 HSP HLS Hjg). rewrite (proj2 (lb_list_eqb_x _ _) HBEG). reflexivity. }
            paj_run_to_tok_xR RUNTOR HS HJ4 SHOK5 lb_Bspan A_dr_seen; [lb_awr1_x|].
            rename HFr into FRg; rename HG0 into GRg; clear HF.
            assert (KPg : lb_keep cx W1 m1 (ms_mem ms0))
              by (apply (lb_keep_run_x cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP9 FRg GRg); lb_nowr_x).
            pmkst HS. prreg HS (19%bv : bv 5) R19. prreg HS (26%bv : bv 5) R26. prreg HS (25%bv : bv 5) R25.
            apply (KG _ _ _ GBegin j 0 GS ltac:(lia));
              [ | | | lia | split; intros _; reflexivity | lb_regs_x HS HAEb | exact KPg | exact HJ4 ].
            ** rewrite R19. lb_ewg_x. rewrite OLDb, F38, Hr10 by lia. reflexivity.
            ** rewrite R26. lb_ewg_x. rewrite OLDb, F38, Hr10 by lia. unfold w64.
               rewrite unsigned_lit_small by (unfold X in *; lia). reflexivity.
            ** rewrite R25, <- R10c. apply lb_w0_x. exact Hc.
         ++ rewrite (lb_br_eq0_x _ _ _ A70) in Hc. apply Z.eqb_neq in Hc.
            assert (HNB : skipn (S j) (dline s1 p q) <> W_BEGIN)
              by (intros E0; apply Hc; apply lb_w0_x; exact (proj2 BC E0)).
            rename Hc into R4nz.
            paj_run_tok_xR RUNR HS HJ4 SHOK5 lb_Bspan; [lb_awr1_x|].
            rename HFr into FR10; rename HG0 into GR10; clear HF.
            assert (KP10 : lb_keep cx W1 m1 (ms_mem ms0))
              by (apply (lb_keep_run_x cx W1 m1 (ms_mem ms) (ms_mem ms0) _ _ KP9 FR10 GR10); lb_nowr_x).
            clear dependent ms. rename ms0 into ms.
            pmkst HS.
            prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
            prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.

         pose proof HJ4 as HARc4. apply ajournal_gx_AR_xR in HARc4.
         pose proof (lb_line_ext_x _ _ X (dline s1 p q) LN0
           (fun a Ha => lb_keep_low_x cx Hpe kr W1 m1 (ms_mem ms) a HB KP10 ltac:(rewrite HLEN in Ha; unfold X in *; lia)))
           as LNc4.
         pose proof (lb_line_skipn_x _ X (dline s1 p q) j LNc4 ltac:(rewrite HLEN; lia)) as LSc4.
         assert (HLSc4 : length (skipn (S j) (dline s1 p q)) = (q - p - S j)%nat) by (rewrite length_skipn, HLEN; reflexivity).
         pose proof (lb_keep_rom_x cx Hpe kr W1 m1 (ms_mem ms) HB KP10 HROM) as ROMc4.
         pose proof (lb_lit_of_dlit_x 21 W_END W1 (ms_mem ms) HLIT7 ROMc4 LBE) as LITc4.
         pose proof (lb_lit_range_x 21 _ HLIT7 ltac:(cbv; lia)) as (Yc4a & Yc4b). unfold IMG_TOP in Yc4b.
         change (Z.of_nat (length (W_END ++ [0]))) with 4 in Yc4b.
         pose proof (pa_obj_img 21 ltac:(lia)) as (Yo4a & Yo4b).
         assert (Vc4 : getr (ms_regs ms) 11 = w64 (VAL (A_OBJ 21))).
         { rewrite Q11. apply bv_eq. unfold w64. rewrite unsigned_lit_small by lia.
           first [ match goal with HI : img_env _ _ ?Ev |- bv_unsigned (ew ?Ev _) = _ => exact (HI (A_OBJ 21) ltac:(cbv; lia)) end
                 | rewrite nth_overflow by (rewrite length_map; cbv; lia);
                   match goal with HI : img_env _ _ ?Ev |- bv_unsigned (ew ?Ev _) = _ =>
                     exact (HI (A_OBJ 21) ltac:(cbv; lia)) end]. }
         assert (Ac4 : getr (ms_regs ms) 10 = w64 (X + Z.of_nat j + 1)).
         { rewrite Q10. lb_ewg_x. rewrite OLDb, F38, Hr10 by lia. unfold w64.
           rewrite unsigned_lit_small by (unfold X in *; lia). reflexivity. }
         assert (SPc4 : spZ (ms_regs ms) = dsp0 cx - DRAIN_FRAME)
           by (unfold spZ; rewrite Q2; lb_ewg_x; rewrite OLDb, OLDa, Usp by lia; reflexivity).
         eapply (YA0nH.SRrG_bind SEGS R R_trans).
         { eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_DR B RG) 0 ([] : list (Z * Z)) (2 * ESTACK) (SIGMA WS_strcmp)
               (fun _ => False) _ W1 (ms_regs ms) (ms_mem ms) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hpe
               (dxW cx) (dxmem cx) (dxmd cx) ([] : list (Z * Z)) ly1 S1 Hp1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ4);
           [ rewrite SPc4; lia
           | reflexivity
           | unfold DRAIN_FRAME; lia
           | unfold ESTACK; lia
           | unfold ESTACK, DRAIN_FRAME; rewrite WS; lia
           | rewrite Q3; lb_ewg_x; rewrite OLDb, OLDa, (EREG 3%nat 3%bv), Hr3 by (first [lia | reflexivity]); exact Hgp
           | rewrite Q4; lb_ewg_x; rewrite OLDb, OLDa, (EREG 4%nat 4%bv), Hr4 by (first [lia | reflexivity]); exact Htp
           | exact Q1
           | apply ret_ok_codeptr_v; [lia | reflexivity]
           | intros _; right; intros []
           | intros a []
           | intros a []
           | ].
           intros HPRE HSC.
           eapply (ASTRCMP ly1 S1 Hp1 W1 (ms_regs ms) (ms_mem ms) _ (X + Z.of_nat j + 1) (VAL (A_OBJ 21))
             (Z.of_nat (q - p) - Z.of_nat j - 1) 3 HPRE HSC).
           - exact Ac4.
           - exact Vc4.
           - unfold X in *; lia.
           - lia.
           - lia.
           - lia.
           - unfold X in *; lia.
           - lia.
           - unfold LINE_LIMIT in *; lia.
           - pose proof (lb_line_first_byte_x W1 (ms_mem ms) _ _ (Z.of_nat (q - p) - Z.of_nat j - 1 + 1) LSc4 ltac:(lia))
               as FB.
             rewrite HLSc4 in FB.
             replace (Z.min (Z.of_nat (q - p) - Z.of_nat j - 1 + 1) (Z.of_nat (q - p - S j)))
               with (Z.of_nat (q - p) - Z.of_nat j - 1) in FB by lia.
             exact FB.
           - pose proof (lb_lit_first_byte_x W1 (ms_mem ms) (VAL (A_OBJ 21)) W_END (3 + 1) LITc4 NZE ltac:(lia)) as FB.
             change (Z.min (3 + 1) (Z.of_nat (length W_END))) with 3 in FB. exact FB.
           - intros a Ha. split.
             + apply (lb_line_vis_x _ _ _ a LSc4). rewrite HLSc4. lia.
             + rewrite SPc4. unfold X in *. lia.
           - intros a Ha. split.
             + apply (lb_lit_vis_x _ _ W_END a LITc4). cbn [length W_END]. lia.
             + rewrite SPc4. lia.
           - split; [|split].
             + apply (lb_amr_blk_x ly1 S1 Hp1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) _ _ HARc4 Hbufin);
                 rewrite ?RQB; unfold X in *; lia.
             + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms) _ (re_buf e1)
                 (re_cap e1) _ _ HARc4 Hbufin); rewrite ?RQB; unfold X in *; lia.
             + intros Hpos. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms) _
                 (re_buf e1) (re_cap e1) _ _ HARc4 Hbufin); rewrite ?RQB; unfold X in *; lia.
           - split; [|split].
             + apply lb_amr_img_x; unfold IMG_TOP; lia.
             + apply (lb_ra_sub_x _ _ _ 4); [exact (proj1 (proj2 (proj2 HLIT7) ly1 S1 Hp1 W1 (ms_mem ms) _ HARc4)) | lia].
             + intros _. apply (lb_hull_sub_x _ _ 4); [exact (HV24 _ _ _ _ _ _ HARc4) | lia].
           - exact ROMc4.
           - split.
             + apply (lb_amr_near_x ly1 S1 Hp1 W1 (ms_mem ms) _ (re_buf e1) (re_cap e1) _ HARc4 Hbufin);
                 rewrite ?RQB; unfold X in *; lia.
             + apply lb_amr_img_x; unfold IMG_TOP; lia. }
         cbv beta. intros W4x c4x Hwle4x (-> & regs5 & mem5 & md4x & -> & HJ5 & HP4x & Hbe & Hfr4x & Hpres4x).
         jafter_call_keep_pi HS 82%nat regs5 (mrestrict (w_H W1) mem5) HP4x ([] : list nat) HS4x.
         specialize (HS4x (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS4x. rename HS4x into HS.
         lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
           assert (HEIc4 : img_env VAL A_LIM Ev) by (apply img_env_havoc; [assumption | cbv; lia]) end.
         pose proof (lb_keep_call_x cx W1 m1 (ms_mem ms) mem5 KP10 Hfr4x Hpres4x) as KP11.

            prreg HS (10%bv : bv 5) R10d.
            lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
              assert (A86 : ew Ev 86 = getr regs5 10) by (rewrite R10d; reflexivity) end.
            assert (BE : getr regs5 10 = w64 0 <-> skipn (S j) (dline s1 p q) = W_END).
            { rewrite Hbe. pose proof (lb_strcmp_iff_x _ X (VAL (A_OBJ 21)) (dline s1 p q) W_END j LNc4 LITc4
                ltac:(rewrite HLEN; lia)) as I.
              rewrite HLEN in I. change (Z.of_nat (length W_END)) with 3 in I. exact I. }
            clear Hbe. clear dependent ms.
            lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
              assert (SHOK6 : sh_ok SEGS lb_Bx [] Ev (mrestrict (w_H W1) mem5)) by constructor end.
            psrr_branch_tok RUNR BRR HS SHOK6 lb_Bspan.
            ** rewrite (lb_br_ne0_x _ _ _ A86) in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
               assert (GN : gesture (dline s1 p q) = None).
               { rewrite (lb_g_some_x _ j HK13 HSP HLS Hjg).
                 destruct (list_eqb (skipn (S j) (dline s1 p q)) W_BEGIN) eqn:EB;
                   [exfalso; apply HNB; apply lb_list_eqb_x; exact EB|].
                 destruct (list_eqb (skipn (S j) (dline s1 p q)) W_END) eqn:EE;
                   [exfalso; apply Hc; apply lb_w0_x; apply BE; apply lb_list_eqb_x; exact EE|].
                 reflexivity. }
               paj_run_to_tok_xR RUNTOR HS HJ5 SHOK6 lb_Bspan A_dr_next; [apply awr_ok_x_nil|].
               rename HFr into FRn; rename HG0 into GRn; clear HF.
               assert (KPn : lb_keep cx W1 m1 (ms_mem ms))
                 by (apply (lb_keep_run_x cx W1 m1 mem5 (ms_mem ms) _ _ KP11 FRn GRn); lb_nowr_x).
               pmkst HS. apply (KN _ _ _ GN); [lb_regs_x HS HAEb | exact KPn | exact HJ5].
            ** rewrite (lb_br_ne0_x _ _ _ A86) in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
               assert (HEND : skipn (S j) (dline s1 p q) = W_END) by (apply BE; apply lb_w0_x; exact Hc).
               assert (GS : gesture (dline s1 p q) = Some (GEnd, firstn j (dline s1 p q))).
               { rewrite (lb_g_some_x _ j HK13 HSP HLS Hjg).
                 destruct (list_eqb (skipn (S j) (dline s1 p q)) W_BEGIN) eqn:EB;
                   [exfalso; apply HNB; apply lb_list_eqb_x; exact EB|].
                 rewrite (proj2 (lb_list_eqb_x _ _) HEND). reflexivity. }
               paj_run_to_tok_xR RUNTOR HS HJ5 SHOK6 lb_Bspan A_dr_seen; [apply awr_ok_x_nil|].
               rename HFr into FRg; rename HG0 into GRg; clear HF.
               assert (KPg : lb_keep cx W1 m1 (ms_mem ms))
                 by (apply (lb_keep_run_x cx W1 m1 mem5 (ms_mem ms) _ _ KP11 FRg GRg); lb_nowr_x).
               pmkst HS. prreg HS (19%bv : bv 5) R19. prreg HS (26%bv : bv 5) R26. prreg HS (25%bv : bv 5) R25.
               pose proof (bv_unsigned_in_range 64 (getr regs4 10)) as RR4. change (bv_modulus 64) with (2 ^ 64) in RR4.
               apply (KG _ _ _ GEnd j (bv_unsigned (getr regs4 10)) GS ltac:(lia));
                 [ | | | exact RR4 | split; [intros E0; contradiction | intros E0; discriminate]
                 | lb_regs_x HS HAEb | exact KPg | exact HJ5 ].
               --- rewrite R19. lb_ewg_x. rewrite OLDb, F38, Hr10 by lia. reflexivity.
               --- rewrite R26. lb_ewg_x. rewrite OLDb, F38, Hr10 by lia. unfold w64.
                   rewrite unsigned_lit_small by (unfold X in *; lia). reflexivity.
               --- rewrite R25, <- R10c. unfold w64. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* R twin of dr_lineb_x *)
Theorem dr_lineb_xR : dr_lineb_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
apply dr_lineb_of_xR.
- intros ly S Hp W mem md HAR. exact (proj2 (proj2 (proj2 HLIT5) ly S Hp W mem md HAR) ltac:(vm_compute; reflexivity)).
- intros ly S Hp W mem md HAR. exact (proj2 (proj2 (proj2 HLIT6) ly S Hp W mem md HAR) ltac:(vm_compute; reflexivity)).
- intros ly S Hp W mem md HAR. exact (proj2 (proj2 (proj2 HLIT7) ly S Hp W mem md HAR) ltac:(vm_compute; reflexivity)).
Qed.
End wR.
(* the strict texts are the R twins above at R := wle: each R premise at wle is the strict hypothesis of the same
   name, and the three laws hold for wle *)
Local Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

(* the cut's core, moved to a memory that keeps drain's frame and every byte below alloc_ceiling + 8: the journal at
   the new memory is the call's (the cut's ghost list Hp1 and allocator state kept), the rest by lb_keep *)
Lemma lb_lcore_keep_x : forall cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  m2 md2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
LCORE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl ->
lb_keep cx W1 m1 m2 ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
LCORE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m2 md2 k1 e1 h1 out1 ev1 LB1
  spent tl.
Proof.
eapply (lb_lcore_keep_xR (@wle SEGS)); wle_inst.
Qed.

Lemma lbB_lcore_none_x : forall cx Hp kr s1 D sent kl kl' l H ka no oc n sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl,
gesture l = None -> kl' = kl ++ [l] ->
LCORE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D sent kl H ka no oc (Z.of_nat (S n)) sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1
  ev1 LB1 spent tl ->
LCORE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D sent kl' H ka no oc (Z.of_nat n) sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1
  ev1 LB1 spent tl.
Proof.
eapply (lbB_lcore_none_xR (@wle SEGS)); wle_inst.
Qed.

(* ---- the two exits: DLN_x (S q) for a non-gesture line, DGS_x for a gesture; the cut's ghost list Hp1, its
   allocator state and its dbud_x are DLS_x's ---- *)
Lemma lb_mk_dln_x : forall cx Hp kr s1 D p q regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl W1
  regs2 m2 md2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
dregs_line RG cx regs1 W1 m1 ->
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) ->
dinband (re_buf e1) (re_cap e1) -> 0 < re_cap e1 ->
dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) ->
dskp s1 p = false -> (q - p <= LINE_LIMIT)%nat ->
LCORE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q])
  (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
dsfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (drlq s1 (S q)) jb o ha ks tl ->
gesture (dline s1 p q) = None ->
spZ regs2 = spZ regs1 ->
getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 -> getr regs2 21 = getr regs1 21 ->
getr regs2 20 = getr regs1 20 -> getr regs2 22 = getr regs1 22 -> getr regs2 27 = getr regs1 27 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 23 = getr regs1 23 ->
lb_keep cx W1 m1 m2 ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
DLN_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S q) W1 (cfg_at SEGS (BASE + A_dr_next) regs2 m2 md2).
Proof.
eapply (lb_mk_dln_xR (@wle SEGS)); wle_inst.
Qed.

Lemma lb_mk_dgs_x : forall cx Hp kr s1 D p q regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl W1
  regs2 m2 md2 (kd : gkind) (jj : nat) (bg : Z),
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
dregs_line RG cx regs1 W1 m1 ->
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) -> getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) ->
dinband (re_buf e1) (re_cap e1) -> 0 < re_cap e1 ->
dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) ->
dskp s1 p = false -> (q - p <= LINE_LIMIT)%nat ->
LCORE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q])
  (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
dsfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (drlq s1 (S q)) jb o ha ks tl ->
spZ regs2 = spZ regs1 ->
getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 -> getr regs2 21 = getr regs1 21 ->
getr regs2 20 = getr regs1 20 -> getr regs2 22 = getr regs1 22 -> getr regs2 27 = getr regs1 27 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 ->
getr regs2 19 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj) ->
getr regs2 26 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj + 1) -> getr regs2 25 = w64 bg ->
0 <= bg < 2 ^ 64 -> (bg = 0 <-> kd = GBegin) ->
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) -> (13 < jj < q - p)%nat ->
lb_keep cx W1 m1 m2 ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
DGS_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q W1 (cfg_at SEGS (BASE + A_dr_seen) regs2 m2 md2).
Proof.
eapply (lb_mk_dgs_xR (@wle SEGS)); wle_inst.
Qed.

(* ---- LINEB over ARx: DLS_x 0x839f4 -> gesture_seen's classification tests -> DLN_x (S q) or DGS_x 0x83aa4.
   dr_lineb_of's walk: the entry's ghost list Hpe and budget kr ride in DBASE_x and dPOST_x untouched; the journal is
   ajournal_gx_x at the cut's Hp1, which the three runtime calls keep. ---- *)
Theorem dr_lineb_of_x :
(forall ly S Hp W mem md, ARx ly S Hp W mem md -> shadow_hull_vis (aview SEGS (w_H W) mem) (VAL (A_OBJ 18)) 14) ->
(forall ly S Hp W mem md, ARx ly S Hp W mem md -> shadow_hull_vis (aview SEGS (w_H W) mem) (VAL (A_OBJ 20)) 6) ->
(forall ly S Hp W mem md, ARx ly S Hp W mem md -> shadow_hull_vis (aview SEGS (w_H W) mem) (VAL (A_OBJ 21)) 4) ->
dr_lineb_stmt_x B PST ARx MT RP MMAX RG.
Proof.
eapply (dr_lineb_of_xR (@wle SEGS)); wle_inst.
Qed.

(* dr_lineb_stmt_x B PST ARx MT RP MMAX RG (lib/B/W_drain_lineb_cx.v Section cx): the three literals' shadow hulls are
   dlit_at_x's ashp_x, at every ARx state *)
Theorem dr_lineb_x : dr_lineb_stmt_x B PST ARx MT RP MMAX RG.
Proof.
eapply (dr_lineb_xR (@wle SEGS)); wle_inst.
Qed.

End cx.
End b.
End a.
