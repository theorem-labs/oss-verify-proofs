(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the held-key search loop of segment GS of the ASan walk of fuzz_reply's drain
   (fuzz_reply.asan 0x83838 .. 0x83894 and the match exit 0x83930 .. 0x8393c, gesture_seen's loop over s->held,
   relay.c:104-108 inlined), in the form of this lane's W_drain_next.v (a call site through aj_gx_entry_at, the
   cut's memory core moved across the call's scratch) and of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v (a loop over concrete cut states, by induction on the iterations left).
   The statement is lib/A/W_gsscanb_cx.v's gs_scan_loop_stmt; the Section header below is that file's, verbatim.

   The loop body, from the cut GSL (0x83838) at slot n:
     0x83838 lbu a0,0(s3); ld s10,80(sp); add s10,s10,s4; bnez a0,83cec    the shadow byte of &held[n]
     0x83848 ld s6,0(s10); mv a0,s6; jal strlen                             held[n], strlen (ASTRLEN)
     0x83854 bne a0,s11,8386c                                               |key| <> jj: no match
     0x83858 mv a0,s6; mv a1,s8; mv a2,s11; jal strncmp; beqz a0,83930      strncmp (ASTRNCMP) over jj bytes
     0x8386c addi s4,s4,8; addi s3,s3,1; bne s9,s4,83838                     on to slot n + 1, or
     0x83878 .. 0x83894  the spilled registers back, j 8389c                 no slot left: GA
     0x83930 ld s6,56(sp); ld s11,48(sp); ld a0,40(sp); beqz a0,836f4        a match: a begin -> DLN (S q),
                                                                            an end -> GF (0x83940)
   The proof has one intermediate cut, GSN (0x8386c: slot n read and not matched), so that the two no-match
   edges of the body share one walk of the loop's bottom:
     gsl_body : GSL n (S kf) -> GSN n (S kf) | DLN (S q) | GF
     gsl_tail : GSN n (S kf) -> GSL (S n) kf (kf > 0) | GA (kf = 0)
   and gs_scan_loop is the induction on the external kf.

   The one ASan report branch of the body, 0x83844 bnez a0 -> 0x83cec (the shadow byte of the 8-byte slot
   &held[n]), is refuted by the token layer: the slot lies in the held array's block (aentry_okx), so the shadow
   entry gl_SH = [mkSHE 33 0 8] over atom 33 = &held[n] is addressable and tok_load folds the byte to 0.  The
   interceptors' own checks are their contracts' premises (first_byte, ain_ok, achecked, the granule tail by
   ALLOC_TAIL), discharged from the key's and the relay buffer's blocks. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx
W_drain_cx W_drain_gs W_gsscanb_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ---------------------------------------------------------------------------------------------------------
   (0) Bytes (W_gsscan_scratch.v's gss_*, copied).
   --------------------------------------------------------------------------------------------------------- *)

Lemma gsl_bzs_app : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.

Lemma gsl_bzs_len : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.

Lemma gsl_aview_garr8 : forall (W : world SEGS) m base l j,
garr8 SEGS (arm W m) base l -> (j < length l)%nat ->
aview SEGS (w_H W) m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m base l j Hg Hj. destruct (Hg j Hj) as (_ & Hr).
unfold aview. change (mrestrict (w_H W) m) with (arm W m).
rewrite (garr8_mbyte SEGS (arm W m) base l j Hg Hj). cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact Hr.
Qed.

Lemma gsl_garr8_sub : forall (W : world SEGS) m base l o n,
garr8 SEGS (arm W m) base l -> (o + n <= length l)%nat ->
garr8 SEGS (arm W m) (base + Z.of_nat o) (firstn n (skipn o l)).
Proof.
intros W m base l o n Hg Hon j Hj.
rewrite length_firstn, length_skipn in Hj.
assert (Hj' : (j < n)%nat) by lia.
rewrite nth_firstn, nth_skipn, (proj2 (Nat.ltb_lt j n) Hj').
replace (base + Z.of_nat o + Z.of_nat j) with (base + Z.of_nat (o + j)) by lia.
apply Hg. lia.
Qed.

Lemma gsl_first_byte : forall (W : world SEGS) m base (l : list Z) (n k : Z),
garr8 SEGS (arm W m) base l -> 0 <= k <= n -> n <= Z.of_nat (length l) ->
(forall i, (i < Z.to_nat k)%nat -> nth i l 0 <> 0) ->
(k < n -> nth (Z.to_nat k) l 0 = 0) ->
first_byte SEGS W m base n 0 k.
Proof.
intros W m base l n k Hg Hkn Hnl Hnz Hz. split; [exact Hkn|]. split.
- intros i Hi. exists (nth (Z.to_nat i) l 0). split.
  + replace (base + i) with (base + Z.of_nat (Z.to_nat i)) by lia.
    apply (gsl_aview_garr8 W m base l (Z.to_nat i) Hg). lia.
  + apply Hnz. lia.
- intros Hlt. replace (base + k) with (base + Z.of_nat (Z.to_nat k)) by lia.
  rewrite (gsl_aview_garr8 W m base l (Z.to_nat k) Hg ltac:(lia)). rewrite (Hz Hlt). reflexivity.
Qed.

Lemma gsl_agree_iff : forall (W : world SEGS) m x y (n : Z) (lx ly : list Z),
garr8 SEGS (arm W m) x lx -> garr8 SEGS (arm W m) y ly ->
0 <= n -> n <= Z.of_nat (length lx) -> n <= Z.of_nat (length ly) ->
(forall i, (i < Z.to_nat n)%nat -> nth i lx 0 <> 0) ->
(astrn_agree W m x y n <-> firstn (Z.to_nat n) lx = firstn (Z.to_nat n) ly).
Proof.
intros W m x y n lx ly Hx Hy Hn Hlx Hly Hnz.
assert (AV : forall i, (i < Z.to_nat n)%nat ->
  aview SEGS (w_H W) m (x + Z.of_nat i) = Some (nth i lx 0) /\
  aview SEGS (w_H W) m (y + Z.of_nat i) = Some (nth i ly 0)).
{ intros i Hi. split; [apply (gsl_aview_garr8 W m x lx i Hx) | apply (gsl_aview_garr8 W m y ly i Hy)]; lia. }
assert (NZ : forall j, 0 <= j < n -> aview SEGS (w_H W) m (x + j) <> Some 0).
{ intros j Hj. replace (x + j) with (x + Z.of_nat (Z.to_nat j)) by lia.
  rewrite (proj1 (AV (Z.to_nat j) ltac:(lia))). intros E. injection E as E.
  exact (Hnz (Z.to_nat j) ltac:(lia) E). }
split.
- intros HA. apply (nth_ext _ _ 0 0).
  { rewrite !length_firstn. lia. }
  intros i Hi. rewrite length_firstn in Hi.
  rewrite !nth_firstn, (proj2 (Nat.ltb_lt i (Z.to_nat n)) ltac:(lia)).
  pose proof (HA (Z.of_nat i) ltac:(lia) ltac:(intros j Hj; apply NZ; lia)) as E.
  rewrite (proj1 (AV i ltac:(lia))), (proj2 (AV i ltac:(lia))) in E.
  injection E as E. exact E.
- intros HE i Hi _. replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia.
  replace (y + i) with (y + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (proj1 (AV (Z.to_nat i) ltac:(lia))), (proj2 (AV (Z.to_nat i) ltac:(lia))).
  f_equal.
  assert (Hfi : nth (Z.to_nat i) (firstn (Z.to_nat n) lx) 0 = nth (Z.to_nat i) (firstn (Z.to_nat n) ly) 0)
    by (rewrite HE; reflexivity).
  rewrite !nth_firstn, (proj2 (Nat.ltb_lt (Z.to_nat i) (Z.to_nat n)) ltac:(lia)) in Hfi. exact Hfi.
Qed.

Lemma gsl_garr8_kept : forall (W : world SEGS) m (W' : world SEGS) m' a l,
garr8 SEGS (arm W m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') a l.
Proof.
intros W m W' m' a l H K. apply (garr8_frame SEGS (arm W m) (arm W' m') a l H).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (K x Hx).
Qed.

Lemma gsl_vm_keep : forall (W : world SEGS) m m' a (n : nat) v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W m') a n v.
Proof.
intros W m m' a n v K H k Hk. unfold arm.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) m m' (a + Z.of_nat k) (K (a + Z.of_nat k) ltac:(lia))).
exact (H k Hk).
Qed.

(* slot n of the held array, from the array's byte image (W_gsscan_scratch.v gss_slot_val, copied) *)
Lemma gsl_le8_bytes : forall v, 0 <= v < 2 ^ 64 -> Mem.le8 (Z_to_bv 64 v) = Z_to_le_bytes 8 v.
Proof.
intros v Hv. unfold Mem.le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact Hv. reflexivity.
Qed.

Lemma gsl_bz_bv8 : forall x, bz (Z_to_bv 8 x) = x mod 256.
Proof. intros x. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. reflexivity. Qed.

Lemma gsl_nth_zle : forall n z k d, (k < n)%nat ->
nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k d Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn [nth]. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma gsl_nth_le_bytes : forall n v k, (k < n)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
nth k (bzs (Z_to_le_bytes n v)) 0 = YO0f.le_byte v n k.
Proof.
intros n v k Hk Hv. unfold bzs.
rewrite (nth_indep (map bz (Z_to_le_bytes n v)) 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite List.map_nth, gsl_nth_zle by exact Hk. rewrite gsl_bz_bv8.
unfold YO0f.le_byte. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.

Lemma gsl_val_of_garr8 : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)) -> val_mem SEGS (arm W m) a n v.
Proof.
intros W m a n v Hv H k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n v)))%nat) by (rewrite gsl_bzs_len, length_Z_to_le_bytes; exact Hk).
rewrite (garr8_mbyte SEGS (arm W m) a _ k H Hl). rewrite gsl_nth_le_bytes by assumption. reflexivity.
Qed.

Lemma gsl_garr8_at : forall mem b l b', garr8 SEGS mem b l -> b = b' -> garr8 SEGS mem b' l.
Proof. intros mem b l b' H <-. exact H. Qed.

Lemma gsl_slot_val : forall (W : world SEGS) m hp (ks : list (Z * list byte * list byte)) (n : nat),
garr8 SEGS (arm W m) hp (bzs (key_ptrs ks)) -> (n < length ks)%nat ->
0 <= key_addr (nth n ks (0, [], [])) < 2 ^ 64 ->
val_mem SEGS (arm W m) (hp + 8 * Z.of_nat n) 8 (key_addr (nth n ks (0, [], []))).
Proof.
intros W m hp ks n Hg Hn Hk.
destruct (nth_split ks (0, [], []) Hn) as (a & b & E & Ha).
set (x := nth n ks (0, [], [])) in *. clearbody x. subst ks n.
rewrite gsx_key_ptrs_cat, gsx_key_ptrs_cons, !gsl_bzs_app in Hg.
apply garr8_app in Hg as [_ Hg]. apply garr8_app in Hg as [Hg _].
rewrite (gsl_le8_bytes (key_addr x) Hk) in Hg.
apply (gsl_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hk|].
apply (gsl_garr8_at _ _ _ _ Hg). rewrite gsl_bzs_len, gs_key_ptrs_len. lia.
Qed.

(* the bytes of a held key: no NUL in its text, the NUL after it *)
Lemma gsl_key_nz : forall t, ~ In (Z_to_bv 8 0) t -> forall i, (i < length t)%nat ->
nth i (bzs (t ++ [Z_to_bv 8 0])) 0 <> 0.
Proof.
intros t Ht i Hi. unfold bzs.
rewrite (nth_indep (map bz (t ++ [Z_to_bv 8 0])) 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_app; cbn [length]; lia).
rewrite List.map_nth, app_nth1 by exact Hi.
intros E. apply Ht. replace (Z_to_bv 8 0) with (nth i t (Z_to_bv 8 0)); [apply nth_In; exact Hi|].
apply bv_eq. unfold bz in E. rewrite E. reflexivity.
Qed.

Lemma gsl_key_z : forall t, nth (length t) (bzs (t ++ [Z_to_bv 8 0])) 0 = 0.
Proof.
intros t. unfold bzs. rewrite map_app. rewrite app_nth2 by (rewrite length_map; lia).
rewrite length_map, Nat.sub_diag. reflexivity.
Qed.

Lemma gsl_bzs_firstn_key : forall t, firstn (length t) (bzs (t ++ [Z_to_bv 8 0])) = bzs t.
Proof. intros t. rewrite gsl_bzs_app, <- (gsl_bzs_len t). apply gsx_firstn_len. Qed.

(* ---------------------------------------------------------------------------------------------------------
   (1) The model of a match on a BEGIN: the held set and the array size do not move, so the line loop's core
   after the sent line is DLC at S q, and what the round still owes is the line loop's rest from S q.
   --------------------------------------------------------------------------------------------------------- *)

Lemma gsl_dlc_same : forall B MT MMAX RG cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl,
GSF s1 p q ->
seen_arr (dlH cx s1 p) (dline s1 p q) = dlH cx s1 p ->
seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) = dlka cx s1 p ->
GSB B MT MMAX RG cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
DLC B MT MMAX RG cx s1 D (S q) ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.
Proof.
intros B MT MMAX RG cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  (HB & HPQ & HQ & HNZ & HK & HL) EH EKA HGS.
destruct (gs_drl s1 p q HB HPQ HQ HNZ HK HL) as (E1 & _ & E3).
unfold DLC. rewrite (gs_dlH cx s1 p q E1), (gs_dlka cx s1 p q E1), (gs_dlno s1 p q E1), (gs_dloc cx s1 p q E1).
rewrite EH, EKA, E3, E1.
unfold GSB, GSno, GSoc in HGS.
unfold LCORE in HGS |- *.
destruct HGS as (HMEM & HLINK & HSAME & HHIST & HRS & HBUD).
split; [exact HMEM|]. split; [exact HLINK|]. split; [exact HSAME|].
split; [|split; [exact HRS | exact HBUD]].
unfold DHIST in HHIST |- *.
destruct HHIST as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
do 8 (split; [assumption|]).
split.
- rewrite app_assoc, gs_upds_snoc.
  pose proof H8 as H8'. apply NoDup_ListNoDup in H8'.
  destruct (seen_arr_ok _ _ (dline s1 p q) H8' H9) as (_ & HS).
  unfold dvirt in HS |- *. cbn [drain_b_c.ds_H] in HS |- *. rewrite EH in HS. exact HS.
- split; [|exact H11]. lia.
Qed.

Lemma gsl_dlfut_same : forall cx s1 p q a jb o ha ks tl,
GSF s1 p q ->
drain_b_c.seen_tr (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) jb ha ks = ([], dlka cx s1 p, (ha, ks)) ->
seen_arr (dlH cx s1 p) (dline s1 p q) = dlH cx s1 p ->
seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) = dlka cx s1 p ->
GSfut cx s1 p q a jb o ha ks tl ->
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlno s1 (S q)) (dloc cx s1 (S q)) (dlH cx s1 (S q))
  (dlka cx s1 (S q)) (drlq s1 (S q)) jb o ha ks tl.
Proof.
intros cx s1 p q a jb o ha ks tl (HB & HPQ & HQ & HNZ & HK & HL) ETR EH EKA HF.
destruct (gs_drl s1 p q HB HPQ HQ HNZ HK HL) as (E1 & _ & _).
rewrite (gs_dlH cx s1 p q E1), (gs_dlka cx s1 p q E1), (gs_dlno s1 p q E1), (gs_dloc cx s1 p q E1), EH, EKA.
unfold GSfut, dsfut in HF. rewrite ETR, EH, EKA in HF. cbn [fst snd] in HF.
destruct HF as (tl2 & Hl & Ht). cbn [app] in Ht. subst tl2.
change (RelayRunT.nret YO0i.sptr []) with 0%nat in Hl. rewrite Nat.add_0_r in Hl.
unfold GSno, GSoc in Hl. exact Hl.
Qed.

(* prreg without the denotation's normal form: the register's symbolic value as the state holds it *)
Ltac gsl_prreg_raw HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the instance's laws *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
(* the walk's globals are .data / .bss cells, never read-only image bytes (the pinned placement decides it) *)
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* the runtime entries drain calls, at their SIGMA pcs (W_sites.v / the donor's YG0d.v) *)
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
(* the allocator's site rules (W_journal.v), at the trampolines the program calls *)
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis ASTRNDUP : astrndup_cf_rule SEGS B MT MMAX (SIGMA WS_strndup).
(* the allocator instance's granule-tail fact (W_drain_cx.v ALLOC_TAIL) *)
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
(* the callees drain calls as a program *)
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
(* instance facts *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 24 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
(* placement of the three cells of aout_at that are not in G_DR (W_drain_cx.v HV9 / HV12 / HSM, as
   W_drain_next.v:266-268 and W_drain_pro.v:74-76 take them) *)
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---------------------------------------------------------------------------------------------------------
   (2) Lowness: every byte the cut's representations touch lies below the allocator ceiling, far below the
   interceptors' scratch (W_gsscan_scratch.v's gss_*_fp_low, copied).
   --------------------------------------------------------------------------------------------------------- *)

Lemma gsl_blk_low : forall ly S (W : world SEGS) mem md qq nn a,
AR SEGS B ly S W mem md -> In (qq, nn) (ablocks B ly S) -> qq <= a -> a < qq + req_size nn ->
0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md qq nn a HAR Hin H1 H2.
destruct (al_blocks SEGS B LAWS ly S W mem md qq nn HAR Hin) as (_ & H4096 & Hceil & _). lia.
Qed.

Lemma gsl_img_low : forall a lo hi, 0x10000 <= lo -> lo <= a -> a < hi -> hi <= 0x5fb000 ->
0 <= a < alloc_ceiling.
Proof. intros a lo hi H1 H2 H3 H4. pose proof asan_consts as (C1 & _). lia. Qed.

Lemma gsl_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma gsl_aentry_fp_low : forall ly S (W : world SEGS) mem md e,
AR SEGS B ly S W mem md -> aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md e HAR HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (HPK : forall k, In k (re_keys e) ->
  key_addr k <= a < key_addr k + Z.of_nat (length (bzs (key_text k ++ [Z_to_bv 8 0]))) ->
  0 <= a < alloc_ceiling).
{ intros k Hk Hak. rewrite gsl_bzs_len, length_app in Hak. cbn [length] in Hak.
  rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
  apply (gsl_blk_low ly S W mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) a HAR Hin); [lia|].
  pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & Hrq). lia. }
assert (HPH : re_hp e <= a < re_hp e + Z.of_nat (length (bzs (key_ptrs (re_keys e)))) ->
  0 <= a < alloc_ceiling).
{ intros Hah. rewrite gsl_bzs_len, gs_key_ptrs_len in Hah.
  destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
  - rewrite Hke in Hah. cbn [length] in Hah. lia.
  - apply (gsl_blk_low ly S W mem md (re_hp e) (re_kh e) a HAR Hin); [lia|].
    pose proof (req_size_pos (re_kh e) ltac:(lia)) as (_ & Hrq). unfold re_nheld in Hk1. lia. }
unfold aentry_fp in Hr.
destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [app In] in Hr.
- destruct Hr as [<- | Hr]; [unfold gfp in Ha; cbn [fst snd] in Ha; exact (HPH Ha)|].
  apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPK k Hk Ha).
- destruct Hr as [<- | [<- | Hr]].
  + unfold gfp in Ha. cbn [fst snd] in Ha. rewrite gsl_bzs_len, length_app in Ha.
    destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (gsl_blk_low ly S W mem md (re_buf e) (re_cap e) a HAR Hin); [lia|].
    pose proof (req_size_pos (re_cap e) ltac:(lia)) as (_ & Hrq). lia.
  + unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPH Ha).
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPK k Hk Ha).
Qed.

Lemma gsl_alist_fp_low : forall ly S (W : world SEGS) mem md LA l lines lo hi,
AR SEGS B ly S W mem md -> alist_at B ly S W mem LA l lines ->
0x10000 <= lo -> lo <= LA -> LA + 16 <= hi -> hi <= 0x5fb000 ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md LA l lines lo hi HAR HL Hlo1 Hlo2 Hhi1 Hhi2 r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (gsl_img_low a lo hi); lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite gsl_bzs_len, length_app, gsl_recs_len in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (gsl_blk_low ly S W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin); [lia|].
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as (_ & Hrq).
    unfold hl_n, AREC in *. lia.
  + apply in_map_iff in Hr as (qq & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite gsl_bzs_len, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs qq Hq) as (Hin & _).
    apply (gsl_blk_low ly S W mem md (fst qq) (Z.of_nat (length (snd qq)) + 1) a HAR Hin); [lia|].
    pose proof (req_size_pos (Z.of_nat (length (snd qq)) + 1) ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma gsl_asrc_fp_low : forall ly S (W : world SEGS) mem md HA h,
AR SEGS B ly S W mem md -> asrc_at B ly S W mem HA h ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md HA h HAR HS Hlo Hhi r Hr a Ha.
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (gsl_img_low a (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. rewrite gsl_bzs_len in Ha.
  apply (gsl_blk_low ly S W mem md (hs_partial h) APARTIAL a HAR Hpb); [lia|].
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq). lia.
- unfold ASRC in *. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + eapply (gsl_alist_fp_low ly S W mem md (HA + 16) (hs_pending h) false (rg_s RG) (rg_s RG + 4 * 96));
      [exact HAR | exact Hpend | lia | lia | lia | lia | exact Hr | exact Ha].
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * eapply (gsl_alist_fp_low ly S W mem md (HA + 64) (hs_expected h) true (rg_s RG) (rg_s RG + 4 * 96));
        [exact HAR | exact Hexp | lia | lia | lia | lia | exact Hr | exact Ha].
    * eapply (gsl_alist_fp_low ly S W mem md (HA + 80) (hs_held h) true (rg_s RG) (rg_s RG + 4 * 96));
        [exact HAR | exact Hheld | lia | lia | lia | lia | exact Hr | exact Ha].
Qed.

Ltac gsl_ing := unfold G_DR, G_SL; cbn [In]; repeat (first [left; reflexivity | right]).

Lemma gsl_aout_fp_low : forall ly S (W : world SEGS) mem md c O mx no cap out,
AR SEGS B ly S W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md c O mx no cap out HAR HOUT r Hr a Ha.
pose proof asan_consts as (C1 & _).
assert (GL2 : forall x l, In (x, l) (G_DR B RG) -> x <= a < x + l -> 0 <= a < alloc_ceiling).
{ intros x l Hin Hx.
  assert (HI : inG (G_DR B RG) a)
    by (unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (pa_img_range _ (proj1 (HG a HI))). lia. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- pose proof HSM as (Hs1 & Hs2). apply (gsl_img_low a (rg_send_max RG) (rg_send_max RG + 8)); lia.
- apply (GL2 (rg_nout RG) 8); [gsl_ing | lia].
- apply (GL2 (rg_capout RG) 8); [gsl_ing | lia].
- apply (GL2 (rg_out RG) 8); [gsl_ing | lia].
- pose proof (pa_obj_img 9 ltac:(lia)) as H9. rewrite HV9 in H9.
  apply (gsl_img_low a (rg_client RG) (rg_client RG + 4)); lia.
- apply (GL2 (rg_client_broken RG) 1); [gsl_ing | lia].
- pose proof (pa_obj_img 12 ltac:(lia)) as H12. rewrite HV12 in H12.
  apply (gsl_img_low a (rg_send_dead RG) (rg_send_dead RG + 1)); lia.
- apply (GL2 (rg_send_eintr RG) 1); [gsl_ing | lia].
- apply (GL2 (as_errno B) 4); [gsl_ing | lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  apply (gsl_blk_low ly S W mem md out cap a HAR Hin); [lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq). lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (3) The cut survives the loop.  The loop stores nothing; its two interceptors write only their scratch
   [sp - 2 ESTACK, sp) below drain's frame.  So every byte outside that scratch keeps its view, presence only
   grows, and the line loop's core moves to the new memory unchanged (W_gsscan_scratch.v gss_core_kept, with
   the interceptors' scratch in place of the stage's frame window).
   --------------------------------------------------------------------------------------------------------- *)
Definition GSKEEP (cx : dcx) (W1 : world SEGS) (m1 m2 : word -> option byte) : Prop :=
(forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - 2 * ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x) /\
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m2 x).

Lemma gsl_keep_trans : forall cx W1 m1 m2 m3, GSKEEP cx W1 m1 m2 -> GSKEEP cx W1 m2 m3 -> GSKEEP cx W1 m1 m3.
Proof.
intros cx W1 m1 m2 m3 (K1 & P1) (K2 & P2). split.
- intros x Hx Hs. rewrite (K2 x Hx Hs). exact (K1 x Hx Hs).
- intros x Hp. exact (P2 x (P1 x Hp)).
Qed.

Lemma gsl_fv_keep : forall cx (W1 : world SEGS) m1 m2 off v,
DRAIN_FRAME <= dsp0 cx <= 2 ^ 47 -> 0 <= off -> off + 8 <= DRAIN_FRAME ->
GSKEEP cx W1 m1 m2 ->
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + off) 8 v -> val_mem SEGS (arm W1 m2) (dsp0 cx - DRAIN_FRAME + off) 8 v.
Proof.
intros cx W1 m1 m2 off v Hsp Ho1 Ho2 (K & _) H.
apply (gsl_vm_keep W1 m1 m2 _ 8%nat _); [|exact H].
intros x Hx. apply K; unfold ESTACK, DRAIN_FRAME in *; cbn in Hx; lia.
Qed.

Lemma gsl_frame_keep : forall cx (W1 : world SEGS) m1 m2,
DRAIN_FRAME <= dsp0 cx <= 2 ^ 47 -> GSKEEP cx W1 m1 m2 ->
dr_frame RG cx W1 m1 -> dr_frame RG cx W1 m2.
Proof.
intros cx W1 m1 m2 Hsp HK HFR. unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
destruct HFR as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 & F224 & F216 & F176 & Hsvd).
repeat split; try (apply (gsl_fv_keep cx W1 m1 m2 _ _ Hsp); [lia | unfold DRAIN_FRAME; lia | exact HK | assumption]).
intros i Hi. specialize (Hsvd i Hi).
replace (dsp0 cx - DRAIN_FRAME + 232 + 8 * Z.of_nat i) with (dsp0 cx - DRAIN_FRAME + (232 + 8 * Z.of_nat i)) in * by lia.
apply (gsl_fv_keep cx W1 m1 m2 _ _ Hsp); [lia | unfold DRAIN_FRAME; lia | exact HK | exact Hsvd].
Qed.

Lemma gsl_core_kept : forall cx s1 D p q ly1 S1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  m2 md2 k2,
alloc_ceiling + 2 * ESTACK + DRAIN_FRAME <= dsp0 cx -> dsp0 cx <= 2 ^ 47 -> (dxj cx < 4)%nat ->
4096 <= dxSA cx -> dxSA cx + 56 <= alloc_ceiling ->
GSB B MT MMAX RG cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k2 ->
GSKEEP cx W1 m1 m2 ->
GSB B MT MMAX RG cx s1 D p q ly1 S1 W1 m2 md2 k2 e1 h1 out1 ev1 LB1 spent tl.
Proof.
intros cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2 k2 HLOW HTOP HJ4 HSA1 HSA2 HGS HJ2 HKP.
pose proof HKP as (KEEP & PRES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
unfold GSB, LCORE in HGS |- *.
destruct HGS as (HMEM & HLINK & HSAME & HHIST & HRS & HBUD).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR1 : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (KL : forall x, 0 <= x < alloc_ceiling -> aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x)
  by (intros x Hx; apply KEEP; lia).
assert (AK : forall fp, (forall r, In r fp -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling) ->
  akept W1 m1 W1 m2 fp) by (intros fp Hlow; exact (gs_akept_of W1 m1 m2 fp KL PRES Hlow)).
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (HBLK : forall b, In b (aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap
    (dvirt cx s1 false (dlH cx s1 p) (dlka cx s1 p) (GSno cx s1 p q) (GSoc cx s1 p q))) out1) ->
  In b (ablocks B ly1 S1)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact Hperm | right].
  apply in_or_app. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left; exact Hb|right].
  apply in_or_app. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left; exact Hb|right].
  apply in_or_app. left. exact Hb. }
split; [|split; [exact HLINK | split; [exact HSAME | split; [exact HHIST | split; [exact HRS | exact HBUD]]]]].
split; [exact HJ2|].
split.
{ intros x Hx. rewrite KL; [exact (Hrom x Hx)|].
  destruct Hx as (sg & Hsg & _ & Hr).
  pose proof (pa_img_range x ltac:(exists sg; split; [exact Hsg | exact Hr])). lia. }
split; [intros x Him Hno Her Hp; exact (PRES x (Hpres x Him Hno Her Hp))|].
split; [exact Hframes|].
split; [exact (gsl_frame_keep cx W1 m1 m2 ltac:(lia) HKP HFR)|].
split.
{ apply (gsl_garr8_kept W1 m1 W1 m2); [exact Hgarr|].
  intros x Hx. rewrite gsl_bzs_len in Hx. apply KL.
  assert (HL56 : length (entry_bytes e1) = 56%nat).
  { pose proof HOKX as (_ & _ & Hp1 & Hp2 & _). unfold entry_bytes.
    rewrite !length_app, Hp1, Hp2, !Mem.length_le8, !Mem.length_le4. reflexivity. }
  rewrite HL56 in Hx. unfold ATABLE, AENT in *. lia. }
split.
{ intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m2 _ (PRES _)). exact (Hawr i Hi). }
split.
{ eapply (gs_aentry_okx_kept B RG).
  - exact HOKX.
  - apply AK. exact (gsl_aentry_fp_low ly1 S1 W1 m1 md1 e1 HAR1 HOKX).
  - intros b Hb. apply HBLK. apply in_or_app. left. exact Hb. }
split.
{ eapply asrc_at_kept.
  - exact Hsrc.
  - apply AK. apply (gsl_asrc_fp_low ly1 S1 W1 m1 md1 (dHA RG cx) h1 HAR1 Hsrc);
      unfold dHA, ASRC in *; lia.
  - intros b Hb. apply HBLK. apply in_or_app. right. apply in_or_app. left. exact Hb. }
split.
{ pose proof HGSB as (Hg1 & Hg2 & _). unfold aothers_at in Hoth |- *.
  intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & Mf & Mo & Hfo).
  exists f, o. split; [|split; [|exact Hfo]];
  apply (gsl_vm_keep W1 m1 m2 _ 4%nat _); [| exact Mf | | exact Mo];
  intros x Hx; apply KL; apply (gsl_img_low x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia. }
split.
{ intros x Hx Hnx. destruct (Hgsk x Hx Hnx) as (Hv & Hw). split.
  - rewrite KL; [exact Hv|]. pose proof HGSB as (Hg1 & Hg2 & _).
    apply (gsl_img_low x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
  - intros Hwr. unfold arm. apply (writable_kept (w_H W1) m1 m2 _ (PRES _)). exact (Hw Hwr). }
split.
{ eapply aout_at_kept.
  - exact Hout.
  - apply AK. exact (gsl_aout_fp_low ly1 S1 W1 m1 md1 _ _ _ _ _ _ HAR1 Hout).
  - intros b Hb. apply HBLK. apply in_or_app. right. apply in_or_app. right. exact Hb. }
split; [exact Hlivout | exact Hperm].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (4) GSN (0x8386c): slot n was read and did not match; the loop's bottom is to come.  GSL's body with the
   pc of the bottom and the no-match clause over S n slots.
   --------------------------------------------------------------------------------------------------------- *)
Definition A_dr_hnext : Z := AF_fr_drain + 0x790.   (* 0x8386c = 0x830dc + 0x790 *)

(* the held keys the relay entry carries are the line loop's set *)
Lemma gsl_link_H : forall cx s1 sk H ka no oc e1 h1,
DLINK (dvirt cx s1 sk H ka no oc) e1 h1 -> drain_b_c.keys_texts (re_keys e1) = H.
Proof. intros cx s1 sk H ka no oc e1 h1 (_ & _ & _ & HH & _). unfold dvirt in HH. cbn [drain_b_c.ds_H] in HH. exact HH. Qed.

Lemma gsl_link_U : forall cx s1 sk H ka no oc e1 h1,
DLINK (dvirt cx s1 sk H ka no oc) e1 h1 -> bzs (re_U e1) = dW s1.
Proof. intros cx s1 sk H ka no oc e1 h1 (_ & HU & _). unfold dvirt in HU. cbn [drain_b_c.ds_u] in HU. exact HU. Qed.

Lemma gsl_div8_succ : forall hp n, (hp + 8 * Z.of_nat n) / 8 + 1 = (hp + 8 * Z.of_nat (S n)) / 8.
Proof.
intros hp n. rewrite Nat2Z.inj_succ.
replace (hp + 8 * Z.succ (Z.of_nat n)) with ((hp + 8 * Z.of_nat n) + 1 * 8) by lia.
rewrite Z.div_add by lia. reflexivity.
Qed.

(* The loop's cut body, shared by GSL (0x83838, no match below n) and GSN (0x8386c, no match below S n):
   GSL's conjunction after its pc clause, with the no-match bound nm as a parameter.  GSL unfolds to it at nm = n
   (gsl_GSL_intro / gsl_GSL_elim are conversions). *)
Definition GSBODY (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf nm : nat) (W1 : world SEGS)
(regs1 : bvmap 5 word) ly1 S1 (m1 : word -> option byte) md1 k1 e1 h1 out1 ev1 LB1 spent
(jb : nat) (a : drain_b_c.dadr) (o ha : RelayRunT.addr YO0i.sptr) (ks : list (RelayRunT.addr YO0i.sptr))
(tl : dtrace) (kd : gkind) (jj : nat) (bg : Z) : Prop :=
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 18 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 8 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 21 = w64 SHADOW_OFF /\
dr_frame RG cx W1 m1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 ((dxSA cx + 8) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 200) 8 (dxSA cx + 16) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 56) 8 (dxSA cx) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 48) 8 (dxSA cx + 24) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 64) 8 (dxSA cx + 32) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 8) 8 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 40) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 24) 8 (re_nheld e1) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 32) 8 (re_buf e1 + Z.of_nat p + Z.of_nat jj) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 40) 8 bg /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 72) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 80) 8 (re_hp e1) /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 19 = w64 ((re_hp e1 + 8 * Z.of_nat n) / 8 + SHADOW_OFF) /\
getr regs1 20 = w64 (8 * Z.of_nat n) /\
getr regs1 25 = w64 (8 * re_nheld e1) /\
getr regs1 27 = w64 (Z.of_nat jj) /\
(n + kf = length (re_keys e1))%nat /\ (0 < kf)%nat /\
(forall i, (i < nm)%nat -> nth i (dlH cx s1 p) [] <> firstn jj (dline s1 p q)) /\
0 <= bg < 2 ^ 64 /\ (bg = 0 <-> kd = GBegin) /\
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
GSF s1 p q /\
GSB B MT MMAX RG cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.

Definition GSN (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_hnext) regs1 m1 md1 /\
GSBODY cx s1 D p q n kf (S n) W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.

Lemma gsl_GSL_elim : forall cx s1 D p q n kf W1 c1,
GSL B MT MMAX RG cx s1 D p q n kf W1 c1 ->
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_hloop) regs1 m1 md1 /\
GSBODY cx s1 D p q n kf n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof. intros cx s1 D p q n kf W1 c1 H. exact H. Qed.

Lemma gsl_GSL_intro : forall cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg,
GSBODY cx s1 D p q n kf n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
GSL B MT MMAX RG cx s1 D p q n kf W1 (cfg_at SEGS (BASE + A_dr_hloop) regs1 m1 md1).
Proof.
intros cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg H.
exists regs1, ly1, S1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl, kd, jj, bg.
split; [reflexivity | exact H].
Qed.

(* the stack facts every walk of the loop uses, from DBASE and the table block *)
Lemma gsl_stack : forall cx, DBASE B MT MMAX RG cx ->
alloc_ceiling + 2 * ESTACK + DRAIN_FRAME <= dsp0 cx /\ dsp0 cx <= 2 ^ 47 /\ dsp0 cx mod 16 = 0 /\
(dxj cx < 4)%nat.
Proof.
intros cx HB.
pose proof HB as (Hafn & _ & _ & _ & _ & HBrest).
pose proof HBrest as (_ & _ & _ & Hj4 & _).
pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
fold (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK = 16848) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HDF : DRAIN_FRAME = 336) by reflexivity.
split; [lia|]. split; [lia|]. split; [exact Hal16 | exact Hj4].
Qed.

(* the relay entry's place, from DBASE and the core's table block *)
Lemma gsl_sa : forall cx ly1 S1 (W1 : world SEGS) m1 md1 k1 e1 h1 s out1 ev1 sent LB1,
DBASE B MT MMAX RG cx -> DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 ->
4096 <= dxSA cx /\ dxSA cx + 56 <= alloc_ceiling.
Proof.
intros cx ly1 S1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 HB HM.
pose proof HB as (_ & _ & _ & HSAlo & HSAhi & _).
pose proof HM as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HTB) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity). rewrite RQT in HGceil.
unfold ATABLE, AENT in *. lia.
Qed.

(* the body at the memory after a step of the loop that keeps every byte outside the interceptors' scratch *)
Lemma gsl_body_keep : forall cx s1 D p q n kf nm W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  m2 md2,
DBASE B MT MMAX RG cx ->
GSBODY cx s1 D p q n kf nm W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k1 ->
GSKEEP cx W1 m1 m2 ->
GSBODY cx s1 D p q n kf nm W1 regs1 ly1 S1 m2 md2 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof.
intros cx s1 D p q n kf nm W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg m2 md2
  HB HBD HJ2 HKP.
destruct (gsl_stack cx HB) as (HS1 & HS2 & _ & Hj4).
unfold GSBODY in HBD |- *.
destruct HBD as (Hsp & R3 & R4 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64
  & M8 & M16 & M24 & M32 & M40 & M72 & M80 & R23 & R24 & R19 & R20 & R25 & R27
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (HMEM & _).
destruct (gsl_sa cx _ _ _ _ _ _ _ _ _ _ _ _ _ HB HMEM) as (HSA1 & HSA2).
assert (HSPR : DRAIN_FRAME <= dsp0 cx <= 2 ^ 47) by (unfold ESTACK, DRAIN_FRAME in *; pose proof asan_consts as (C1 & _); lia).
do 7 (split; [assumption|]).
split; [exact (gsl_frame_keep cx W1 m1 m2 HSPR HKP HFR)|].
do 12 (split; [apply (gsl_fv_keep cx W1 m1 m2 _ _ HSPR); [lia | unfold DRAIN_FRAME; lia | exact HKP | assumption]|]).
do 14 (split; [assumption|]).
split; [|exact HFUT].
exact (gsl_core_kept cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2 k1
  HS1 HS2 Hj4 HSA1 HSA2 HCORE HJ2 HKP).
Qed.

(* the registers the body pins other than s3 / s4 *)
Definition GSREGS (regs1 regs2 : bvmap 5 word) : Prop :=
getr regs2 2 = getr regs1 2 /\ getr regs2 3 = getr regs1 3 /\ getr regs2 4 = getr regs1 4 /\
getr regs2 8 = getr regs1 8 /\ getr regs2 9 = getr regs1 9 /\ getr regs2 18 = getr regs1 18 /\
getr regs2 21 = getr regs1 21 /\ getr regs2 23 = getr regs1 23 /\ getr regs2 24 = getr regs1 24 /\
getr regs2 25 = getr regs1 25 /\ getr regs2 27 = getr regs1 27.

(* GSN from the head's body: the registers unchanged, slot n not matched *)
Lemma gsl_mk_gsn : forall cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY cx s1 D p q n kf n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
GSREGS regs1 regs2 -> getr regs2 19 = getr regs1 19 -> getr regs2 20 = getr regs1 20 ->
nth n (dlH cx s1 p) [] <> firstn jj (dline s1 p q) ->
GSBODY cx s1 D p q n kf (S n) W1 regs2 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof.
intros cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q21 & Q23 & Q24 & Q25 & Q27) Q19 Q20 Hn.
unfold GSBODY in HBD |- *.
destruct HBD as (Hsp & R3 & R4 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64
  & M8 & M16 & M24 & M32 & M40 & M72 & M80 & R23 & R24 & R19 & R20 & R25 & R27
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hgest & Hjjr & HGSF & HCORE & HFUT).
unfold spZ in *. rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q21, Q23, Q24, Q25, Q27, Q19, Q20.
do 28 (split; [assumption|]).
split; [intros i Hi; destruct (Nat.eq_dec i n) as [->|Hne]; [exact Hn | apply Hnm; lia]|].
do 6 (split; [assumption|]). exact HFUT.
Qed.

(* the loop's head at S n from GSN at n, s3 and s4 stepped *)
Lemma gsl_mk_loop : forall cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY cx s1 D p q n (S kf) (S n) W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
(0 < kf)%nat ->
GSREGS regs1 regs2 ->
getr regs2 19 = Z_to_bv 64 (bv_unsigned (getr regs1 19) + 1) ->
getr regs2 20 = Z_to_bv 64 (bv_unsigned (getr regs1 20) + 8) ->
GSBODY cx s1 D p q (S n) kf (S n) W1 regs2 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof.
intros cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD Hkf0 (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q21 & Q23 & Q24 & Q25 & Q27) Q19 Q20.
unfold GSBODY in HBD |- *.
destruct HBD as (Hsp & R3 & R4 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64
  & M8 & M16 & M24 & M32 & M40 & M72 & M80 & R23 & R24 & R19 & R20 & R25 & R27
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (HMEM & _).
pose proof HMEM as (HJ & _ & _ & _ & _ & _ & _ & HOKX & _).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HOKX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hnheld & Hheld & _).
assert (HHPR : 0 <= re_hp e1 < 2 ^ 47).
{ pose proof asan_consts as (C1 & _).
  destruct Hheld as [(Hz & _)|(Hz & Hin & Hk1 & Hk2 & _)]; [lia|].
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_hp e1) (re_kh e1) HAR Hin) as (_ & H4 & Hc & _).
  pose proof (req_size_pos (re_kh e1) ltac:(lia)) as (Hr1 & Hr2). lia. }
unfold spZ in *. rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q21, Q23, Q24, Q25, Q27, Q19, Q20, R19, R20.
unfold re_nheld in Hnheld.
do 22 (split; [assumption|]).
split.
{ assert (Hd : 0 <= (re_hp e1 + 8 * Z.of_nat n) / 8 <= re_hp e1 + 8 * Z.of_nat n)
    by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
  f_equal. rewrite <- gsl_div8_succ. lia. }
split; [unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
do 2 (split; [assumption|]).
split; [lia|]. split; [exact Hkf0|].
do 7 (split; [assumption|]). exact HFUT.
Qed.

(* GA from GSN at the last slot: the spilled registers back *)
Lemma gsl_mk_ga : forall cx s1 D p q n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY cx s1 D p q n 1 (S n) W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 21 = getr regs1 21 -> getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 ->
getr regs2 22 = w64 (dxSA cx) -> getr regs2 27 = w64 (dxSA cx + 24) ->
getr regs2 25 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj) -> getr regs2 19 = w64 bg ->
getr regs2 10 = w64 (re_nheld e1) -> getr regs2 11 = w64 (re_nheld e1) ->
getr regs2 12 = w64 ((dxSA cx + 40) / 8) ->
GA B MT MMAX RG cx s1 D p q W1 (cfg_at SEGS (BASE + A_dr_add) regs2 m1 md1).
Proof.
intros cx s1 D p q n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD Q2 Q3 Q4 Q8 Q9 Q18 Q21 Q23 Q24 Q22 Q27 Q25 Q19 Q10 Q11 Q12.
unfold GSBODY in HBD.
destruct HBD as (Hsp & R3 & R4 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64
  & M8 & M16 & M24 & M32 & M40 & M72 & M80 & R23 & R24 & R19 & R20 & R25 & R27
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hgest & Hjjr & HGSF & HCORE & HFUT).
exists regs2, ly1, S1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl, kd, jj, bg.
split; [reflexivity|].
split.
{ unfold dregs_line, spZ in *. rewrite Q2, Q3, Q4, Q18, Q9, Q8, Q21, Q22, Q27.
  do 9 (split; [first [assumption | reflexivity]|]). split; [exact HFR|]. do 4 (split; [assumption|]). exact M64. }
rewrite Q23, Q24.
do 12 (split; [assumption|]).
split.
{ apply gs_index_none. intros i Hi. apply Hnm.
  pose proof HCORE as (_ & HLINK & _).
  rewrite <- (gsl_link_H _ _ _ _ _ _ _ _ _ HLINK), gs_keys_texts_len in Hi. lia. }
split; [exact HGSF|]. split; [exact HCORE | exact HFUT].
Qed.

(* the held key at slot n, as the line loop's set names it *)
Lemma gsl_nth_H : forall cx s1 sk H ka no oc e1 h1 n,
DLINK (dvirt cx s1 sk H ka no oc) e1 h1 -> (n < length (re_keys e1))%nat ->
nth n H [] = bzs (key_text (nth n (re_keys e1) (0, [], []))).
Proof.
intros cx s1 sk H ka no oc e1 h1 n HL Hn. rewrite <- (gsl_link_H _ _ _ _ _ _ _ _ _ HL). apply gs_keys_texts_nth. exact Hn.
Qed.

(* the line's bytes at s->buf + p *)
Lemma gsl_line_garr8 : forall (W : world SEGS) m s1 p q e1,
garr8 SEGS (arm W m) (re_buf e1) (bzs (re_U e1 ++ re_junk e1)) -> bzs (re_U e1) = dW s1 ->
(p <= q < length (dW s1))%nat ->
garr8 SEGS (arm W m) (re_buf e1 + Z.of_nat p) (dline s1 p q).
Proof.
intros W m s1 p q e1 Hg HU Hpq.
assert (E : dline s1 p q = firstn (q - p) (skipn p (bzs (re_U e1 ++ re_junk e1)))).
{ unfold dline. rewrite gsl_bzs_app, HU, skipn_app, firstn_app.
  replace (p - length (dW s1))%nat with 0%nat by lia.
  rewrite length_skipn. replace (q - p - (length (dW s1) - p))%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r. reflexivity. }
rewrite E. apply gsl_garr8_sub; [exact Hg|].
rewrite gsl_bzs_len, length_app. rewrite <- gsl_bzs_len, HU. lia.
Qed.

Lemma gsl_dline_nth_nz : forall s1 p q, (p <= q < length (dW s1))%nat ->
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) ->
forall i, (i < q - p)%nat -> nth i (dline s1 p q) 0 <> 0.
Proof.
intros s1 p q Hpq Hnz i Hi E. unfold dline in E.
rewrite nth_firstn, (proj2 (Nat.ltb_lt i (q - p)) Hi), nth_skipn in E.
apply (Hnz (p + i)%nat); [lia|]. rewrite (nth_error_nth' (dW s1) 0) by lia. rewrite E. reflexivity.
Qed.

(* GSN from the head's body at a later memory: slot n not matched *)
Lemma gsl_exit_gsn : forall cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2 m2 md2,
DBASE B MT MMAX RG cx ->
GSBODY cx s1 D p q n kf n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k1 ->
GSKEEP cx W1 m1 m2 ->
GSREGS regs1 regs2 -> getr regs2 19 = getr regs1 19 -> getr regs2 20 = getr regs1 20 ->
nth n (dlH cx s1 p) [] <> firstn jj (dline s1 p q) ->
GSN cx s1 D p q n kf W1 (cfg_at SEGS (BASE + A_dr_hnext) regs2 m2 md2).
Proof.
intros cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2 m2 md2
  HB HBD HJ HKP HR Q19 Q20 Hn.
exists regs2, ly1, S1, m2, md2, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl, kd, jj, bg.
split; [reflexivity|].
apply (gsl_mk_gsn cx s1 D p q n kf W1 regs1 ly1 S1 m2 md2 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2);
  [| exact HR | exact Q19 | exact Q20 | exact Hn].
exact (gsl_body_keep cx s1 D p q n kf n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  m2 md2 HB HBD HJ HKP).
Qed.

(* a BEGIN whose key is held at slot n: DLN (S q), the registers s6 / s11 back *)
Lemma gsl_mk_dln : forall cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY cx s1 D p q n kf n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q) -> bg = 0 ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 21 = getr regs1 21 -> getr regs2 23 = getr regs1 23 ->
getr regs2 22 = w64 (dxSA cx) -> getr regs2 27 = w64 (dxSA cx + 24) ->
DLN B MT MMAX RG cx s1 D (S q) W1 (cfg_at SEGS (BASE + A_dr_next) regs2 m1 md1).
Proof.
intros cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD Hmt Hbg0 Q2 Q3 Q4 Q8 Q9 Q18 Q21 Q23 Q22 Q27.
unfold GSBODY in HBD.
destruct HBD as (Hsp & R3 & R4 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64
  & M8 & M16 & M24 & M32 & M40 & M72 & M80 & R23 & R24 & R19 & R20 & R25 & R27
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (_ & HLINK & _).
assert (Hkd : kd = GBegin) by (apply Hbgk; exact Hbg0). subst kd.
assert (Hlen : (n < length (dlH cx s1 p))%nat)
  by (rewrite <- (gsl_link_H _ _ _ _ _ _ _ _ _ HLINK), gs_keys_texts_len; lia).
pose proof (gs_index_some _ _ n Hlen Hmt Hnm) as HI.
destruct (gs_seen_begin_old (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) _ n jb ha ks Hgest HI) as (S1e & S2e & S3e).
pose proof HGSF as (Hbd & Hpq & Hq0 & _).
exists regs2, ly1, S1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
split; [reflexivity|].
split.
{ unfold dregs_line, spZ in *. rewrite Q2, Q3, Q4, Q18, Q9, Q8, Q21, Q22, Q27.
  do 9 (split; [first [assumption | reflexivity]|]). split; [exact HFR|]. do 4 (split; [assumption|]). exact M64. }
split; [rewrite Q23, R23; unfold w64; f_equal; lia|].
split; [unfold dbound; split; [lia|right]; replace (S q - 1)%nat with q by lia; exact Hq0|].
split; [lia|].
split; [exact (gsl_dlc_same B MT MMAX RG cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl HGSF S1e S3e HCORE)|].
exact (gsl_dlfut_same cx s1 p q a jb o ha ks tl HGSF S2e S1e S3e HFUT).
Qed.

(* an END whose key is held at slot n: GF *)
Lemma gsl_mk_gf : forall cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY cx s1 D p q n kf n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q) -> bg <> 0 ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 21 = getr regs1 21 -> getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 ->
getr regs2 19 = getr regs1 19 -> getr regs2 20 = getr regs1 20 ->
getr regs2 22 = w64 (dxSA cx) -> getr regs2 27 = w64 (dxSA cx + 24) ->
getr regs2 26 = w64 (re_hp e1 + 8 * Z.of_nat n) ->
GF B MT MMAX RG cx s1 D p q W1 (cfg_at SEGS (BASE + A_dr_free) regs2 m1 md1).
Proof.
intros cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD Hmt Hbg0 Q2 Q3 Q4 Q8 Q9 Q18 Q21 Q23 Q24 Q19 Q20 Q22 Q27 Q26.
unfold GSBODY in HBD.
destruct HBD as (Hsp & R3 & R4 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64
  & M8 & M16 & M24 & M32 & M40 & M72 & M80 & R23 & R24 & R19 & R20 & R25 & R27
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (_ & HLINK & _).
assert (Hkd : kd = GEnd) by (destruct kd; [exfalso; apply Hbg0; apply Hbgk; reflexivity | reflexivity]). subst kd.
assert (Hlen : (n < length (dlH cx s1 p))%nat)
  by (rewrite <- (gsl_link_H _ _ _ _ _ _ _ _ _ HLINK), gs_keys_texts_len; lia).
pose proof (gs_index_some _ _ n Hlen Hmt Hnm) as HI.
exists regs2, ly1, S1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl, jj, n.
split; [reflexivity|].
split.
{ unfold dregs_line, spZ in *. rewrite Q2, Q3, Q4, Q18, Q9, Q8, Q21, Q22, Q27.
  do 9 (split; [first [assumption | reflexivity]|]). split; [exact HFR|]. do 4 (split; [assumption|]). exact M64. }
rewrite Q23, Q24, Q19, Q20, Q26.
do 7 (split; [first [assumption | reflexivity]|]).
split; [lia|].
do 4 (split; [assumption|]).
split; [exact HCORE | exact HFUT].
Qed.

(* ---- The symbolic state at GSN (0x8386c). ----
   Atoms beyond the 32 registers: 32 = SA, 33 = (&s->held) >> 3, 34 = s->nheld, 35 = s->buf + p + jj, 36 = bg, the
   values of the spill slots 16(sp) .. 56(sp) the bottom's exit edge reloads.  No region has a write window. *)
Definition gn_frame : YP09.region := YP09.mkRegion (Some 2%nat) 16 64 16 16
  [ YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0));
    YP09.mkChunk 32 (CVal 8 (SOff 35 0)); YP09.mkChunk 40 (CVal 8 (SOff 36 0));
    YP09.mkChunk 48 (CVal 8 (SOff 32 24)); YP09.mkChunk 56 (CVal 8 (SOff 32 0)) ].
Definition gn_regions : smem := [ gn_frame ].
Definition gn_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) ] [] [].
Definition ss_gn : sstate := mkSS A_dr_hnext sr_atoms gn_regions None gn_facts.
Definition gn_Bx : sv := SOff 21 0.
Definition gn_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gn_extra (SA S40 NH LJ BG : Z) : list word := map (Z_to_bv 64) [SA; S40; NH; LJ; BG].

Lemma gn_entry : forall (W : world SEGS) regs1 m1 sp SA S40 NH LJ BG,
spZ regs1 = sp -> 2 ^ 46 <= sp -> sp + DRAIN_FRAME <= 2 ^ 47 -> sp mod 16 = 0 ->
0 <= SA -> SA + 24 < 2 ^ 64 -> 0 <= S40 < 2 ^ 64 -> 0 <= NH < 2 ^ 64 -> 0 <= LJ < 2 ^ 64 -> 0 <= BG < 2 ^ 64 ->
val_mem SEGS (arm W m1) (sp + 16) 8 S40 ->
val_mem SEGS (arm W m1) (sp + 24) 8 NH ->
val_mem SEGS (arm W m1) (sp + 32) 8 LJ ->
val_mem SEGS (arm W m1) (sp + 40) 8 BG ->
val_mem SEGS (arm W m1) (sp + 48) 8 (SA + 24) ->
val_mem SEGS (arm W m1) (sp + 56) 8 SA ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (gn_extra SA S40 NH LJ BG))) ss_gn
(restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_hnext)) m1 (seg_rom SEGS))).
Proof.
intros W regs1 m1 sp SA S40 NH LJ BG Hsp Hlo Hhi Hal HSA1 HSA2 HS40 HNH HLJ HBG M16 M24 M32 M40 M48 M56.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (gn_extra SA S40 NH LJ BG))).
assert (E2 : ew E 2 = getr regs1 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 S40) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 NH) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 LJ) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 BG) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
unfold DRAIN_FRAME in Hhi.
unfold ss_gn. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold gn_regions, gn_frame.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ sp 16 8 (SOff 33 0) S40);
      [rewrite (den_atom0 E 33%nat S40 E33) by lia; reflexivity | cbn; lia | cbn; lia | exact M16].
  + apply (chunk_ok_val SEGS E _ sp 24 8 (SOff 34 0) NH);
      [rewrite (den_atom0 E 34%nat NH E34) by lia; reflexivity | cbn; lia | cbn; lia | exact M24].
  + apply (chunk_ok_val SEGS E _ sp 32 8 (SOff 35 0) LJ);
      [rewrite (den_atom0 E 35%nat LJ E35) by lia; reflexivity | cbn; lia | cbn; lia | exact M32].
  + apply (chunk_ok_val SEGS E _ sp 40 8 (SOff 36 0) BG);
      [rewrite (den_atom0 E 36%nat BG E36) by lia; reflexivity | cbn; lia | cbn; lia | exact M40].
  + apply (chunk_ok_val SEGS E _ sp 48 8 (SOff 32 24) (SA + 24));
      [rewrite (den_atom E 32%nat SA 24 E32) by lia; reflexivity | cbn; lia | cbn; lia | exact M48].
  + apply (chunk_ok_val SEGS E _ sp 56 8 (SOff 32 0) SA);
      [rewrite (den_atom0 E 32%nat SA E32) by lia; reflexivity | cbn; lia | cbn; lia | exact M56].
- cbn [pairwise_disjoint gn_regions all_disjoint]. split; exact I.
- split; [|split; [exact I | exact I]].
  cbn [gn_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16.
  repeat match goal with |- _ /\ _ => split end; (exact I || lia).
Qed.

(* a run whose regions have no write window writes nothing (W_drain_next.v dn_frame_nil, for any such regions) *)
Lemma gsl_frame_nil : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hn a Ha. apply (aview_kept_out E rs H m m' HF a Ha).
intros (r & Hin & Hr). rewrite forallb_forall in Hn. specialize (Hn r Hin). apply Z.leb_le in Hn. lia.
Qed.


(* ---- The loop's bottom: GSN n (S kf) -> GSL (S n) kf when a slot is left, GA when none is. ---- *)
Lemma gsl_tail : forall cx s1 D p q n kf W1 c1,
DBASE B MT MMAX RG cx -> GSN cx s1 D p q n (S kf) W1 c1 ->
(forall W2 c2, GA B MT MMAX RG cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
((0 < kf)%nat -> forall c2, GSL B MT MMAX RG cx s1 D p q (S n) kf W1 c2 -> SRr SEGS W1 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).
Proof.
intros cx s1 D p q n kf W1 c1 HB HGN HGA HGL.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HGN as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & oo & ha & ks & tl
  & kd & jj & bg & Hcfg & HBD).
destruct (gsl_stack cx HB) as (HSTK1 & HSTK2 & Hal16 & Hj4).
pose proof HBD as (Hsp & R3 & R4 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64
  & M8 & M16 & M24 & M32 & M40 & M72 & M80 & R23 & R24 & R19 & R20 & R25 & R27
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (HMEM & HLINK & _).
pose proof HMEM as (HJ & _ & _ & _ & _ & _ & _ & HOKX & _).
destruct (gsl_sa cx _ _ _ _ _ _ _ _ _ _ _ _ _ HB HMEM) as (HSA1 & HSA2).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HOKX as (_ & _ & _ & _ & _ & _ & HUlen & Husedr & Hbufc & Hnheld & _).
pose proof (gsl_link_U _ _ _ _ _ _ _ _ _ HLINK) as HUW.
assert (HUL : re_used e1 = Z.of_nat (length (dW s1))) by (rewrite <- HUW, gsl_bzs_len; lia).
pose proof HGSF as (_ & Hpq & _).
assert (HLJ : 0 <= re_buf e1 + Z.of_nat p + Z.of_nat jj < 2 ^ 64).
{ destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & _)]; [lia|].
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hbin) as (_ & HB4096 & HBceil & _).
  assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
  rewrite RQC in HBceil. lia. }
assert (HNHR : 0 <= re_nheld e1 < 2 ^ 26) by (split; [unfold re_nheld; lia | exact Hnheld]).
assert (HS40 : 0 <= (dxSA cx + 40) / 8 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (gn_entry W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) ((dxSA cx + 40) / 8) (re_nheld e1)
  (re_buf e1 + Z.of_nat p + Z.of_nat jj) bg Hsp ltac:(unfold ESTACK, DRAIN_FRAME in *; lia)
  ltac:(unfold DRAIN_FRAME in *; lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)
  ltac:(lia) ltac:(lia) HS40 ltac:(lia) HLJ Hbgr M16 M24 M32 M40 M48 M56) as HS.
remember (Eimg (Ereg regs1 (gn_extra (dxSA cx) ((dxSA cx + 40) / 8) (re_nheld e1)
  (re_buf e1 + Z.of_nat p + Z.of_nat jj) bg))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n0 r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 ((dxSA cx + 40) / 8)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_nheld e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (re_buf e1 + Z.of_nat p + Z.of_nat jj)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 bg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E20 : ew E 20 = Z_to_bv 64 (8 * Z.of_nat n)) by (rewrite (EREG 20%nat 20%bv ltac:(lia) eq_refl), R20; reflexivity).
assert (E25 : ew E 25 = Z_to_bv 64 (8 * re_nheld e1)) by (rewrite (EREG 25%nat 25%bv ltac:(lia) eq_refl), R25; reflexivity).
assert (SHOK : sh_ok SEGS gn_Bx [] E (mrestrict (w_H W1) m1)) by constructor.
clear HE.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_hnext)) with (Z_to_bv 64 (BASE + A_dr_hnext)).
paj_run_tok RUN HS HJ SHOK gn_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
match goal with Hg : mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ms)) |- _ => rename Hg into GR1 end.
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ms)) |- _ => rename Hf into HFr1 end.
assert (Hn8 : 0 <= 8 * Z.of_nat n + 8 < 2 ^ 64) by (unfold re_nheld in HNHR; lia).
assert (Hh8 : 0 <= 8 * re_nheld e1 < 2 ^ 64) by lia.
psrr_branch_tok RUN BR HS SHOK gn_Bspan.
- (* a slot is left (8 nheld <> 8 (n + 1)): back to the loop's head at S n *)
  rewrite branch_ne_U, (U_atom E 25 (8 * re_nheld e1) E25 Hh8), (U_atom_off E 20 (8 * Z.of_nat n) 8 E20 ltac:(lia) Hn8) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hkf0 : (0 < kf)%nat) by (clear - Hc Hnk; unfold re_nheld in Hc; lia).
  paj_run_to_tok RUNTO HS HJ SHOK gn_Bspan A_dr_hloop. { apply awr_ok_x_of0. awr_ok_tac. }
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem ms)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hf into HFrF end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem ms)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hg into GRF end.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  prreg HS (27%bv : bv 5) P27.
  repeat rewrite wvb_collapse in HJ.
  match goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
  assert (HKP : GSKEEP cx W1 m1 (ms_mem msF)).
  { split.
    - intros y Hy _. rewrite (gsl_frame_nil _ _ _ _ _ HFrF ltac:(vm_compute; reflexivity) y Hy).
      exact (gsl_frame_nil _ _ _ _ _ HFr1 ltac:(vm_compute; reflexivity) y Hy).
    - intros y Hp. exact (apresent_grows _ _ _ y GRF (apresent_grows _ _ _ y GR1 Hp)). }
  clear HS SHOK HFrF HFr1.
  assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew E k -> Nat.ltb k 32 = true ->
    Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
  { intros r k Hr Hk Hkr. rewrite Hr. apply EREG; [apply Nat.ltb_lt; exact Hk | exact Hkr]. }
  apply (HGL Hkf0).
  apply (gsl_GSL_intro cx s1 D p q (S n) kf W1 (ms_regs msF) ly1 S1 (ms_mem msF) mdF k1 e1 h1 out1 ev1 LB1 spent jb aa oo
    ha ks tl kd jj bg).
  apply (gsl_mk_loop cx s1 D p q n kf W1 regs1 ly1 S1 (ms_mem msF) mdF k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg
    (ms_regs msF)).
  + exact (gsl_body_keep cx s1 D p q n (S kf) (S n) W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl
      kd jj bg (ms_mem msF) mdF HB HBD HJ HKP).
  + exact Hkf0.
  + split; [exact (RK _ 2%nat P2 eq_refl eq_refl)|]. split; [exact (RK _ 3%nat P3 eq_refl eq_refl)|].
    split; [exact (RK _ 4%nat P4 eq_refl eq_refl)|]. split; [exact (RK _ 8%nat P8 eq_refl eq_refl)|].
    split; [exact (RK _ 9%nat P9 eq_refl eq_refl)|]. split; [exact (RK _ 18%nat P18 eq_refl eq_refl)|].
    split; [exact (RK _ 21%nat P21 eq_refl eq_refl)|]. split; [exact (RK _ 23%nat P23 eq_refl eq_refl)|].
    split; [exact (RK _ 24%nat P24 eq_refl eq_refl)|]. split; [exact (RK _ 25%nat P25 eq_refl eq_refl)|].
    exact (RK _ 27%nat P27 eq_refl eq_refl).
  + rewrite P19, (EREG 19%nat 19%bv (proj1 (Nat.ltb_lt 19 32) eq_refl) eq_refl). reflexivity.
  + rewrite P20, (EREG 20%nat 20%bv (proj1 (Nat.ltb_lt 20 32) eq_refl) eq_refl). reflexivity.
- (* no slot is left (8 nheld = 8 (n + 1)): the registers back, on to GA *)
  rewrite branch_ne_U, (U_atom E 25 (8 * re_nheld e1) E25 Hh8), (U_atom_off E 20 (8 * Z.of_nat n) 8 E20 ltac:(lia) Hn8) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hkf0 : kf = 0%nat) by (clear - Hc Hnk; unfold re_nheld in Hc; lia). subst kf.
  paj_run_to_tok RUNTO HS HJ SHOK gn_Bspan A_dr_add. { apply awr_ok_x_of0. awr_ok_tac. }
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem ms)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hf into HFrF end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem ms)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hg into GRF end.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
  prreg HS (25%bv : bv 5) P25. prreg HS (27%bv : bv 5) P27.
  prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
  repeat rewrite wvb_collapse in HJ.
  match goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
  assert (HKP : GSKEEP cx W1 m1 (ms_mem msF)).
  { split.
    - intros y Hy _. rewrite (gsl_frame_nil _ _ _ _ _ HFrF ltac:(vm_compute; reflexivity) y Hy).
      exact (gsl_frame_nil _ _ _ _ _ HFr1 ltac:(vm_compute; reflexivity) y Hy).
    - intros y Hp. exact (apresent_grows _ _ _ y GRF (apresent_grows _ _ _ y GR1 Hp)). }
  clear HS SHOK HFrF HFr1.
  assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew E k -> Nat.ltb k 32 = true ->
    Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
  { intros r k Hr Hk Hkr. rewrite Hr. apply EREG; [apply Nat.ltb_lt; exact Hk | exact Hkr]. }
  apply HGA.
  apply (gsl_mk_ga cx s1 D p q n W1 regs1 ly1 S1 (ms_mem msF) mdF k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg
    (ms_regs msF)
    (gsl_body_keep cx s1 D p q n 1 (S n) W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl
      kd jj bg (ms_mem msF) mdF HB HBD HJ HKP)
    (RK _ 2%nat P2 eq_refl eq_refl) (RK _ 3%nat P3 eq_refl eq_refl) (RK _ 4%nat P4 eq_refl eq_refl)
    (RK _ 8%nat P8 eq_refl eq_refl) (RK _ 9%nat P9 eq_refl eq_refl) (RK _ 18%nat P18 eq_refl eq_refl)
    (RK _ 21%nat P21 eq_refl eq_refl) (RK _ 23%nat P23 eq_refl eq_refl) (RK _ 24%nat P24 eq_refl eq_refl)).
  + rewrite P22, E32. reflexivity.
  + rewrite P27, E32, unsigned_lit_small by (clear - HSA1 HSA2 C1; lia). reflexivity.
  + rewrite P25, E35. reflexivity.
  + rewrite P19, E36. reflexivity.
  + rewrite P10, E34. reflexivity.
  + rewrite P11, E34. reflexivity.
  + rewrite P12, E33. reflexivity.
Qed.

(* ---- The symbolic state at GSL (0x83838). ----
   Atoms beyond the 32 registers: 32 = s->held (hp), 33 = &s->held[n] (hp + 8 n), 34 = s->held[n] (the key's
   address), 35 = SA, 36 = bg.  Register 19 (s3) carries the shadow EXPRESSION of atom 33, so that the shadow
   check at 0x83838 is in the engine's own form and the shadow entry gl_SH over the slot decides it; the alias
   names hp + 8 n, which the walk builds out of 80(sp) and s4, as atom 33 (W_gsfree_scratch.v's form).  The frame
   region holds the four spill slots the body reads (40, 48, 56, 80); no region has a write window. *)
Definition GL_PHI : Z := 140737479966720.   (* the literal bound of ASAN_CEIL; never the abstract one *)
Definition gl_shE (m : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff m 0) (SLit 3)) (SOff 21 0).
Definition gl_frame : YP09.region := YP09.mkRegion (Some 2%nat) 40 88 40 40
  [ YP09.mkChunk 40 (CVal 8 (SOff 36 0)); YP09.mkChunk 48 (CVal 8 (SOff 35 24));
    YP09.mkChunk 56 (CVal 8 (SOff 35 0)); YP09.mkChunk 80 (CVal 8 (SOff 32 0)) ].
Definition gl_slot : YP09.region := YP09.mkRegion (Some 33%nat) 0 8 0 0
  [ YP09.mkChunk 0 (CVal 8 (SOff 34 0)) ].
Definition gl_regions : smem := [ gl_frame; gl_slot ].
Definition gl_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (21%nat, mkAF SB SB 0);
          (32%nat, mkAF 4096 GL_PHI 3); (33%nat, mkAF 4096 GL_PHI 3); (20%nat, mkAF 0 (2 ^ 29) 3);
          (34%nat, mkAF 4096 GL_PHI 0); (35%nat, mkAF 4096 GL_PHI 0) ] []
  [ (SAlu ALU_ADD (SOff 32 0) (SOff 20 0), SOff 33 0) ].
Definition gl_regs : list sv := sr_set sr_atoms 19%bv (gl_shE 33).
Definition ss_gl : sstate := mkSS A_dr_hloop gl_regs gl_regions None gl_facts.
Definition gl_Bx : sv := SOff 21 0.
Definition gl_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gl_SH : list shent := [ mkSHE 33 0 8 ].
Definition gl_extra (HP SL KP SA BG : Z) : list word := map (Z_to_bv 64) [HP; SL; KP; SA; BG].

Lemma gl_U_shadow : forall E n v, ew E n = Z_to_bv 64 v -> ew E 21 = Z_to_bv 64 SHADOW_OFF -> 0 <= v < 2 ^ 47 ->
U E (gl_shE n) = v / 8 + SHADOW_OFF.
Proof.
intros E n v Hn H21 Hv. unfold gl_shE. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_srl3, (U_atom E n v Hn) by lia. rewrite (U_atom E 21 SHADOW_OFF H21) by (unfold SHADOW_OFF; lia).
assert (Hd : 0 <= v / 8 <= v) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

Lemma gl_entry : forall (W : world SEGS) regs1 m1 sp HP n KP SA BG,
spZ regs1 = sp -> 2 ^ 46 <= sp -> sp + DRAIN_FRAME <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs1 21 = w64 SHADOW_OFF ->
getr regs1 20 = w64 (8 * Z.of_nat n) -> 8 * Z.of_nat n < 2 ^ 29 ->
getr regs1 19 = w64 ((HP + 8 * Z.of_nat n) / 8 + SHADOW_OFF) ->
4096 <= HP -> HP mod 8 = 0 -> HP + 8 * Z.of_nat n + 8 <= GL_PHI -> HP + 8 * Z.of_nat n + 8 <= sp ->
4096 <= KP <= GL_PHI -> 4096 <= SA -> SA + 24 <= GL_PHI -> 0 <= BG < 2 ^ 64 ->
val_mem SEGS (arm W m1) (sp + 40) 8 BG ->
val_mem SEGS (arm W m1) (sp + 48) 8 (SA + 24) ->
val_mem SEGS (arm W m1) (sp + 56) 8 SA ->
val_mem SEGS (arm W m1) (sp + 80) 8 HP ->
val_mem SEGS (arm W m1) (HP + 8 * Z.of_nat n) 8 KP ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (gl_extra HP (HP + 8 * Z.of_nat n) KP SA BG))) ss_gl
(restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_hloop)) m1 (seg_rom SEGS))).
Proof.
intros W regs1 m1 sp HP n KP SA BG Hsp Hlo Hhi Hal R21 R20 Hn8 R19 HHP1 HHP8 HHP2 HHP3 HKP HSA1 HSA2 HBG
  M40 M48 M56 M80 MSL.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (gl_extra HP (HP + 8 * Z.of_nat n) KP SA BG))).
assert (EREG : forall k (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r).
{ intros k r Hk Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E20 : ew E 20 = Z_to_bv 64 (8 * Z.of_nat n)) by (rewrite (EREG 20%nat 20%bv ltac:(lia) eq_refl); exact R20).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EREG 21%nat 21%bv ltac:(lia) eq_refl); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 HP) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (HP + 8 * Z.of_nat n)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 KP) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 BG) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (Usl : bv_unsigned (ew E 33) = HP + 8 * Z.of_nat n) by (rewrite E33; apply unsigned_lit_small; unfold GL_PHI in *; lia).
unfold GL_PHI in *. unfold DRAIN_FRAME in Hhi.
unfold ss_gl. apply pa_entry_st_ok_full.
- unfold gl_regs. apply regs_ok_pin;
    [ | intros X; discriminate X | ].
  + subst E. apply regs_ok_Eimg_Ereg.
  + rewrite denot_lit_U, (gl_U_shadow E 33 (HP + 8 * Z.of_nat n) E33 E21) by lia. exact R19.
- vm_compute. reflexivity.
- unfold gl_regions, gl_frame, gl_slot.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?Usp, ?Usl.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp 40 8 (SOff 36 0) BG);
        [rewrite (den_atom0 E 36%nat BG E36) by lia; reflexivity | cbn; lia | cbn; lia | exact M40].
    * apply (chunk_ok_val SEGS E _ sp 48 8 (SOff 35 24) (SA + 24));
        [rewrite (den_atom E 35%nat SA 24 E35) by lia; reflexivity | cbn; lia | cbn; lia | exact M48].
    * apply (chunk_ok_val SEGS E _ sp 56 8 (SOff 35 0) SA);
        [rewrite (den_atom0 E 35%nat SA E35) by lia; reflexivity | cbn; lia | cbn; lia | exact M56].
    * apply (chunk_ok_val SEGS E _ sp 80 8 (SOff 32 0) HP);
        [rewrite (den_atom0 E 32%nat HP E32) by lia; reflexivity | cbn; lia | cbn; lia | exact M80].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (HP + 8 * Z.of_nat n) 0 8 (SOff 34 0) KP);
      [rewrite (den_atom0 E 34%nat KP E34) by lia; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact MSL].
- apply pairwise_disjoint_of_extents.
  unfold gl_regions, gl_frame, gl_slot, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Usl.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [gl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Usl, E21, E32, E34, E35, E20, !unsigned_lit_small by (unfold SB, SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (A2 : (8 * Z.of_nat n) mod 8 = 0) by (rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity).
    assert (A1 : (HP + 8 * Z.of_nat n) mod 8 = 0) by (rewrite Z.add_mod, HHP8, A2 by lia; reflexivity).
    unfold SB, SHADOW_OFF, GL_PHI. repeat match goal with |- _ /\ _ => split end; (exact I || assumption || lia).
  + cbn [gl_facts f_alias alias_ok]. split; [|exact I].
    rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 32 HP E32), (U_atom E 20 (8 * Z.of_nat n) E20), (U_atom E 33 (HP + 8 * Z.of_nat n) E33) by lia.
    apply zcanon_id. unfold M64. lia.
Qed.

(* ---- The loop's body: GSL n (S kf) -> GSN n (S kf) (no match at slot n), DLN (S q) (a begin held at slot n)
   or GF (an end held at slot n). ---- *)
Lemma gsl_body : forall cx s1 D p q n kf W1 c1,
DBASE B MT MMAX RG cx -> GSL B MT MMAX RG cx s1 D p q n (S kf) W1 c1 ->
(forall W2 c2, DLN B MT MMAX RG cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, GF B MT MMAX RG cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall c2, GSN cx s1 D p q n (S kf) W1 c2 -> SRr SEGS W1 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).
Proof.
intros cx s1 D p q n kf W1 c1 HB HGL HDLN HGF HGN.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@ASAN_CEIL_range rc) as (HAC & _). unfold ASAN_CEIL in HAC.
destruct (gsl_GSL_elim _ _ _ _ _ _ _ _ _ HGL) as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1
  & spent & jb & aa & oo & ha & ks & tl & kd & jj & bg & Hcfg & HBD).
clear HGL.
destruct (gsl_stack cx HB) as (HSTK1 & HSTK2 & Hal16 & Hj4).
pose proof HBD as (Hsp & R3 & R4 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64
  & M8 & M16 & M24 & M32 & M40 & M72 & M80 & R23 & R24 & R19 & R20 & R25 & R27
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (HMEM & HLINK & _).
pose proof HMEM as (HJ & Hrom & _ & _ & _ & _ & _ & HOKX & _).
destruct (gsl_sa cx _ _ _ _ _ _ _ _ _ _ _ _ _ HB HMEM) as (HSA1 & HSA2).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HOKX as (_ & _ & _ & _ & _ & Hcapr & HUlen & Husedr & Hbufc & Hnheld & Hheld & _ & _ & Hkeys).
assert (Hnlen : (n < length (re_keys e1))%nat) by lia.
destruct Hheld as [(Hz & Hk0) | (Hz & Hin & Hk1 & Hk2 & Hg8)]; [rewrite Hk0 in Hnlen; cbn [length] in Hnlen; lia|].
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_hp e1) (re_kh e1) HAR Hin) as (HH16 & HH4096 & HHceil & HHia & _).
assert (Hrq : re_kh e1 <= req_size (re_kh e1)) by (unfold req_size; destruct (Z.eqb_spec (re_kh e1) 0); lia).
assert (HHP8 : re_hp e1 mod 8 = 0).
{ rewrite (Z.div_mod (re_hp e1) 16) by lia. rewrite HH16, Z.add_0_r.
  replace (16 * (re_hp e1 / 16)) with ((2 * (re_hp e1 / 16)) * 8) by lia. apply Z.mod_mul. lia. }
set (kn := nth n (re_keys e1) (0, [], [])).
assert (Hkn : In kn (re_keys e1)) by (apply nth_In; exact Hnlen).
rewrite Forall_forall in Hkeys. destruct (Hkeys kn Hkn) as (HKin & HKg & HKnz & HKlen).
unfold APARTIAL in HKlen.
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (key_addr kn) (Z.of_nat (length (key_text kn)) + 1) HAR HKin)
  as (HK16 & HK4096 & HKceil & HKia & _).
assert (RQK : req_size (Z.of_nat (length (key_text kn)) + 1) = Z.of_nat (length (key_text kn)) + 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (key_text kn)) + 1) 0); lia).
rewrite RQK in HKceil, HKia.
pose proof (gsl_slot_val W1 m1 (re_hp e1) (re_keys e1) n Hg8 Hnlen ltac:(change (nth n (re_keys e1) (0, [], [])) with kn; lia))
  as MSL. fold kn in MSL.
pose proof (gsl_link_U _ _ _ _ _ _ _ _ _ HLINK) as HUW.
assert (HUL : re_used e1 = Z.of_nat (length (dW s1))) by (rewrite <- HUW, gsl_bzs_len; lia).
pose proof HGSF as (Hbd & Hpq & Hq0 & Hnzl & Hskp & Hlim).
assert (Hcap0 : re_cap e1 <> 0) by (intros Hc; rewrite Hc in Husedr; lia).
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjunk & Hbuf8)]; [lia|].
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hbin) as (HB16 & HB4096 & HBceil & HBia & _).
assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQC in HBceil, HBia.
pose proof (gsl_line_garr8 W1 m1 s1 p q e1 Hbuf8 HUW ltac:(lia)) as HLg.
unfold re_nheld in Hnheld, Hk1.
pose proof (gl_entry W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (re_hp e1) n (key_addr kn) (dxSA cx) bg
  Hsp ltac:(unfold ESTACK, DRAIN_FRAME in *; lia) ltac:(unfold DRAIN_FRAME in *; lia)
  ltac:(rewrite Zminus_mod, Hal16; reflexivity) R21 R20 ltac:(lia) R19
  HH4096 HHP8 ltac:(unfold GL_PHI; lia) ltac:(unfold ESTACK, DRAIN_FRAME in *; lia) ltac:(unfold GL_PHI; lia)
  HSA1 ltac:(unfold GL_PHI; lia) Hbgr M40 M48 M56 M80 MSL) as HS.
remember (Eimg (Ereg regs1 (gl_extra (re_hp e1) (re_hp e1 + 8 * Z.of_nat n) (key_addr kn) (dxSA cx) bg))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall k (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r).
{ intros k r Hk Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EREG 21%nat 21%bv ltac:(lia) eq_refl); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 (re_hp e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (key_addr kn)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (dxSA cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 bg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (SHOK : sh_ok SEGS gl_Bx gl_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E gl_Bx 33 (re_hp e1 + 8 * Z.of_nat n) 8 (re_hp e1 + 8 * Z.of_nat n) 0 8).
  - apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 (re_hp e1) (re_kh e1)); [exact HAR | exact Hin | lia | lia].
  - unfold gl_Bx. rewrite (U_atom E 21 SHADOW_OFF E21) by (unfold SHADOW_OFF; lia). reflexivity.
  - apply (U_atom E 33 _ E33). lia.
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia. }
clear HE.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_hloop)) with (Z_to_bv 64 (BASE + A_dr_hloop)).
paj_run_tok RUN HS HJ SHOK gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10.
match goal with Hg : mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ms)) |- _ => rename Hg into GR1 end.
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ms)) |- _ => rename Hf into HFr1 end.
assert (KEEP1 : forall y, 0 <= y < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) y = aview SEGS (w_H W1) m1 y)
  by (intros y Hy; exact (gsl_frame_nil _ _ _ _ _ HFr1 ltac:(vm_compute; reflexivity) y Hy)).
clear HFr1.
set (mdm := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody mdm.
assert (HARm : AR SEGS B ly1 S1 W1 (ms_mem ms) mdm) by (eapply ajournal_gx_AR; exact HJ).
assert (ROM1 : rom_view SEGS W1 (ms_mem ms)).
{ intros y Hy. rewrite KEEP1; [exact (Hrom y Hy)|].
  destruct Hy as (sg & Hsg & _ & Hr). pose proof (pa_img_range y ltac:(exists sg; split; [exact Hsg | exact Hr])). lia. }
pose proof HB as (Hafn & _). pose proof Hafn as (_ & _ & _ & Hgp & Htp & _).
assert (Usp1 : spZ (ms_regs ms) = dsp0 cx - DRAIN_FRAME)
  by (unfold spZ; rewrite Q2, (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
assert (G3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, (EREG 3%nat 3%bv ltac:(lia) eq_refl), R3; exact Hgp).
assert (G4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, (EREG 4%nat 4%bv ltac:(lia) eq_refl), R4; exact Htp).
set (x := key_addr kn) in *. set (klen := Z.of_nat (length (key_text kn))) in *.
assert (G10 : getr (ms_regs ms) 10 = w64 x) by (rewrite Q10, E34; reflexivity).
assert (HKg1 : garr8 SEGS (arm W1 (ms_mem ms)) x (bzs (key_text kn ++ [Z_to_bv 8 0]))).
{ apply (gsl_garr8_kept W1 m1 W1 (ms_mem ms)); [exact HKg|]. intros y Hy. apply KEEP1.
  rewrite gsl_bzs_len, length_app in Hy. cbn [length] in Hy. lia. }
assert (HKL : Z.to_nat klen = length (key_text kn)) by (unfold klen; lia).
assert (HDF : DRAIN_FRAME = 336) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HDS : DRAIN_STK = 16848) by reflexivity.
(* strlen (held[n]) *)
eapply SRr_bind.
{ eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 ([] : list (Z * Z)) (2 * ESTACK) (SIGMA WS_strlen)
    (fun _ => False) (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 klen)
    W1 (ms_regs ms) (ms_mem ms) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx)
    ([] : list (Z * Z)) ly1 S1 _ k1 (- DRAIN_FRAME) (Z_to_bv 64 (BASE + 5480)) HG eq_refl HJ).
  - rewrite Usp1. lia.
  - rewrite HDF. reflexivity.
  - lia.
  - lia.
  - lia.
  - exact G3.
  - exact G4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros _. right. intros [].
  - intros y [].
  - intros y [].
  - intros HPRE HSC. eapply SRr_mono.
    { refine (ASTRLEN ly1 S1 W1 (ms_regs ms) (ms_mem ms) mdm x klen HPRE (proj1 HSC) (proj2 HSC) G10
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) _ _ _ _ _ _ _ _ ROM1).
      - apply (gsl_first_byte W1 (ms_mem ms) x (bzs (key_text kn ++ [Z_to_bv 8 0])) (klen + 1) klen HKg1).
        + lia.
        + rewrite gsl_bzs_len, length_app. cbn [length]. lia.
        + intros i Hi. apply (gsl_key_nz _ HKnz). lia.
        + intros _. rewrite HKL. apply gsl_key_z.
      - intros y Hy. split.
        + replace y with (x + Z.of_nat (Z.to_nat (y - x))) by lia.
          rewrite (gsl_aview_garr8 W1 (ms_mem ms) x _ _ HKg1); [discriminate|].
          rewrite gsl_bzs_len, length_app. cbn [length]. lia.
        + rewrite Usp1. lia.
      - intros y Hy. rewrite Usp1. lia.
      - unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HKia |- *. lia.
      - apply (amem_range_near_block B RG LAWS HGSB ly1 S1 W1 (ms_mem ms) mdm x (klen + 1) x HARm HKin); [lia|].
        rewrite RQK. lia.
      - apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) mdm x (klen + 1)); [exact HARm | exact HKin | lia | rewrite RQK; lia].
      - apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) mdm x (klen + 1)); [exact HARm | exact HKin | lia | rewrite RQK; lia | lia].
      - intros y Hy. apply (ALLOC_TAIL ly1 S1 W1 (ms_mem ms) mdm x (klen + 1) y HARm HKin). rewrite RQK.
        replace (x + (klen + 1) - 1) with (x + klen) by lia. exact Hy. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpr).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|]. split; [exact Hres|].
    split; [intros y Hy _ Hs; exact (Hfr y Hy Hs) | exact Hpr]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres & Hfr2 & Hpres2).
jafter_call_keep_pi HS 37%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0%nat] HS2.
assert (Usp0 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
assert (HRK : region_kept SEGS E (ms_mem (restrict (w_H W1) ms)) (mrestrict (w_H W1) mem2) gl_frame).
{ split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi gl_frame base_val]; rewrite Usp0;
    intros y Hy; [|lia].
  change (ms_mem (restrict (w_H W1) ms)) with (mrestrict (w_H W1) (ms_mem ms)).
  apply (mbyte_of_aview SEGS). apply Hfr2; [clear - Hy HSTK1 HSTK2 C1; unfold ESTACK, DRAIN_FRAME in *; lia | intros [] | clear - Hy; unfold ESTACK in *; lia]. }
specialize (HS2 ltac:(constructor; [exact HRK | constructor])).
clear HS HRK. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 37 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 37)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
prreg HS (10%bv : bv 5) R10b.
assert (A41 : ew Ea 41 = Z_to_bv 64 klen) by (rewrite <- R10b, Hres; reflexivity).
assert (A27 : ew Ea 27 = Z_to_bv 64 (Z.of_nat jj))
  by (rewrite (OLDa 27%nat ltac:(lia)), (EREG 27%nat 27%bv ltac:(lia) eq_refl), R27; reflexivity).
assert (SHOK2 : sh_ok SEGS gl_Bx [] Ea (mrestrict (w_H W1) mem2)) by constructor.
assert (KEEP2 : GSKEEP cx W1 m1 mem2).
{ split.
  - intros y Hy Hs. rewrite (Hfr2 y Hy (fun H => H) ltac:(clear - Hs; unfold ESTACK in *; lia)). exact (KEEP1 y Hy).
  - intros y Hp. apply Hpres2. exact (apresent_grows _ _ _ y GR1 Hp). }
clear KEEP1 Hfr2.
paj_run_tok RUN HS HJ2 SHOK2 gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) mem2) (mrestrict (w_H W1) (ms_mem ?mx)) |- _ => rename Hf into HFrB; rename mx into msB end.
match goal with Hg : mem_grows (mrestrict (w_H W1) mem2) (mrestrict (w_H W1) (ms_mem msB)) |- _ => rename Hg into GRB end.
assert (KEEPB : GSKEEP cx W1 m1 (ms_mem msB)).
{ apply (gsl_keep_trans cx W1 m1 mem2 (ms_mem msB) KEEP2). split.
  - intros y Hy _. exact (gsl_frame_nil _ _ _ _ _ HFrB ltac:(vm_compute; reflexivity) y Hy).
  - intros y Hp. exact (apresent_grows _ _ _ y GRB Hp). }
clear HFrB.
assert (Hk64 : 0 <= klen < 2 ^ 64) by (clear - HKlen; unfold klen; lia).
assert (Hj64 : 0 <= Z.of_nat jj < 2 ^ 64) by (clear - Hjjr Hpq HUL Husedr HBceil HB4096 C1; lia).
psrr_branch_tok RUN BR HS SHOK2 gl_Bspan.
- (* |held[n]| <> jj: no match at slot n *)
  rewrite branch_ne_U, (U_atom Ea 41 klen A41 Hk64), (U_atom Ea 27 (Z.of_nat jj) A27 Hj64) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK2 gl_Bspan A_dr_hnext. { apply awr_ok_x_of0. awr_ok_tac. }
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hf into HFrF end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hg into GRF end.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. gsl_prreg_raw HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  prreg HS (27%bv : bv 5) P27.
  repeat rewrite wvb_collapse in HJ2.
  match goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
  assert (HKP : GSKEEP cx W1 m1 (ms_mem msF)).
  { apply (gsl_keep_trans cx W1 m1 (ms_mem msB) (ms_mem msF) KEEPB). split.
    - intros y Hy _. exact (gsl_frame_nil _ _ _ _ _ HFrF ltac:(vm_compute; reflexivity) y Hy).
    - intros y Hp. exact (apresent_grows _ _ _ y GRF Hp). }
  clear HS SHOK2 HFrF.
  assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Ea k -> Nat.ltb k 32 = true ->
    Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
  { intros r k Hr Hk Hkr. apply Nat.ltb_lt in Hk. rewrite Hr, (OLDa k ltac:(lia)). apply EREG; [exact Hk | exact Hkr]. }
  assert (P19' : getr (ms_regs msF) 19 = getr regs1 19).
  { rewrite P19, denot_lit_U, R19.
    change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 0) (SLit 3)) (SOff 21 0)) with (gl_shE 33).
    rewrite (gl_U_shadow Ea 33 (re_hp e1 + 8 * Z.of_nat n)); [reflexivity | | |].
    - rewrite (OLDa 33%nat ltac:(lia)). exact E33.
    - rewrite (OLDa 21%nat ltac:(lia)). exact E21.
    - clear - HH4096 HHceil Hrq Hk1 Hnlen C1. lia. }
  apply HGN.
  apply (gsl_exit_gsn cx s1 D p q n (S kf) W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg
    (ms_regs msF) (ms_mem msF) mdF HB HBD HJ2 HKP).
  + split; [exact (RK _ 2%nat P2 eq_refl eq_refl)|]. split; [exact (RK _ 3%nat P3 eq_refl eq_refl)|].
    split; [exact (RK _ 4%nat P4 eq_refl eq_refl)|]. split; [exact (RK _ 8%nat P8 eq_refl eq_refl)|].
    split; [exact (RK _ 9%nat P9 eq_refl eq_refl)|]. split; [exact (RK _ 18%nat P18 eq_refl eq_refl)|].
    split; [exact (RK _ 21%nat P21 eq_refl eq_refl)|]. split; [exact (RK _ 23%nat P23 eq_refl eq_refl)|].
    split; [exact (RK _ 24%nat P24 eq_refl eq_refl)|]. split; [exact (RK _ 25%nat P25 eq_refl eq_refl)|].
    exact (RK _ 27%nat P27 eq_refl eq_refl).
  + exact P19'.
  + exact (RK _ 20%nat P20 eq_refl eq_refl).
  + rewrite (gsl_nth_H _ _ _ _ _ _ _ _ _ n HLINK Hnlen). fold kn. intros Heq.
    apply (f_equal (@length Z)) in Heq. rewrite gsl_bzs_len, length_firstn, (gs_dline_len s1 p q Hpq) in Heq.
    clear - Heq Hc Hjjr. unfold klen in Hc. lia.
- (* |held[n]| = jj: strncmp (held[n], line + p, jj) *)
  rewrite branch_ne_U, (U_atom Ea 41 klen A41 Hk64), (U_atom Ea 27 (Z.of_nat jj) A27 Hj64) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ2 SHOK2 gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem ?mx)) |- _ => rename Hf into HFrC; rename mx into msC end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msC)) |- _ => rename Hg into GRC end.
  assert (KEEPC : GSKEEP cx W1 m1 (ms_mem msC)).
  { apply (gsl_keep_trans cx W1 m1 (ms_mem msB) (ms_mem msC) KEEPB). split.
    - intros z Hw _. exact (gsl_frame_nil _ _ _ _ _ HFrC ltac:(vm_compute; reflexivity) z Hw).
    - intros z Hp. exact (apresent_grows _ _ _ z GRC Hp). }
  clear HFrC.
  pmkst HS.
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
  repeat rewrite wvb_collapse in HJ2.
  match goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdc := mdx) in * end.
  clearbody mdc.
  assert (HARc : AR SEGS B ly1 S1 W1 (ms_mem msC) mdc) by (eapply ajournal_gx_AR; exact HJ2).
  pose proof KEEPC as (KC & PC).
  assert (KLC : forall z, 0 <= z < alloc_ceiling -> aview SEGS (w_H W1) (ms_mem msC) z = aview SEGS (w_H W1) m1 z)
    by (intros z Hw; apply KC; [clear - Hw C1; lia | clear - Hw HSTK1; unfold ESTACK, DRAIN_FRAME in *; lia]).
  assert (ROMc : rom_view SEGS W1 (ms_mem msC)).
  { intros z Hw. rewrite KLC; [exact (Hrom z Hw)|].
    destruct Hw as (sg & Hsg & _ & Hr). pose proof (pa_img_range z ltac:(exists sg; split; [exact Hsg | exact Hr])).
    clear - H C1. lia. }
  set (y := re_buf e1 + Z.of_nat p) in *.
  assert (Usp2 : spZ (ms_regs msC) = dsp0 cx - DRAIN_FRAME)
    by (unfold spZ; rewrite T2, (OLDa 2%nat ltac:(lia)), (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
  assert (H3 : getr (ms_regs msC) 3 = w64 (as_gp B))
    by (rewrite T3, (OLDa 3%nat ltac:(lia)), (EREG 3%nat 3%bv ltac:(lia) eq_refl), R3; exact Hgp).
  assert (H4 : getr (ms_regs msC) 4 = w64 (as_tp B))
    by (rewrite T4, (OLDa 4%nat ltac:(lia)), (EREG 4%nat 4%bv ltac:(lia) eq_refl), R4; exact Htp).
  assert (H10 : getr (ms_regs msC) 10 = w64 x) by (rewrite T10, (OLDa 34%nat ltac:(lia)), E34; reflexivity).
  assert (H11 : getr (ms_regs msC) 11 = w64 y)
    by (rewrite T11, (OLDa 24%nat ltac:(lia)), (EREG 24%nat 24%bv ltac:(lia) eq_refl), R24; reflexivity).
  assert (H12 : getr (ms_regs msC) 12 = w64 (Z.of_nat jj)) by (rewrite T12, A27; reflexivity).
  assert (HKgC : garr8 SEGS (arm W1 (ms_mem msC)) x (bzs (key_text kn ++ [Z_to_bv 8 0]))).
  { apply (gsl_garr8_kept W1 m1 W1 (ms_mem msC)); [exact HKg|]. intros z Hw. apply KLC.
    rewrite gsl_bzs_len, length_app in Hw. cbn [length] in Hw. clear - Hw HK4096 HKceil. unfold klen, x in *. lia. }
  assert (HLgC : garr8 SEGS (arm W1 (ms_mem msC)) y (dline s1 p q)).
  { apply (gsl_garr8_kept W1 m1 W1 (ms_mem msC)); [exact HLg|]. intros z Hw. apply KLC.
    rewrite (gs_dline_len s1 p q Hpq) in Hw. clear - Hw Hpq HUL Husedr HBceil HB4096. unfold y in *. lia. }
  assert (HJJ : Z.to_nat (Z.of_nat jj) = jj) by lia.
  assert (Hjk : length (key_text kn) = jj) by (clear - Hc; unfold klen in Hc; lia).
  (* strncmp (held[n], s->buf + p, jj) *)
  eapply SRr_bind.
  { eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 ([] : list (Z * Z)) (2 * ESTACK) (SIGMA WS_strncmp)
      (fun _ => False)
      (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 0 <-> astrn_agree W1 (ms_mem msC) x y (Z.of_nat jj))
      W1 (ms_regs msC) (ms_mem msC) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx)
      ([] : list (Z * Z)) ly1 S1 _ k1 (- DRAIN_FRAME) (Z_to_bv 64 (BASE + 5500)) HG eq_refl HJ2).
    - rewrite Usp2. lia.
    - rewrite HDF. reflexivity.
    - lia.
    - lia.
    - lia.
    - exact H3.
    - exact H4.
    - exact T1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros _. right. intros [].
    - intros z [].
    - intros z [].
    - intros HPRE HSC.
      assert (HM : Z.min (Z.of_nat jj) (Z.of_nat jj + 1) = Z.of_nat jj) by lia.
      refine (ASTRNCMP ly1 S1 W1 (ms_regs msC) (ms_mem msC) mdc x y (Z.of_nat jj) (Z.of_nat jj) (Z.of_nat jj)
        HPRE HSC H10 H11 H12 _ _ _ _ _ _ _ _ _ _ _ _ ROMc _); rewrite ?HM.
      + clear - Hjjr Hpq HUL Husedr HBceil HB4096 C1. lia.
      + clear - Hjjr Hpq HUL Husedr Hcapr. destruct Hcapr as [Hq | [Hq | Hq]]; lia.
      + clear - HK4096. unfold x. lia.
      + clear - HB4096. unfold y. lia.
      + apply (gsl_first_byte W1 (ms_mem msC) x (bzs (key_text kn ++ [Z_to_bv 8 0])) (Z.of_nat jj) (Z.of_nat jj) HKgC).
        * lia.
        * rewrite gsl_bzs_len, length_app. cbn [length]. lia.
        * intros i Hi. apply (gsl_key_nz _ HKnz). lia.
        * intros Hlt. lia.
      + apply (gsl_first_byte W1 (ms_mem msC) y (dline s1 p q) (Z.of_nat jj) (Z.of_nat jj) HLgC).
        * lia.
        * rewrite (gs_dline_len s1 p q Hpq). lia.
        * intros i Hi. apply (gsl_dline_nth_nz s1 p q Hpq Hnzl). lia.
        * intros Hlt. lia.
      + clear - HKceil HK4096 Hjk C1. unfold x, klen in *. lia.
      + clear - Hjjr Hpq HUL Husedr HBceil HB4096 C1. unfold y. lia.
      + intros z Hw. split.
        * replace z with (x + Z.of_nat (Z.to_nat (z - x))) by lia.
          rewrite (gsl_aview_garr8 W1 (ms_mem msC) x _ _ HKgC); [discriminate|].
          rewrite gsl_bzs_len, length_app. cbn [length]. lia.
        * rewrite Usp2. clear - Hw HKceil HK4096 Hjk C1 HSTK1. unfold x, klen, ESTACK, DRAIN_FRAME in *. lia.
      + intros z Hw. split.
        * replace z with (y + Z.of_nat (Z.to_nat (z - y))) by lia.
          rewrite (gsl_aview_garr8 W1 (ms_mem msC) y _ _ HLgC); [discriminate|].
          rewrite (gs_dline_len s1 p q Hpq). lia.
        * rewrite Usp2. clear - Hw Hjjr Hpq HUL Husedr HBceil HB4096 C1 HSTK1. unfold y, ESTACK, DRAIN_FRAME in *. lia.
      + split; [|split].
        * unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HKia |- *.
          clear - HKia Hjk C1. unfold x, klen in *. lia.
        * apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msC) mdc x (klen + 1)); [exact HARc | exact HKin | lia |].
          rewrite RQK. clear - Hjk. unfold klen. lia.
        * intros Hp0. apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msC) mdc x (klen + 1));
            [exact HARc | exact HKin | lia | rewrite RQK; clear - Hjk; unfold klen; lia | exact Hp0].
      + split; [|split].
        * unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HBia |- *.
          clear - HBia Hjjr Hpq HUL Husedr C1. unfold y. lia.
        * apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msC) mdc (re_buf e1) (re_cap e1)); [exact HARc | exact Hbin | unfold y; lia |].
          rewrite RQC. clear - Hjjr Hpq HUL Husedr. unfold y. lia.
        * intros Hp0. apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msC) mdc (re_buf e1) (re_cap e1));
            [exact HARc | exact Hbin | unfold y; lia | rewrite RQC; clear - Hjjr Hpq HUL Husedr; unfold y; lia | exact Hp0].
      + split.
        * apply (amem_range_near_block B RG LAWS HGSB ly1 S1 W1 (ms_mem msC) mdc x (klen + 1) x HARc HKin); [lia|].
          rewrite RQK. lia.
        * apply (amem_range_near_block B RG LAWS HGSB ly1 S1 W1 (ms_mem msC) mdc (re_buf e1) (re_cap e1) y HARc Hbin);
            [unfold y; lia | rewrite RQC; clear - Hpq HUL Husedr; unfold y; lia]. }
  cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hres3 & Hfr3 & Hpres3).
  assert (HAG : astrn_agree W1 (ms_mem msC) x y (Z.of_nat jj) <-> nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q)).
  { rewrite (gsl_agree_iff W1 (ms_mem msC) x y (Z.of_nat jj) _ _ HKgC HLgC);
      [| lia | rewrite gsl_bzs_len, length_app; cbn [length]; lia | rewrite (gs_dline_len s1 p q Hpq); lia
       | intros i Hi; apply (gsl_key_nz _ HKnz); lia].
    rewrite HJJ, (gsl_nth_H _ _ _ _ _ _ _ _ _ n HLINK Hnlen). fold kn.
    replace (firstn jj (bzs (key_text kn ++ [Z_to_bv 8 0]))) with (bzs (key_text kn))
      by (rewrite <- Hjk; symmetry; apply gsl_bzs_firstn_key).
    reflexivity. }
  jafter_call_keep_pi HS 53%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0%nat] HS3.
  assert (UspA : bv_unsigned (ew Ea 2) = dsp0 cx - DRAIN_FRAME) by (rewrite (OLDa 2%nat ltac:(lia)); exact Usp0).
  assert (HRK : region_kept SEGS Ea (ms_mem (restrict (w_H W1) msC)) (mrestrict (w_H W1) mem3) gl_frame).
  { split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi gl_frame base_val]; rewrite UspA;
      intros z Hw; [|lia].
    change (ms_mem (restrict (w_H W1) msC)) with (mrestrict (w_H W1) (ms_mem msC)).
    apply (mbyte_of_aview SEGS). apply Hfr3;
      [clear - Hw HSTK1 HSTK2 C1; unfold ESTACK, DRAIN_FRAME in *; lia | intros [] | clear - Hw; unfold ESTACK in *; lia]. }
  specialize (HS3 ltac:(constructor; [exact HRK | constructor])).
  clear HS HRK. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  remember (havoc Ea 53 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
  assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
  assert (OLDb : forall m, (m < 53)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
  clear HEb.
  prreg HS (10%bv : bv 5) R10c.
  set (r0 := getr regs3 10) in *.
  assert (A57 : ew Eb 57 = Z_to_bv 64 (bv_unsigned r0)) by (rewrite <- R10c, Z_to_bv_bv_unsigned; reflexivity).
  assert (Hr0 : 0 <= bv_unsigned r0 < 2 ^ 64) by exact (bv_unsigned_in_range 64 r0).
  assert (SHOK3 : sh_ok SEGS gl_Bx [] Eb (mrestrict (w_H W1) mem3)) by constructor.
  assert (KEEP3 : GSKEEP cx W1 m1 mem3).
  { apply (gsl_keep_trans cx W1 m1 (ms_mem msC) mem3 KEEPC). split.
    - intros z Hw Hs. exact (Hfr3 z Hw (fun H => H) ltac:(clear - Hs; unfold ESTACK in *; lia)).
    - exact Hpres3. }
  clear Hfr3.
  paj_run_tok RUN HS HJ3 SHOK3 gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) mem3) (mrestrict (w_H W1) (ms_mem ?mx)) |- _ => rename Hf into HFrD; rename mx into msD end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) mem3) (mrestrict (w_H W1) (ms_mem msD)) |- _ => rename Hg into GRD end.
  assert (KEEPD : GSKEEP cx W1 m1 (ms_mem msD)).
  { apply (gsl_keep_trans cx W1 m1 mem3 (ms_mem msD) KEEP3). split.
    - intros z Hw _. exact (gsl_frame_nil _ _ _ _ _ HFrD ltac:(vm_compute; reflexivity) z Hw).
    - intros z Hp. exact (apresent_grows _ _ _ z GRD Hp). }
  clear HFrD.
  psrr_branch_tok RUN BR HS SHOK3 gl_Bspan.
  + (* strncmp = 0: the key is held at slot n *)
    match goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hb3 end.
    rewrite branch_eq_U, (U_atom Eb 57 (bv_unsigned r0) A57 Hr0), (U_lit Eb 0) in Hb3 by lia.
    apply Z.eqb_eq in Hb3.
    assert (Hmt : nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q)).
    { apply HAG, Hres3. fold r0. apply bv_eq. rewrite Hb3. reflexivity. }
    paj_run_tok RUN HS HJ3 SHOK3 gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
    match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msD)) (mrestrict (w_H W1) (ms_mem ?mx)) |- _ => rename Hf into HFrE; rename mx into msE end.
    match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msD)) (mrestrict (w_H W1) (ms_mem msE)) |- _ => rename Hg into GRE end.
    assert (KEEPE : GSKEEP cx W1 m1 (ms_mem msE)).
    { apply (gsl_keep_trans cx W1 m1 (ms_mem msD) (ms_mem msE) KEEPD). split.
      - intros z Hw _. exact (gsl_frame_nil _ _ _ _ _ HFrE ltac:(vm_compute; reflexivity) z Hw).
      - intros z Hp. exact (apresent_grows _ _ _ z GRE Hp). }
    clear HFrE KEEPD. rename KEEPE into KEEPD. rename msE into msD0.
    assert (B36 : ew Eb 36 = Z_to_bv 64 bg) by (rewrite (OLDb 36%nat ltac:(lia)), (OLDa 36%nat ltac:(lia)); exact E36).
    psrr_branch_tok RUN BR HS SHOK3 gl_Bspan.
    * (* bg = 0: a begin whose key is held: on to the next line *)
      match goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hb4 end.
      rewrite branch_eq_U, (U_atom Eb 36 bg B36 Hbgr), (U_lit Eb 0) in Hb4 by lia.
      apply Z.eqb_eq in Hb4.
      paj_run_to_tok RUNTO HS HJ3 SHOK3 gl_Bspan A_dr_next. { apply awr_ok_x_of0. awr_ok_tac. }
      match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
      match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msD0)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hf into HFrF end.
      match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msD0)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hg into GRF end.
      pmkst HS.
      prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
      prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. gsl_prreg_raw HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
      prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
      prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
      repeat rewrite wvb_collapse in HJ3.
      match goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
      assert (HKP : GSKEEP cx W1 m1 (ms_mem msF)).
      { apply (gsl_keep_trans cx W1 m1 (ms_mem msD0) (ms_mem msF) KEEPD). split.
        - intros z Hw _. exact (gsl_frame_nil _ _ _ _ _ HFrF ltac:(vm_compute; reflexivity) z Hw).
        - intros z Hp. exact (apresent_grows _ _ _ z GRF Hp). }
      clear HS SHOK3 HFrF.
      assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Eb k -> Nat.ltb k 32 = true ->
        Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
      { intros r k Hr Hk Hkr. apply Nat.ltb_lt in Hk. rewrite Hr, (OLDb k ltac:(lia)), (OLDa k ltac:(lia)).
        apply EREG; [exact Hk | exact Hkr]. }
      assert (B35 : ew Eb 35 = Z_to_bv 64 (dxSA cx)) by (rewrite (OLDb 35%nat ltac:(lia)), (OLDa 35%nat ltac:(lia)); exact E35).
      assert (B33 : ew Eb 33 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (rewrite (OLDb 33%nat ltac:(lia)), (OLDa 33%nat ltac:(lia)); exact E33).
      assert (Q22 : getr (ms_regs msF) 22 = w64 (dxSA cx)) by (rewrite P22, B35; reflexivity).
      assert (Q27 : getr (ms_regs msF) 27 = w64 (dxSA cx + 24))
        by (rewrite P27, B35, unsigned_lit_small by (clear - HSA1 HSA2 C1; lia); reflexivity).
      pose proof (gsl_body_keep cx s1 D p q n (S kf) n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl
        kd jj bg (ms_mem msF) mdF HB HBD HJ3 HKP) as HBDF.
      apply (HDLN W1).
      exact (gsl_mk_dln cx s1 D p q n (S kf) W1 regs1 ly1 S1 (ms_mem msF) mdF k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl
        kd jj bg (ms_regs msF) HBDF Hmt Hb4
        (RK _ 2%nat P2 eq_refl eq_refl) (RK _ 3%nat P3 eq_refl eq_refl) (RK _ 4%nat P4 eq_refl eq_refl)
        (RK _ 8%nat P8 eq_refl eq_refl) (RK _ 9%nat P9 eq_refl eq_refl) (RK _ 18%nat P18 eq_refl eq_refl)
        (RK _ 21%nat P21 eq_refl eq_refl) (RK _ 23%nat P23 eq_refl eq_refl) Q22 Q27).
    * (* bg <> 0: an end whose key is held: GF *)
      match goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hb4 end.
      rewrite branch_eq_U, (U_atom Eb 36 bg B36 Hbgr), (U_lit Eb 0) in Hb4 by lia.
      apply Z.eqb_neq in Hb4.
      paj_run_to_tok RUNTO HS HJ3 SHOK3 gl_Bspan A_dr_free. { apply awr_ok_x_of0. awr_ok_tac. }
      match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
      match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msD0)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hf into HFrF end.
      match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msD0)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hg into GRF end.
      pmkst HS.
      prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
      prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. gsl_prreg_raw HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
      prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
      prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
      repeat rewrite wvb_collapse in HJ3.
      match goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
      assert (HKP : GSKEEP cx W1 m1 (ms_mem msF)).
      { apply (gsl_keep_trans cx W1 m1 (ms_mem msD0) (ms_mem msF) KEEPD). split.
        - intros z Hw _. exact (gsl_frame_nil _ _ _ _ _ HFrF ltac:(vm_compute; reflexivity) z Hw).
        - intros z Hp. exact (apresent_grows _ _ _ z GRF Hp). }
      clear HS SHOK3 HFrF.
      assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Eb k -> Nat.ltb k 32 = true ->
        Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
      { intros r k Hr Hk Hkr. apply Nat.ltb_lt in Hk. rewrite Hr, (OLDb k ltac:(lia)), (OLDa k ltac:(lia)).
        apply EREG; [exact Hk | exact Hkr]. }
      assert (B35 : ew Eb 35 = Z_to_bv 64 (dxSA cx)) by (rewrite (OLDb 35%nat ltac:(lia)), (OLDa 35%nat ltac:(lia)); exact E35).
      assert (B33 : ew Eb 33 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (rewrite (OLDb 33%nat ltac:(lia)), (OLDa 33%nat ltac:(lia)); exact E33).
      assert (Q22 : getr (ms_regs msF) 22 = w64 (dxSA cx)) by (rewrite P22, B35; reflexivity).
      assert (Q27 : getr (ms_regs msF) 27 = w64 (dxSA cx + 24))
        by (rewrite P27, B35, unsigned_lit_small by (clear - HSA1 HSA2 C1; lia); reflexivity).
      pose proof (gsl_body_keep cx s1 D p q n (S kf) n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl
        kd jj bg (ms_mem msF) mdF HB HBD HJ3 HKP) as HBDF.
      assert (P19' : getr (ms_regs msF) 19 = getr regs1 19).
      { rewrite P19, denot_lit_U, R19.
        change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 0) (SLit 3)) (SOff 21 0)) with (gl_shE 33).
        rewrite (gl_U_shadow Eb 33 (re_hp e1 + 8 * Z.of_nat n)); [reflexivity | exact B33 | |].
        - rewrite (OLDb 21%nat ltac:(lia)), (OLDa 21%nat ltac:(lia)). exact E21.
        - clear - HH4096 HHceil Hrq Hk1 Hnlen C1. lia. }
      apply (HGF W1).
      exact (gsl_mk_gf cx s1 D p q n (S kf) W1 regs1 ly1 S1 (ms_mem msF) mdF k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl
        kd jj bg (ms_regs msF) HBDF Hmt Hb4
        (RK _ 2%nat P2 eq_refl eq_refl) (RK _ 3%nat P3 eq_refl eq_refl) (RK _ 4%nat P4 eq_refl eq_refl)
        (RK _ 8%nat P8 eq_refl eq_refl) (RK _ 9%nat P9 eq_refl eq_refl) (RK _ 18%nat P18 eq_refl eq_refl)
        (RK _ 21%nat P21 eq_refl eq_refl) (RK _ 23%nat P23 eq_refl eq_refl) (RK _ 24%nat P24 eq_refl eq_refl)
        P19' (RK _ 20%nat P20 eq_refl eq_refl) Q22 Q27 ltac:(rewrite P26, B33; reflexivity)).
  + (* strncmp <> 0: no match at slot n *)
    match goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hb3 end.
    rewrite branch_eq_U, (U_atom Eb 57 (bv_unsigned r0) A57 Hr0), (U_lit Eb 0) in Hb3 by lia.
    apply Z.eqb_neq in Hb3.
    assert (Hmis : nth n (dlH cx s1 p) [] <> firstn jj (dline s1 p q)).
    { intros Hm. apply HAG, Hres3 in Hm. fold r0 in Hm. apply Hb3. rewrite Hm. reflexivity. }
    paj_run_to_tok RUNTO HS HJ3 SHOK3 gl_Bspan A_dr_hnext. { apply awr_ok_x_of0. awr_ok_tac. }
    match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
    match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msD)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hf into HFrF end.
    match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msD)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hg into GRF end.
    pmkst HS.
    prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
    prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. gsl_prreg_raw HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
    prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
    prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
    repeat rewrite wvb_collapse in HJ3.
    match goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
    assert (HKP : GSKEEP cx W1 m1 (ms_mem msF)).
    { apply (gsl_keep_trans cx W1 m1 (ms_mem msD) (ms_mem msF) KEEPD). split.
      - intros z Hw _. exact (gsl_frame_nil _ _ _ _ _ HFrF ltac:(vm_compute; reflexivity) z Hw).
      - intros z Hp. exact (apresent_grows _ _ _ z GRF Hp). }
    clear HS SHOK3 HFrF.
    assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Eb k -> Nat.ltb k 32 = true ->
      Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
    { intros r k Hr Hk Hkr. apply Nat.ltb_lt in Hk. rewrite Hr, (OLDb k ltac:(lia)), (OLDa k ltac:(lia)).
      apply EREG; [exact Hk | exact Hkr]. }
    assert (B35 : ew Eb 35 = Z_to_bv 64 (dxSA cx)) by (rewrite (OLDb 35%nat ltac:(lia)), (OLDa 35%nat ltac:(lia)); exact E35).
    assert (B33 : ew Eb 33 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (rewrite (OLDb 33%nat ltac:(lia)), (OLDa 33%nat ltac:(lia)); exact E33).
    pose proof (gsl_body_keep cx s1 D p q n (S kf) n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl
      kd jj bg (ms_mem msF) mdF HB HBD HJ3 HKP) as HBDF.
    assert (P19' : getr (ms_regs msF) 19 = getr regs1 19).
    { rewrite P19, denot_lit_U, R19.
      change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 0) (SLit 3)) (SOff 21 0)) with (gl_shE 33).
      rewrite (gl_U_shadow Eb 33 (re_hp e1 + 8 * Z.of_nat n)); [reflexivity | exact B33 | |].
      - rewrite (OLDb 21%nat ltac:(lia)), (OLDa 21%nat ltac:(lia)). exact E21.
      - clear - HH4096 HHceil Hrq Hk1 Hnlen C1. lia. }
    apply HGN.
    apply (gsl_exit_gsn cx s1 D p q n (S kf) W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg
      (ms_regs msF) (ms_mem msF) mdF HB HBD HJ3 HKP).
    * split; [exact (RK _ 2%nat P2 eq_refl eq_refl)|]. split; [exact (RK _ 3%nat P3 eq_refl eq_refl)|].
      split; [exact (RK _ 4%nat P4 eq_refl eq_refl)|]. split; [exact (RK _ 8%nat P8 eq_refl eq_refl)|].
      split; [exact (RK _ 9%nat P9 eq_refl eq_refl)|]. split; [exact (RK _ 18%nat P18 eq_refl eq_refl)|].
      split; [exact (RK _ 21%nat P21 eq_refl eq_refl)|]. split; [exact (RK _ 23%nat P23 eq_refl eq_refl)|].
      split; [exact (RK _ 24%nat P24 eq_refl eq_refl)|]. split; [exact (RK _ 25%nat P25 eq_refl eq_refl)|].
      exact (RK _ 27%nat P27 eq_refl eq_refl).
    * exact P19'.
    * exact (RK _ 20%nat P20 eq_refl eq_refl).
    * exact Hmis.
Qed.

(* ---- The loop: by induction on the external kf, the number of slots left. ---- *)
Theorem gs_scan_loop : gs_scan_loop_stmt B MT MMAX RG.
Proof.
unfold gs_scan_loop_stmt. intros cx s1 D p q n kf. revert n.
induction kf as [|kf IH]; intros n W1 c1 HB HGL HDLN HGA HGF.
- exfalso. destruct (gsl_GSL_elim _ _ _ _ _ _ _ _ _ HGL) as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1
    & spent & jb & aa & oo & ha & ks & tl & kd & jj & bg & _ & HBD).
  unfold GSBODY in HBD. destruct HBD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & _ & _ & Hkf & _). lia.
- apply (gsl_body cx s1 D p q n kf W1 c1 HB HGL HDLN HGF).
  intros c2 HGN.
  apply (gsl_tail cx s1 D p q n kf W1 c2 HB HGN HGA).
  intros Hkf0 c3 HGL3.
  exact (IH (S n) W1 c3 HB HGL3 HDLN HGA HGF).
Qed.

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (DR_x slice D, 2026-10-30): gs_scan_loop_x proves W_gsscanb_cx.v's
   gs_scan_loop_stmt_x over W_drain_cx_x.v's Section variables (B PST ARx MT RP MMAX RG), with the entry's ghost list
   Hp and budget kr after cx and a cut's ghost list Hp1 after S1.  Everything above is unchanged.
   - The AR-free names of the AR file are CITED (the byte lemmas, gsl_dlfut_same, GSKEEP / gsl_keep_trans /
     gsl_fv_keep / gsl_frame_keep, A_dr_hnext, gsl_link_H / gsl_link_U / gsl_nth_H / gsl_div8_succ, GSREGS,
     gsl_line_garr8, gsl_dline_nth_nz, gsl_img_low, gsl_recs_len, gsl_frame_nil and the two symbolic states gn_* /
     gl_* with gn_entry, gl_entry, gl_U_shadow); every lemma whose statement names AR, the journal, DBASE, DMEM,
     LCORE, DLC, GSB, GSL, GSN, GA, GF or DLN has its twin NAME_x below, with the AR proof's text.
   - The loop calls strlen (0x83850, ASTRLEN) and strncmp (0x83864, ASTRNCMP) and no allocator rule: the Section
     declares no context table, no rule and no RMM, and the cut's dbud_x (with its trace tl) reaches every exit
     (GA_x, GF_x, DLN_x, or GSL_x at n + 1) unchanged.
   - A key's strlen reads to its granule end: the AR proof's ALLOC_TAIL is W_drain_cx_x.alloc_tail_x, a theorem of
     the laws.  A block's shadow facts are W_journal_x's _hp0_x lemmas under HP0. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_cx W_drain_cx_x W_drain_gs.
(* W_drain_cx_x.v loads FCiface, which sets Zify's euclidean flag: this file's setting again *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ax. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section bx.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

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
(* W_drain_cx_x.v's Section c hypotheses this walk uses, in that file's order and text *)
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

(* gsl_prreg_raw_x (Section b above, so not visible here), the same text *)
Ltac gsl_prreg_raw_x HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.

(* ---- (2) Lowness over ARx: every byte the cut's representations touch lies below the allocator ceiling. ---- *)
Lemma gsl_blk_low_x : forall ly S Hp (W : world SEGS) mem md qq nn a,
ARx ly S Hp W mem md -> In (qq, nn) (ablocks B ly S) -> qq <= a -> a < qq + req_size nn ->
0 <= a < alloc_ceiling.
Proof.
intros ly S Hp W mem md qq nn a HAR Hin H1 H2.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md qq nn HAR Hin) as (_ & H4096 & Hceil & _). lia.
Qed.

Lemma gsl_aentry_fp_low_x : forall ly S Hp (W : world SEGS) mem md e,
ARx ly S Hp W mem md -> aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof.
intros ly S Hp W mem md e HAR HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (HPK : forall k, In k (re_keys e) ->
  key_addr k <= a < key_addr k + Z.of_nat (length (bzs (key_text k ++ [Z_to_bv 8 0]))) ->
  0 <= a < alloc_ceiling).
{ intros k Hk Hak. rewrite gsl_bzs_len, length_app in Hak. cbn [length] in Hak.
  rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
  apply (gsl_blk_low_x ly S Hp W mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) a HAR Hin); [lia|].
  pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & Hrq). lia. }
assert (HPH : re_hp e <= a < re_hp e + Z.of_nat (length (bzs (key_ptrs (re_keys e)))) ->
  0 <= a < alloc_ceiling).
{ intros Hah. rewrite gsl_bzs_len, gs_key_ptrs_len in Hah.
  destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
  - rewrite Hke in Hah. cbn [length] in Hah. lia.
  - apply (gsl_blk_low_x ly S Hp W mem md (re_hp e) (re_kh e) a HAR Hin); [lia|].
    pose proof (req_size_pos (re_kh e) ltac:(lia)) as (_ & Hrq). unfold re_nheld in Hk1. lia. }
unfold aentry_fp in Hr.
destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [app In] in Hr.
- destruct Hr as [<- | Hr]; [unfold gfp in Ha; cbn [fst snd] in Ha; exact (HPH Ha)|].
  apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPK k Hk Ha).
- destruct Hr as [<- | [<- | Hr]].
  + unfold gfp in Ha. cbn [fst snd] in Ha. rewrite gsl_bzs_len, length_app in Ha.
    destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (gsl_blk_low_x ly S Hp W mem md (re_buf e) (re_cap e) a HAR Hin); [lia|].
    pose proof (req_size_pos (re_cap e) ltac:(lia)) as (_ & Hrq). lia.
  + unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPH Ha).
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPK k Hk Ha).
Qed.

Lemma gsl_alist_fp_low_x : forall ly S Hp (W : world SEGS) mem md LA l lines lo hi,
ARx ly S Hp W mem md -> alist_at B ly S W mem LA l lines ->
0x10000 <= lo -> lo <= LA -> LA + 16 <= hi -> hi <= 0x5fb000 ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof.
intros ly S Hp W mem md LA l lines lo hi HAR HL Hlo1 Hlo2 Hhi1 Hhi2 r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (gsl_img_low RG HGSB a lo hi); lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite gsl_bzs_len, length_app, (gsl_recs_len RG) in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (gsl_blk_low_x ly S Hp W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin); [lia|].
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as (_ & Hrq).
    unfold hl_n, AREC in *. lia.
  + apply in_map_iff in Hr as (qq & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite gsl_bzs_len, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs qq Hq) as (Hin & _).
    apply (gsl_blk_low_x ly S Hp W mem md (fst qq) (Z.of_nat (length (snd qq)) + 1) a HAR Hin); [lia|].
    pose proof (req_size_pos (Z.of_nat (length (snd qq)) + 1) ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma gsl_asrc_fp_low_x : forall ly S Hp (W : world SEGS) mem md HA h,
ARx ly S Hp W mem md -> asrc_at B ly S W mem HA h ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof.
intros ly S Hp W mem md HA h HAR HS Hlo Hhi r Hr a Ha.
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (gsl_img_low RG HGSB a (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. rewrite gsl_bzs_len in Ha.
  apply (gsl_blk_low_x ly S Hp W mem md (hs_partial h) APARTIAL a HAR Hpb); [lia|].
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq). lia.
- unfold ASRC in *. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + eapply (gsl_alist_fp_low_x ly S Hp W mem md (HA + 16) (hs_pending h) false (rg_s RG) (rg_s RG + 4 * 96));
      [exact HAR | exact Hpend | lia | lia | lia | lia | exact Hr | exact Ha].
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * eapply (gsl_alist_fp_low_x ly S Hp W mem md (HA + 64) (hs_expected h) true (rg_s RG) (rg_s RG + 4 * 96));
        [exact HAR | exact Hexp | lia | lia | lia | lia | exact Hr | exact Ha].
    * eapply (gsl_alist_fp_low_x ly S Hp W mem md (HA + 80) (hs_held h) true (rg_s RG) (rg_s RG + 4 * 96));
        [exact HAR | exact Hheld | lia | lia | lia | lia | exact Hr | exact Ha].
Qed.

Ltac gsl_ing_x := unfold G_DR, G_SL; cbn [In]; repeat (first [left; reflexivity | right]).

Lemma gsl_aout_fp_low_x : forall ly S Hp (W : world SEGS) mem md c O mx no cap out,
ARx ly S Hp W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof.
intros ly S Hp W mem md c O mx no cap out HAR HOUT r Hr a Ha.
pose proof asan_consts as (C1 & _).
assert (GL2 : forall x l, In (x, l) (G_DR B RG) -> x <= a < x + l -> 0 <= a < alloc_ceiling).
{ intros x l Hin Hx.
  assert (HI : inG (G_DR B RG) a)
    by (unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (pa_img_range _ (proj1 (HG a HI))). lia. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- pose proof HSM as (Hs1 & Hs2). apply (gsl_img_low RG HGSB a (rg_send_max RG) (rg_send_max RG + 8)); lia.
- apply (GL2 (rg_nout RG) 8); [gsl_ing_x | lia].
- apply (GL2 (rg_capout RG) 8); [gsl_ing_x | lia].
- apply (GL2 (rg_out RG) 8); [gsl_ing_x | lia].
- pose proof (pa_obj_img 9 ltac:(lia)) as H9. rewrite HV9 in H9.
  apply (gsl_img_low RG HGSB a (rg_client RG) (rg_client RG + 4)); lia.
- apply (GL2 (rg_client_broken RG) 1); [gsl_ing_x | lia].
- pose proof (pa_obj_img 12 ltac:(lia)) as H12. rewrite HV12 in H12.
  apply (gsl_img_low RG HGSB a (rg_send_dead RG) (rg_send_dead RG + 1)); lia.
- apply (GL2 (rg_send_eintr RG) 1); [gsl_ing_x | lia].
- apply (GL2 (as_errno B) 4); [gsl_ing_x | lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  apply (gsl_blk_low_x ly S Hp W mem md out cap a HAR Hin); [lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq). lia.
Qed.

(* ---- (4) GSN_x (0x8386c): slot n was read and did not match. ---- *)
(* GSBODY / GSN over GSB_x (the cut's ghost list Hp1 after S1): GSL_x unfolds to GSBODY_x at nm = n
   (gsl_GSL_intro_x / gsl_GSL_elim_x are conversions). *)
Definition GSBODY_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf nm : nat) (W1 : world SEGS)
(regs1 : bvmap 5 word) ly1 S1 (Hp1 : list Z) (m1 : word -> option byte) md1 k1 e1 h1 out1 ev1 LB1 spent
(jb : nat) (a : drain_b_c.dadr) (o ha : RelayRunT.addr YO0i.sptr) (ks : list (RelayRunT.addr YO0i.sptr))
(tl : dtrace) (kd : gkind) (jj : nat) (bg : Z) : Prop :=
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 18 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 8 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 21 = w64 SHADOW_OFF /\
dr_frame RG cx W1 m1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 ((dxSA cx + 8) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 200) 8 (dxSA cx + 16) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 56) 8 (dxSA cx) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 48) 8 (dxSA cx + 24) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 64) 8 (dxSA cx + 32) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 8) 8 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 40) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 24) 8 (re_nheld e1) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 32) 8 (re_buf e1 + Z.of_nat p + Z.of_nat jj) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 40) 8 bg /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 72) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 80) 8 (re_hp e1) /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 19 = w64 ((re_hp e1 + 8 * Z.of_nat n) / 8 + SHADOW_OFF) /\
getr regs1 20 = w64 (8 * Z.of_nat n) /\
getr regs1 25 = w64 (8 * re_nheld e1) /\
getr regs1 27 = w64 (Z.of_nat jj) /\
(n + kf = length (re_keys e1))%nat /\ (0 < kf)%nat /\
(forall i, (i < nm)%nat -> nth i (dlH cx s1 p) [] <> firstn jj (dline s1 p q)) /\
0 <= bg < 2 ^ 64 /\ (bg = 0 <-> kd = GBegin) /\
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
GSF s1 p q /\
GSB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.

Definition GSN_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_hnext) regs1 m1 md1 /\
GSBODY_x cx Hp kr s1 D p q n kf (S n) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.

(* the stack facts every walk of the loop uses, from DBASE and the table block *)
Lemma gsl_stack_x : forall cx Hp kr, DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
alloc_ceiling + 2 * ESTACK + DRAIN_FRAME <= dsp0 cx /\ dsp0 cx <= 2 ^ 47 /\ dsp0 cx mod 16 = 0 /\
(dxj cx < 4)%nat.
Proof.
intros cx Hp kr HB.
pose proof HB as (Hafn & _ & _ & _ & _ & HBrest).
pose proof HBrest as (_ & _ & _ & Hj4 & _).
pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
fold (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK_x = 16976) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HDF : DRAIN_FRAME = 336) by reflexivity.
split; [lia|]. split; [lia|]. split; [exact Hal16 | exact Hj4].
Qed.


(* The pieces of this Section at a world relation R (route R): each <name>R below is <name> with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the cf rules and every carrier or statement it names
   -> their R twins; every other token is the strict text's. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNR := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

(* ---- (1) A match on a BEGIN: the line loop's core after the sent line is DLC_x at S q. ---- *)
Lemma gsl_dlc_same_xR : forall cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl,
GSF s1 p q ->
seen_arr (dlH cx s1 p) (dline s1 p q) = dlH cx s1 p ->
seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) = dlka cx s1 p ->
GSB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
DLC_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S q) ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.
Proof.
intros cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  (HB & HPQ & HQ & HNZ & HK & HL) EH EKA HGS.
destruct (gs_drl s1 p q HB HPQ HQ HNZ HK HL) as (E1 & _ & E3).
unfold DLC_xR. rewrite (gs_dlH cx s1 p q E1), (gs_dlka cx s1 p q E1), (gs_dlno s1 p q E1), (gs_dloc cx s1 p q E1).
rewrite EH, EKA, E3, E1.
unfold GSB_xR, GSno, GSoc in HGS.
unfold LCORE_xR in HGS |- *.
destruct HGS as (HMEM & HLINK & HSAME & HHIST & HRS & HBUD).
split; [exact HMEM|]. split; [exact HLINK|]. split; [exact HSAME|].
split; [|split; [exact HRS | exact HBUD]].
unfold DHIST in HHIST |- *.
destruct HHIST as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
do 8 (split; [assumption|]).
split.
- rewrite app_assoc, gs_upds_snoc.
  pose proof H8 as H8'. apply NoDup_ListNoDup in H8'.
  destruct (seen_arr_ok _ _ (dline s1 p q) H8' H9) as (_ & HS).
  unfold dvirt in HS |- *. cbn [drain_b_c.ds_H] in HS |- *. rewrite EH in HS. exact HS.
- split; [|exact H11]. lia.
Qed.
(* ---- (3) The cut survives the loop (the interceptors write only their scratch below drain's frame). ---- *)
Lemma gsl_core_kept_xR : forall cx Hp kr s1 D p q ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  m2 md2 k2,
alloc_ceiling + 2 * ESTACK + DRAIN_FRAME <= dsp0 cx -> dsp0 cx <= 2 ^ 47 -> (dxj cx < 4)%nat ->
4096 <= dxSA cx -> dxSA cx + 56 <= alloc_ceiling ->
GSB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k2 ->
GSKEEP cx W1 m1 m2 ->
GSB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q ly1 S1 Hp1 W1 m2 md2 k2 e1 h1 out1 ev1 LB1 spent tl.
Proof.
intros cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2 k2 HLOW HTOP HJ4 HSA1 HSA2 HGS HJ2 HKP.
pose proof HKP as (KEEP & PRES).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
unfold GSB_xR, LCORE_xR in HGS |- *.
destruct HGS as (HMEM & HLINK & HSAME & HHIST & HRS & HBUD).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR1 : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (KL : forall x, 0 <= x < alloc_ceiling -> aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x)
  by (intros x Hx; apply KEEP; lia).
assert (AK : forall fp, (forall r, In r fp -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling) ->
  akept W1 m1 W1 m2 fp) by (intros fp Hlow; exact (gs_akept_of W1 m1 m2 fp KL PRES Hlow)).
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (HBLK : forall b, In b (aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap
    (dvirt cx s1 false (dlH cx s1 p) (dlka cx s1 p) (GSno cx s1 p q) (GSoc cx s1 p q))) out1) ->
  In b (ablocks B ly1 S1)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact Hperm | right].
  apply in_or_app. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left; exact Hb|right].
  apply in_or_app. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left; exact Hb|right].
  apply in_or_app. left. exact Hb. }
split; [|split; [exact HLINK | split; [exact HSAME | split; [exact HHIST | split; [exact HRS | exact HBUD]]]]].
split; [exact HJ2|].
split.
{ intros x Hx. rewrite KL; [exact (Hrom x Hx)|].
  destruct Hx as (sg & Hsg & _ & Hr).
  pose proof (pa_img_range x ltac:(exists sg; split; [exact Hsg | exact Hr])). lia. }
split; [intros x Him Hno Her Hpz; exact (PRES x (Hpres x Him Hno Her Hpz))|].
split; [exact Hframes|].
split; [exact (gsl_frame_keep RG HGSB cx W1 m1 m2 ltac:(lia) HKP HFR)|].
split.
{ apply (gsl_garr8_kept W1 m1 W1 m2); [exact Hgarr|].
  intros x Hx. rewrite gsl_bzs_len in Hx. apply KL.
  assert (HL56 : length (entry_bytes e1) = 56%nat).
  { pose proof HOKX as (_ & _ & HQ1 & HQ2 & _). unfold entry_bytes.
    rewrite !length_app, HQ1, HQ2, !Mem.length_le8, !Mem.length_le4. reflexivity. }
  rewrite HL56 in Hx. unfold ATABLE, AENT in *. lia. }
split.
{ intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m2 _ (PRES _)). exact (Hawr i Hi). }
split.
{ eapply (gs_aentry_okx_kept B RG).
  - exact HOKX.
  - apply AK. exact (gsl_aentry_fp_low_x ly1 S1 Hp1 W1 m1 md1 e1 HAR1 HOKX).
  - intros b Hb. apply HBLK. apply in_or_app. left. exact Hb. }
split.
{ eapply asrc_at_kept.
  - exact Hsrc.
  - apply AK. apply (gsl_asrc_fp_low_x ly1 S1 Hp1 W1 m1 md1 (dHA RG cx) h1 HAR1 Hsrc);
      unfold dHA, ASRC in *; lia.
  - intros b Hb. apply HBLK. apply in_or_app. right. apply in_or_app. left. exact Hb. }
split.
{ pose proof HGSB as (Hg1 & Hg2 & _). unfold aothers_at in Hoth |- *.
  intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & Mf & Mo & Hfo).
  exists f, o. split; [|split; [|exact Hfo]];
  apply (gsl_vm_keep W1 m1 m2 _ 4%nat _); [| exact Mf | | exact Mo];
  intros x Hx; apply KL; apply (gsl_img_low RG HGSB x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia. }
split.
{ intros x Hx Hnx. destruct (Hgsk x Hx Hnx) as (Hv & Hw). split.
  - rewrite KL; [exact Hv|]. pose proof HGSB as (Hg1 & Hg2 & _).
    apply (gsl_img_low RG HGSB x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
  - intros Hwr. unfold arm. apply (writable_kept (w_H W1) m1 m2 _ (PRES _)). exact (Hw Hwr). }
split.
{ eapply aout_at_kept.
  - exact Hout.
  - apply AK. exact (gsl_aout_fp_low_x ly1 S1 Hp1 W1 m1 md1 _ _ _ _ _ _ HAR1 Hout).
  - intros b Hb. apply HBLK. apply in_or_app. right. apply in_or_app. right. exact Hb. }
split; [exact Hlivout | exact Hperm].
Qed.
(* ---- (4) GSN_x (0x8386c): slot n was read and did not match. ---- *)
(* GSBODY / GSN over GSB_x (the cut's ghost list Hp1 after S1): GSL_x unfolds to GSBODY_x at nm = n
   (gsl_GSL_intro_x / gsl_GSL_elim_x are conversions). *)
Definition GSBODY_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf nm : nat) (W1 : world SEGS)
(regs1 : bvmap 5 word) ly1 S1 (Hp1 : list Z) (m1 : word -> option byte) md1 k1 e1 h1 out1 ev1 LB1 spent
(jb : nat) (a : drain_b_c.dadr) (o ha : RelayRunT.addr YO0i.sptr) (ks : list (RelayRunT.addr YO0i.sptr))
(tl : dtrace) (kd : gkind) (jj : nat) (bg : Z) : Prop :=
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 18 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 8 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 21 = w64 SHADOW_OFF /\
dr_frame RG cx W1 m1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 ((dxSA cx + 8) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 200) 8 (dxSA cx + 16) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 56) 8 (dxSA cx) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 48) 8 (dxSA cx + 24) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 64) 8 (dxSA cx + 32) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 8) 8 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 40) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 24) 8 (re_nheld e1) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 32) 8 (re_buf e1 + Z.of_nat p + Z.of_nat jj) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 40) 8 bg /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 72) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 80) 8 (re_hp e1) /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 19 = w64 ((re_hp e1 + 8 * Z.of_nat n) / 8 + SHADOW_OFF) /\
getr regs1 20 = w64 (8 * Z.of_nat n) /\
getr regs1 25 = w64 (8 * re_nheld e1) /\
getr regs1 27 = w64 (Z.of_nat jj) /\
(n + kf = length (re_keys e1))%nat /\ (0 < kf)%nat /\
(forall i, (i < nm)%nat -> nth i (dlH cx s1 p) [] <> firstn jj (dline s1 p q)) /\
0 <= bg < 2 ^ 64 /\ (bg = 0 <-> kd = GBegin) /\
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
GSF s1 p q /\
GSB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.
Definition GSN_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_hnext) regs1 m1 md1 /\
GSBODY_xR cx Hp kr s1 D p q n kf (S n) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Lemma gsl_GSL_elim_xR : forall cx Hp kr s1 D p q n kf W1 c1,
GSL_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q n kf W1 c1 ->
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_hloop) regs1 m1 md1 /\
GSBODY_xR cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof. intros cx Hp kr s1 D p q n kf W1 c1 H. exact H. Qed.
Lemma gsl_GSL_intro_xR : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg,
GSBODY_xR cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
GSL_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q n kf W1 (cfg_at SEGS (BASE + A_dr_hloop) regs1 m1 md1).
Proof.
intros cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg H.
exists regs1, ly1, S1, Hp1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl, kd, jj, bg.
split; [reflexivity | exact H].
Qed.
(* the relay entry's place, from DBASE and the core's table block *)
Lemma gsl_sa_xR : forall cx Hp kr ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 s out1 ev1 sent LB1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 ->
4096 <= dxSA cx /\ dxSA cx + 56 <= alloc_ceiling.
Proof.
intros cx Hp kr ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 HB HM.
pose proof HB as (_ & _ & _ & HSAlo & HSAhi & _).
pose proof HM as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR HTB) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity). rewrite RQT in HGceil.
unfold ATABLE, AENT in *. lia.
Qed.
(* the body at the memory after a step of the loop that keeps every byte outside the interceptors' scratch *)
Lemma gsl_body_keep_xR : forall cx Hp kr s1 D p q n kf nm W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  m2 md2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
GSBODY_xR cx Hp kr s1 D p q n kf nm W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
GSKEEP cx W1 m1 m2 ->
GSBODY_xR cx Hp kr s1 D p q n kf nm W1 regs1 ly1 S1 Hp1 m2 md2 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof.
intros cx Hp kr s1 D p q n kf nm W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg m2 md2
  HB HBD HJ2 HKP.
destruct (gsl_stack_x cx Hp kr HB) as (HS1 & HS2 & _ & Hj4).
unfold GSBODY_xR in HBD |- *.
destruct HBD as (Hsp & R3 & R4 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64
  & M8 & M16 & M24 & M32 & M40 & M72 & M80 & R23 & R24 & R19 & R20 & R25 & R27
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (HMEM & _).
destruct (gsl_sa_xR cx Hp kr _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB HMEM) as (HSA1 & HSA2).
assert (HSPR : DRAIN_FRAME <= dsp0 cx <= 2 ^ 47) by (unfold ESTACK, DRAIN_FRAME in *; pose proof asan_consts as (C1 & _); lia).
do 7 (split; [assumption|]).
split; [exact (gsl_frame_keep RG HGSB cx W1 m1 m2 HSPR HKP HFR)|].
do 12 (split; [apply (gsl_fv_keep RG HGSB cx W1 m1 m2 _ _ HSPR); [lia | unfold DRAIN_FRAME; lia | exact HKP | assumption]|]).
do 14 (split; [assumption|]).
split; [|exact HFUT].
exact (gsl_core_kept_xR cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2 k1
  HS1 HS2 Hj4 HSA1 HSA2 HCORE HJ2 HKP).
Qed.
(* GSN from the head's body: the registers unchanged, slot n not matched *)
Lemma gsl_mk_gsn_xR : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY_xR cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
GSREGS regs1 regs2 -> getr regs2 19 = getr regs1 19 -> getr regs2 20 = getr regs1 20 ->
nth n (dlH cx s1 p) [] <> firstn jj (dline s1 p q) ->
GSBODY_xR cx Hp kr s1 D p q n kf (S n) W1 regs2 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof.
intros cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q21 & Q23 & Q24 & Q25 & Q27) Q19 Q20 Hn.
unfold GSBODY_xR in HBD |- *.
destruct HBD as (Hsp & R3 & R4 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64
  & M8 & M16 & M24 & M32 & M40 & M72 & M80 & R23 & R24 & R19 & R20 & R25 & R27
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hgest & Hjjr & HGSF & HCORE & HFUT).
unfold spZ in *. rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q21, Q23, Q24, Q25, Q27, Q19, Q20.
do 28 (split; [assumption|]).
split; [intros i Hi; destruct (Nat.eq_dec i n) as [->|Hne]; [exact Hn | apply Hnm; lia]|].
do 6 (split; [assumption|]). exact HFUT.
Qed.
(* the loop's head at S n from GSN at n, s3 and s4 stepped *)
Lemma gsl_mk_loop_xR : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY_xR cx Hp kr s1 D p q n (S kf) (S n) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
(0 < kf)%nat ->
GSREGS regs1 regs2 ->
getr regs2 19 = Z_to_bv 64 (bv_unsigned (getr regs1 19) + 1) ->
getr regs2 20 = Z_to_bv 64 (bv_unsigned (getr regs1 20) + 8) ->
GSBODY_xR cx Hp kr s1 D p q (S n) kf (S n) W1 regs2 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof.
intros cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD Hkf0 (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q21 & Q23 & Q24 & Q25 & Q27) Q19 Q20.
unfold GSBODY_xR in HBD |- *.
destruct HBD as (Hsp & R3 & R4 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64
  & M8 & M16 & M24 & M32 & M40 & M72 & M80 & R23 & R24 & R19 & R20 & R25 & R27
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (HMEM & _).
pose proof HMEM as (HJ & _ & _ & _ & _ & _ & _ & HOKX & _).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HOKX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hnheld & Hheld & _).
assert (HHPR : 0 <= re_hp e1 < 2 ^ 47).
{ pose proof asan_consts as (C1 & _).
  destruct Hheld as [(Hz & _)|(Hz & Hin & Hk1 & Hk2 & _)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_hp e1) (re_kh e1) HAR Hin) as (_ & H4 & Hc & _).
  pose proof (req_size_pos (re_kh e1) ltac:(lia)) as (Hr1 & Hr2). lia. }
unfold spZ in *. rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q21, Q23, Q24, Q25, Q27, Q19, Q20, R19, R20.
unfold re_nheld in Hnheld.
do 22 (split; [assumption|]).
split.
{ assert (Hd : 0 <= (re_hp e1 + 8 * Z.of_nat n) / 8 <= re_hp e1 + 8 * Z.of_nat n)
    by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
  f_equal. rewrite <- (gsl_div8_succ RG). lia. }
split; [unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
do 2 (split; [assumption|]).
split; [lia|]. split; [exact Hkf0|].
do 7 (split; [assumption|]). exact HFUT.
Qed.
(* GA from GSN at the last slot: the spilled registers back *)
Lemma gsl_mk_ga_xR : forall cx Hp kr s1 D p q n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY_xR cx Hp kr s1 D p q n 1 (S n) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 21 = getr regs1 21 -> getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 ->
getr regs2 22 = w64 (dxSA cx) -> getr regs2 27 = w64 (dxSA cx + 24) ->
getr regs2 25 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj) -> getr regs2 19 = w64 bg ->
getr regs2 10 = w64 (re_nheld e1) -> getr regs2 11 = w64 (re_nheld e1) ->
getr regs2 12 = w64 ((dxSA cx + 40) / 8) ->
GA_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W1 (cfg_at SEGS (BASE + A_dr_add) regs2 m1 md1).
Proof.
intros cx Hp kr s1 D p q n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD Q2 Q3 Q4 Q8 Q9 Q18 Q21 Q23 Q24 Q22 Q27 Q25 Q19 Q10 Q11 Q12.
unfold GSBODY_xR in HBD.
destruct HBD as (Hsp & R3 & R4 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64
  & M8 & M16 & M24 & M32 & M40 & M72 & M80 & R23 & R24 & R19 & R20 & R25 & R27
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hgest & Hjjr & HGSF & HCORE & HFUT).
exists regs2, ly1, S1, Hp1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl, kd, jj, bg.
split; [reflexivity|].
split.
{ unfold dregs_line, spZ in *. rewrite Q2, Q3, Q4, Q18, Q9, Q8, Q21, Q22, Q27.
  do 9 (split; [first [assumption | reflexivity]|]). split; [exact HFR|]. do 4 (split; [assumption|]). exact M64. }
rewrite Q23, Q24.
do 12 (split; [assumption|]).
split.
{ apply gs_index_none. intros i Hi. apply Hnm.
  pose proof HCORE as (_ & HLINK & _).
  rewrite <- (gsl_link_H _ _ _ _ _ _ _ _ _ HLINK), gs_keys_texts_len in Hi. lia. }
split; [exact HGSF|]. split; [exact HCORE | exact HFUT].
Qed.
(* GSN from the head's body at a later memory: slot n not matched *)
Lemma gsl_exit_gsn_xR : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2 m2 md2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
GSBODY_xR cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
GSKEEP cx W1 m1 m2 ->
GSREGS regs1 regs2 -> getr regs2 19 = getr regs1 19 -> getr regs2 20 = getr regs1 20 ->
nth n (dlH cx s1 p) [] <> firstn jj (dline s1 p q) ->
GSN_xR cx Hp kr s1 D p q n kf W1 (cfg_at SEGS (BASE + A_dr_hnext) regs2 m2 md2).
Proof.
intros cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2 m2 md2
  HB HBD HJ HKP HR Q19 Q20 Hn.
exists regs2, ly1, S1, Hp1, m2, md2, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl, kd, jj, bg.
split; [reflexivity|].
apply (gsl_mk_gsn_xR cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m2 md2 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2);
  [| exact HR | exact Q19 | exact Q20 | exact Hn].
exact (gsl_body_keep_xR cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  m2 md2 HB HBD HJ HKP).
Qed.
(* a BEGIN whose key is held at slot n: DLN (S q), the registers s6 / s11 back *)
Lemma gsl_mk_dln_xR : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY_xR cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q) -> bg = 0 ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 21 = getr regs1 21 -> getr regs2 23 = getr regs1 23 ->
getr regs2 22 = w64 (dxSA cx) -> getr regs2 27 = w64 (dxSA cx + 24) ->
DLN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S q) W1 (cfg_at SEGS (BASE + A_dr_next) regs2 m1 md1).
Proof.
intros cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD Hmt Hbg0 Q2 Q3 Q4 Q8 Q9 Q18 Q21 Q23 Q22 Q27.
unfold GSBODY_xR in HBD.
destruct HBD as (Hsp & R3 & R4 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64
  & M8 & M16 & M24 & M32 & M40 & M72 & M80 & R23 & R24 & R19 & R20 & R25 & R27
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (_ & HLINK & _).
assert (Hkd : kd = GBegin) by (apply Hbgk; exact Hbg0). subst kd.
assert (Hlen : (n < length (dlH cx s1 p))%nat)
  by (rewrite <- (gsl_link_H _ _ _ _ _ _ _ _ _ HLINK), gs_keys_texts_len; lia).
pose proof (gs_index_some _ _ n Hlen Hmt Hnm) as HI.
destruct (gs_seen_begin_old (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) _ n jb ha ks Hgest HI) as (S1e & S2e & S3e).
pose proof HGSF as (Hbd & Hpq & Hq0 & _).
exists regs2, ly1, S1, Hp1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
split; [reflexivity|].
split.
{ unfold dregs_line, spZ in *. rewrite Q2, Q3, Q4, Q18, Q9, Q8, Q21, Q22, Q27.
  do 9 (split; [first [assumption | reflexivity]|]). split; [exact HFR|]. do 4 (split; [assumption|]). exact M64. }
split; [rewrite Q23, R23; unfold w64; f_equal; lia|].
split; [unfold dbound; split; [lia|right]; replace (S q - 1)%nat with q by lia; exact Hq0|].
split; [lia|].
split; [exact (gsl_dlc_same_xR cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl HGSF S1e S3e HCORE)|].
exact (gsl_dlfut_same cx s1 p q a jb o ha ks tl HGSF S2e S1e S3e HFUT).
Qed.
(* an END whose key is held at slot n: GF *)
Lemma gsl_mk_gf_xR : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY_xR cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q) -> bg <> 0 ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 21 = getr regs1 21 -> getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 ->
getr regs2 19 = getr regs1 19 -> getr regs2 20 = getr regs1 20 ->
getr regs2 22 = w64 (dxSA cx) -> getr regs2 27 = w64 (dxSA cx + 24) ->
getr regs2 26 = w64 (re_hp e1 + 8 * Z.of_nat n) ->
GF_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W1 (cfg_at SEGS (BASE + A_dr_free) regs2 m1 md1).
Proof.
intros cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD Hmt Hbg0 Q2 Q3 Q4 Q8 Q9 Q18 Q21 Q23 Q24 Q19 Q20 Q22 Q27 Q26.
unfold GSBODY_xR in HBD.
destruct HBD as (Hsp & R3 & R4 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64
  & M8 & M16 & M24 & M32 & M40 & M72 & M80 & R23 & R24 & R19 & R20 & R25 & R27
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (_ & HLINK & _).
assert (Hkd : kd = GEnd) by (destruct kd; [exfalso; apply Hbg0; apply Hbgk; reflexivity | reflexivity]). subst kd.
assert (Hlen : (n < length (dlH cx s1 p))%nat)
  by (rewrite <- (gsl_link_H _ _ _ _ _ _ _ _ _ HLINK), gs_keys_texts_len; lia).
pose proof (gs_index_some _ _ n Hlen Hmt Hnm) as HI.
exists regs2, ly1, S1, Hp1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl, jj, n.
split; [reflexivity|].
split.
{ unfold dregs_line, spZ in *. rewrite Q2, Q3, Q4, Q18, Q9, Q8, Q21, Q22, Q27.
  do 9 (split; [first [assumption | reflexivity]|]). split; [exact HFR|]. do 4 (split; [assumption|]). exact M64. }
rewrite Q23, Q24, Q19, Q20, Q26.
do 7 (split; [first [assumption | reflexivity]|]).
split; [lia|].
do 4 (split; [assumption|]).
split; [exact HCORE | exact HFUT].
Qed.
(* ---- The loop's bottom: GSN n (S kf) -> GSL (S n) kf when a slot is left, GA when none is. ---- *)
Lemma gsl_tail_xR : forall cx Hp kr s1 D p q n kf W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GSN_xR cx Hp kr s1 D p q n (S kf) W1 c1 ->
(forall W2 c2, GA_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
((0 < kf)%nat -> forall c2, GSL_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q (S n) kf W1 c2 ->
   SRrG SEGS R W1 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).
Proof.
intros cx Hp kr s1 D p q n kf W1 c1 HB HGN HGA HGL.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HGN as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & oo & ha & ks & tl
  & kd & jj & bg & Hcfg & HBD).
destruct (gsl_stack_x cx Hp kr HB) as (HSTK1 & HSTK2 & Hal16 & Hj4).
pose proof HBD as (Hsp & R3 & R4 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64
  & M8 & M16 & M24 & M32 & M40 & M72 & M80 & R23 & R24 & R19 & R20 & R25 & R27
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (HMEM & HLINK & _).
pose proof HMEM as (HJ & _ & _ & _ & _ & _ & _ & HOKX & _).
destruct (gsl_sa_xR cx Hp kr _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB HMEM) as (HSA1 & HSA2).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HOKX as (_ & _ & _ & _ & _ & _ & HUlen & Husedr & Hbufc & Hnheld & _).
pose proof (gsl_link_U _ _ _ _ _ _ _ _ _ HLINK) as HUW.
assert (HUL : re_used e1 = Z.of_nat (length (dW s1))) by (rewrite <- HUW, gsl_bzs_len; lia).
pose proof HGSF as (_ & Hpq & _).
assert (HLJ : 0 <= re_buf e1 + Z.of_nat p + Z.of_nat jj < 2 ^ 64).
{ destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & _)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hbin) as (_ & HB4096 & HBceil & _).
  assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
  rewrite RQC in HBceil. lia. }
assert (HNHR : 0 <= re_nheld e1 < 2 ^ 26) by (split; [unfold re_nheld; lia | exact Hnheld]).
assert (HS40 : 0 <= (dxSA cx + 40) / 8 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (gn_entry RG W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) ((dxSA cx + 40) / 8) (re_nheld e1)
  (re_buf e1 + Z.of_nat p + Z.of_nat jj) bg Hsp ltac:(unfold ESTACK, DRAIN_FRAME in *; lia)
  ltac:(unfold DRAIN_FRAME in *; lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)
  ltac:(lia) ltac:(lia) HS40 ltac:(lia) HLJ Hbgr M16 M24 M32 M40 M48 M56) as HS.
remember (Eimg (Ereg regs1 (gn_extra (dxSA cx) ((dxSA cx + 40) / 8) (re_nheld e1)
  (re_buf e1 + Z.of_nat p + Z.of_nat jj) bg))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n0 r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 ((dxSA cx + 40) / 8)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_nheld e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (re_buf e1 + Z.of_nat p + Z.of_nat jj)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 bg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E20 : ew E 20 = Z_to_bv 64 (8 * Z.of_nat n)) by (rewrite (EREG 20%nat 20%bv ltac:(lia) eq_refl), R20; reflexivity).
assert (E25 : ew E 25 = Z_to_bv 64 (8 * re_nheld e1)) by (rewrite (EREG 25%nat 25%bv ltac:(lia) eq_refl), R25; reflexivity).
assert (SHOK : sh_ok SEGS gn_Bx [] E (mrestrict (w_H W1) m1)) by constructor.
clear HE.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_hnext)) with (Z_to_bv 64 (BASE + A_dr_hnext)).
paj_run_tok_xR RUNR HS HJ SHOK gn_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
match goal with Hg : mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ms)) |- _ => rename Hg into GR1 end.
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ms)) |- _ => rename Hf into HFr1 end.
assert (Hn8 : 0 <= 8 * Z.of_nat n + 8 < 2 ^ 64) by (unfold re_nheld in HNHR; lia).
assert (Hh8 : 0 <= 8 * re_nheld e1 < 2 ^ 64) by lia.
psrr_branch_tok RUNR BRR HS SHOK gn_Bspan.
- (* a slot is left (8 nheld <> 8 (n + 1)): back to the loop's head at S n *)
  rewrite branch_ne_U, (U_atom E 25 (8 * re_nheld e1) E25 Hh8), (U_atom_off E 20 (8 * Z.of_nat n) 8 E20 ltac:(lia) Hn8) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hkf0 : (0 < kf)%nat) by (clear - Hc Hnk; unfold re_nheld in Hc; lia).
  paj_run_to_tok_xR RUNTOR HS HJ SHOK gn_Bspan A_dr_hloop. { apply awr_ok_x_of0. awr_ok_tac. }
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem ms)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hf into HFrF end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem ms)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hg into GRF end.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) PX24. prreg HS (25%bv : bv 5) P25.
  prreg HS (27%bv : bv 5) P27.
  repeat rewrite wvb_collapse in HJ.
  match goal with |- SRrG _ R _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
  assert (HKP : GSKEEP cx W1 m1 (ms_mem msF)).
  { split.
    - intros y Hy _. rewrite (gsl_frame_nil RG HGSB _ _ _ _ _ HFrF ltac:(vm_compute; reflexivity) y Hy).
      exact (gsl_frame_nil RG HGSB _ _ _ _ _ HFr1 ltac:(vm_compute; reflexivity) y Hy).
    - intros y Hpz. exact (apresent_grows _ _ _ y GRF (apresent_grows _ _ _ y GR1 Hpz)). }
  clear HS SHOK HFrF HFr1.
  assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew E k -> Nat.ltb k 32 = true ->
    Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
  { intros r k Hr Hk Hkr. rewrite Hr. apply EREG; [apply Nat.ltb_lt; exact Hk | exact Hkr]. }
  apply (HGL Hkf0).
  apply (gsl_GSL_intro_xR cx Hp kr s1 D p q (S n) kf W1 (ms_regs msF) ly1 S1 Hp1 (ms_mem msF) mdF k1 e1 h1 out1 ev1 LB1 spent jb aa oo
    ha ks tl kd jj bg).
  apply (gsl_mk_loop_xR cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 (ms_mem msF) mdF k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg
    (ms_regs msF)).
  + exact (gsl_body_keep_xR cx Hp kr s1 D p q n (S kf) (S n) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl
      kd jj bg (ms_mem msF) mdF HB HBD HJ HKP).
  + exact Hkf0.
  + split; [exact (RK _ 2%nat P2 eq_refl eq_refl)|]. split; [exact (RK _ 3%nat P3 eq_refl eq_refl)|].
    split; [exact (RK _ 4%nat P4 eq_refl eq_refl)|]. split; [exact (RK _ 8%nat P8 eq_refl eq_refl)|].
    split; [exact (RK _ 9%nat P9 eq_refl eq_refl)|]. split; [exact (RK _ 18%nat P18 eq_refl eq_refl)|].
    split; [exact (RK _ 21%nat P21 eq_refl eq_refl)|]. split; [exact (RK _ 23%nat P23 eq_refl eq_refl)|].
    split; [exact (RK _ 24%nat PX24 eq_refl eq_refl)|]. split; [exact (RK _ 25%nat P25 eq_refl eq_refl)|].
    exact (RK _ 27%nat P27 eq_refl eq_refl).
  + rewrite P19, (EREG 19%nat 19%bv (proj1 (Nat.ltb_lt 19 32) eq_refl) eq_refl). reflexivity.
  + rewrite P20, (EREG 20%nat 20%bv (proj1 (Nat.ltb_lt 20 32) eq_refl) eq_refl). reflexivity.
- (* no slot is left (8 nheld = 8 (n + 1)): the registers back, on to GA *)
  rewrite branch_ne_U, (U_atom E 25 (8 * re_nheld e1) E25 Hh8), (U_atom_off E 20 (8 * Z.of_nat n) 8 E20 ltac:(lia) Hn8) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hkf0 : kf = 0%nat) by (clear - Hc Hnk; unfold re_nheld in Hc; lia). subst kf.
  paj_run_to_tok_xR RUNTOR HS HJ SHOK gn_Bspan A_dr_add. { apply awr_ok_x_of0. awr_ok_tac. }
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem ms)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hf into HFrF end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem ms)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hg into GRF end.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) PX24.
  prreg HS (25%bv : bv 5) P25. prreg HS (27%bv : bv 5) P27.
  prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
  repeat rewrite wvb_collapse in HJ.
  match goal with |- SRrG _ R _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
  assert (HKP : GSKEEP cx W1 m1 (ms_mem msF)).
  { split.
    - intros y Hy _. rewrite (gsl_frame_nil RG HGSB _ _ _ _ _ HFrF ltac:(vm_compute; reflexivity) y Hy).
      exact (gsl_frame_nil RG HGSB _ _ _ _ _ HFr1 ltac:(vm_compute; reflexivity) y Hy).
    - intros y Hpz. exact (apresent_grows _ _ _ y GRF (apresent_grows _ _ _ y GR1 Hpz)). }
  clear HS SHOK HFrF HFr1.
  assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew E k -> Nat.ltb k 32 = true ->
    Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
  { intros r k Hr Hk Hkr. rewrite Hr. apply EREG; [apply Nat.ltb_lt; exact Hk | exact Hkr]. }
  apply HGA.
  apply (gsl_mk_ga_xR cx Hp kr s1 D p q n W1 regs1 ly1 S1 Hp1 (ms_mem msF) mdF k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg
    (ms_regs msF)
    (gsl_body_keep_xR cx Hp kr s1 D p q n 1 (S n) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl
      kd jj bg (ms_mem msF) mdF HB HBD HJ HKP)
    (RK _ 2%nat P2 eq_refl eq_refl) (RK _ 3%nat P3 eq_refl eq_refl) (RK _ 4%nat P4 eq_refl eq_refl)
    (RK _ 8%nat P8 eq_refl eq_refl) (RK _ 9%nat P9 eq_refl eq_refl) (RK _ 18%nat P18 eq_refl eq_refl)
    (RK _ 21%nat P21 eq_refl eq_refl) (RK _ 23%nat P23 eq_refl eq_refl) (RK _ 24%nat PX24 eq_refl eq_refl)).
  + rewrite P22, E32. reflexivity.
  + rewrite P27, E32, unsigned_lit_small by (clear - HSA1 HSA2 C1; lia). reflexivity.
  + rewrite P25, E35. reflexivity.
  + rewrite P19, E36. reflexivity.
  + rewrite P10, E34. reflexivity.
  + rewrite P11, E34. reflexivity.
  + rewrite P12, E33. reflexivity.
Qed.
(* ---- The loop's body: GSL n (S kf) -> GSN n (S kf) (no match at slot n), DLN (S q) (a begin held at slot n)
   or GF (an end held at slot n). ---- *)
Lemma gsl_body_xR : forall cx Hp kr s1 D p q n kf W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GSL_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q n (S kf) W1 c1 ->
(forall W2 c2, DLN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S q) W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall W2 c2, GF_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall c2, GSN_xR cx Hp kr s1 D p q n (S kf) W1 c2 -> SRrG SEGS R W1 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).
Proof.
intros cx Hp kr s1 D p q n kf W1 c1 HB HGL HDLN HGF HGN.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@ASAN_CEIL_range rc) as (HAC & _). unfold ASAN_CEIL in HAC.
destruct (gsl_GSL_elim_xR _ _ _ _ _ _ _ _ _ _ _ HGL) as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1
  & spent & jb & aa & oo & ha & ks & tl & kd & jj & bg & Hcfg & HBD).
clear HGL.
destruct (gsl_stack_x cx Hp kr HB) as (HSTK1 & HSTK2 & Hal16 & Hj4).
pose proof HBD as (Hsp & R3 & R4 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64
  & M8 & M16 & M24 & M32 & M40 & M72 & M80 & R23 & R24 & R19 & R20 & R25 & R27
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (HMEM & HLINK & _).
pose proof HMEM as (HJ & Hrom & _ & _ & _ & _ & _ & HOKX & _).
destruct (gsl_sa_xR cx Hp kr _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB HMEM) as (HSA1 & HSA2).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HOKX as (_ & _ & _ & _ & _ & Hcapr & HUlen & Husedr & Hbufc & Hnheld & Hheld & _ & _ & Hkeys).
assert (Hnlen : (n < length (re_keys e1))%nat) by lia.
destruct Hheld as [(Hz & Hk0) | (Hz & Hin & Hk1 & Hk2 & Hg8)]; [rewrite Hk0 in Hnlen; cbn [length] in Hnlen; lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_hp e1) (re_kh e1) HAR Hin) as (HH16 & HH4096 & HHceil & HHia & _).
assert (Hrq : re_kh e1 <= req_size (re_kh e1)) by (unfold req_size; destruct (Z.eqb_spec (re_kh e1) 0); lia).
assert (HHP8 : re_hp e1 mod 8 = 0).
{ rewrite (Z.div_mod (re_hp e1) 16) by lia. rewrite HH16, Z.add_0_r.
  replace (16 * (re_hp e1 / 16)) with ((2 * (re_hp e1 / 16)) * 8) by lia. apply Z.mod_mul. lia. }
set (kn := nth n (re_keys e1) (0, [], [])).
assert (Hkn : In kn (re_keys e1)) by (apply nth_In; exact Hnlen).
rewrite Forall_forall in Hkeys. destruct (Hkeys kn Hkn) as (HKin & HKg & HKnz & HKlen).
unfold APARTIAL in HKlen.
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (key_addr kn) (Z.of_nat (length (key_text kn)) + 1) HAR HKin)
  as (HK16 & HK4096 & HKceil & HKia & _).
assert (RQK : req_size (Z.of_nat (length (key_text kn)) + 1) = Z.of_nat (length (key_text kn)) + 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (key_text kn)) + 1) 0); lia).
rewrite RQK in HKceil, HKia.
pose proof (gsl_slot_val W1 m1 (re_hp e1) (re_keys e1) n Hg8 Hnlen ltac:(change (nth n (re_keys e1) (0, [], [])) with kn; lia))
  as MSL. fold kn in MSL.
pose proof (gsl_link_U _ _ _ _ _ _ _ _ _ HLINK) as HUW.
assert (HUL : re_used e1 = Z.of_nat (length (dW s1))) by (rewrite <- HUW, gsl_bzs_len; lia).
pose proof HGSF as (Hbd & Hpq & Hq0 & Hnzl & Hskp & Hlim).
assert (Hcap0 : re_cap e1 <> 0) by (intros Hc; rewrite Hc in Husedr; lia).
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjunk & Hbuf8)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hbin) as (HB16 & HB4096 & HBceil & HBia & _).
assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQC in HBceil, HBia.
pose proof (gsl_line_garr8 RG HGSB W1 m1 s1 p q e1 Hbuf8 HUW ltac:(lia)) as HLg.
unfold re_nheld in Hnheld, Hk1.
pose proof (gl_entry RG HGSB W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (re_hp e1) n (key_addr kn) (dxSA cx) bg
  Hsp ltac:(unfold ESTACK, DRAIN_FRAME in *; lia) ltac:(unfold DRAIN_FRAME in *; lia)
  ltac:(rewrite Zminus_mod, Hal16; reflexivity) R21 R20 ltac:(lia) R19
  HH4096 HHP8 ltac:(unfold GL_PHI; lia) ltac:(unfold ESTACK, DRAIN_FRAME in *; lia) ltac:(unfold GL_PHI; lia)
  HSA1 ltac:(unfold GL_PHI; lia) Hbgr M40 M48 M56 M80 MSL) as HS.
remember (Eimg (Ereg regs1 (gl_extra (re_hp e1) (re_hp e1 + 8 * Z.of_nat n) (key_addr kn) (dxSA cx) bg))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall k (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r).
{ intros k r Hk Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EREG 21%nat 21%bv ltac:(lia) eq_refl); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 (re_hp e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (key_addr kn)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (dxSA cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 bg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (SHOK : sh_ok SEGS gl_Bx gl_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E gl_Bx 33 (re_hp e1 + 8 * Z.of_nat n) 8 (re_hp e1 + 8 * Z.of_nat n) 0 8).
  - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (re_hp e1) (re_kh e1));
      [exact HAR | exact Hin | lia | lia].
  - unfold gl_Bx. rewrite (U_atom E 21 SHADOW_OFF E21) by (unfold SHADOW_OFF; lia). reflexivity.
  - apply (U_atom E 33 _ E33). lia.
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia. }
clear HE.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_hloop)) with (Z_to_bv 64 (BASE + A_dr_hloop)).
paj_run_tok_xR RUNR HS HJ SHOK gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10.
match goal with Hg : mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ms)) |- _ => rename Hg into GR1 end.
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ms)) |- _ => rename Hf into HFr1 end.
assert (KEEP1 : forall y, 0 <= y < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) y = aview SEGS (w_H W1) m1 y)
  by (intros y Hy; exact (gsl_frame_nil RG HGSB _ _ _ _ _ HFr1 ltac:(vm_compute; reflexivity) y Hy)).
clear HFr1.
set (mdm := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody mdm.
assert (HARm : ARx ly1 S1 Hp1 W1 (ms_mem ms) mdm) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (ROM1 : rom_view SEGS W1 (ms_mem ms)).
{ intros y Hy. rewrite KEEP1; [exact (Hrom y Hy)|].
  destruct Hy as (sg & Hsg & _ & Hr). pose proof (pa_img_range y ltac:(exists sg; split; [exact Hsg | exact Hr])). lia. }
pose proof HB as (Hafn & _). pose proof Hafn as (_ & _ & _ & Hgp & Htp & _).
assert (Usp1 : spZ (ms_regs ms) = dsp0 cx - DRAIN_FRAME)
  by (unfold spZ; rewrite Q2, (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
assert (G3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, (EREG 3%nat 3%bv ltac:(lia) eq_refl), R3; exact Hgp).
assert (G4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, (EREG 4%nat 4%bv ltac:(lia) eq_refl), R4; exact Htp).
set (x := key_addr kn) in *. set (klen := Z.of_nat (length (key_text kn))) in *.
assert (G10 : getr (ms_regs ms) 10 = w64 x) by (rewrite Q10, E34; reflexivity).
assert (HKg1 : garr8 SEGS (arm W1 (ms_mem ms)) x (bzs (key_text kn ++ [Z_to_bv 8 0]))).
{ apply (gsl_garr8_kept W1 m1 W1 (ms_mem ms)); [exact HKg|]. intros y Hy. apply KEEP1.
  rewrite gsl_bzs_len, length_app in Hy. cbn [length] in Hy. lia. }
assert (HKL : Z.to_nat klen = length (key_text kn)) by (unfold klen; lia).
assert (HDF : DRAIN_FRAME = 336) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HDS : DRAIN_STK_x = 16976) by reflexivity.
(* strlen (held[n]) *)
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_DR B RG) 0 ([] : list (Z * Z)) (2 * ESTACK) (SIGMA WS_strlen)
    (fun _ => False) (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 klen)
    W1 (ms_regs ms) (ms_mem ms) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx)
    ([] : list (Z * Z)) ly1 S1 Hp1 _ k1 (- DRAIN_FRAME) (Z_to_bv 64 (BASE + 5480)) HG eq_refl HJ).
  - rewrite Usp1. lia.
  - rewrite HDF. reflexivity.
  - lia.
  - lia.
  - lia.
  - exact G3.
  - exact G4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros _. right. intros [].
  - intros y [].
  - intros y [].
  - intros HPRE HSC. eapply SRr_mono.
    { refine (ASTRLEN ly1 S1 Hp1 W1 (ms_regs ms) (ms_mem ms) mdm x klen HPRE (proj1 HSC) (proj2 HSC) G10
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) _ _ _ _ _ _ _ _ ROM1).
      - apply (gsl_first_byte W1 (ms_mem ms) x (bzs (key_text kn ++ [Z_to_bv 8 0])) (klen + 1) klen HKg1).
        + lia.
        + rewrite gsl_bzs_len, length_app. cbn [length]. lia.
        + intros i Hi. apply (gsl_key_nz _ HKnz). lia.
        + intros _. rewrite HKL. apply gsl_key_z.
      - intros y Hy. split.
        + replace y with (x + Z.of_nat (Z.to_nat (y - x))) by lia.
          rewrite (gsl_aview_garr8 W1 (ms_mem ms) x _ _ HKg1); [discriminate|].
          rewrite gsl_bzs_len, length_app. cbn [length]. lia.
        + rewrite Usp1. lia.
      - intros y Hy. rewrite Usp1. lia.
      - unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HKia |- *. lia.
      - apply (amem_range_near_block_x B ARx RG LAWS HGSB ly1 S1 Hp1 W1 (ms_mem ms) mdm x (klen + 1) x HARm HKin); [lia|].
        rewrite RQK. lia.
      - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms) mdm x (klen + 1)); [exact HARm | exact HKin | lia | rewrite RQK; lia].
      - apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms) mdm x (klen + 1)); [exact HARm | exact HKin | lia | rewrite RQK; lia | lia].
      - intros y Hy. apply (alloc_tail_x SEGS B ARx LAWS ly1 S1 Hp1 W1 (ms_mem ms) mdm x (klen + 1) y HARm HKin). rewrite RQK.
        replace (x + (klen + 1) - 1) with (x + klen) by lia. exact Hy. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpr).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|]. split; [exact Hres|].
    split; [intros y Hy _ Hs; exact (Hfr y Hy Hs) | exact Hpr]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres & Hfr2 & Hpres2).
jafter_call_keep_pi HS 37%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0%nat] HS2.
assert (Usp0 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
assert (HRK : region_kept SEGS E (ms_mem (restrict (w_H W1) ms)) (mrestrict (w_H W1) mem2) gl_frame).
{ split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi gl_frame base_val]; rewrite Usp0;
    intros y Hy; [|lia].
  change (ms_mem (restrict (w_H W1) ms)) with (mrestrict (w_H W1) (ms_mem ms)).
  apply (mbyte_of_aview SEGS). apply Hfr2; [clear - Hy HSTK1 HSTK2 C1; unfold ESTACK, DRAIN_FRAME in *; lia | intros [] | clear - Hy; unfold ESTACK in *; lia]. }
specialize (HS2 ltac:(constructor; [exact HRK | constructor])).
clear HS HRK. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 37 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 37)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
prreg HS (10%bv : bv 5) R10b.
assert (A41 : ew Ea 41 = Z_to_bv 64 klen) by (rewrite <- R10b, Hres; reflexivity).
assert (A27 : ew Ea 27 = Z_to_bv 64 (Z.of_nat jj))
  by (rewrite (OLDa 27%nat ltac:(lia)), (EREG 27%nat 27%bv ltac:(lia) eq_refl), R27; reflexivity).
assert (SHOK2 : sh_ok SEGS gl_Bx [] Ea (mrestrict (w_H W1) mem2)) by constructor.
assert (KEEP2 : GSKEEP cx W1 m1 mem2).
{ split.
  - intros y Hy Hs. rewrite (Hfr2 y Hy (fun H => H) ltac:(clear - Hs; unfold ESTACK in *; lia)). exact (KEEP1 y Hy).
  - intros y Hpz. apply Hpres2. exact (apresent_grows _ _ _ y GR1 Hpz). }
clear KEEP1 Hfr2.
paj_run_tok_xR RUNR HS HJ2 SHOK2 gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) mem2) (mrestrict (w_H W1) (ms_mem ?mx)) |- _ => rename Hf into HFrB; rename mx into msB end.
match goal with Hg : mem_grows (mrestrict (w_H W1) mem2) (mrestrict (w_H W1) (ms_mem msB)) |- _ => rename Hg into GRB end.
assert (KEEPB : GSKEEP cx W1 m1 (ms_mem msB)).
{ apply (gsl_keep_trans cx W1 m1 mem2 (ms_mem msB) KEEP2). split.
  - intros y Hy _. exact (gsl_frame_nil RG HGSB _ _ _ _ _ HFrB ltac:(vm_compute; reflexivity) y Hy).
  - intros y Hpz. exact (apresent_grows _ _ _ y GRB Hpz). }
clear HFrB.
assert (Hk64 : 0 <= klen < 2 ^ 64) by (clear - HKlen; unfold klen; lia).
assert (Hj64 : 0 <= Z.of_nat jj < 2 ^ 64) by (clear - Hjjr Hpq HUL Husedr HBceil HB4096 C1; lia).
psrr_branch_tok RUNR BRR HS SHOK2 gl_Bspan.
- (* |held[n]| <> jj: no match at slot n *)
  rewrite branch_ne_U, (U_atom Ea 41 klen A41 Hk64), (U_atom Ea 27 (Z.of_nat jj) A27 Hj64) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok_xR RUNTOR HS HJ2 SHOK2 gl_Bspan A_dr_hnext. { apply awr_ok_x_of0. awr_ok_tac. }
  match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hf into HFrF end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hg into GRF end.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. gsl_prreg_raw_x HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) PX24. prreg HS (25%bv : bv 5) P25.
  prreg HS (27%bv : bv 5) P27.
  repeat rewrite wvb_collapse in HJ2.
  match goal with |- SRrG _ R _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
  assert (HKP : GSKEEP cx W1 m1 (ms_mem msF)).
  { apply (gsl_keep_trans cx W1 m1 (ms_mem msB) (ms_mem msF) KEEPB). split.
    - intros y Hy _. exact (gsl_frame_nil RG HGSB _ _ _ _ _ HFrF ltac:(vm_compute; reflexivity) y Hy).
    - intros y Hpz. exact (apresent_grows _ _ _ y GRF Hpz). }
  clear HS SHOK2 HFrF.
  assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Ea k -> Nat.ltb k 32 = true ->
    Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
  { intros r k Hr Hk Hkr. apply Nat.ltb_lt in Hk. rewrite Hr, (OLDa k ltac:(lia)). apply EREG; [exact Hk | exact Hkr]. }
  assert (P19' : getr (ms_regs msF) 19 = getr regs1 19).
  { rewrite P19, denot_lit_U, R19.
    change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 0) (SLit 3)) (SOff 21 0)) with (gl_shE 33).
    rewrite (gl_U_shadow RG HGSB Ea 33 (re_hp e1 + 8 * Z.of_nat n)); [reflexivity | | |].
    - rewrite (OLDa 33%nat ltac:(lia)). exact E33.
    - rewrite (OLDa 21%nat ltac:(lia)). exact E21.
    - clear - HH4096 HHceil Hrq Hk1 Hnlen C1. lia. }
  apply HGN.
  apply (gsl_exit_gsn_xR cx Hp kr s1 D p q n (S kf) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg
    (ms_regs msF) (ms_mem msF) mdF HB HBD HJ2 HKP).
  + split; [exact (RK _ 2%nat P2 eq_refl eq_refl)|]. split; [exact (RK _ 3%nat P3 eq_refl eq_refl)|].
    split; [exact (RK _ 4%nat P4 eq_refl eq_refl)|]. split; [exact (RK _ 8%nat P8 eq_refl eq_refl)|].
    split; [exact (RK _ 9%nat P9 eq_refl eq_refl)|]. split; [exact (RK _ 18%nat P18 eq_refl eq_refl)|].
    split; [exact (RK _ 21%nat P21 eq_refl eq_refl)|]. split; [exact (RK _ 23%nat P23 eq_refl eq_refl)|].
    split; [exact (RK _ 24%nat PX24 eq_refl eq_refl)|]. split; [exact (RK _ 25%nat P25 eq_refl eq_refl)|].
    exact (RK _ 27%nat P27 eq_refl eq_refl).
  + exact P19'.
  + exact (RK _ 20%nat P20 eq_refl eq_refl).
  + rewrite (gsl_nth_H _ _ _ _ _ _ _ _ _ n HLINK Hnlen). fold kn. intros Heq.
    apply (f_equal (@length Z)) in Heq. rewrite gsl_bzs_len, length_firstn, (gs_dline_len s1 p q Hpq) in Heq.
    clear - Heq Hc Hjjr. unfold klen in Hc. lia.
- (* |held[n]| = jj: strncmp (held[n], line + p, jj) *)
  rewrite branch_ne_U, (U_atom Ea 41 klen A41 Hk64), (U_atom Ea 27 (Z.of_nat jj) A27 Hj64) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_tok_xR RUNR HS HJ2 SHOK2 gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem ?mx)) |- _ => rename Hf into HFrC; rename mx into msC end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msB)) (mrestrict (w_H W1) (ms_mem msC)) |- _ => rename Hg into GRC end.
  assert (KEEPC : GSKEEP cx W1 m1 (ms_mem msC)).
  { apply (gsl_keep_trans cx W1 m1 (ms_mem msB) (ms_mem msC) KEEPB). split.
    - intros z Hw _. exact (gsl_frame_nil RG HGSB _ _ _ _ _ HFrC ltac:(vm_compute; reflexivity) z Hw).
    - intros z Hpz. exact (apresent_grows _ _ _ z GRC Hpz). }
  clear HFrC.
  pmkst HS.
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
  repeat rewrite wvb_collapse in HJ2.
  match goal with |- SRrG _ R _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdc := mdx) in * end.
  clearbody mdc.
  assert (HARc : ARx ly1 S1 Hp1 W1 (ms_mem msC) mdc) by (eapply ajournal_gx_AR_xR; exact HJ2).
  pose proof KEEPC as (KC & PC).
  assert (KLC : forall z, 0 <= z < alloc_ceiling -> aview SEGS (w_H W1) (ms_mem msC) z = aview SEGS (w_H W1) m1 z)
    by (intros z Hw; apply KC; [clear - Hw C1; lia | clear - Hw HSTK1; unfold ESTACK, DRAIN_FRAME in *; lia]).
  assert (ROMc : rom_view SEGS W1 (ms_mem msC)).
  { intros z Hw. rewrite KLC; [exact (Hrom z Hw)|].
    destruct Hw as (sg & Hsg & _ & Hr). pose proof (pa_img_range z ltac:(exists sg; split; [exact Hsg | exact Hr])).
    clear - H C1. lia. }
  set (y := re_buf e1 + Z.of_nat p) in *.
  assert (Usp2 : spZ (ms_regs msC) = dsp0 cx - DRAIN_FRAME)
    by (unfold spZ; rewrite T2, (OLDa 2%nat ltac:(lia)), (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
  assert (H3 : getr (ms_regs msC) 3 = w64 (as_gp B))
    by (rewrite T3, (OLDa 3%nat ltac:(lia)), (EREG 3%nat 3%bv ltac:(lia) eq_refl), R3; exact Hgp).
  assert (H4 : getr (ms_regs msC) 4 = w64 (as_tp B))
    by (rewrite T4, (OLDa 4%nat ltac:(lia)), (EREG 4%nat 4%bv ltac:(lia) eq_refl), R4; exact Htp).
  assert (H10 : getr (ms_regs msC) 10 = w64 x) by (rewrite T10, (OLDa 34%nat ltac:(lia)), E34; reflexivity).
  assert (H11 : getr (ms_regs msC) 11 = w64 y)
    by (rewrite T11, (OLDa 24%nat ltac:(lia)), (EREG 24%nat 24%bv ltac:(lia) eq_refl), R24; reflexivity).
  assert (H12 : getr (ms_regs msC) 12 = w64 (Z.of_nat jj)) by (rewrite T12, A27; reflexivity).
  assert (HKgC : garr8 SEGS (arm W1 (ms_mem msC)) x (bzs (key_text kn ++ [Z_to_bv 8 0]))).
  { apply (gsl_garr8_kept W1 m1 W1 (ms_mem msC)); [exact HKg|]. intros z Hw. apply KLC.
    rewrite gsl_bzs_len, length_app in Hw. cbn [length] in Hw. clear - Hw HK4096 HKceil. unfold klen, x in *. lia. }
  assert (HLgC : garr8 SEGS (arm W1 (ms_mem msC)) y (dline s1 p q)).
  { apply (gsl_garr8_kept W1 m1 W1 (ms_mem msC)); [exact HLg|]. intros z Hw. apply KLC.
    rewrite (gs_dline_len s1 p q Hpq) in Hw. clear - Hw Hpq HUL Husedr HBceil HB4096. unfold y in *. lia. }
  assert (HJJ : Z.to_nat (Z.of_nat jj) = jj) by lia.
  assert (Hjk : length (key_text kn) = jj) by (clear - Hc; unfold klen in Hc; lia).
  (* strncmp (held[n], s->buf + p, jj) *)
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_DR B RG) 0 ([] : list (Z * Z)) (2 * ESTACK) (SIGMA WS_strncmp)
      (fun _ => False)
      (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 0 <-> astrn_agree W1 (ms_mem msC) x y (Z.of_nat jj))
      W1 (ms_regs msC) (ms_mem msC) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx)
      ([] : list (Z * Z)) ly1 S1 Hp1 _ k1 (- DRAIN_FRAME) (Z_to_bv 64 (BASE + 5500)) HG eq_refl HJ2).
    - rewrite Usp2. lia.
    - rewrite HDF. reflexivity.
    - lia.
    - lia.
    - lia.
    - exact H3.
    - exact H4.
    - exact T1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros _. right. intros [].
    - intros z [].
    - intros z [].
    - intros HPRE HSC.
      assert (HM : Z.min (Z.of_nat jj) (Z.of_nat jj + 1) = Z.of_nat jj) by lia.
      refine (ASTRNCMP ly1 S1 Hp1 W1 (ms_regs msC) (ms_mem msC) mdc x y (Z.of_nat jj) (Z.of_nat jj) (Z.of_nat jj)
        HPRE HSC H10 H11 H12 _ _ _ _ _ _ _ _ _ _ _ _ ROMc _); rewrite ?HM.
      + clear - Hjjr Hpq HUL Husedr HBceil HB4096 C1. lia.
      + clear - Hjjr Hpq HUL Husedr Hcapr. destruct Hcapr as [Hq | [Hq | Hq]]; lia.
      + clear - HK4096. unfold x. lia.
      + clear - HB4096. unfold y. lia.
      + apply (gsl_first_byte W1 (ms_mem msC) x (bzs (key_text kn ++ [Z_to_bv 8 0])) (Z.of_nat jj) (Z.of_nat jj) HKgC).
        * lia.
        * rewrite gsl_bzs_len, length_app. cbn [length]. lia.
        * intros i Hi. apply (gsl_key_nz _ HKnz). lia.
        * intros Hlt. lia.
      + apply (gsl_first_byte W1 (ms_mem msC) y (dline s1 p q) (Z.of_nat jj) (Z.of_nat jj) HLgC).
        * lia.
        * rewrite (gs_dline_len s1 p q Hpq). lia.
        * intros i Hi. apply (gsl_dline_nth_nz RG HGSB s1 p q Hpq Hnzl). lia.
        * intros Hlt. lia.
      + clear - HKceil HK4096 Hjk C1. unfold x, klen in *. lia.
      + clear - Hjjr Hpq HUL Husedr HBceil HB4096 C1. unfold y. lia.
      + intros z Hw. split.
        * replace z with (x + Z.of_nat (Z.to_nat (z - x))) by lia.
          rewrite (gsl_aview_garr8 W1 (ms_mem msC) x _ _ HKgC); [discriminate|].
          rewrite gsl_bzs_len, length_app. cbn [length]. lia.
        * rewrite Usp2. clear - Hw HKceil HK4096 Hjk C1 HSTK1. unfold x, klen, ESTACK, DRAIN_FRAME in *. lia.
      + intros z Hw. split.
        * replace z with (y + Z.of_nat (Z.to_nat (z - y))) by lia.
          rewrite (gsl_aview_garr8 W1 (ms_mem msC) y _ _ HLgC); [discriminate|].
          rewrite (gs_dline_len s1 p q Hpq). lia.
        * rewrite Usp2. clear - Hw Hjjr Hpq HUL Husedr HBceil HB4096 C1 HSTK1. unfold y, ESTACK, DRAIN_FRAME in *. lia.
      + split; [|split].
        * unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HKia |- *.
          clear - HKia Hjk C1. unfold x, klen in *. lia.
        * apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem msC) mdc x (klen + 1)); [exact HARc | exact HKin | lia |].
          rewrite RQK. clear - Hjk. unfold klen. lia.
        * intros Hp0. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem msC) mdc x (klen + 1));
            [exact HARc | exact HKin | lia | rewrite RQK; clear - Hjk; unfold klen; lia | exact Hp0].
      + split; [|split].
        * unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HBia |- *.
          clear - HBia Hjjr Hpq HUL Husedr C1. unfold y. lia.
        * apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem msC) mdc (re_buf e1) (re_cap e1)); [exact HARc | exact Hbin | unfold y; lia |].
          rewrite RQC. clear - Hjjr Hpq HUL Husedr. unfold y. lia.
        * intros Hp0. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem msC) mdc (re_buf e1) (re_cap e1));
            [exact HARc | exact Hbin | unfold y; lia | rewrite RQC; clear - Hjjr Hpq HUL Husedr; unfold y; lia | exact Hp0].
      + split.
        * apply (amem_range_near_block_x B ARx RG LAWS HGSB ly1 S1 Hp1 W1 (ms_mem msC) mdc x (klen + 1) x HARc HKin); [lia|].
          rewrite RQK. lia.
        * apply (amem_range_near_block_x B ARx RG LAWS HGSB ly1 S1 Hp1 W1 (ms_mem msC) mdc (re_buf e1) (re_cap e1) y HARc Hbin);
            [unfold y; lia | rewrite RQC; clear - Hpq HUL Husedr; unfold y; lia]. }
  cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hres3 & Hfr3 & Hpres3).
  assert (HAG : astrn_agree W1 (ms_mem msC) x y (Z.of_nat jj) <-> nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q)).
  { rewrite (gsl_agree_iff W1 (ms_mem msC) x y (Z.of_nat jj) _ _ HKgC HLgC);
      [| lia | rewrite gsl_bzs_len, length_app; cbn [length]; lia | rewrite (gs_dline_len s1 p q Hpq); lia
       | intros i Hi; apply (gsl_key_nz _ HKnz); lia].
    rewrite HJJ, (gsl_nth_H _ _ _ _ _ _ _ _ _ n HLINK Hnlen). fold kn.
    replace (firstn jj (bzs (key_text kn ++ [Z_to_bv 8 0]))) with (bzs (key_text kn))
      by (rewrite <- Hjk; symmetry; apply gsl_bzs_firstn_key).
    reflexivity. }
  jafter_call_keep_pi HS 53%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0%nat] HS3.
  assert (UspA : bv_unsigned (ew Ea 2) = dsp0 cx - DRAIN_FRAME) by (rewrite (OLDa 2%nat ltac:(lia)); exact Usp0).
  assert (HRK : region_kept SEGS Ea (ms_mem (restrict (w_H W1) msC)) (mrestrict (w_H W1) mem3) gl_frame).
  { split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi gl_frame base_val]; rewrite UspA;
      intros z Hw; [|lia].
    change (ms_mem (restrict (w_H W1) msC)) with (mrestrict (w_H W1) (ms_mem msC)).
    apply (mbyte_of_aview SEGS). apply Hfr3;
      [clear - Hw HSTK1 HSTK2 C1; unfold ESTACK, DRAIN_FRAME in *; lia | intros [] | clear - Hw; unfold ESTACK in *; lia]. }
  specialize (HS3 ltac:(constructor; [exact HRK | constructor])).
  clear HS HRK. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  remember (havoc Ea 53 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
  assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
  assert (OLDb : forall m, (m < 53)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
  clear HEb.
  prreg HS (10%bv : bv 5) R10c.
  set (r0 := getr regs3 10) in *.
  assert (A57 : ew Eb 57 = Z_to_bv 64 (bv_unsigned r0)) by (rewrite <- R10c, Z_to_bv_bv_unsigned; reflexivity).
  assert (Hr0 : 0 <= bv_unsigned r0 < 2 ^ 64) by exact (bv_unsigned_in_range 64 r0).
  assert (SHOK3 : sh_ok SEGS gl_Bx [] Eb (mrestrict (w_H W1) mem3)) by constructor.
  assert (KEEP3 : GSKEEP cx W1 m1 mem3).
  { apply (gsl_keep_trans cx W1 m1 (ms_mem msC) mem3 KEEPC). split.
    - intros z Hw Hs. exact (Hfr3 z Hw (fun H => H) ltac:(clear - Hs; unfold ESTACK in *; lia)).
    - exact Hpres3. }
  clear Hfr3.
  paj_run_tok_xR RUNR HS HJ3 SHOK3 gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
  match goal with Hf : frame_of _ _ (mrestrict (w_H W1) mem3) (mrestrict (w_H W1) (ms_mem ?mx)) |- _ => rename Hf into HFrD; rename mx into msD end.
  match goal with Hg : mem_grows (mrestrict (w_H W1) mem3) (mrestrict (w_H W1) (ms_mem msD)) |- _ => rename Hg into GRD end.
  assert (KEEPD : GSKEEP cx W1 m1 (ms_mem msD)).
  { apply (gsl_keep_trans cx W1 m1 mem3 (ms_mem msD) KEEP3). split.
    - intros z Hw _. exact (gsl_frame_nil RG HGSB _ _ _ _ _ HFrD ltac:(vm_compute; reflexivity) z Hw).
    - intros z Hpz. exact (apresent_grows _ _ _ z GRD Hpz). }
  clear HFrD.
  psrr_branch_tok RUNR BRR HS SHOK3 gl_Bspan.
  + (* strncmp = 0: the key is held at slot n *)
    match goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hb3 end.
    rewrite branch_eq_U, (U_atom Eb 57 (bv_unsigned r0) A57 Hr0), (U_lit Eb 0) in Hb3 by lia.
    apply Z.eqb_eq in Hb3.
    assert (Hmt : nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q)).
    { apply HAG, Hres3. fold r0. apply bv_eq. rewrite Hb3. reflexivity. }
    paj_run_tok_xR RUNR HS HJ3 SHOK3 gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
    match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msD)) (mrestrict (w_H W1) (ms_mem ?mx)) |- _ => rename Hf into HFrE; rename mx into msE end.
    match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msD)) (mrestrict (w_H W1) (ms_mem msE)) |- _ => rename Hg into GRE end.
    assert (KEEPE : GSKEEP cx W1 m1 (ms_mem msE)).
    { apply (gsl_keep_trans cx W1 m1 (ms_mem msD) (ms_mem msE) KEEPD). split.
      - intros z Hw _. exact (gsl_frame_nil RG HGSB _ _ _ _ _ HFrE ltac:(vm_compute; reflexivity) z Hw).
      - intros z Hpz. exact (apresent_grows _ _ _ z GRE Hpz). }
    clear HFrE KEEPD. rename KEEPE into KEEPD. rename msE into msD0.
    assert (B36 : ew Eb 36 = Z_to_bv 64 bg) by (rewrite (OLDb 36%nat ltac:(lia)), (OLDa 36%nat ltac:(lia)); exact E36).
    psrr_branch_tok RUNR BRR HS SHOK3 gl_Bspan.
    * (* bg = 0: a begin whose key is held: on to the next line *)
      match goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hb4 end.
      rewrite branch_eq_U, (U_atom Eb 36 bg B36 Hbgr), (U_lit Eb 0) in Hb4 by lia.
      apply Z.eqb_eq in Hb4.
      paj_run_to_tok_xR RUNTOR HS HJ3 SHOK3 gl_Bspan A_dr_next. { apply awr_ok_x_of0. awr_ok_tac. }
      match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
      match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msD0)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hf into HFrF end.
      match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msD0)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hg into GRF end.
      pmkst HS.
      prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
      prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. gsl_prreg_raw_x HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
      prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) PX24.
      prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
      repeat rewrite wvb_collapse in HJ3.
      match goal with |- SRrG _ R _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
      assert (HKP : GSKEEP cx W1 m1 (ms_mem msF)).
      { apply (gsl_keep_trans cx W1 m1 (ms_mem msD0) (ms_mem msF) KEEPD). split.
        - intros z Hw _. exact (gsl_frame_nil RG HGSB _ _ _ _ _ HFrF ltac:(vm_compute; reflexivity) z Hw).
        - intros z Hpz. exact (apresent_grows _ _ _ z GRF Hpz). }
      clear HS SHOK3 HFrF.
      assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Eb k -> Nat.ltb k 32 = true ->
        Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
      { intros r k Hr Hk Hkr. apply Nat.ltb_lt in Hk. rewrite Hr, (OLDb k ltac:(lia)), (OLDa k ltac:(lia)).
        apply EREG; [exact Hk | exact Hkr]. }
      assert (B35 : ew Eb 35 = Z_to_bv 64 (dxSA cx)) by (rewrite (OLDb 35%nat ltac:(lia)), (OLDa 35%nat ltac:(lia)); exact E35).
      assert (B33 : ew Eb 33 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (rewrite (OLDb 33%nat ltac:(lia)), (OLDa 33%nat ltac:(lia)); exact E33).
      assert (Q22 : getr (ms_regs msF) 22 = w64 (dxSA cx)) by (rewrite P22, B35; reflexivity).
      assert (Q27 : getr (ms_regs msF) 27 = w64 (dxSA cx + 24))
        by (rewrite P27, B35, unsigned_lit_small by (clear - HSA1 HSA2 C1; lia); reflexivity).
      pose proof (gsl_body_keep_xR cx Hp kr s1 D p q n (S kf) n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl
        kd jj bg (ms_mem msF) mdF HB HBD HJ3 HKP) as HBDF.
      apply (HDLN W1).
      exact (gsl_mk_dln_xR cx Hp kr s1 D p q n (S kf) W1 regs1 ly1 S1 Hp1 (ms_mem msF) mdF k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl
        kd jj bg (ms_regs msF) HBDF Hmt Hb4
        (RK _ 2%nat P2 eq_refl eq_refl) (RK _ 3%nat P3 eq_refl eq_refl) (RK _ 4%nat P4 eq_refl eq_refl)
        (RK _ 8%nat P8 eq_refl eq_refl) (RK _ 9%nat P9 eq_refl eq_refl) (RK _ 18%nat P18 eq_refl eq_refl)
        (RK _ 21%nat P21 eq_refl eq_refl) (RK _ 23%nat P23 eq_refl eq_refl) Q22 Q27).
    * (* bg <> 0: an end whose key is held: GF *)
      match goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hb4 end.
      rewrite branch_eq_U, (U_atom Eb 36 bg B36 Hbgr), (U_lit Eb 0) in Hb4 by lia.
      apply Z.eqb_neq in Hb4.
      paj_run_to_tok_xR RUNTOR HS HJ3 SHOK3 gl_Bspan A_dr_free. { apply awr_ok_x_of0. awr_ok_tac. }
      match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
      match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msD0)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hf into HFrF end.
      match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msD0)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hg into GRF end.
      pmkst HS.
      prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
      prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. gsl_prreg_raw_x HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
      prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) PX24.
      prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
      repeat rewrite wvb_collapse in HJ3.
      match goal with |- SRrG _ R _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
      assert (HKP : GSKEEP cx W1 m1 (ms_mem msF)).
      { apply (gsl_keep_trans cx W1 m1 (ms_mem msD0) (ms_mem msF) KEEPD). split.
        - intros z Hw _. exact (gsl_frame_nil RG HGSB _ _ _ _ _ HFrF ltac:(vm_compute; reflexivity) z Hw).
        - intros z Hpz. exact (apresent_grows _ _ _ z GRF Hpz). }
      clear HS SHOK3 HFrF.
      assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Eb k -> Nat.ltb k 32 = true ->
        Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
      { intros r k Hr Hk Hkr. apply Nat.ltb_lt in Hk. rewrite Hr, (OLDb k ltac:(lia)), (OLDa k ltac:(lia)).
        apply EREG; [exact Hk | exact Hkr]. }
      assert (B35 : ew Eb 35 = Z_to_bv 64 (dxSA cx)) by (rewrite (OLDb 35%nat ltac:(lia)), (OLDa 35%nat ltac:(lia)); exact E35).
      assert (B33 : ew Eb 33 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (rewrite (OLDb 33%nat ltac:(lia)), (OLDa 33%nat ltac:(lia)); exact E33).
      assert (Q22 : getr (ms_regs msF) 22 = w64 (dxSA cx)) by (rewrite P22, B35; reflexivity).
      assert (Q27 : getr (ms_regs msF) 27 = w64 (dxSA cx + 24))
        by (rewrite P27, B35, unsigned_lit_small by (clear - HSA1 HSA2 C1; lia); reflexivity).
      pose proof (gsl_body_keep_xR cx Hp kr s1 D p q n (S kf) n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl
        kd jj bg (ms_mem msF) mdF HB HBD HJ3 HKP) as HBDF.
      assert (P19' : getr (ms_regs msF) 19 = getr regs1 19).
      { rewrite P19, denot_lit_U, R19.
        change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 0) (SLit 3)) (SOff 21 0)) with (gl_shE 33).
        rewrite (gl_U_shadow RG HGSB Eb 33 (re_hp e1 + 8 * Z.of_nat n)); [reflexivity | exact B33 | |].
        - rewrite (OLDb 21%nat ltac:(lia)), (OLDa 21%nat ltac:(lia)). exact E21.
        - clear - HH4096 HHceil Hrq Hk1 Hnlen C1. lia. }
      apply (HGF W1).
      exact (gsl_mk_gf_xR cx Hp kr s1 D p q n (S kf) W1 regs1 ly1 S1 Hp1 (ms_mem msF) mdF k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl
        kd jj bg (ms_regs msF) HBDF Hmt Hb4
        (RK _ 2%nat P2 eq_refl eq_refl) (RK _ 3%nat P3 eq_refl eq_refl) (RK _ 4%nat P4 eq_refl eq_refl)
        (RK _ 8%nat P8 eq_refl eq_refl) (RK _ 9%nat P9 eq_refl eq_refl) (RK _ 18%nat P18 eq_refl eq_refl)
        (RK _ 21%nat P21 eq_refl eq_refl) (RK _ 23%nat P23 eq_refl eq_refl) (RK _ 24%nat PX24 eq_refl eq_refl)
        P19' (RK _ 20%nat P20 eq_refl eq_refl) Q22 Q27 ltac:(rewrite P26, B33; reflexivity)).
  + (* strncmp <> 0: no match at slot n *)
    match goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hb3 end.
    rewrite branch_eq_U, (U_atom Eb 57 (bv_unsigned r0) A57 Hr0), (U_lit Eb 0) in Hb3 by lia.
    apply Z.eqb_neq in Hb3.
    assert (Hmis : nth n (dlH cx s1 p) [] <> firstn jj (dline s1 p q)).
    { intros Hm. apply HAG, Hres3 in Hm. fold r0 in Hm. apply Hb3. rewrite Hm. reflexivity. }
    paj_run_to_tok_xR RUNTOR HS HJ3 SHOK3 gl_Bspan A_dr_hnext. { apply awr_ok_x_of0. awr_ok_tac. }
    match type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into msF end.
    match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msD)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hf into HFrF end.
    match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msD)) (mrestrict (w_H W1) (ms_mem msF)) |- _ => rename Hg into GRF end.
    pmkst HS.
    prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
    prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. gsl_prreg_raw_x HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
    prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) PX24.
    prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
    repeat rewrite wvb_collapse in HJ3.
    match goal with |- SRrG _ R _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
    assert (HKP : GSKEEP cx W1 m1 (ms_mem msF)).
    { apply (gsl_keep_trans cx W1 m1 (ms_mem msD) (ms_mem msF) KEEPD). split.
      - intros z Hw _. exact (gsl_frame_nil RG HGSB _ _ _ _ _ HFrF ltac:(vm_compute; reflexivity) z Hw).
      - intros z Hpz. exact (apresent_grows _ _ _ z GRF Hpz). }
    clear HS SHOK3 HFrF.
    assert (RK : forall (r : bv 5) (k : nat), getr (ms_regs msF) r = ew Eb k -> Nat.ltb k 32 = true ->
      Z.of_nat k = bv_unsigned r -> getr (ms_regs msF) r = getr regs1 r).
    { intros r k Hr Hk Hkr. apply Nat.ltb_lt in Hk. rewrite Hr, (OLDb k ltac:(lia)), (OLDa k ltac:(lia)).
      apply EREG; [exact Hk | exact Hkr]. }
    assert (B35 : ew Eb 35 = Z_to_bv 64 (dxSA cx)) by (rewrite (OLDb 35%nat ltac:(lia)), (OLDa 35%nat ltac:(lia)); exact E35).
    assert (B33 : ew Eb 33 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (rewrite (OLDb 33%nat ltac:(lia)), (OLDa 33%nat ltac:(lia)); exact E33).
    pose proof (gsl_body_keep_xR cx Hp kr s1 D p q n (S kf) n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl
      kd jj bg (ms_mem msF) mdF HB HBD HJ3 HKP) as HBDF.
    assert (P19' : getr (ms_regs msF) 19 = getr regs1 19).
    { rewrite P19, denot_lit_U, R19.
      change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 0) (SLit 3)) (SOff 21 0)) with (gl_shE 33).
      rewrite (gl_U_shadow RG HGSB Eb 33 (re_hp e1 + 8 * Z.of_nat n)); [reflexivity | exact B33 | |].
      - rewrite (OLDb 21%nat ltac:(lia)), (OLDa 21%nat ltac:(lia)). exact E21.
      - clear - HH4096 HHceil Hrq Hk1 Hnlen C1. lia. }
    apply HGN.
    apply (gsl_exit_gsn_xR cx Hp kr s1 D p q n (S kf) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg
      (ms_regs msF) (ms_mem msF) mdF HB HBD HJ3 HKP).
    * split; [exact (RK _ 2%nat P2 eq_refl eq_refl)|]. split; [exact (RK _ 3%nat P3 eq_refl eq_refl)|].
      split; [exact (RK _ 4%nat P4 eq_refl eq_refl)|]. split; [exact (RK _ 8%nat P8 eq_refl eq_refl)|].
      split; [exact (RK _ 9%nat P9 eq_refl eq_refl)|]. split; [exact (RK _ 18%nat P18 eq_refl eq_refl)|].
      split; [exact (RK _ 21%nat P21 eq_refl eq_refl)|]. split; [exact (RK _ 23%nat P23 eq_refl eq_refl)|].
      split; [exact (RK _ 24%nat PX24 eq_refl eq_refl)|]. split; [exact (RK _ 25%nat P25 eq_refl eq_refl)|].
      exact (RK _ 27%nat P27 eq_refl eq_refl).
    * exact P19'.
    * exact (RK _ 20%nat P20 eq_refl eq_refl).
    * exact Hmis.
Qed.
(* ---- The loop: by induction on the external kf, the number of slots left. ---- *)
Theorem gs_scan_loop_xR : gs_scan_loop_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold gs_scan_loop_stmt_xR. intros cx Hp kr s1 D p q n kf. revert n.
induction kf as [|kf IH]; intros n W1 c1 HB HGL HDLN HGA HGF.
- exfalso. destruct (gsl_GSL_elim_xR _ _ _ _ _ _ _ _ _ _ _ HGL) as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1
    & spent & jb & aa & oo & ha & ks & tl & kd & jj & bg & _ & HBD).
  unfold GSBODY_xR in HBD. destruct HBD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & _ & _ & Hkf & _). lia.
- apply (gsl_body_xR cx Hp kr s1 D p q n kf W1 c1 HB HGL HDLN HGF).
  intros c2 HGN.
  apply (gsl_tail_xR cx Hp kr s1 D p q n kf W1 c2 HB HGN HGA).
  intros Hkf0 c3 HGL3.
  exact (IH (S n) W1 c3 HB HGL3 HDLN HGA HGF).
Qed.
End wR.


(* ---- (1) A match on a BEGIN: the line loop's core after the sent line is DLC_x at S q. ---- *)
Lemma gsl_dlc_same_x : forall cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl,
GSF s1 p q ->
seen_arr (dlH cx s1 p) (dline s1 p q) = dlH cx s1 p ->
seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) = dlka cx s1 p ->
GSB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
DLC_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S q) ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.
Proof. eapply (gsl_dlc_same_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* ---- (3) The cut survives the loop (the interceptors write only their scratch below drain's frame). ---- *)
Lemma gsl_core_kept_x : forall cx Hp kr s1 D p q ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  m2 md2 k2,
alloc_ceiling + 2 * ESTACK + DRAIN_FRAME <= dsp0 cx -> dsp0 cx <= 2 ^ 47 -> (dxj cx < 4)%nat ->
4096 <= dxSA cx -> dxSA cx + 56 <= alloc_ceiling ->
GSB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k2 ->
GSKEEP cx W1 m1 m2 ->
GSB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q ly1 S1 Hp1 W1 m2 md2 k2 e1 h1 out1 ev1 LB1 spent tl.
Proof. eapply (gsl_core_kept_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


Lemma gsl_GSL_elim_x : forall cx Hp kr s1 D p q n kf W1 c1,
GSL_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q n kf W1 c1 ->
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_hloop) regs1 m1 md1 /\
GSBODY_x cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof. eapply (gsl_GSL_elim_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


Lemma gsl_GSL_intro_x : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg,
GSBODY_x cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
GSL_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q n kf W1 (cfg_at SEGS (BASE + A_dr_hloop) regs1 m1 md1).
Proof. eapply (gsl_GSL_intro_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* the relay entry's place, from DBASE and the core's table block *)
Lemma gsl_sa_x : forall cx Hp kr ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 s out1 ev1 sent LB1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DMEM_x B PST ARx RG cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 ->
4096 <= dxSA cx /\ dxSA cx + 56 <= alloc_ceiling.
Proof. eapply (gsl_sa_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* the body at the memory after a step of the loop that keeps every byte outside the interceptors' scratch *)
Lemma gsl_body_keep_x : forall cx Hp kr s1 D p q n kf nm W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  m2 md2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
GSBODY_x cx Hp kr s1 D p q n kf nm W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
GSKEEP cx W1 m1 m2 ->
GSBODY_x cx Hp kr s1 D p q n kf nm W1 regs1 ly1 S1 Hp1 m2 md2 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof. eapply (gsl_body_keep_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* GSN from the head's body: the registers unchanged, slot n not matched *)
Lemma gsl_mk_gsn_x : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY_x cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
GSREGS regs1 regs2 -> getr regs2 19 = getr regs1 19 -> getr regs2 20 = getr regs1 20 ->
nth n (dlH cx s1 p) [] <> firstn jj (dline s1 p q) ->
GSBODY_x cx Hp kr s1 D p q n kf (S n) W1 regs2 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof. eapply (gsl_mk_gsn_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* the loop's head at S n from GSN at n, s3 and s4 stepped *)
Lemma gsl_mk_loop_x : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY_x cx Hp kr s1 D p q n (S kf) (S n) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
(0 < kf)%nat ->
GSREGS regs1 regs2 ->
getr regs2 19 = Z_to_bv 64 (bv_unsigned (getr regs1 19) + 1) ->
getr regs2 20 = Z_to_bv 64 (bv_unsigned (getr regs1 20) + 8) ->
GSBODY_x cx Hp kr s1 D p q (S n) kf (S n) W1 regs2 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof. eapply (gsl_mk_loop_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* GA from GSN at the last slot: the spilled registers back *)
Lemma gsl_mk_ga_x : forall cx Hp kr s1 D p q n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY_x cx Hp kr s1 D p q n 1 (S n) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 21 = getr regs1 21 -> getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 ->
getr regs2 22 = w64 (dxSA cx) -> getr regs2 27 = w64 (dxSA cx + 24) ->
getr regs2 25 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj) -> getr regs2 19 = w64 bg ->
getr regs2 10 = w64 (re_nheld e1) -> getr regs2 11 = w64 (re_nheld e1) ->
getr regs2 12 = w64 ((dxSA cx + 40) / 8) ->
GA_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q W1 (cfg_at SEGS (BASE + A_dr_add) regs2 m1 md1).
Proof. eapply (gsl_mk_ga_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* GSN from the head's body at a later memory: slot n not matched *)
Lemma gsl_exit_gsn_x : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2 m2 md2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
GSBODY_x cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
GSKEEP cx W1 m1 m2 ->
GSREGS regs1 regs2 -> getr regs2 19 = getr regs1 19 -> getr regs2 20 = getr regs1 20 ->
nth n (dlH cx s1 p) [] <> firstn jj (dline s1 p q) ->
GSN_x cx Hp kr s1 D p q n kf W1 (cfg_at SEGS (BASE + A_dr_hnext) regs2 m2 md2).
Proof. eapply (gsl_exit_gsn_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* a BEGIN whose key is held at slot n: DLN (S q), the registers s6 / s11 back *)
Lemma gsl_mk_dln_x : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY_x cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q) -> bg = 0 ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 21 = getr regs1 21 -> getr regs2 23 = getr regs1 23 ->
getr regs2 22 = w64 (dxSA cx) -> getr regs2 27 = w64 (dxSA cx + 24) ->
DLN_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S q) W1 (cfg_at SEGS (BASE + A_dr_next) regs2 m1 md1).
Proof. eapply (gsl_mk_dln_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* an END whose key is held at slot n: GF *)
Lemma gsl_mk_gf_x : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY_x cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q) -> bg <> 0 ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 21 = getr regs1 21 -> getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 ->
getr regs2 19 = getr regs1 19 -> getr regs2 20 = getr regs1 20 ->
getr regs2 22 = w64 (dxSA cx) -> getr regs2 27 = w64 (dxSA cx + 24) ->
getr regs2 26 = w64 (re_hp e1 + 8 * Z.of_nat n) ->
GF_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q W1 (cfg_at SEGS (BASE + A_dr_free) regs2 m1 md1).
Proof. eapply (gsl_mk_gf_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* ---- The loop's bottom: GSN n (S kf) -> GSL (S n) kf when a slot is left, GA when none is. ---- *)
Lemma gsl_tail_x : forall cx Hp kr s1 D p q n kf W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GSN_x cx Hp kr s1 D p q n (S kf) W1 c1 ->
(forall W2 c2, GA_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q W2 c2 ->
   SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
((0 < kf)%nat -> forall c2, GSL_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q (S n) kf W1 c2 ->
   SRr SEGS W1 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr).
Proof. eapply (gsl_tail_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* ---- The loop's body: GSL n (S kf) -> GSN n (S kf) (no match at slot n), DLN (S q) (a begin held at slot n)
   or GF (an end held at slot n). ---- *)
Lemma gsl_body_x : forall cx Hp kr s1 D p q n kf W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GSL_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q n (S kf) W1 c1 ->
(forall W2 c2, DLN_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S q) W2 c2 ->
   SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
(forall W2 c2, GF_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q W2 c2 ->
   SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
(forall c2, GSN_x cx Hp kr s1 D p q n (S kf) W1 c2 -> SRr SEGS W1 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr).
Proof. eapply (gsl_body_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* ---- The loop: by induction on the external kf, the number of slots left. ---- *)
Theorem gs_scan_loop_x : gs_scan_loop_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (gs_scan_loop_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.
End cx.
End bx.
End ax.
