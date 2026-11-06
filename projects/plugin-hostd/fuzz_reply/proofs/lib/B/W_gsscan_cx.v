(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the held-key search of segment GS of the ASan+UBSan walk (image B,
   fuzz_reply.asan-ubsan) of fuzz_reply's drain -- gesture_seen's loop over e->held (relay.c:104-108, inlined),
   0x83b34 .. 0x83b9c, its match exit 0x83cac / 0x83d9c and its no-match exit 0x83ba0 -- its cut predicates,
   the machine-state helpers of the walk and the loop's two symbolic seats.  Proves no function (kind: segment
   lemma of drain's image-B walk, GS piece gs_scan).  The stage statement is lib/B/W_drain_gs.v's gs_scan_stmt;
   the Section header below is that file's, verbatim.
   Structure from image A's lib/A/W_gsscanb_cx.v / W_gsscanb.v (a working branch 0c06ccc287f); every
   pc, register, frame slot and trap is read from image B's listing (fuzz_reply.objdump.txt (sha256 17f5c434bf57; internal record) 0x83aa4 .. 0x83db0)
   and checked against the symbolic engine's own states (the cuts below are the ones it computes).

   THE LOOP ON IMAGE B (pc = 0x83278 + offset; the loop keeps hp in s6 and the slot count in s3, where A
   reloads hp from the frame):
     0x83b34 add s10,s6,s4; bltu s10,s6,unimp            PTR_BLTU: the engine stops; trap_ptr_wrap_atom
     0x83b3c seqz; xor a0,s9,a0; beqz a0,unimp            NULL_XOR folded (s9 = snez hp = 1): trap_null_xor_folded
     0x83b48 ld a0,168(sp); beqz a0,unimp                 NONNULL on the one-time flag 168(sp) = 1: decided
     0x83b50 srli; ld 240(sp); add; lbu; bnez -> report   shadow of &held[n]: folded by the token layer
     0x83b64 ld s11,0(s10); strlen                        held[n] (ASTRLEN)
     0x83b70 ld a1,192(sp); bne a0,a1,0x83b8c             |held[n]| <> jj: no match
     0x83b78 strncmp (held[n], s8, 192(sp)); beqz a0,0x83cac   (ASTRNCMP)
     0x83b8c addi s4,8; addiw s3,-1; ld s11,176(sp); ld a0,160(sp); bne a0,s4,0x83b34   GSN: the bottom
     0x83ba0 GA (W_drain_gs.v)
     0x83cac ld a0,24(sp); beqz a0,0x83d9c                bg = 0: a begin held
     0x83cb4 GF (W_drain_gs.v)                            bg <> 0: an end held
     0x83d9c ld s5,144; ld s6,136; ld s4,128; ld s11,176; bnez s3,0x839d4   DLN (S q); s3 = kf >= 1 is a seated
             fact, so the dead `j 0x83bbc` is never reached
   Cuts: GSL (0x83b34, slot n read next, none below n matched) and GSN (0x83b8c, slot n read and not matched),
   both GSBODY with the head's pc / no-match bound n or S n.  kf = the slots left = s3, so the induction is on
   the external kf. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_drain_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_drain_gs W_drain_gs_model W_drain_gs_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_traps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).

(* the lemmas below need only the section hypotheses their Proof using names; clear the rest so lia sees none *)
Ltac gsc_clr0 := repeat match goal with H : _ |- _ => clear H end.

(* ---------------------------------------------------------------------------------------------------------
   (0) Bytes and values (image-free).
   --------------------------------------------------------------------------------------------------------- *)
Lemma gsc_bzs_app : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.

Lemma gsc_bzs_len : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.

Lemma gsc_bz_bv8 : forall x, bz (Z_to_bv 8 x) = x mod 256.
Proof. intros x. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. reflexivity. Qed.

Lemma gsc_nth_zle : forall n z k d, (k < n)%nat ->
nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k d Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn [nth]. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma gsc_nth_le_bytes : forall n v k, (k < n)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
nth k (bzs (Z_to_le_bytes n v)) 0 = YO0f.le_byte v n k.
Proof.
intros n v k Hk Hv. unfold bzs.
rewrite (nth_indep (map bz (Z_to_le_bytes n v)) 0 (bz (Z_to_bv 8 0)))
  by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite List.map_nth, gsc_nth_zle by exact Hk. rewrite gsc_bz_bv8.
unfold YO0f.le_byte. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.

Lemma gsc_le8_bytes : forall v, 0 <= v < 2 ^ 64 -> Mem.le8 (Z_to_bv 64 v) = Z_to_le_bytes 8 v.
Proof.
intros v Hv. unfold Mem.le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact Hv. reflexivity.
Qed.

Lemma gsc_key_nz : forall t, ~ In (Z_to_bv 8 0) t -> forall i, (i < length t)%nat ->
nth i (bzs (t ++ [Z_to_bv 8 0])) 0 <> 0.
Proof.
intros t Ht i Hi. unfold bzs.
rewrite (nth_indep (map bz (t ++ [Z_to_bv 8 0])) 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_app; cbn [length]; lia).
rewrite List.map_nth, app_nth1 by exact Hi.
intros E. apply Ht. replace (Z_to_bv 8 0) with (nth i t (Z_to_bv 8 0)); [apply nth_In; exact Hi|].
apply bv_eq. unfold bz in E. rewrite E. reflexivity.
Qed.

Lemma gsc_key_z : forall t, nth (length t) (bzs (t ++ [Z_to_bv 8 0])) 0 = 0.
Proof.
intros t. unfold bzs. rewrite map_app. rewrite app_nth2 by (rewrite length_map; lia).
rewrite length_map, Nat.sub_diag. reflexivity.
Qed.

Lemma gsc_firstn_len : forall {A} (l1 l2 : list A), firstn (length l1) (l1 ++ l2) = l1.
Proof. intros A l1 l2. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. apply app_nil_r. Qed.

Lemma gsc_bzs_firstn_key : forall t, firstn (length t) (bzs (t ++ [Z_to_bv 8 0])) = bzs t.
Proof. intros t. rewrite gsc_bzs_app, <- (gsc_bzs_len t). apply gsc_firstn_len. Qed.

Lemma gsc_div8_succ : forall hp n, (hp + 8 * Z.of_nat n) / 8 + 1 = (hp + 8 * Z.of_nat (S n)) / 8.
Proof.
intros hp n. rewrite Nat2Z.inj_succ.
replace (hp + 8 * Z.succ (Z.of_nat n)) with ((hp + 8 * Z.of_nat n) + 1 * 8) by lia.
rewrite Z.div_add by lia. reflexivity.
Qed.

(* ---- the symbolic values the stage computes ---- *)
Lemma gsc_den : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma gsc_U_srl : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8.
Proof.
intros E n v c Hn Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn Hv Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

(* srli; add <the shadow base atom b> *)
Lemma gsc_U_shadow : forall E n b v c, ew E n = Z_to_bv 64 v -> ew E b = Z_to_bv 64 SHADOW_OFF ->
0 <= v < 2 ^ 63 -> 0 <= v + c < 2 ^ 63 ->
U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff b 0)) = (v + c) / 8 + SHADOW_OFF.
Proof.
intros E n b v c Hn Hb Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (gsc_U_srl E n v c Hn ltac:(lia) ltac:(lia)), (U_atom E b SHADOW_OFF Hb) by (unfold SHADOW_OFF; lia).
assert (Hd : 0 <= (v + c) / 8 < 2 ^ 61) by
  (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

Lemma gsc_shadow_range : forall v, 0 <= v < 2 ^ 63 -> 0 <= v / 8 + SHADOW_OFF < 2 ^ 64.
Proof.
intros v Hv. pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_lt_upper_bound v 8 (2 ^ 60) ltac:(lia) ltac:(lia)). unfold SHADOW_OFF. lia.
Qed.

(* sub a0,s3,s8, as the engine writes it *)
Lemma gsc_U_sub2 : forall E m n vm vn, ew E m = Z_to_bv 64 vm -> ew E n = Z_to_bv 64 vn ->
0 <= vm -> vm <= vn -> vn < 2 ^ 63 ->
U E (SAlu ALU_ADD (SOff n 0) (SMd M_MUL (SOff m 0) (SLit (-1)))) = vn - vm.
Proof.
intros E m n vm vn Hm Hn Hm0 Hmn Hn63.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E m vm Hm) by lia. rewrite (U_atom E n vn Hn) by lia. rewrite U_SLit.
unfold zcanon, M64.
replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
replace (vm * (2 ^ 64 - 1)) with (- vm + vm * 2 ^ 64) by ring.
rewrite Z_mod_plus_full, Zplus_mod_idemp_r.
replace (vn + - vm) with (vn - vm) by ring.
apply Z.mod_small. lia.
Qed.

(* sgtz; neg; and; slli 3 of a positive count (160(sp) = 8 nheld) *)
Lemma gsc_U_nh8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 < v < 2 ^ 26 ->
U E (SAlu ALU_SLL (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff n 0))) (SOff n 0)) (SLit 3))
  = 8 * v.
Proof.
intros E n v Hn Hv.
assert (Ua : U E (SOff n 0) = v) by (apply (U_atom E n v Hn); lia).
assert (Us : U E (SAlu ALU_SLT (SLit 0) (SOff n 0)) = 1).
{ rewrite U_SAlu, U_SLit, Ua. cbn [zalu_raw]. rewrite (zcanon_id 0) by (unfold M64; lia).
  rewrite (swrap64_id 0) by (unfold half64; lia). rewrite (swrap64_id v) by (unfold half64; lia).
  destruct (Z.ltb_spec 0 v); [|lia]. apply zcanon_id. unfold M64. lia. }
assert (Ud : U E (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff n 0))) = 2 ^ 64 - 1).
{ rewrite U_SAlu, U_SLit, Us. cbn [zalu_raw]. rewrite (zcanon_id 0) by (unfold M64; lia).
  unfold zcanon, M64. reflexivity. }
assert (Uand : U E (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff n 0))) (SOff n 0)) = v).
{ rewrite U_SAlu, Ud, Ua. cbn [zalu_raw].
  replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity. rewrite Z.land_comm, Z.land_ones by lia.
  rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia. }
rewrite U_SAlu, Uand, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma gsc_lts_lit : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
intros x y Hx Hy.
assert (Ux : bv_unsigned (Z_to_bv 64 x) = x) by (apply unsigned_lit_small; lia).
assert (Uy : bv_unsigned (Z_to_bv 64 y) = y) by (apply unsigned_lit_small; lia).
rewrite bv_lts_signed.
rewrite (signed_of_small (Z_to_bv 64 x)) by (rewrite Ux; unfold half64; lia).
rewrite (signed_of_small (Z_to_bv 64 y)) by (rewrite Uy; unfold half64; lia).
rewrite Ux, Uy. reflexivity.
Qed.

(* blez a1 (bge zero, a1) on a nonnegative atom *)
Lemma gsc_bge0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = (v <=? 0).
Proof.
intros E n v Hn Hv. unfold branch_taken. cbn [sv_denot].
rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite (gsc_lts_lit 0 v) by lia.
destruct (Z.ltb_spec 0 v), (Z.leb_spec v 0); try reflexivity; lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Lemma gsc_aview_garr8 : forall (W : world SEGS) m base l j,
garr8 SEGS (arm W m) base l -> (j < length l)%nat ->
aview SEGS (w_H W) m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m base l j Hg Hj. destruct (Hg j Hj) as (_ & Hr).
unfold aview. change (mrestrict (w_H W) m) with (arm W m).
rewrite (garr8_mbyte SEGS (arm W m) base l j Hg Hj). cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact Hr.
Qed.

Lemma gsc_garr8_sub : forall (W : world SEGS) m base l o n,
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

Lemma gsc_first_byte : forall (W : world SEGS) m base (l : list Z) (n k : Z),
garr8 SEGS (arm W m) base l -> 0 <= k <= n -> n <= Z.of_nat (length l) ->
(forall i, (i < Z.to_nat k)%nat -> nth i l 0 <> 0) ->
(k < n -> nth (Z.to_nat k) l 0 = 0) ->
first_byte SEGS W m base n 0 k.
Proof.
intros W m base l n k Hg Hkn Hnl Hnz Hz. split; [exact Hkn|]. split.
- intros i Hi. exists (nth (Z.to_nat i) l 0). split.
  + replace (base + i) with (base + Z.of_nat (Z.to_nat i)) by lia.
    apply (gsc_aview_garr8 W m base l (Z.to_nat i) Hg). lia.
  + apply Hnz. lia.
- intros Hlt. replace (base + k) with (base + Z.of_nat (Z.to_nat k)) by lia.
  rewrite (gsc_aview_garr8 W m base l (Z.to_nat k) Hg ltac:(lia)). rewrite (Hz Hlt). reflexivity.
Qed.

Lemma gsc_agree_iff : forall (W : world SEGS) m x y (n : Z) (lx ly : list Z),
garr8 SEGS (arm W m) x lx -> garr8 SEGS (arm W m) y ly ->
0 <= n -> n <= Z.of_nat (length lx) -> n <= Z.of_nat (length ly) ->
(forall i, (i < Z.to_nat n)%nat -> nth i lx 0 <> 0) ->
(astrn_agree W m x y n <-> firstn (Z.to_nat n) lx = firstn (Z.to_nat n) ly).
Proof.
intros W m x y n lx ly Hx Hy Hn Hlx Hly Hnz.
assert (AV : forall i, (i < Z.to_nat n)%nat ->
  aview SEGS (w_H W) m (x + Z.of_nat i) = Some (nth i lx 0) /\
  aview SEGS (w_H W) m (y + Z.of_nat i) = Some (nth i ly 0)).
{ intros i Hi. split; [apply (gsc_aview_garr8 W m x lx i Hx) | apply (gsc_aview_garr8 W m y ly i Hy)]; lia. }
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

Lemma gsc_garr8_kept : forall (W : world SEGS) m (W' : world SEGS) m' a l,
garr8 SEGS (arm W m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') a l.
Proof.
intros W m W' m' a l H K. apply (garr8_frame SEGS (arm W m) (arm W' m') a l H).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (K x Hx).
Qed.

Lemma gsc_vm_keep : forall (W : world SEGS) m m' a (n : nat) v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W m') a n v.
Proof.
intros W m m' a n v K H k Hk. unfold arm.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) m m' (a + Z.of_nat k) (K (a + Z.of_nat k) ltac:(lia))).
exact (H k Hk).
Qed.

Lemma gsc_val_of_garr8 : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)) -> val_mem SEGS (arm W m) a n v.
Proof.
intros W m a n v Hv H k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n v)))%nat) by (rewrite gsc_bzs_len, length_Z_to_le_bytes; exact Hk).
rewrite (garr8_mbyte SEGS (arm W m) a _ k H Hl). rewrite gsc_nth_le_bytes by assumption. reflexivity.
Qed.

Lemma gsc_garr8_at : forall mem b l b', garr8 SEGS mem b l -> b = b' -> garr8 SEGS mem b' l.
Proof. intros mem b l b' H <-. exact H. Qed.

(* slot n of the held array, from the array's byte image *)
Lemma gsc_slot_val : forall (W : world SEGS) m hp (ks : list (Z * list byte * list byte)) (n : nat),
garr8 SEGS (arm W m) hp (bzs (key_ptrs ks)) -> (n < length ks)%nat ->
0 <= key_addr (nth n ks (0, [], [])) < 2 ^ 64 ->
val_mem SEGS (arm W m) (hp + 8 * Z.of_nat n) 8 (key_addr (nth n ks (0, [], []))).
Proof.
intros W m hp ks n Hg Hn Hk.
destruct (nth_split ks (0, [], []) Hn) as (a & b & E & Ha).
set (x := nth n ks (0, [], [])) in *. clearbody x. subst ks n.
rewrite gsx_key_ptrs_cat, gsx_key_ptrs_cons, !gsc_bzs_app in Hg.
apply garr8_app in Hg as [_ Hg]. apply garr8_app in Hg as [Hg _].
rewrite (gsc_le8_bytes (key_addr x) Hk) in Hg.
apply (gsc_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hk|].
apply (gsc_garr8_at _ _ _ _ Hg). rewrite gsc_bzs_len, gs_key_ptrs_len. lia.
Qed.

(* the line's bytes at s->buf + p *)
Lemma gsc_line_garr8 : forall (W : world SEGS) m s1 p q e1,
garr8 SEGS (arm W m) (re_buf e1) (bzs (re_U e1 ++ re_junk e1)) -> bzs (re_U e1) = dW s1 ->
(p <= q < length (dW s1))%nat ->
garr8 SEGS (arm W m) (re_buf e1 + Z.of_nat p) (dline s1 p q).
Proof.
intros W m s1 p q e1 Hg HU Hpq.
assert (E : dline s1 p q = firstn (q - p) (skipn p (bzs (re_U e1 ++ re_junk e1)))).
{ unfold dline. rewrite gsc_bzs_app, HU, skipn_app, firstn_app.
  replace (p - length (dW s1))%nat with 0%nat by lia.
  rewrite length_skipn. replace (q - p - (length (dW s1) - p))%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r. reflexivity. }
rewrite E. apply gsc_garr8_sub; [exact Hg|].
rewrite gsc_bzs_len, length_app. rewrite <- gsc_bzs_len, HU. lia.
Qed.

Lemma gsc_dline_nth_nz : forall s1 p q, (p <= q < length (dW s1))%nat ->
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) ->
forall i, (i < q - p)%nat -> nth i (dline s1 p q) 0 <> 0.
Proof.
intros s1 p q Hpq Hnz i Hi E. unfold dline in E.
rewrite nth_firstn, (proj2 (Nat.ltb_lt i (q - p)) Hi), nth_skipn in E.
apply (Hnz (p + i)%nat); [lia|]. rewrite (nth_error_nth' (dW s1) 0) by lia. rewrite E. reflexivity.
Qed.

(* a run whose regions have no write window writes nothing (W_drain_next.v dn_frame_nil, for any regions) *)
Lemma gsc_frame_nil : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hn a Ha. apply (aview_kept_out E rs H m m' HF a Ha).
intros (r & Hin & Hr). rewrite forallb_forall in Hn. specialize (Hn r Hin). apply Z.leb_le in Hn. lia.
Qed.

(* ---- The line loop's model after a BEGIN whose key is held: nothing moves (W_gsscanb.v gsl_dlc_same). ---- *)
Lemma gsc_dlc_same : forall B MT MMAX RG cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl,
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

Lemma gsc_dlfut_same : forall cx s1 p q a jb o ha ks tl,
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

(* the held keys the relay entry carries are the line loop's set *)
Lemma gsc_link_H : forall cx s1 sk H ka no oc e1 h1,
DLINK (dvirt cx s1 sk H ka no oc) e1 h1 -> drain_b_c.keys_texts (re_keys e1) = H.
Proof. intros cx s1 sk H ka no oc e1 h1 (_ & _ & _ & HH & _). unfold dvirt in HH. cbn [drain_b_c.ds_H] in HH. exact HH. Qed.

Lemma gsc_link_U : forall cx s1 sk H ka no oc e1 h1,
DLINK (dvirt cx s1 sk H ka no oc) e1 h1 -> bzs (re_U e1) = dW s1.
Proof. intros cx s1 sk H ka no oc e1 h1 (_ & HU & _). unfold dvirt in HU. cbn [drain_b_c.ds_u] in HU. exact HU. Qed.

Lemma gsc_nth_H : forall cx s1 sk H ka no oc e1 h1 n,
DLINK (dvirt cx s1 sk H ka no oc) e1 h1 -> (n < length (re_keys e1))%nat ->
nth n H [] = bzs (key_text (nth n (re_keys e1) (0, [], []))).
Proof.
intros cx s1 sk H ka no oc e1 h1 n HL Hn. rewrite <- (gsc_link_H _ _ _ _ _ _ _ _ _ HL). apply gs_keys_texts_nth. exact Hn.
Qed.

(* the frame slots the GS stage writes (relative to drain's sp): 0, 16, 24, 96, 112, 160, 168, 192; every other
   byte of the frame (dr_frame's 23 one-time slots and the 13 saves) is never written by the stage *)
Definition gsW (o : Z) : Prop :=
(0 <= o < 8) \/ (16 <= o < 32) \/ (96 <= o < 104) \/ (112 <= o < 120) \/ (160 <= o < 176) \/ (192 <= o < 200).

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

(* ---------------------------------------------------------------------------------------------------------
   (1) Lowness: every byte the line loop's core reads lies below alloc_ceiling, far below drain's frame.
   --------------------------------------------------------------------------------------------------------- *)
Lemma gsc_blk_low : forall ly S (W : world SEGS) mem md qq nn a,
AR SEGS B ly S W mem md -> In (qq, nn) (ablocks B ly S) -> qq <= a -> a < qq + req_size nn ->
0 <= a < alloc_ceiling.
Proof using LAWS. clear - LAWS.
intros ly S W mem md qq nn a HAR Hin H1 H2.
destruct (al_blocks SEGS B LAWS ly S W mem md qq nn HAR Hin) as (_ & H4096 & Hceil & _). lia.
Qed.

Lemma gsc_img_low : forall a lo hi, 0x10000 <= lo -> lo <= a -> a < hi -> hi <= IMG_TOP ->
0 <= a < alloc_ceiling.
Proof using. gsc_clr0. intros a lo hi H1 H2 H3 H4. pose proof asan_consts as (C1 & _). unfold IMG_TOP in *. lia. Qed.

Lemma gsc_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof using. gsc_clr0.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma gsc_aentry_fp_low : forall ly S (W : world SEGS) mem md e,
AR SEGS B ly S W mem md -> aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof using LAWS. clear - LAWS.
intros ly S W mem md e HAR HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (HPK : forall k, In k (re_keys e) ->
  key_addr k <= a < key_addr k + Z.of_nat (length (bzs (key_text k ++ [Z_to_bv 8 0]))) ->
  0 <= a < alloc_ceiling).
{ intros k Hk Hak. rewrite gsc_bzs_len, length_app in Hak. cbn [length] in Hak.
  rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
  apply (gsc_blk_low ly S W mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) a HAR Hin); [lia|].
  pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & Hrq). lia. }
assert (HPH : re_hp e <= a < re_hp e + Z.of_nat (length (bzs (key_ptrs (re_keys e)))) ->
  0 <= a < alloc_ceiling).
{ intros Hah. rewrite gsc_bzs_len, gs_key_ptrs_len in Hah.
  destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
  - rewrite Hke in Hah. cbn [length] in Hah. lia.
  - apply (gsc_blk_low ly S W mem md (re_hp e) (re_kh e) a HAR Hin); [lia|].
    pose proof (req_size_pos (re_kh e) ltac:(lia)) as (_ & Hrq). unfold re_nheld in Hk1. lia. }
unfold aentry_fp in Hr.
destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [app In] in Hr.
- destruct Hr as [<- | Hr]; [unfold gfp in Ha; cbn [fst snd] in Ha; exact (HPH Ha)|].
  apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPK k Hk Ha).
- destruct Hr as [<- | [<- | Hr]].
  + unfold gfp in Ha. cbn [fst snd] in Ha. rewrite gsc_bzs_len, length_app in Ha.
    destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (gsc_blk_low ly S W mem md (re_buf e) (re_cap e) a HAR Hin); [lia|].
    pose proof (req_size_pos (re_cap e) ltac:(lia)) as (_ & Hrq). lia.
  + unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPH Ha).
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPK k Hk Ha).
Qed.

Lemma gsc_alist_fp_low : forall ly S (W : world SEGS) mem md LA l lines lo hi,
AR SEGS B ly S W mem md -> alist_at B ly S W mem LA l lines ->
0x10000 <= lo -> lo <= LA -> LA + 16 <= hi -> hi <= IMG_TOP ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof using LAWS. clear - LAWS.
intros ly S W mem md LA l lines lo hi HAR HL Hlo1 Hlo2 Hhi1 Hhi2 r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (gsc_img_low a lo hi); lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite gsc_bzs_len, length_app, gsc_recs_len in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (gsc_blk_low ly S W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin); [lia|].
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as (_ & Hrq).
    unfold hl_n, AREC in *. lia.
  + apply in_map_iff in Hr as (qq & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite gsc_bzs_len, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs qq Hq) as (Hin & _).
    apply (gsc_blk_low ly S W mem md (fst qq) (Z.of_nat (length (snd qq)) + 1) a HAR Hin); [lia|].
    pose proof (req_size_pos (Z.of_nat (length (snd qq)) + 1) ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma gsc_asrc_fp_low : forall ly S (W : world SEGS) mem md HA h,
AR SEGS B ly S W mem md -> asrc_at B ly S W mem HA h ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof using LAWS HGSB. clear - LAWS HGSB.
intros ly S W mem md HA h HAR HS Hlo Hhi r Hr a Ha.
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (gsc_img_low a (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. rewrite gsc_bzs_len in Ha.
  apply (gsc_blk_low ly S W mem md (hs_partial h) APARTIAL a HAR Hpb); [lia|].
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq). lia.
- unfold ASRC in *. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + eapply (gsc_alist_fp_low ly S W mem md (HA + 16) (hs_pending h) false (rg_s RG) (rg_s RG + 4 * 96));
      [exact HAR | exact Hpend | lia | lia | lia | lia | exact Hr | exact Ha].
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * eapply (gsc_alist_fp_low ly S W mem md (HA + 64) (hs_expected h) true (rg_s RG) (rg_s RG + 4 * 96));
        [exact HAR | exact Hexp | lia | lia | lia | lia | exact Hr | exact Ha].
    * eapply (gsc_alist_fp_low ly S W mem md (HA + 80) (hs_held h) true (rg_s RG) (rg_s RG + 4 * 96));
        [exact HAR | exact Hheld | lia | lia | lia | lia | exact Hr | exact Ha].
Qed.

Ltac gsc_ing := unfold G_DR, G_SL; cbn [In]; repeat (first [left; reflexivity | right]).

Lemma gsc_aout_fp_low : forall ly S (W : world SEGS) mem md c O mx no cap out,
AR SEGS B ly S W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof using LAWS HG HSM HV9 HSD. clear - LAWS HG HSM HV9 HSD.
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
- pose proof HSM as (Hs1 & Hs2). apply (gsc_img_low a (rg_send_max RG) (rg_send_max RG + 8)); lia.
- apply (GL2 (rg_nout RG) 8); [gsc_ing | lia].
- apply (GL2 (rg_capout RG) 8); [gsc_ing | lia].
- apply (GL2 (rg_out RG) 8); [gsc_ing | lia].
- pose proof (pa_obj_img 9 ltac:(lia)) as H9. rewrite HV9 in H9.
  apply (gsc_img_low a (rg_client RG) (rg_client RG + 4)); unfold IMG_TOP; lia.
- apply (GL2 (rg_client_broken RG) 1); [gsc_ing | lia].
- pose proof HSD as (Hs1 & Hs2). apply (gsc_img_low a (rg_send_dead RG) (rg_send_dead RG + 1)); lia.
- apply (GL2 (rg_send_eintr RG) 1); [gsc_ing | lia].
- apply (GL2 (as_errno B) 4); [gsc_ing | lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  apply (gsc_blk_low ly S W mem md out cap a HAR Hin); [lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq). lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (2) The cut survives the stage: dr_frame across a step that keeps every frame byte outside the stage's own
   slots, and the line loop's core across a step that keeps every byte below alloc_ceiling.
   --------------------------------------------------------------------------------------------------------- *)
Lemma gsc_frame_keep : forall cx (W1 : world SEGS) m1 m2,
(forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> ~ gsW (x - (dsp0 cx - DRAIN_FRAME)) ->
  aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x) ->
dr_frame RG cx W1 m1 -> dr_frame RG cx W1 m2.
Proof using. gsc_clr0.
intros cx W1 m1 m2 K HFR. unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
destruct HFR as (F8 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F104 & F120 & F128 & F136 & F144 & F152 &
  F176 & F184 & F200 & F208 & F216 & F224 & F232 & F240 & Hsvd).
repeat match goal with |- _ /\ _ => split end;
  try (apply (gsc_vm_keep W1 m1 m2 _ 8%nat _);
       [intros x Hx; cbn in Hx; apply K; unfold gsW, DRAIN_FRAME in *; lia | assumption]).
unfold dr_saved in Hsvd |- *. intros i Hi. apply (gsc_vm_keep W1 m1 m2 _ 8%nat _); [|exact (Hsvd i Hi)].
intros x Hx. cbn in Hx. apply K; unfold gsW, DR_SAVE_OFF, DRAIN_FRAME in *; lia.
Qed.

Lemma gsc_core_kept : forall cx s1 D p q ly1 S1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2 k2,
(dxj cx < 4)%nat -> 4096 <= dxSA cx -> dxSA cx + 56 <= alloc_ceiling ->
GSB B MT MMAX RG cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k2 ->
(forall x, 0 <= x < alloc_ceiling -> aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m2 x) ->
dr_frame RG cx W1 m2 ->
GSB B MT MMAX RG cx s1 D p q ly1 S1 W1 m2 md2 k2 e1 h1 out1 ev1 LB1 spent tl.
Proof using LAWS HG HGSB HV9 HSD HSM. clear - LAWS HG HGSB HV9 HSD HSM.
intros cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2 k2 HJ4 HSA1 HSA2 HGS HJ2 KL PRES HFR2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold GSB, LCORE in HGS |- *.
destruct HGS as (HMEM & HLINK & HSAME & HHIST & HRS & HBUD).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR1 : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (AK : forall fp, (forall r, In r fp -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling) ->
  akept W1 m1 W1 m2 fp) by (intros fp Hlow; exact (gs_akept_of W1 m1 m2 fp KL PRES Hlow)).
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
split; [exact HFR2|].
split.
{ apply (gsc_garr8_kept W1 m1 W1 m2); [exact Hgarr|].
  intros x Hx. rewrite gsc_bzs_len in Hx. apply KL.
  assert (HL56 : length (entry_bytes e1) = 56%nat).
  { pose proof HOKX as (_ & _ & Hp1 & Hp2 & _). unfold entry_bytes.
    rewrite !length_app, Hp1, Hp2, !Mem.length_le8, !Mem.length_le4. reflexivity. }
  rewrite HL56 in Hx. lia. }
split.
{ intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m2 _ (PRES _)). exact (Hawr i Hi). }
split.
{ eapply (gs_aentry_okx_kept B).
  - exact HOKX.
  - apply AK. exact (gsc_aentry_fp_low ly1 S1 W1 m1 md1 e1 HAR1 HOKX).
  - intros b Hb. apply HBLK. apply in_or_app. left. exact Hb. }
split.
{ eapply asrc_at_kept.
  - exact Hsrc.
  - apply AK. apply (gsc_asrc_fp_low ly1 S1 W1 m1 md1 (dHA RG cx) h1 HAR1 Hsrc);
      unfold dHA, ASRC in *; lia.
  - intros b Hb. apply HBLK. apply in_or_app. right. apply in_or_app. left. exact Hb. }
split.
{ pose proof HGSB as (Hg1 & Hg2 & _). unfold aothers_at in Hoth |- *.
  intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & Mf & Mo & Hfo).
  exists f, o. split; [|split; [|exact Hfo]];
  apply (gsc_vm_keep W1 m1 m2 _ 4%nat _); [| exact Mf | | exact Mo];
  intros x Hx; apply KL; apply (gsc_img_low x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; cbn in Hx; lia. }
split.
{ intros x Hx Hnx. destruct (Hgsk x Hx Hnx) as (Hv & Hw). split.
  - rewrite KL; [exact Hv|]. pose proof HGSB as (Hg1 & Hg2 & _).
    apply (gsc_img_low x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
  - intros Hwr. unfold arm. apply (writable_kept (w_H W1) m1 m2 _ (PRES _)). exact (Hw Hwr). }
split.
{ eapply aout_at_kept.
  - exact Hout.
  - apply AK. exact (gsc_aout_fp_low ly1 S1 W1 m1 md1 _ _ _ _ _ _ HAR1 Hout).
  - intros b Hb. apply HBLK. apply in_or_app. right. apply in_or_app. right. exact Hb. }
split; [exact Hlivout | exact Hperm].
Qed.

(* the stack facts every walk of the stage uses, from DBASE *)
Lemma gsc_stack : forall cx, DBASE B MT MMAX RG cx ->
alloc_ceiling + 2 * ESTACK + DRAIN_FRAME <= dsp0 cx /\ dsp0 cx <= 2 ^ 47 /\ dsp0 cx mod 16 = 0 /\
(dxj cx < 4)%nat.
Proof using. gsc_clr0.
intros cx HB.
pose proof HB as (Hafn & _ & _ & _ & _ & _ & _ & _ & _ & Hj4 & _).
pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HDS : DRAIN_STK = 16880) by reflexivity. rewrite HDS in Hslo.
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
unfold dsp0. split; [lia|]. split; [lia|]. split; [exact Hal16 | exact Hj4].
Qed.

(* the relay entry's place, from DBASE and the core's table block *)
Lemma gsc_sa : forall cx ly1 S1 (W1 : world SEGS) m1 md1 k1 e1 h1 s out1 ev1 sent LB1,
DBASE B MT MMAX RG cx -> DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 ->
4096 <= dxSA cx /\ dxSA cx + 56 <= alloc_ceiling.
Proof using LAWS. clear - LAWS.
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

(* ---------------------------------------------------------------------------------------------------------
   (3) The loop's cuts.
   --------------------------------------------------------------------------------------------------------- *)
Definition A_dr_hnext : Z := AF_fr_drain + 0x914.   (* 0x83b8c, the loop's bottom *)

Lemma P0_dr_hnext : fr_B0 + A_dr_hnext = 0x83b8c.
Proof using. gsc_clr0. reflexivity. Qed.

(* The body shared by GSL (0x83b34, no match below n) and GSN (0x83b8c, no match below S n), with the no-match
   bound nm as a parameter.  s3 (x19) = kf, the slots left; s4 (x20) = 8 n; s6 (x22) = e->hp; s9 (x25) = 1
   (snez hp); the stage's scratch slots 0, 16, 24, 96, 112 (what GA / GF read), 160 = 8 nheld, 168 = 1 (hp
   aligned and not null) and 192 = jj. *)
Definition GSBODY (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf nm : nat) (W1 : world SEGS)
(regs1 : bvmap 5 word) ly1 S1 (m1 : word -> option byte) md1 k1 e1 h1 out1 ev1 LB1 spent
(jb : nat) (a : drain_b_c.dadr) (o ha : dadrF) (ks : list dadrF) (tl : dtrace) (kd : gkind) (jj : nat) (bg : Z)
: Prop :=
dregs_gs RG cx regs1 W1 m1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME) 8 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 24) 8 bg /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 96) 8 ((dxSA cx + 40) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 112) 8 (re_nheld e1) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 160) 8 (8 * re_nheld e1) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 168) 8 1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 (Z.of_nat jj) /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 19 = w64 (Z.of_nat kf) /\ getr regs1 20 = w64 (8 * Z.of_nat n) /\
getr regs1 22 = w64 (re_hp e1) /\ getr regs1 25 = w64 1 /\
(n + kf = length (re_keys e1))%nat /\ (0 < kf)%nat /\
(forall i, (i < nm)%nat -> nth i (dlH cx s1 p) [] <> firstn jj (dline s1 p q)) /\
0 <= bg < 2 ^ 64 /\ (bg = 0 <-> kd = GBegin) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
GSF s1 p q /\
GSB B MT MMAX RG cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.

Definition GSL (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_hloop) regs1 m1 md1 /\
GSBODY cx s1 D p q n kf n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.

Definition GSN (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_hnext) regs1 m1 md1 /\
GSBODY cx s1 D p q n kf (S n) W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.

(* The loop, by induction on kf.  It consumes GSL at n and reaches one of the segment's three exits. *)
Definition gs_scan_loop_stmt : Prop :=
forall cx s1 D p q n kf W1 c1,
DBASE B MT MMAX RG cx -> GSL cx s1 D p q n kf W1 c1 ->
(forall W2 c2, DLN B MT MMAX RG cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, GA B MT MMAX RG cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, GF B MT MMAX RG cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

(* ---- the body across a step that writes only the interceptors' scratch below drain's frame ---- *)
Definition GSKEEP (cx : dcx) (W1 : world SEGS) (m1 m2 : word -> option byte) : Prop :=
(forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME - 2 * ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
   aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x) /\
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m2 x).

Lemma gsc_keep_trans : forall cx W1 m1 m2 m3, GSKEEP cx W1 m1 m2 -> GSKEEP cx W1 m2 m3 -> GSKEEP cx W1 m1 m3.
Proof using. gsc_clr0.
intros cx W1 m1 m2 m3 (K1 & P1) (K2 & P2). split.
- intros x Hx Hs. rewrite (K2 x Hx Hs). exact (K1 x Hx Hs).
- intros x Hp. exact (P2 x (P1 x Hp)).
Qed.

Lemma gsc_fv_keep : forall cx (W1 : world SEGS) m1 m2 off v,
DRAIN_FRAME <= dsp0 cx <= 2 ^ 47 -> 0 <= off -> off + 8 <= DRAIN_FRAME ->
GSKEEP cx W1 m1 m2 ->
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + off) 8 v -> val_mem SEGS (arm W1 m2) (dsp0 cx - DRAIN_FRAME + off) 8 v.
Proof using. gsc_clr0.
intros cx W1 m1 m2 off v Hsp Ho1 Ho2 (K & _) H.
apply (gsc_vm_keep W1 m1 m2 _ 8%nat _); [|exact H].
intros x Hx. apply K; unfold ESTACK, DRAIN_FRAME in *; cbn in Hx; lia.
Qed.

Lemma gsc_dregs_keep : forall cx (W1 : world SEGS) m1 m2 regs1,
DRAIN_FRAME <= dsp0 cx <= 2 ^ 47 -> GSKEEP cx W1 m1 m2 ->
dregs_gs RG cx regs1 W1 m1 -> dregs_gs RG cx regs1 W1 m2.
Proof using. gsc_clr0.
intros cx W1 m1 m2 regs1 Hsp (K & _) (R2 & R3 & R4 & R8 & R9 & R18 & HFR).
do 6 (split; [assumption|]).
apply (gsc_frame_keep cx W1 m1 m2); [|exact HFR].
intros x Hx _. apply K; unfold ESTACK, DRAIN_FRAME in *; lia.
Qed.

Lemma gsc_body_keep : forall cx s1 D p q n kf nm W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  m2 md2,
DBASE B MT MMAX RG cx ->
GSBODY cx s1 D p q n kf nm W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k1 ->
GSKEEP cx W1 m1 m2 ->
GSBODY cx s1 D p q n kf nm W1 regs1 ly1 S1 m2 md2 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof using LAWS HG HGSB HV9 HSD HSM. clear - LAWS HG HGSB HV9 HSD HSM.
intros cx s1 D p q n kf nm W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg m2 md2
  HB HBD HJ2 HKP.
destruct (gsc_stack cx HB) as (HS1 & HS2 & _ & Hj4).
pose proof asan_consts as (C1 & _).
unfold GSBODY in HBD |- *.
destruct HBD as (HRG & M0 & M16 & M24 & M96 & M112 & M160 & M168 & M192 & R23 & R24 & R19 & R20 & R22 & R25
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (HMEM & _).
destruct (gsc_sa cx _ _ _ _ _ _ _ _ _ _ _ _ _ HB HMEM) as (HSA1 & HSA2).
assert (HSPR : DRAIN_FRAME <= dsp0 cx <= 2 ^ 47) by (unfold ESTACK, DRAIN_FRAME in *; lia).
split; [exact (gsc_dregs_keep cx W1 m1 m2 regs1 HSPR HKP HRG)|].
split; [replace (dsp0 cx - DRAIN_FRAME) with (dsp0 cx - DRAIN_FRAME + 0) in M0 |- * by lia;
  apply (gsc_fv_keep cx W1 m1 m2 _ _ HSPR); [lia | unfold DRAIN_FRAME; lia | exact HKP | exact M0]|].
do 7 (split; [apply (gsc_fv_keep cx W1 m1 m2 _ _ HSPR); [lia | unfold DRAIN_FRAME; lia | exact HKP | assumption]|]).
do 16 (split; [assumption|]).
split; [|exact HFUT].
pose proof HKP as (KEEP & PRES).
apply (gsc_core_kept cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2 k1 Hj4 HSA1 HSA2 HCORE HJ2).
- intros x Hx. apply KEEP; [lia|]. unfold ESTACK, DRAIN_FRAME in *. lia.
- exact PRES.
- exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (gsc_dregs_keep cx W1 m1 m2 regs1 HSPR HKP HRG))))))).
Qed.

(* the registers the body pins other than s3 / s4 *)
Definition GSREGS (regs1 regs2 : bvmap 5 word) : Prop :=
getr regs2 2 = getr regs1 2 /\ getr regs2 3 = getr regs1 3 /\ getr regs2 4 = getr regs1 4 /\
getr regs2 8 = getr regs1 8 /\ getr regs2 9 = getr regs1 9 /\ getr regs2 18 = getr regs1 18 /\
getr regs2 22 = getr regs1 22 /\ getr regs2 23 = getr regs1 23 /\ getr regs2 24 = getr regs1 24 /\
getr regs2 25 = getr regs1 25.

Lemma gsc_dregs_regs : forall cx regs1 regs2 (W1 : world SEGS) m1,
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
dregs_gs RG cx regs1 W1 m1 -> dregs_gs RG cx regs2 W1 m1.
Proof using. gsc_clr0.
intros cx regs1 regs2 W1 m1 Q2 Q3 Q4 Q8 Q9 Q18 (R2 & R3 & R4 & R8 & R9 & R18 & HFR).
unfold dregs_gs, spZ in *. rewrite Q2, Q3, Q4, Q8, Q9, Q18. tauto.
Qed.

(* GSN's body from the head's: the registers unchanged, slot n not matched *)
Lemma gsc_mk_gsn : forall cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY cx s1 D p q n kf n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
GSREGS regs1 regs2 -> getr regs2 19 = getr regs1 19 -> getr regs2 20 = getr regs1 20 ->
nth n (dlH cx s1 p) [] <> firstn jj (dline s1 p q) ->
GSBODY cx s1 D p q n kf (S n) W1 regs2 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof using. gsc_clr0.
intros cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q22 & Q23 & Q24 & Q25) Q19 Q20 Hn.
unfold GSBODY in HBD |- *.
destruct HBD as (HRG & M0 & M16 & M24 & M96 & M112 & M160 & M168 & M192 & R23 & R24 & R19 & R20 & R22 & R25
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr & HGSF & HCORE & HFUT).
split; [exact (gsc_dregs_regs cx regs1 regs2 W1 m1 Q2 Q3 Q4 Q8 Q9 Q18 HRG)|].
rewrite Q19, Q20, Q22, Q23, Q24, Q25.
do 16 (split; [assumption|]).
split; [intros i Hi; destruct (Nat.eq_dec i n) as [->|Hne]; [exact Hn | apply Hnm; lia]|].
do 8 (split; [assumption|]). exact HFUT.
Qed.

(* the loop's head at S n from GSN at n, s3 and s4 stepped *)
Lemma gsc_mk_loop : forall cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY cx s1 D p q n (S kf) (S n) W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
(0 < kf)%nat ->
GSREGS regs1 regs2 ->
getr regs2 19 = w64 (Z.of_nat kf) -> getr regs2 20 = w64 (8 * Z.of_nat (S n)) ->
GSBODY cx s1 D p q (S n) kf (S n) W1 regs2 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof using. gsc_clr0.
intros cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD Hkf0 (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q22 & Q23 & Q24 & Q25) Q19 Q20.
unfold GSBODY in HBD |- *.
destruct HBD as (HRG & M0 & M16 & M24 & M96 & M112 & M160 & M168 & M192 & R23 & R24 & R19 & R20 & R22 & R25
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr & HGSF & HCORE & HFUT).
split; [exact (gsc_dregs_regs cx regs1 regs2 W1 m1 Q2 Q3 Q4 Q8 Q9 Q18 HRG)|].
rewrite Q22, Q23, Q24, Q25.
do 10 (split; [assumption|]).
split; [exact Q19|]. split; [exact Q20|].
do 2 (split; [assumption|]).
split; [lia|]. split; [exact Hkf0|].
do 9 (split; [assumption|]). exact HFUT.
Qed.

(* GA from GSN at the last slot *)
Lemma gsc_mk_ga : forall cx s1 D p q n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY cx s1 D p q n 1 (S n) W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 ->
getr regs2 27 = w64 (dxSA cx + 32) ->
GA B MT MMAX RG cx s1 D p q W1 (cfg_at SEGS (BASE + A_dr_add) regs2 m1 md1).
Proof using. gsc_clr0.
intros cx s1 D p q n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD Q2 Q3 Q4 Q8 Q9 Q18 Q23 Q24 Q27.
unfold GSBODY in HBD.
destruct HBD as (HRG & M0 & M16 & M24 & M96 & M112 & M160 & M168 & M192 & R23 & R24 & R19 & R20 & R22 & R25
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr & HGSF & HCORE & HFUT).
exists regs2, ly1, S1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl, kd, jj, bg.
split; [reflexivity|].
split; [exact (gsc_dregs_regs cx regs1 regs2 W1 m1 Q2 Q3 Q4 Q8 Q9 Q18 HRG)|].
split; [exact Q27|].
rewrite Q23, Q24.
do 13 (split; [assumption|]).
split.
{ apply gs_index_none. intros i Hi. apply Hnm.
  pose proof HCORE as (_ & HLINK & _).
  rewrite <- (gsc_link_H _ _ _ _ _ _ _ _ _ HLINK), gs_keys_texts_len in Hi. lia. }
split; [exact HGSF|]. split; [exact HCORE | exact HFUT].
Qed.

(* a BEGIN whose key is held at slot n: DLN (S q), with s5 / s6 / s4 / s11 restored from the frame *)
Lemma gsc_mk_dln : forall cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY cx s1 D p q n kf n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q) -> bg = 0 ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 23 = getr regs1 23 ->
getr regs2 21 = w64 (dxSA cx) -> getr regs2 20 = w64 (dxSA cx + 16) ->
getr regs2 22 = w64 (dxSA cx + 24) -> getr regs2 27 = w64 (dxSA cx + 32) ->
DLN B MT MMAX RG cx s1 D (S q) W1 (cfg_at SEGS (BASE + A_dr_next) regs2 m1 md1).
Proof using. gsc_clr0.
intros cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD Hmt Hbg0 Q2 Q3 Q4 Q8 Q9 Q18 Q23 Q21 Q20 Q22 Q27.
unfold GSBODY in HBD.
destruct HBD as (HRG & M0 & M16 & M24 & M96 & M112 & M160 & M168 & M192 & R23 & R24 & R19 & R20 & R22 & R25
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (_ & HLINK & _).
assert (Hkd : kd = GBegin) by (apply Hbgk; exact Hbg0). subst kd.
assert (Hlen : (n < length (dlH cx s1 p))%nat)
  by (rewrite <- (gsc_link_H _ _ _ _ _ _ _ _ _ HLINK), gs_keys_texts_len; lia).
pose proof (gs_index_some _ _ n Hlen Hmt Hnm) as HI.
destruct (gs_seen_begin_old (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) _ n jb ha ks Hgest HI) as (S1e & S2e & S3e).
pose proof HGSF as (Hbd & Hpq & Hq0 & _).
pose proof HRG as (R2 & R3 & R4 & R8 & R9 & R18 & HFR).
exists regs2, ly1, S1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
split; [reflexivity|].
split.
{ unfold dregs_line, spZ in *. rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q21, Q20, Q22, Q27.
  repeat (split; [first [assumption | reflexivity]|]). exact HFR. }
split; [rewrite Q23, R23; unfold w64; f_equal; lia|].
split; [exact Hband|]. split; [exact Hcap|].
split; [unfold dbound; split; [lia|right]; replace (S q - 1)%nat with q by lia; exact Hq0|].
split; [lia|].
split; [exact (gsc_dlc_same B MT MMAX RG cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl HGSF S1e S3e HCORE)|].
exact (gsc_dlfut_same cx s1 p q a jb o ha ks tl HGSF S2e S1e S3e HFUT).
Qed.

(* an END whose key is held at slot n: GF *)
Lemma gsc_mk_gf : forall cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2,
GSBODY cx s1 D p q n kf n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q) -> bg <> 0 ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 ->
getr regs2 20 = getr regs1 20 -> getr regs2 22 = getr regs1 22 ->
getr regs2 26 = w64 (re_hp e1 + 8 * Z.of_nat n) ->
getr regs2 21 = w64 ((re_hp e1 + 8 * Z.of_nat n) / 8 + SHADOW_OFF) ->
GF B MT MMAX RG cx s1 D p q W1 (cfg_at SEGS (BASE + A_dr_free) regs2 m1 md1).
Proof using. gsc_clr0.
intros cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD Hmt Hbg0 Q2 Q3 Q4 Q8 Q9 Q18 Q23 Q24 Q20 Q22 Q26 Q21.
unfold GSBODY in HBD.
destruct HBD as (HRG & M0 & M16 & M24 & M96 & M112 & M160 & M168 & M192 & R23 & R24 & R19 & R20 & R22 & R25
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (_ & HLINK & _).
assert (Hkd : kd = GEnd) by (destruct kd; [exfalso; apply Hbg0; apply Hbgk; reflexivity | reflexivity]). subst kd.
assert (Hlen : (n < length (dlH cx s1 p))%nat)
  by (rewrite <- (gsc_link_H _ _ _ _ _ _ _ _ _ HLINK), gs_keys_texts_len; lia).
pose proof (gs_index_some _ _ n Hlen Hmt Hnm) as HI.
exists regs2, ly1, S1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl, jj, n.
split; [reflexivity|].
split; [exact (gsc_dregs_regs cx regs1 regs2 W1 m1 Q2 Q3 Q4 Q8 Q9 Q18 HRG)|].
rewrite Q23, Q24, Q20, Q22, Q26, Q21.
do 6 (split; [first [assumption | reflexivity]|]).
split; [exact M0|]. split; [exact M16|].
split; [exact Hband|]. split; [exact Hcap|].
split; [lia|].
split; [exact Hgest|]. split; [exact Hjjr|].
split; [exact HI|].
split; [exact HGSF|]. split; [exact HCORE | exact HFUT].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (4) The loop's two symbolic seats, as the engine computes them from image B's listing.
   GSL (0x83b34): registers are their own atoms; s3 = atom 19 (kf, in [1, 2^26]: `bnez s3` at 0x83dac decided),
   s4 = atom 20 (8 n), s6 = atom 22 (hp), s9 = atom 25 (= 1).  Atoms 32 = hp + 8 n (both sums aliased),
   33 = held[n], 34 = SHADOW_OFF (240(sp), the shadow base), 35 = 168(sp) = 1, 36 = jj, 37 = SA, 38 = bg,
   39 = 8 nheld.  The frame region carries the slots the loop and its exits read; no region has a write window.
   GSN (0x83b8c): atoms 32 = 8 nheld (160(sp)), 33 = SA (176(sp) = SA + 32); s3's fact makes `addiw s3,-1` the
   64-bit SOff 19 (-1).
   --------------------------------------------------------------------------------------------------------- *)
Definition GL_PHI : Z := 140737479966720.   (* the literal bound of ASAN_CEIL *)
Definition gl_frame : YP09.region := YP09.mkRegion (Some 2%nat) 24 248 0 0
  [ YP09.mkChunk 24 (CVal 8 (SOff 38 0)); YP09.mkChunk 128 (CVal 8 (SOff 37 16));
    YP09.mkChunk 136 (CVal 8 (SOff 37 24)); YP09.mkChunk 144 (CVal 8 (SOff 37 0));
    YP09.mkChunk 160 (CVal 8 (SOff 39 0)); YP09.mkChunk 168 (CVal 8 (SOff 35 0));
    YP09.mkChunk 176 (CVal 8 (SOff 37 32)); YP09.mkChunk 192 (CVal 8 (SOff 36 0));
    YP09.mkChunk 240 (CVal 8 (SOff 34 0)) ].
Definition gl_slot : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 0 [ YP09.mkChunk 0 (CVal 8 (SOff 33 0)) ].
Definition gl_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (34%nat, mkAF SB SB 0);
          (22%nat, mkAF 4096 GL_PHI 3); (20%nat, mkAF 0 (2 ^ 29) 3); (32%nat, mkAF 4096 GL_PHI 3);
          (33%nat, mkAF 4096 GL_PHI 0); (25%nat, mkAF 1 1 0); (35%nat, mkAF 1 1 0); (19%nat, mkAF 1 (2 ^ 26) 0) ] []
  [ (SAlu ALU_ADD (SOff 22 0) (SOff 20 0), SOff 32 0); (SAlu ALU_ADD (SOff 20 0) (SOff 22 0), SOff 32 0) ].
Definition ss_gl : sstate := mkSS A_dr_hloop sr_atoms [ gl_frame; gl_slot ] None gl_facts.
Definition gl_Bx : sv := SOff 34 0.
Definition gl_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gl_SH : list shent := [ mkSHE 32 0 8 ].
Definition gl_extra (SL KP J SA BG NH8 : Z) : list word := map (Z_to_bv 64) [SL; KP; SHADOW_OFF; 1; J; SA; BG; NH8].

Lemma gl_entry : forall (W : world SEGS) regs1 m1 sp HP n KF KP J SA BG NH8,
spZ regs1 = sp -> 2 ^ 46 <= sp -> sp + DRAIN_FRAME <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs1 19 = w64 KF -> 1 <= KF <= 2 ^ 26 ->
getr regs1 20 = w64 (8 * Z.of_nat n) -> 8 * Z.of_nat n <= 2 ^ 29 ->
getr regs1 22 = w64 HP -> getr regs1 25 = w64 1 ->
4096 <= HP -> HP mod 8 = 0 -> HP + 8 * Z.of_nat n + 8 <= GL_PHI -> HP + 8 * Z.of_nat n + 8 <= sp ->
4096 <= KP <= GL_PHI -> 0 <= J < 2 ^ 64 -> 0 <= SA -> SA + 32 < 2 ^ 64 -> 0 <= BG < 2 ^ 64 ->
0 <= NH8 < 2 ^ 64 ->
val_mem SEGS (arm W m1) (sp + 24) 8 BG ->
val_mem SEGS (arm W m1) (sp + 128) 8 (SA + 16) ->
val_mem SEGS (arm W m1) (sp + 136) 8 (SA + 24) ->
val_mem SEGS (arm W m1) (sp + 144) 8 SA ->
val_mem SEGS (arm W m1) (sp + 160) 8 NH8 ->
val_mem SEGS (arm W m1) (sp + 168) 8 1 ->
val_mem SEGS (arm W m1) (sp + 176) 8 (SA + 32) ->
val_mem SEGS (arm W m1) (sp + 192) 8 J ->
val_mem SEGS (arm W m1) (sp + 240) 8 SHADOW_OFF ->
val_mem SEGS (arm W m1) (HP + 8 * Z.of_nat n) 8 KP ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (gl_extra (HP + 8 * Z.of_nat n) KP J SA BG NH8))) ss_gl
(restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_hloop)) m1 (seg_rom SEGS))).
Proof using. gsc_clr0.
intros W regs1 m1 sp HP n KF KP J SA BG NH8 Hsp Hlo Hhi Hal R19 HKF R20 Hn8 R22 R25 HHP1 HHP8 HHP2 HHP3 HKP
  HJ HSA1 HSA2 HBG HNH8 M24 M128 M136 M144 M160 M168 M176 M192 M240 MSL.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (gl_extra (HP + 8 * Z.of_nat n) KP J SA BG NH8))).
assert (EREG : forall k (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r).
{ intros k r Hk Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E19 : ew E 19 = Z_to_bv 64 KF) by (rewrite (EREG 19%nat 19%bv ltac:(lia) eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 (8 * Z.of_nat n)) by (rewrite (EREG 20%nat 20%bv ltac:(lia) eq_refl); exact R20).
assert (E22 : ew E 22 = Z_to_bv 64 HP) by (rewrite (EREG 22%nat 22%bv ltac:(lia) eq_refl); exact R22).
assert (E25 : ew E 25 = Z_to_bv 64 1) by (rewrite (EREG 25%nat 25%bv ltac:(lia) eq_refl); exact R25).
assert (E32 : ew E 32 = Z_to_bv 64 (HP + 8 * Z.of_nat n)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 KP) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 J) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 BG) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 NH8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 7)).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (Usl : bv_unsigned (ew E 32) = HP + 8 * Z.of_nat n) by (rewrite E32; apply unsigned_lit_small; unfold GL_PHI in *; lia).
unfold GL_PHI in *. unfold DRAIN_FRAME in Hhi.
unfold ss_gl. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold gl_frame, gl_slot.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?Usp, ?Usl.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp 24 8 (SOff 38 0) BG);
        [rewrite (den_atom0 E 38%nat BG E38) by lia; reflexivity | cbn; lia | cbn; lia | exact M24].
    * apply (chunk_ok_val SEGS E _ sp 128 8 (SOff 37 16) (SA + 16));
        [rewrite (den_atom E 37%nat SA 16 E37) by lia; reflexivity | cbn; lia | cbn; lia | exact M128].
    * apply (chunk_ok_val SEGS E _ sp 136 8 (SOff 37 24) (SA + 24));
        [rewrite (den_atom E 37%nat SA 24 E37) by lia; reflexivity | cbn; lia | cbn; lia | exact M136].
    * apply (chunk_ok_val SEGS E _ sp 144 8 (SOff 37 0) SA);
        [rewrite (den_atom0 E 37%nat SA E37) by lia; reflexivity | cbn; lia | cbn; lia | exact M144].
    * apply (chunk_ok_val SEGS E _ sp 160 8 (SOff 39 0) NH8);
        [rewrite (den_atom0 E 39%nat NH8 E39) by lia; reflexivity | cbn; lia | cbn; lia | exact M160].
    * apply (chunk_ok_val SEGS E _ sp 168 8 (SOff 35 0) 1);
        [rewrite (den_atom0 E 35%nat 1 E35) by lia; reflexivity | cbn; lia | cbn; lia | exact M168].
    * apply (chunk_ok_val SEGS E _ sp 176 8 (SOff 37 32) (SA + 32));
        [rewrite (den_atom E 37%nat SA 32 E37) by lia; reflexivity | cbn; lia | cbn; lia | exact M176].
    * apply (chunk_ok_val SEGS E _ sp 192 8 (SOff 36 0) J);
        [rewrite (den_atom0 E 36%nat J E36) by lia; reflexivity | cbn; lia | cbn; lia | exact M192].
    * apply (chunk_ok_val SEGS E _ sp 240 8 (SOff 34 0) SHADOW_OFF);
        [rewrite (den_atom0 E 34%nat SHADOW_OFF E34) by (unfold SHADOW_OFF; lia); reflexivity
        | cbn; unfold SHADOW_OFF; lia | cbn; lia | exact M240].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (HP + 8 * Z.of_nat n) 0 8 (SOff 33 0) KP);
      [rewrite (den_atom0 E 33%nat KP E33) by lia; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact MSL].
- apply pairwise_disjoint_of_extents.
  unfold gl_frame, gl_slot, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Usl.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [gl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Usl, E34, E22, E20, E33, E25, E35, E19, !unsigned_lit_small by (unfold SB, SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (A2 : (8 * Z.of_nat n) mod 8 = 0) by (rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity).
    assert (A1 : (HP + 8 * Z.of_nat n) mod 8 = 0) by (rewrite Z.add_mod, HHP8, A2 by lia; reflexivity).
    unfold SB, SHADOW_OFF, GL_PHI. repeat match goal with |- _ /\ _ => split end; (exact I || assumption || lia).
  + cbn [gl_facts f_alias alias_ok]. split; [|split; [|exact I]].
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 22 HP E22), (U_atom E 20 (8 * Z.of_nat n) E20), (U_atom E 32 (HP + 8 * Z.of_nat n) E32) by lia.
      apply zcanon_id. unfold M64. lia.
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 22 HP E22), (U_atom E 20 (8 * Z.of_nat n) E20), (U_atom E 32 (HP + 8 * Z.of_nat n) E32) by lia.
      replace (8 * Z.of_nat n + HP) with (HP + 8 * Z.of_nat n) by lia. apply zcanon_id. unfold M64. lia.
Qed.

Definition gn_frame : YP09.region := YP09.mkRegion (Some 2%nat) 160 184 0 0
  [ YP09.mkChunk 160 (CVal 8 (SOff 32 0)); YP09.mkChunk 176 (CVal 8 (SOff 33 32)) ].
Definition gn_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (19%nat, mkAF 1 (2 ^ 26) 0) ] [] [].
Definition ss_gn : sstate := mkSS A_dr_hnext sr_atoms [ gn_frame ] None gn_facts.
Definition gn_Bx : sv := SOff 34 0.
Definition gn_extra (NH8 SA : Z) : list word := map (Z_to_bv 64) [NH8; SA].

Lemma gn_entry : forall (W : world SEGS) regs1 m1 sp NH8 SA KF,
spZ regs1 = sp -> 2 ^ 46 <= sp -> sp + DRAIN_FRAME <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs1 19 = w64 KF -> 1 <= KF <= 2 ^ 26 ->
0 <= NH8 < 2 ^ 64 -> 0 <= SA -> SA + 32 < 2 ^ 64 ->
val_mem SEGS (arm W m1) (sp + 160) 8 NH8 ->
val_mem SEGS (arm W m1) (sp + 176) 8 (SA + 32) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (gn_extra NH8 SA))) ss_gn
(restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_hnext)) m1 (seg_rom SEGS))).
Proof using. gsc_clr0.
intros W regs1 m1 sp NH8 SA KF Hsp Hlo Hhi Hal R19 HKF HNH8 HSA1 HSA2 M160 M176.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (gn_extra NH8 SA))).
assert (EREG : forall k (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r).
{ intros k r Hk Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E19 : ew E 19 = Z_to_bv 64 KF) by (rewrite (EREG 19%nat 19%bv ltac:(lia) eq_refl); exact R19).
assert (E32 : ew E 32 = Z_to_bv 64 NH8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
unfold DRAIN_FRAME in Hhi.
unfold ss_gn. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold gn_frame.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ sp 160 8 (SOff 32 0) NH8);
      [rewrite (den_atom0 E 32%nat NH8 E32) by lia; reflexivity | cbn; lia | cbn; lia | exact M160].
  + apply (chunk_ok_val SEGS E _ sp 176 8 (SOff 33 32) (SA + 32));
      [rewrite (den_atom E 33%nat SA 32 E33) by lia; reflexivity | cbn; lia | cbn; lia | exact M176].
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; [exact I | exact I]].
  cbn [gn_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E19, unsigned_lit_small by lia. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; (exact I || lia).
Qed.

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (image B's DR_x slice D, 2026-10-30; the B twin of lib/A/W_gsscanb_cx.v's
   Section cx and of lib/A/W_gsscanb.v's cut lemmas at a working branch 50623273289): the loop's cuts and
   the machine-state helpers over lib/B/W_drain_cx_x.v's Section variables (B PST ARx MT RP MMAX RG), with the entry's
   ghost list Hp and budget kr after cx and a cut's own ghost list Hp1 after S1 (lib/B/W_drain_gs.v's GSB_x).
   Everything above this line is unchanged, so every AR statement of this file keeps its text and its Section list.
   - The AR-free names above are CITED: the byte and value lemmas (gsc_bzs_app .. gsc_bge0, gsc_aview_garr8 ..
     gsc_line_garr8, gsc_dline_nth_nz), gsc_frame_nil, gsc_dlfut_same, gsc_link_H / gsc_link_U / gsc_nth_H, gsW,
     gsc_img_low, gsc_recs_len, gsc_frame_keep, A_dr_hnext, GSKEEP, gsc_keep_trans, gsc_fv_keep, gsc_dregs_keep,
     GSREGS, gsc_dregs_regs and the loop's two symbolic seats gl_* / gn_* with gl_entry and gn_entry.  Every name whose
     statement names AR, the journal, DBASE, DMEM, LCORE, DLC, GSB, GSL, GSN, GA, GF or DLN has its twin NAME_x below,
     with the AR proof's text (AR -> ARx with the ghost list after S, al_blocks -> alx_blocks, ajournal_gx_AR ->
     ajournal_gx_AR_x).
   - The Section takes lib/B/W_drain_cx_x.v's Section c items these lemmas use, in that file's text: LAWS, HG, HGSB,
     HV9, HSD, HSM.  No allocator rule, no context table. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_drain_cx W_drain_cx_x.
(* W_drain_cx_x.v loads FCiface, which sets Zify's euclidean flag: this file's setting again *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ax. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section bx.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
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
(* lib/B/W_drain_cx_x.v's Section c items the cut lemmas use, in that file's order and text *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.


(* ---------------------------------------------------------------------------------------------------------
   (1) Lowness over ARx: every byte the line loop's core reads lies below alloc_ceiling (the law alx_blocks).
   --------------------------------------------------------------------------------------------------------- *)
Lemma gsc_blk_low_x : forall ly S Hp (W : world SEGS) mem md qq nn a,
ARx ly S Hp W mem md -> In (qq, nn) (ablocks B ly S) -> qq <= a -> a < qq + req_size nn ->
0 <= a < alloc_ceiling.
Proof using LAWS. clear - LAWS.
intros ly S Hp W mem md qq nn a HAR Hin H1 H2.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md qq nn HAR Hin) as (_ & H4096 & Hceil & _). lia.
Qed.

Lemma gsc_aentry_fp_low_x : forall ly S Hp (W : world SEGS) mem md e,
ARx ly S Hp W mem md -> aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof using LAWS. clear - LAWS.
intros ly S Hp W mem md e HAR HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (HPK : forall k, In k (re_keys e) ->
  key_addr k <= a < key_addr k + Z.of_nat (length (bzs (key_text k ++ [Z_to_bv 8 0]))) ->
  0 <= a < alloc_ceiling).
{ intros k Hk Hak. rewrite gsc_bzs_len, length_app in Hak. cbn [length] in Hak.
  rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
  apply (gsc_blk_low_x ly S Hp W mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) a HAR Hin); [lia|].
  pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & Hrq). lia. }
assert (HPH : re_hp e <= a < re_hp e + Z.of_nat (length (bzs (key_ptrs (re_keys e)))) ->
  0 <= a < alloc_ceiling).
{ intros Hah. rewrite gsc_bzs_len, gs_key_ptrs_len in Hah.
  destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
  - rewrite Hke in Hah. cbn [length] in Hah. lia.
  - apply (gsc_blk_low_x ly S Hp W mem md (re_hp e) (re_kh e) a HAR Hin); [lia|].
    pose proof (req_size_pos (re_kh e) ltac:(lia)) as (_ & Hrq). unfold re_nheld in Hk1. lia. }
unfold aentry_fp in Hr.
destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [app In] in Hr.
- destruct Hr as [<- | Hr]; [unfold gfp in Ha; cbn [fst snd] in Ha; exact (HPH Ha)|].
  apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPK k Hk Ha).
- destruct Hr as [<- | [<- | Hr]].
  + unfold gfp in Ha. cbn [fst snd] in Ha. rewrite gsc_bzs_len, length_app in Ha.
    destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (gsc_blk_low_x ly S Hp W mem md (re_buf e) (re_cap e) a HAR Hin); [lia|].
    pose proof (req_size_pos (re_cap e) ltac:(lia)) as (_ & Hrq). lia.
  + unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPH Ha).
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPK k Hk Ha).
Qed.

Lemma gsc_alist_fp_low_x : forall ly S Hp (W : world SEGS) mem md LA l lines lo hi,
ARx ly S Hp W mem md -> alist_at B ly S W mem LA l lines ->
0x10000 <= lo -> lo <= LA -> LA + 16 <= hi -> hi <= IMG_TOP ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof using LAWS. clear - LAWS.
intros ly S Hp W mem md LA l lines lo hi HAR HL Hlo1 Hlo2 Hhi1 Hhi2 r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (gsc_img_low a lo hi); lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite gsc_bzs_len, length_app, gsc_recs_len in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (gsc_blk_low_x ly S Hp W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin); [lia|].
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as (_ & Hrq).
    unfold hl_n, AREC in *. lia.
  + apply in_map_iff in Hr as (qq & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite gsc_bzs_len, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs qq Hq) as (Hin & _).
    apply (gsc_blk_low_x ly S Hp W mem md (fst qq) (Z.of_nat (length (snd qq)) + 1) a HAR Hin); [lia|].
    pose proof (req_size_pos (Z.of_nat (length (snd qq)) + 1) ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma gsc_asrc_fp_low_x : forall ly S Hp (W : world SEGS) mem md HA h,
ARx ly S Hp W mem md -> asrc_at B ly S W mem HA h ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof using LAWS HGSB. clear - LAWS HGSB.
intros ly S Hp W mem md HA h HAR HS Hlo Hhi r Hr a Ha.
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (gsc_img_low a (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. rewrite gsc_bzs_len in Ha.
  apply (gsc_blk_low_x ly S Hp W mem md (hs_partial h) APARTIAL a HAR Hpb); [lia|].
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq). lia.
- unfold ASRC in *. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + eapply (gsc_alist_fp_low_x ly S Hp W mem md (HA + 16) (hs_pending h) false (rg_s RG) (rg_s RG + 4 * 96));
      [exact HAR | exact Hpend | lia | lia | lia | lia | exact Hr | exact Ha].
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * eapply (gsc_alist_fp_low_x ly S Hp W mem md (HA + 64) (hs_expected h) true (rg_s RG) (rg_s RG + 4 * 96));
        [exact HAR | exact Hexp | lia | lia | lia | lia | exact Hr | exact Ha].
    * eapply (gsc_alist_fp_low_x ly S Hp W mem md (HA + 80) (hs_held h) true (rg_s RG) (rg_s RG + 4 * 96));
        [exact HAR | exact Hheld | lia | lia | lia | lia | exact Hr | exact Ha].
Qed.

(* gsc_ing (Section c above, so not visible here), the same text *)
Ltac gsc_ing_x := unfold G_DR, G_SL; cbn [In]; repeat (first [left; reflexivity | right]).

Lemma gsc_aout_fp_low_x : forall ly S Hp (W : world SEGS) mem md c O mx no cap out,
ARx ly S Hp W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof using LAWS HG HSM HV9 HSD. clear - LAWS HG HSM HV9 HSD.
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
- pose proof HSM as (Hs1 & Hs2). apply (gsc_img_low a (rg_send_max RG) (rg_send_max RG + 8)); lia.
- apply (GL2 (rg_nout RG) 8); [gsc_ing_x | lia].
- apply (GL2 (rg_capout RG) 8); [gsc_ing_x | lia].
- apply (GL2 (rg_out RG) 8); [gsc_ing_x | lia].
- pose proof (pa_obj_img 9 ltac:(lia)) as H9. rewrite HV9 in H9.
  apply (gsc_img_low a (rg_client RG) (rg_client RG + 4)); unfold IMG_TOP; lia.
- apply (GL2 (rg_client_broken RG) 1); [gsc_ing_x | lia].
- pose proof HSD as (Hs1 & Hs2). apply (gsc_img_low a (rg_send_dead RG) (rg_send_dead RG + 1)); lia.
- apply (GL2 (rg_send_eintr RG) 1); [gsc_ing_x | lia].
- apply (GL2 (as_errno B) 4); [gsc_ing_x | lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  apply (gsc_blk_low_x ly S Hp W mem md out cap a HAR Hin); [lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq). lia.
Qed.


(* the stack facts every walk of the stage uses, from DBASE_x *)
Lemma gsc_stack_x : forall cx Hp kr, DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
alloc_ceiling + 2 * ESTACK + DRAIN_FRAME <= dsp0 cx /\ dsp0 cx <= 2 ^ 47 /\ dsp0 cx mod 16 = 0 /\
(dxj cx < 4)%nat.
Proof using. gsc_clr0.
intros cx Hp kr HB.
pose proof HB as (Hafn & _ & _ & _ & _ & _ & _ & _ & _ & Hj4 & _).
pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HDS : DRAIN_STK_x = 17008) by reflexivity. rewrite HDS in Hslo.
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
unfold dsp0. split; [lia|]. split; [lia|]. split; [exact Hal16 | exact Hj4].
Qed.


(* ---------------------------------------------------------------------------------------------------------
   (3) The loop's cuts over GSB_x: GSBODY's text with the entry's Hp / kr after cx and the cut's Hp1 after S1.
   --------------------------------------------------------------------------------------------------------- *)
Definition GSBODY_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf nm : nat)
(W1 : world SEGS) (regs1 : bvmap 5 word) ly1 S1 (Hp1 : list Z) (m1 : word -> option byte) md1 k1 e1 h1 out1 ev1 LB1
spent (jb : nat) (a : drain_b_c.dadr) (o ha : dadrF) (ks : list dadrF) (tl : dtrace) (kd : gkind) (jj : nat) (bg : Z)
: Prop :=
dregs_gs RG cx regs1 W1 m1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME) 8 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 24) 8 bg /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 96) 8 ((dxSA cx + 40) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 112) 8 (re_nheld e1) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 160) 8 (8 * re_nheld e1) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 168) 8 1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 (Z.of_nat jj) /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 19 = w64 (Z.of_nat kf) /\ getr regs1 20 = w64 (8 * Z.of_nat n) /\
getr regs1 22 = w64 (re_hp e1) /\ getr regs1 25 = w64 1 /\
(n + kf = length (re_keys e1))%nat /\ (0 < kf)%nat /\
(forall i, (i < nm)%nat -> nth i (dlH cx s1 p) [] <> firstn jj (dline s1 p q)) /\
0 <= bg < 2 ^ 64 /\ (bg = 0 <-> kd = GBegin) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
GSF s1 p q /\
GSB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.

Definition GSL_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_hloop) regs1 m1 md1 /\
GSBODY_x cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.

Definition GSN_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_hnext) regs1 m1 md1 /\
GSBODY_x cx Hp kr s1 D p q n kf (S n) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.

(* The loop, by induction on kf, over the entry's ghost list Hp and budget kr. *)
Definition gs_scan_loop_stmt_x : Prop :=
forall cx Hp kr s1 D p q n kf W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GSL_x cx Hp kr s1 D p q n kf W1 c1 ->
(forall W2 c2, DLN_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S q) W2 c2 ->
   SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
(forall W2 c2, GA_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q W2 c2 ->
   SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
(forall W2 c2, GF_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q W2 c2 ->
   SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr).








(* ==== route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0): the R twins of this section's journal-carrying blocks.  Each X_xR
   is X_x with the carriers and engine texts replaced by their R twins (R after the carrier's section
   variables), ajournal_gx_x -> ajournal_gx_xR .. R, ajournal_x -> ajournal_xR .. R and SRr SEGS -> SRrG SEGS R;
   the strict text is untouched.  Blocks that name no journal, no step relation and no carrier have no twin. ==== *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.

(* R twin of gsc_dlc_same_x *)
Lemma gsc_dlc_same_xR : forall cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl,
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

(* R twin of gsc_core_kept_x *)
Lemma gsc_core_kept_xR : forall cx Hp kr s1 D p q ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  m2 md2 k2,
(dxj cx < 4)%nat -> 4096 <= dxSA cx -> dxSA cx + 56 <= alloc_ceiling ->
GSB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k2 ->
(forall x, 0 <= x < alloc_ceiling -> aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m2 x) ->
dr_frame RG cx W1 m2 ->
GSB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q ly1 S1 Hp1 W1 m2 md2 k2 e1 h1 out1 ev1 LB1 spent tl.
Proof. clear - LAWS HG HGSB HV9 HSD HSM.
intros cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2 k2 HJ4 HSA1 HSA2 HGS HJ2 KL PRES
  HFR2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold GSB_xR, LCORE_xR in HGS |- *.
destruct HGS as (HMEM & HLINK & HSAME & HHIST & HRS & HBUD).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR1 : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (AK : forall fp, (forall r, In r fp -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling) ->
  akept W1 m1 W1 m2 fp) by (intros fp Hlow; exact (gs_akept_of W1 m1 m2 fp KL PRES Hlow)).
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
split; [exact HFR2|].
split.
{ apply (gsc_garr8_kept W1 m1 W1 m2); [exact Hgarr|].
  intros x Hx. rewrite gsc_bzs_len in Hx. apply KL.
  assert (HL56 : length (entry_bytes e1) = 56%nat).
  { pose proof HOKX as (_ & _ & HQ1 & HQ2 & _). unfold entry_bytes.
    rewrite !length_app, HQ1, HQ2, !Mem.length_le8, !Mem.length_le4. reflexivity. }
  rewrite HL56 in Hx. lia. }
split.
{ intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m2 _ (PRES _)). exact (Hawr i Hi). }
split.
{ eapply (gs_aentry_okx_kept B).
  - exact HOKX.
  - apply AK. exact (gsc_aentry_fp_low_x ly1 S1 Hp1 W1 m1 md1 e1 HAR1 HOKX).
  - intros b Hb. apply HBLK. apply in_or_app. left. exact Hb. }
split.
{ eapply asrc_at_kept.
  - exact Hsrc.
  - apply AK. apply (gsc_asrc_fp_low_x ly1 S1 Hp1 W1 m1 md1 (dHA RG cx) h1 HAR1 Hsrc);
      unfold dHA, ASRC in *; lia.
  - intros b Hb. apply HBLK. apply in_or_app. right. apply in_or_app. left. exact Hb. }
split.
{ pose proof HGSB as (Hg1 & Hg2 & _). unfold aothers_at in Hoth |- *.
  intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & Mf & Mo & Hfo).
  exists f, o. split; [|split; [|exact Hfo]];
  apply (gsc_vm_keep W1 m1 m2 _ 4%nat _); [| exact Mf | | exact Mo];
  intros x Hx; apply KL; apply (gsc_img_low x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; cbn in Hx; lia. }
split.
{ intros x Hx Hnx. destruct (Hgsk x Hx Hnx) as (Hv & Hw). split.
  - rewrite KL; [exact Hv|]. pose proof HGSB as (Hg1 & Hg2 & _).
    apply (gsc_img_low x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
  - intros Hwr. unfold arm. apply (writable_kept (w_H W1) m1 m2 _ (PRES _)). exact (Hw Hwr). }
split.
{ eapply aout_at_kept.
  - exact Hout.
  - apply AK. exact (gsc_aout_fp_low_x ly1 S1 Hp1 W1 m1 md1 _ _ _ _ _ _ HAR1 Hout).
  - intros b Hb. apply HBLK. apply in_or_app. right. apply in_or_app. right. exact Hb. }
split; [exact Hlivout | exact Hperm].
Qed.

(* R twin of gsc_sa_x *)
Lemma gsc_sa_xR : forall cx Hp kr ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 s out1 ev1 sent LB1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 ->
4096 <= dxSA cx /\ dxSA cx + 56 <= alloc_ceiling.
Proof. clear - LAWS.
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

(* R twin of GSBODY_x *)
Definition GSBODY_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf nm : nat)
(W1 : world SEGS) (regs1 : bvmap 5 word) ly1 S1 (Hp1 : list Z) (m1 : word -> option byte) md1 k1 e1 h1 out1 ev1 LB1
spent (jb : nat) (a : drain_b_c.dadr) (o ha : dadrF) (ks : list dadrF) (tl : dtrace) (kd : gkind) (jj : nat) (bg : Z)
: Prop :=
dregs_gs RG cx regs1 W1 m1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME) 8 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 24) 8 bg /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 96) 8 ((dxSA cx + 40) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 112) 8 (re_nheld e1) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 160) 8 (8 * re_nheld e1) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 168) 8 1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 (Z.of_nat jj) /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 19 = w64 (Z.of_nat kf) /\ getr regs1 20 = w64 (8 * Z.of_nat n) /\
getr regs1 22 = w64 (re_hp e1) /\ getr regs1 25 = w64 1 /\
(n + kf = length (re_keys e1))%nat /\ (0 < kf)%nat /\
(forall i, (i < nm)%nat -> nth i (dlH cx s1 p) [] <> firstn jj (dline s1 p q)) /\
0 <= bg < 2 ^ 64 /\ (bg = 0 <-> kd = GBegin) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
GSF s1 p q /\
GSB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.

(* R twin of GSL_x *)
Definition GSL_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_hloop) regs1 m1 md1 /\
GSBODY_xR cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.

(* R twin of GSN_x *)
Definition GSN_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_hnext) regs1 m1 md1 /\
GSBODY_xR cx Hp kr s1 D p q n kf (S n) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.

(* R twin of gs_scan_loop_stmt_x *)
Definition gs_scan_loop_stmt_xR : Prop :=
forall cx Hp kr s1 D p q n kf W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GSL_xR cx Hp kr s1 D p q n kf W1 c1 ->
(forall W2 c2, DLN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S q) W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall W2 c2, GA_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall W2 c2, GF_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).

(* R twin of gsc_body_keep_x *)
Lemma gsc_body_keep_xR : forall cx Hp kr s1 D p q n kf nm W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o
  ha ks tl kd jj bg m2 md2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
GSBODY_xR cx Hp kr s1 D p q n kf nm W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
GSKEEP cx W1 m1 m2 ->
GSBODY_xR cx Hp kr s1 D p q n kf nm W1 regs1 ly1 S1 Hp1 m2 md2 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof. clear - LAWS HG HGSB HV9 HSD HSM.
intros cx Hp kr s1 D p q n kf nm W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg m2
  md2 HB HBD HJ2 HKP.
destruct (gsc_stack_x cx Hp kr HB) as (HS1 & HS2 & _ & Hj4).
pose proof asan_consts as (C1 & _).
unfold GSBODY_xR in HBD |- *.
destruct HBD as (HRG & M0 & M16 & M24 & M96 & M112 & M160 & M168 & M192 & R23 & R24 & R19 & R20 & R22 & R25
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (HMEM & _).
destruct (gsc_sa_xR cx Hp kr _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB HMEM) as (HSA1 & HSA2).
assert (HSPR : DRAIN_FRAME <= dsp0 cx <= 2 ^ 47) by (unfold ESTACK, DRAIN_FRAME in *; lia).
split; [exact (gsc_dregs_keep RG cx W1 m1 m2 regs1 HSPR HKP HRG)|].
split; [replace (dsp0 cx - DRAIN_FRAME) with (dsp0 cx - DRAIN_FRAME + 0) in M0 |- * by lia;
  apply (gsc_fv_keep cx W1 m1 m2 _ _ HSPR); [lia | unfold DRAIN_FRAME; lia | exact HKP | exact M0]|].
do 7 (split; [apply (gsc_fv_keep cx W1 m1 m2 _ _ HSPR); [lia | unfold DRAIN_FRAME; lia | exact HKP | assumption]|]).
do 16 (split; [assumption|]).
split; [|exact HFUT].
pose proof HKP as (KEEP & PRES).
apply (gsc_core_kept_xR cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2 k1 Hj4 HSA1 HSA2
  HCORE HJ2).
- intros x Hx. apply KEEP; [lia|]. unfold ESTACK, DRAIN_FRAME in *. lia.
- exact PRES.
- exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (gsc_dregs_keep RG cx W1 m1 m2 regs1 HSPR HKP HRG))))))).
Qed.

(* R twin of gsc_mk_gsn_x *)
Lemma gsc_mk_gsn_xR : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks
  tl kd jj bg regs2,
GSBODY_xR cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
GSREGS regs1 regs2 -> getr regs2 19 = getr regs1 19 -> getr regs2 20 = getr regs1 20 ->
nth n (dlH cx s1 p) [] <> firstn jj (dline s1 p q) ->
GSBODY_xR cx Hp kr s1 D p q n kf (S n) W1 regs2 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof. gsc_clr0.
intros cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q22 & Q23 & Q24 & Q25) Q19 Q20 Hn.
unfold GSBODY_xR in HBD |- *.
destruct HBD as (HRG & M0 & M16 & M24 & M96 & M112 & M160 & M168 & M192 & R23 & R24 & R19 & R20 & R22 & R25
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr & HGSF & HCORE & HFUT).
split; [exact (gsc_dregs_regs RG cx regs1 regs2 W1 m1 Q2 Q3 Q4 Q8 Q9 Q18 HRG)|].
rewrite Q19, Q20, Q22, Q23, Q24, Q25.
do 16 (split; [assumption|]).
split; [intros i Hi; destruct (Nat.eq_dec i n) as [->|Hne]; [exact Hn | apply Hnm; lia]|].
do 8 (split; [assumption|]). exact HFUT.
Qed.

(* R twin of gsc_mk_loop_x *)
Lemma gsc_mk_loop_xR : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks
  tl kd jj bg regs2,
GSBODY_xR cx Hp kr s1 D p q n (S kf) (S n) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj
  bg ->
(0 < kf)%nat ->
GSREGS regs1 regs2 ->
getr regs2 19 = w64 (Z.of_nat kf) -> getr regs2 20 = w64 (8 * Z.of_nat (S n)) ->
GSBODY_xR cx Hp kr s1 D p q (S n) kf (S n) W1 regs2 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj
  bg.
Proof. gsc_clr0.
intros cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD Hkf0 (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q22 & Q23 & Q24 & Q25) Q19 Q20.
unfold GSBODY_xR in HBD |- *.
destruct HBD as (HRG & M0 & M16 & M24 & M96 & M112 & M160 & M168 & M192 & R23 & R24 & R19 & R20 & R22 & R25
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr & HGSF & HCORE & HFUT).
split; [exact (gsc_dregs_regs RG cx regs1 regs2 W1 m1 Q2 Q3 Q4 Q8 Q9 Q18 HRG)|].
rewrite Q22, Q23, Q24, Q25.
do 10 (split; [assumption|]).
split; [exact Q19|]. split; [exact Q20|].
do 2 (split; [assumption|]).
split; [lia|]. split; [exact Hkf0|].
do 9 (split; [assumption|]). exact HFUT.
Qed.

(* R twin of gsc_mk_ga_x *)
Lemma gsc_mk_ga_xR : forall cx Hp kr s1 D p q n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl
  kd jj bg regs2,
GSBODY_xR cx Hp kr s1 D p q n 1 (S n) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 ->
getr regs2 27 = w64 (dxSA cx + 32) ->
GA_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W1 (cfg_at SEGS (BASE + A_dr_add) regs2 m1 md1).
Proof. gsc_clr0.
intros cx Hp kr s1 D p q n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD Q2 Q3 Q4 Q8 Q9 Q18 Q23 Q24 Q27.
unfold GSBODY_xR in HBD.
destruct HBD as (HRG & M0 & M16 & M24 & M96 & M112 & M160 & M168 & M192 & R23 & R24 & R19 & R20 & R22 & R25
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr & HGSF & HCORE & HFUT).
exists regs2, ly1, S1, Hp1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl, kd, jj, bg.
split; [reflexivity|].
split; [exact (gsc_dregs_regs RG cx regs1 regs2 W1 m1 Q2 Q3 Q4 Q8 Q9 Q18 HRG)|].
split; [exact Q27|].
rewrite Q23, Q24.
do 13 (split; [assumption|]).
split.
{ apply gs_index_none. intros i Hi. apply Hnm.
  pose proof HCORE as (_ & HLINK & _).
  rewrite <- (gsc_link_H _ _ _ _ _ _ _ _ _ HLINK), gs_keys_texts_len in Hi. lia. }
split; [exact HGSF|]. split; [exact HCORE | exact HFUT].
Qed.

(* R twin of gsc_mk_dln_x *)
Lemma gsc_mk_dln_xR : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks
  tl kd jj bg regs2,
GSBODY_xR cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q) -> bg = 0 ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 23 = getr regs1 23 ->
getr regs2 21 = w64 (dxSA cx) -> getr regs2 20 = w64 (dxSA cx + 16) ->
getr regs2 22 = w64 (dxSA cx + 24) -> getr regs2 27 = w64 (dxSA cx + 32) ->
DLN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S q) W1 (cfg_at SEGS (BASE + A_dr_next) regs2 m1 md1).
Proof. gsc_clr0.
intros cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD Hmt Hbg0 Q2 Q3 Q4 Q8 Q9 Q18 Q23 Q21 Q20 Q22 Q27.
unfold GSBODY_xR in HBD.
destruct HBD as (HRG & M0 & M16 & M24 & M96 & M112 & M160 & M168 & M192 & R23 & R24 & R19 & R20 & R22 & R25
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (_ & HLINK & _).
assert (Hkd : kd = GBegin) by (apply Hbgk; exact Hbg0). subst kd.
assert (Hlen : (n < length (dlH cx s1 p))%nat)
  by (rewrite <- (gsc_link_H _ _ _ _ _ _ _ _ _ HLINK), gs_keys_texts_len; lia).
pose proof (gs_index_some _ _ n Hlen Hmt Hnm) as HI.
destruct (gs_seen_begin_old (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) _ n jb ha ks Hgest HI) as (S1e & S2e & S3e).
pose proof HGSF as (Hbd & Hpq & Hq0 & _).
pose proof HRG as (R2 & R3 & R4 & R8 & R9 & R18 & HFR).
exists regs2, ly1, S1, Hp1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
split; [reflexivity|].
split.
{ unfold dregs_line, spZ in *. rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q21, Q20, Q22, Q27.
  repeat (split; [first [assumption | reflexivity]|]). exact HFR. }
split; [rewrite Q23, R23; unfold w64; f_equal; lia|].
split; [exact Hband|]. split; [exact Hcap|].
split; [unfold dbound; split; [lia|right]; replace (S q - 1)%nat with q by lia; exact Hq0|].
split; [lia|].
split; [exact (gsc_dlc_same_xR cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl HGSF S1e S3e
  HCORE)|].
exact (gsc_dlfut_same cx s1 p q a jb o ha ks tl HGSF S2e S1e S3e HFUT).
Qed.

(* R twin of gsc_mk_gf_x *)
Lemma gsc_mk_gf_xR : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks
  tl kd jj bg regs2,
GSBODY_xR cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q) -> bg <> 0 ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 ->
getr regs2 20 = getr regs1 20 -> getr regs2 22 = getr regs1 22 ->
getr regs2 26 = w64 (re_hp e1 + 8 * Z.of_nat n) ->
getr regs2 21 = w64 ((re_hp e1 + 8 * Z.of_nat n) / 8 + SHADOW_OFF) ->
GF_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W1 (cfg_at SEGS (BASE + A_dr_free) regs2 m1 md1).
Proof. gsc_clr0.
intros cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2
  HBD Hmt Hbg0 Q2 Q3 Q4 Q8 Q9 Q18 Q23 Q24 Q20 Q22 Q26 Q21.
unfold GSBODY_xR in HBD.
destruct HBD as (HRG & M0 & M16 & M24 & M96 & M112 & M160 & M168 & M192 & R23 & R24 & R19 & R20 & R22 & R25
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HCORE as (_ & HLINK & _).
assert (Hkd : kd = GEnd) by (destruct kd; [exfalso; apply Hbg0; apply Hbgk; reflexivity | reflexivity]). subst kd.
assert (Hlen : (n < length (dlH cx s1 p))%nat)
  by (rewrite <- (gsc_link_H _ _ _ _ _ _ _ _ _ HLINK), gs_keys_texts_len; lia).
pose proof (gs_index_some _ _ n Hlen Hmt Hnm) as HI.
exists regs2, ly1, S1, Hp1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl, jj, n.
split; [reflexivity|].
split; [exact (gsc_dregs_regs RG cx regs1 regs2 W1 m1 Q2 Q3 Q4 Q8 Q9 Q18 HRG)|].
rewrite Q23, Q24, Q20, Q22, Q26, Q21.
do 6 (split; [first [assumption | reflexivity]|]).
split; [exact M0|]. split; [exact M16|].
split; [exact Hband|]. split; [exact Hcap|].
split; [lia|].
split; [exact Hgest|]. split; [exact Hjjr|].
split; [exact HI|].
split; [exact HGSF|]. split; [exact HCORE | exact HFUT].
Qed.

End wR.

(* commit (2): each strict lemma below is its R twin at R := wle (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0) *)
Local Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

(* ---- The line loop's model after a BEGIN whose key is held, over GSB_x (gsc_dlc_same). ---- *)
Lemma gsc_dlc_same_x : forall cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl,
GSF s1 p q ->
seen_arr (dlH cx s1 p) (dline s1 p q) = dlH cx s1 p ->
seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) = dlka cx s1 p ->
GSB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
DLC_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S q) ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.
Proof. eapply (gsc_dlc_same_xR (@wle SEGS)); wle_inst. Qed.

(* ---------------------------------------------------------------------------------------------------------
   (2) The line loop's core across a step that keeps every byte below alloc_ceiling (gsc_core_kept), and the
   stack and table facts from DBASE_x / DMEM_x (gsc_stack, gsc_sa).
   --------------------------------------------------------------------------------------------------------- *)
Lemma gsc_core_kept_x : forall cx Hp kr s1 D p q ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  m2 md2 k2,
(dxj cx < 4)%nat -> 4096 <= dxSA cx -> dxSA cx + 56 <= alloc_ceiling ->
GSB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k2 ->
(forall x, 0 <= x < alloc_ceiling -> aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m2 x) ->
dr_frame RG cx W1 m2 ->
GSB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q ly1 S1 Hp1 W1 m2 md2 k2 e1 h1 out1 ev1 LB1 spent tl.
Proof. eapply (gsc_core_kept_xR (@wle SEGS)); wle_inst. Qed.

(* the relay entry's place, from DBASE_x and the core's table block *)
Lemma gsc_sa_x : forall cx Hp kr ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 s out1 ev1 sent LB1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
DMEM_x B PST ARx RG cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s out1 ev1 sent LB1 ->
4096 <= dxSA cx /\ dxSA cx + 56 <= alloc_ceiling.
Proof. eapply (gsc_sa_xR (@wle SEGS)); wle_inst. Qed.

(* ---- the body across a step that writes only the interceptors' scratch below drain's frame ---- *)
Lemma gsc_body_keep_x : forall cx Hp kr s1 D p q n kf nm W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o
  ha ks tl kd jj bg m2 md2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
GSBODY_x cx Hp kr s1 D p q n kf nm W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
GSKEEP cx W1 m1 m2 ->
GSBODY_x cx Hp kr s1 D p q n kf nm W1 regs1 ly1 S1 Hp1 m2 md2 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof. eapply (gsc_body_keep_xR (@wle SEGS)); wle_inst. Qed.

(* GSN's body from the head's: the registers unchanged, slot n not matched *)
Lemma gsc_mk_gsn_x : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks
  tl kd jj bg regs2,
GSBODY_x cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
GSREGS regs1 regs2 -> getr regs2 19 = getr regs1 19 -> getr regs2 20 = getr regs1 20 ->
nth n (dlH cx s1 p) [] <> firstn jj (dline s1 p q) ->
GSBODY_x cx Hp kr s1 D p q n kf (S n) W1 regs2 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg.
Proof. eapply (gsc_mk_gsn_xR (@wle SEGS)); wle_inst. Qed.

(* the loop's head at S n from GSN at n, s3 and s4 stepped *)
Lemma gsc_mk_loop_x : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks
  tl kd jj bg regs2,
GSBODY_x cx Hp kr s1 D p q n (S kf) (S n) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj
  bg ->
(0 < kf)%nat ->
GSREGS regs1 regs2 ->
getr regs2 19 = w64 (Z.of_nat kf) -> getr regs2 20 = w64 (8 * Z.of_nat (S n)) ->
GSBODY_x cx Hp kr s1 D p q (S n) kf (S n) W1 regs2 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj
  bg.
Proof. eapply (gsc_mk_loop_xR (@wle SEGS)); wle_inst. Qed.

(* GA_x from GSN at the last slot *)
Lemma gsc_mk_ga_x : forall cx Hp kr s1 D p q n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl
  kd jj bg regs2,
GSBODY_x cx Hp kr s1 D p q n 1 (S n) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 ->
getr regs2 27 = w64 (dxSA cx + 32) ->
GA_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q W1 (cfg_at SEGS (BASE + A_dr_add) regs2 m1 md1).
Proof. eapply (gsc_mk_ga_xR (@wle SEGS)); wle_inst. Qed.

(* a BEGIN whose key is held at slot n: DLN_x (S q), with s5 / s6 / s4 / s11 restored from the frame *)
Lemma gsc_mk_dln_x : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks
  tl kd jj bg regs2,
GSBODY_x cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q) -> bg = 0 ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 23 = getr regs1 23 ->
getr regs2 21 = w64 (dxSA cx) -> getr regs2 20 = w64 (dxSA cx + 16) ->
getr regs2 22 = w64 (dxSA cx + 24) -> getr regs2 27 = w64 (dxSA cx + 32) ->
DLN_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S q) W1 (cfg_at SEGS (BASE + A_dr_next) regs2 m1 md1).
Proof. eapply (gsc_mk_dln_xR (@wle SEGS)); wle_inst. Qed.

(* an END whose key is held at slot n: GF_x *)
Lemma gsc_mk_gf_x : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks
  tl kd jj bg regs2,
GSBODY_x cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q) -> bg <> 0 ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 ->
getr regs2 20 = getr regs1 20 -> getr regs2 22 = getr regs1 22 ->
getr regs2 26 = w64 (re_hp e1 + 8 * Z.of_nat n) ->
getr regs2 21 = w64 ((re_hp e1 + 8 * Z.of_nat n) / 8 + SHADOW_OFF) ->
GF_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q W1 (cfg_at SEGS (BASE + A_dr_free) regs2 m1 md1).
Proof. eapply (gsc_mk_gf_xR (@wle SEGS)); wle_inst. Qed.

End cx.
End bx.
End ax.
