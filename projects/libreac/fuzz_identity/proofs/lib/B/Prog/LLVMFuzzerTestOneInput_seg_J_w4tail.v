(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:275-278
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1557-1564, 1568-1573, 1593-1605 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Segment J of LLVMFuzzerTestOneInput's build-B walk (fuzz_identity.asan-ubsan), the piece +0x15c4 .. +0x16b8
   (0x81d38 .. 0x81e2c): j_w4tail_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v, from the cut jc4 to jc5.

   The code (the neutral listing of fuzz_identity.asan-ubsan):
     0x81d38  x22 := the bitwise complement of x25 = &exp_nm (the UBSan bound of the name index)
     0x81d40  x20 := x25 + x27 = &exp_nm + ln
     0x81d44  ln < 4: to 0x81d7c (no tail to compare)
     0x81d48 .. 0x81d58  UBSan traps ln > 32, x22 < ln, x20 < 5 (refuted)
     0x81d5c .. 0x81d68  the bcmp wrapper on (x20 - 4, &w4, 4) (abcmp_realizes), back at 0x81d6c
     0x81d6c  a0 = 0 (the stem ends in the four digits): to 0x81e28, x6 := mf+168, the join 0x81e2c
     0x81d70 .. 0x81d78  x6 := mf+168; the trap ln = 32 (refuted)
     0x81d7c  the trap x22 < ln (refuted); 0x81d80 .. 0x81d8c the shadow byte of exp_nm + ln (0)
     0x81d90, 0x81d94  exp_nm[ln] := '-'; 0x81d98 x15 := w4[0]; 0x81d9c x27 := ln + 1
     0x81da0  w4[0] = 0: to 0x81e2c (refuted: no digit is NUL)
     0x81da4 .. 0x81db4  the copy loop's registers; 0x81db8 the loop, j_w4cpy_stmt with i = 0, ld = ln + 1
   The piece is cut at two slots of its own: w4t_c6c at 0x81d6c (back from the wrapper) and w4t_c7c at 0x81d7c
   (the dash path). w4t_L1 runs jc4 to one of them, w4t_L2 runs w4t_c6c to jc5 or to w4t_c7c, w4t_L3 runs w4t_c7c
   through the loop to jc5. The memory facts cross every run and the call through w4t_move. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg_J_loops_stmt.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require LLVMFuzzerTestOneInput_seg_J_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef MemchrDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_J_pre.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; this segment's address arithmetic (shadow_addr, the
   frame's 64-byte alignment) needs it, so this file turns it back on, as lib/A/Prog/LLVMFuzzerTestOneInput_D6.v
   does. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the model: the three buffers' strings fit their capacities when n_r = 0 (SlotModel) ---------------- *)
Module W4TM.
Import IdentSpec RcIdentModel SlotModel.
Lemma has_dash_len : forall l, has_dash l = true -> (1 <= length l)%nat.
Proof. intros [|b r] H; [discriminate H | cbn; lia]. Qed.
Lemma tok_len : forall l d,
  length (tok_go d l) = (length l - (if negb d && has_dash l then 1 else 0))%nat.
Proof.
  induction l as [|b r IH]; intros d; [reflexivity|].
  assert (HD : has_dash (b :: r) = (bz b =? 45) || has_dash r) by reflexivity. rewrite HD. destruct d.
  - cbn [tok_go negb andb Datatypes.length]. rewrite IH. cbn [negb andb]. lia.
  - destruct (bz b =? 45) eqn:E; cbn [tok_go negb andb orb Datatypes.length]; rewrite E; cbn [andb orb].
    + rewrite IH. cbn [negb andb]. lia.
    + cbn [Datatypes.length]. rewrite IH. cbn [negb andb]. destruct (has_dash r) eqn:D; [|lia].
      pose proof (has_dash_len r D). lia.
Qed.
Lemma tk_len : forall inp, Z.of_nat (length (n_TK inp)) = n_lt inp.
Proof.
  intro inp. unfold n_TK, TOK, n_lt, n_ln. rewrite tok_len. cbn [negb andb].
  destruct (has_dash (n_EXP_NM inp)) eqn:D; [|lia]. pose proof (has_dash_len _ D). lia.
Qed.
Lemma r0_fits : forall inp, n_r inp = 0 -> n_wok inp = true /\ n_fits inp = true.
Proof.
  intros inp H. unfold n_r in H. destruct (n_wok inp && n_fits inp) eqn:E; [|discriminate].
  apply andb_true_iff in E. exact E.
Qed.
Lemma fits_lens : forall inp, n_r inp = 0 ->
  Z.of_nat (length (n_EXP_NM inp ++ [zb 0])) <= t_cap_name inp /\
  Z.of_nat (length (n_TK inp ++ [zb 0])) <= t_cap_tok inp /\
  Z.of_nat (length (n_EXP_DP inp ++ [zb 0])) <= t_cap_disp inp.
Proof.
  intros inp H. destruct (r0_fits inp H) as [_ Hf]. unfold n_fits in Hf.
  apply andb_true_iff in Hf as [Hf Hd]. apply andb_true_iff in Hf as [Hn Ht].
  apply Z.ltb_lt in Hn, Ht, Hd. rewrite !length_app. cbn [length].
  pose proof (tk_len inp) as HT. unfold n_ln in Hn. unfold n_ld in Hd. lia.
Qed.
End W4TM.

(* ---- arithmetic of the symbolic values ------------------------------------------------------------------- *)
Lemma w4t_xor_m1 : forall x, 0 <= x < 2 ^ 64 -> zcanon (Z.lxor x (zcanon (-1))) = Z.lnot x mod 2 ^ 64.
Proof.
intros x Hx. unfold zcanon, M64. change ((-1) mod 2 ^ 64) with (Z.ones 64).
apply Z.bits_inj'. intros n Hn.
destruct (Z_lt_le_dec n 64) as [Hl | Hh].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.lxor_spec, Z.lnot_spec by lia.
  rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma w4t_lnot_mod : forall x, 0 <= x < 2 ^ 64 -> Z.lnot x mod 2 ^ 64 = 2 ^ 64 - 1 - x.
Proof.
intros x Hx. assert (E : Z.lnot x = (2 ^ 64 - 1 - x) + (-1) * 2 ^ 64) by (unfold Z.lnot; lia).
rewrite E, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma w4t_bv_mod : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.
Lemma w4t_wm1 : w64 18446744073709551615 = w64 (-1).
Proof. unfold w64. rewrite <- (w4t_bv_mod (-1)). reflexivity. Qed.
Lemma w4t_den_atom : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. rewrite denot_lit_U, U_SOff, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 (ew E n)) as H. change (bv_modulus 64) with (2 ^ 64) in H.
rewrite zcanon_id by (unfold M64; lia). apply Z_to_bv_bv_unsigned.
Qed.
Lemma w4t_den_lit : forall E z, 0 <= z < 2 ^ 64 -> sv_denot E (SLit z) = w64 z.
Proof. intros E z Hz. unfold w64. rewrite denot_lit_U, U_SLit, zcanon_id by (unfold M64; lia). reflexivity. Qed.
Lemma w4t_den_off : forall E n c x z, bv_unsigned (ew E n) = x -> z = x + c -> 0 <= z < 2 ^ 64 ->
  sv_denot E (SOff n c) = w64 z.
Proof.
intros E n c x z Hx Hz Hr. subst z. unfold w64. rewrite denot_lit_U, U_SOff, Hx.
rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma w4t_U_add : forall E n m c d x y, bv_unsigned (ew E n) = x -> bv_unsigned (ew E m) = y ->
  0 <= x + c < 2 ^ 64 -> 0 <= y + d < 2 ^ 64 -> 0 <= x + c + (y + d) < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff n c) (SOff m d)) = x + c + (y + d).
Proof.
intros E n m c d x y Hx Hy H1 H2 H3. rewrite U_SAlu, !U_SOff, Hx, Hy. cbn [zalu_raw].
rewrite (zcanon_id (x + c)) by (unfold M64; lia). rewrite (zcanon_id (y + d)) by (unfold M64; lia).
apply zcanon_id. unfold M64. lia.
Qed.
Lemma w4t_den_add : forall E n m c d x y z, bv_unsigned (ew E n) = x -> bv_unsigned (ew E m) = y ->
  0 <= x + c < 2 ^ 64 -> 0 <= y + d < 2 ^ 64 -> z = x + c + (y + d) -> 0 <= z < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n c) (SOff m d)) = w64 z.
Proof.
intros E n m c d x y z Hx Hy H1 H2 Hz H3. subst z. unfold w64. rewrite denot_lit_U.
rewrite (w4t_U_add E n m c d x y Hx Hy H1 H2 H3). reflexivity.
Qed.
Lemma w4t_U_not : forall E n x, bv_unsigned (ew E n) = x -> 0 <= x < 2 ^ 64 ->
  U E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = Z.lnot x mod 2 ^ 64.
Proof.
intros E n x Hx Hr. rewrite U_SAlu, U_SOff, U_SLit, Hx, Z.add_0_r. cbn [zalu_raw].
rewrite (zcanon_id x) by (unfold M64; lia). apply w4t_xor_m1. exact Hr.
Qed.
Lemma w4t_den_not : forall E n x, bv_unsigned (ew E n) = x -> 0 <= x < 2 ^ 64 ->
  sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = w64 (Z.lnot x).
Proof. intros E n x Hx Hr. unfold w64. rewrite denot_lit_U, (w4t_U_not E n x Hx Hr). apply w4t_bv_mod. Qed.
Lemma w4t_U_atom_w : forall E n z, ew E n = Z_to_bv 64 z -> U E (SOff n 0) = z mod 2 ^ 64.
Proof.
intros E n z H. rewrite U_SOff, H, Z.add_0_r, Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma w4t_U_zext8 : forall E n b, bv_unsigned (ew E n) = b -> 0 <= b < 256 -> U E (SExt false 8 (SOff n 0)) = b.
Proof.
intros E n b Hb Hr. rewrite U_SExt, U_SOff, Hb, Z.add_0_r. change (2 ^ Z.of_N 8) with 256.
rewrite (zcanon_id b) by (unfold M64; lia). cbv beta iota. rewrite Z.mod_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma w4t_den_zext8 : forall E n b, bv_unsigned (ew E n) = b -> 0 <= b < 256 ->
  sv_denot E (SExt false 8 (SOff n 0)) = w64 b.
Proof. intros E n b Hb Hr. unfold w64. rewrite denot_lit_U, (w4t_U_zext8 E n b Hb Hr). reflexivity. Qed.
(* The branch on the wrapper's result (beqz a0). *)
Lemma w4t_br_eq0 : forall E n (v : word), ew E n = v ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true -> v = w64 0.
Proof.
intros E n v Hn Hb. rewrite branch_eq_U in Hb. apply Z.eqb_eq in Hb.
unfold U in Hb. cbn [sv_denot] in Hb. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned in Hb.
apply bv_eq. exact Hb.
Qed.
Lemma w4t_br_ne0 : forall E n (v : word), ew E n = v ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false -> v <> w64 0.
Proof.
intros E n v Hn Hb Hv. rewrite branch_eq_U in Hb. apply Z.eqb_neq in Hb. apply Hb.
unfold U. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned, Hv. reflexivity.
Qed.

(* ---- byte lists -------------------------------------------------------------------------------------------- *)
Lemma w4t_bz0 : bv_unsigned (RcIdentModel.zb 0) = 0.
Proof. unfold RcIdentModel.zb. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma w4t_nth_map : forall (l : list byte) j,
  nth j (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth j l (RcIdentModel.zb 0)).
Proof.
induction l as [|x l IH]; intros [|j]; cbn [map nth]; try (symmetry; apply w4t_bz0); try reflexivity. apply IH.
Qed.
Lemma w4t_nth_skipn : forall {A : Type} (l : list A) k n d, nth n (skipn k l) d = nth (k + n) l d.
Proof.
intros A l k. revert l. induction k as [|k IH]; intros l n d; [reflexivity|].
destruct l as [|x l]; cbn [skipn]; [destruct n; reflexivity|]. cbn [Nat.add nth]. apply IH.
Qed.
Lemma w4t_bytes_eqb : forall xs ys, length xs = length ys ->
  (IdentSpec.bytes_eqb xs ys = true <->
   forall i, (i < length xs)%nat ->
   bv_unsigned (nth i xs (RcIdentModel.zb 0)) = bv_unsigned (nth i ys (RcIdentModel.zb 0))).
Proof.
induction xs as [|x xs IH]; intros [|y ys] Hl; cbn [length] in Hl; try discriminate.
- cbn [IdentSpec.bytes_eqb length]. split; [intros _ i Hi; lia | reflexivity].
- injection Hl as Hl. cbn [IdentSpec.bytes_eqb]. rewrite andb_true_iff, Z.eqb_eq, (IH ys Hl). split.
  + intros [H0 H1] [|i] Hi; cbn [nth]; [exact H0|]. apply H1. cbn [length] in Hi. lia.
  + intros H. split; [exact (H 0%nat ltac:(cbn [length]; lia))|].
    intros i Hi. exact (H (S i) ltac:(cbn [length]; lia)).
Qed.
Lemma w4t_garr8_snoc : forall segs (mem : word -> option byte) a (l : list Z) v,
  garr8 segs mem a l -> val_mem segs mem (a + Z.of_nat (length l)) 1 v -> 0 <= v < 256 ->
  garr8 segs mem a (l ++ [v]).
Proof.
intros segs mem a l v Hg Hv Hr j Hj. rewrite length_app in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j (length l)) as [Hlt | Hge].
- rewrite app_nth1 by exact Hlt. exact (Hg j Hlt).
- assert (Ej : j = length l) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
  split; [exact Hv | exact Hr].
Qed.
Lemma w4t_vm1 : forall segs H (m : word -> option byte) a v,
  aview segs H m a = Some v -> val_mem segs (mrestrict H m) a 1 v.
Proof.
intros segs H m a v Hv k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte segs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in Hv. injection Hv as <-. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_wrap.
change (bv_modulus 8) with 256 in *. change (2 ^ 8) with 256.
repeat rewrite (Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
Qed.

(* ---- the symbolic states of this piece ------------------------------------------------------------------- *)
(* 0x81d6c: region 0 is the machine-frame word mf+168 (the shadow base), atom 32, read-only. *)
Definition w4t_mf : YP09.region := YP09.mkRegion (Some 9%nat) 168 176 168 168 [YP09.mkChunk 168 (CVal 8 (SOff 32 0))].
(* 0x81d7c: region 0 is exp_nm[ln] (x20 = &exp_nm + ln), the one byte the run writes; region 1 its shadow
   byte, atom 32 = SHADOW_OFF + (&exp_nm + ln) / 8, an alias of the address the code computes from x20 and
   x6; region 2 is w4[0] (x18 = &w4), atom 33. *)
Definition w4t_dash : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 1 [].
Definition w4t_shc : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition w4t_w40 : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition w4t_alias : list (sv * sv) :=
  [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 0) (SLit 3)) (SOff 6 0), SOff 32 0)].
Definition ss_w4t3 : sstate := mkSS 0x1608 sr_atoms [w4t_dash; w4t_shc; w4t_w40] None (mkFacts [] [] w4t_alias).

(* A register of the state at the end of a run, as the symbolic expression the run computed. *)
Ltac w4t_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* A run whose state has no write window keeps the restricted memory. *)
Ltac w4t_ro HFr :=
  apply functional_extensionality; intros ?xq; apply HFr;
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in let Hra := fresh "Hra" in
  intros (rr & Hrr & Hra); cbn in Hrr;
  repeat (destruct Hrr as [<- | Hrr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi w4t_mf] in Hra; clear - Hra; lia|]);
  destruct Hrr.

(* Membership in a concrete list, without tauto (tauto's term mentions every section variable). *)
Ltac w4t_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac w4t_sub Hr := cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [w4t_in |]); destruct Hr.

(* The write windows of a run of the dash state: only exp_nm[ln] (x20). *)
Ltac w4t_win U20 :=
  intros ?bb ?wlo ?whi ?aa ?Hin ?Hr; cbn in Hin;
  repeat (destruct Hin as [?Eq | Hin];
          [injection Eq as <- <- <-; cbn [base_val] in Hr; rewrite ?U20 in Hr; cbv beta; clear - Hr; lia|]);
  destruct Hin.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable G : list (Z * Z).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JKEEP := (jkeep B).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JC4 := (jc4 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JC5 := (jc5 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation W4CPY := (j_w4cpy_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).

(* ---- the two cuts of this piece --------------------------------------------------------------------------- *)
(* +0x15f8 (0x81d6c), back from the bcmp wrapper: a0 = 0 exactly when the stem's last four bytes are w4's
   digits; x20 = &exp_nm + ln and x22 = ~&exp_nm (callee-saved across the wrapper). *)
Definition w4t_c6c (g : ectx) (pos mf nm tk dp : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x15f8)
(fun ly2 S2 W2 regs2 mem2 md2 =>
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
(getr regs2 10 = w64 0 <-> SlotModel.n_ends_w4 (e_pl g) = true) /\
getr regs2 18 = w64 (SFa g pos + V_w4) /\
getr regs2 20 = w64 (SFa g pos + V_nm + Z.of_nat (length (SlotModel.n_stem (e_pl g)))) /\
getr regs2 22 = w64 (Z.lnot (SFa g pos + V_nm)) /\
getr regs2 25 = w64 (SFa g pos + V_nm) /\ getr regs2 26 = w64 (SFa g pos + V_dp) /\
getr regs2 27 = w64 (Z.of_nat (length (SlotModel.n_stem (e_pl g)))) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\ sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
sh_zero W2 mem2 (SFa g pos + V_w4) N_w4 /\
bytes_at8 W2 mem2 (SFa g pos + V_w4) (SlotModel.n_W4 (e_pl g) ++ [RcIdentModel.zb 0]) /\
val_mem SEGS (rd W2 mem2) (mf + M_n2) 8 0 /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_stem (e_pl g))).

(* +0x1608 (0x81d7c), the dash path: the stem does not end in w4's digits; x6 = the shadow base. *)
Definition w4t_c7c (g : ectx) (pos mf nm tk dp : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1608)
(fun ly2 S2 W2 regs2 mem2 md2 =>
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
getr regs2 6 = w64 SHADOW_OFF /\
getr regs2 18 = w64 (SFa g pos + V_w4) /\
getr regs2 20 = w64 (SFa g pos + V_nm + Z.of_nat (length (SlotModel.n_stem (e_pl g)))) /\
getr regs2 22 = w64 (Z.lnot (SFa g pos + V_nm)) /\
getr regs2 25 = w64 (SFa g pos + V_nm) /\ getr regs2 26 = w64 (SFa g pos + V_dp) /\
getr regs2 27 = w64 (Z.of_nat (length (SlotModel.n_stem (e_pl g)))) /\
SlotModel.n_ends_w4 (e_pl g) = false /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\ sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
sh_zero W2 mem2 (SFa g pos + V_w4) N_w4 /\
bytes_at8 W2 mem2 (SFa g pos + V_w4) (SlotModel.n_W4 (e_pl g) ++ [RcIdentModel.zb 0]) /\
val_mem SEGS (rd W2 mem2) (mf + M_n2) 8 0 /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_stem (e_pl g))).

(* ---- reading the state ------------------------------------------------------------------------------------- *)
Lemma w4t_aview_garr8 : forall (W : world SEGS) mem a (l : list Z) (j : nat),
  garr8 SEGS (rd W mem) a l -> (j < length l)%nat ->
  aview SEGS (w_H W) mem (a + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W mem a l j Hg Hj. unfold aview. rewrite (garr8_mbyte SEGS _ a l j Hg Hj).
cbn [option_map]. f_equal. destruct (Hg j Hj) as (_ & Hr).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.
(* The value of the chunk at offset off of region i of a state (as lib/B/Prog/LLVMFuzzerTestOneInput_seg_C.v). *)
Lemma w4t_chunk : forall E ss ms i r off (n : N) e b v,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> base_val E (YP09.r_base r) = b ->
  In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem SEGS (ms_mem ms) (b + off) (N.to_nat n) v.
Proof.
intros E ss ms i r off n e b v HS Hi Hb Hin He Hv Hn.
pose proof (st_ok_pi_region_nth E ss ms i r HS Hi) as (_ & _ & _ & Hc). rewrite Hb in Hc.
apply (val_of_chunk_ok SEGS E (ms_mem ms) b off n e v); [|exact He | exact Hv | exact Hn].
exact (proj1 (Forall_forall _ _) Hc _ Hin).
Qed.
Ltac w4t_ck HS i off b Hb :=
  lazymatch type of HS with st_ok_pi _ _ ?E ?ss ?msr =>
    let rs := eval vm_compute in (ss_mem ss) in
    let r := eval vm_compute in (nth i rs (YP09.mkRegion None 0 0 0 0 [])) in
    let c := eval vm_compute in (List.find (fun c => Z.eqb (YP09.c_off c) off) (YP09.r_chunks r)) in
    lazymatch c with Some (YP09.mkChunk _ (CVal ?n ?e)) =>
      apply (w4t_chunk E ss msr i r off n e b _ HS ltac:(vm_compute; reflexivity)
        ltac:(cbn [base_val YP09.r_base]; exact Hb)
        ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right])))
    end
  end.

(* The stem's last four bytes against w4's, as the wrapper compares them. *)
Lemma w4t_cmp_iff : forall (g : ectx) pos (W : world SEGS) mem,
  SlotModel.n_wok (e_pl g) = true -> (4 <= length (SlotModel.n_stem (e_pl g)))%nat ->
  bytes_at8 W mem (SFa g pos + V_nm) (SlotModel.n_stem (e_pl g)) ->
  bytes_at8 W mem (SFa g pos + V_w4) (SlotModel.n_W4 (e_pl g) ++ [RcIdentModel.zb 0]) ->
  ((forall i, 0 <= i < 4 ->
    aview SEGS (w_H W) mem (SFa g pos + V_nm + Z.of_nat (length (SlotModel.n_stem (e_pl g))) - 4 + i) =
    aview SEGS (w_H W) mem (SFa g pos + V_w4 + i)) <-> SlotModel.n_ends_w4 (e_pl g) = true).
Proof.
intros g pos W mem Hwok H4 Bn Bw.
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m1_W4_len _ Hwok) as HW.
rewrite (LLVMFuzzerTestOneInput_seg_J_model.m1_ends_w4_long _ Hwok H4).
unfold bytes_at8 in Bn, Bw.
set (st := SlotModel.n_stem (e_pl g)) in *. set (w4 := SlotModel.n_W4 (e_pl g)) in *.
assert (Hlen : length (skipn (length st - 4) st) = length w4) by (rewrite length_skipn, HW; lia).
rewrite (w4t_bytes_eqb _ _ Hlen). rewrite Hlen, HW.
assert (AN : forall i, (i < 4)%nat ->
  aview SEGS (w_H W) mem (SFa g pos + V_nm + Z.of_nat (length st) - 4 + Z.of_nat i) =
  Some (bv_unsigned (nth i (skipn (length st - 4) st) (RcIdentModel.zb 0)))).
{ intros i Hi.
  replace (SFa g pos + V_nm + Z.of_nat (length st) - 4 + Z.of_nat i)
    with (SFa g pos + V_nm + Z.of_nat (length st - 4 + i)) by lia.
  rewrite (w4t_aview_garr8 W mem _ _ _ Bn) by (rewrite length_map; lia).
  rewrite w4t_nth_map, w4t_nth_skipn. reflexivity. }
assert (AW : forall i, (i < 4)%nat ->
  aview SEGS (w_H W) mem (SFa g pos + V_w4 + Z.of_nat i) = Some (bv_unsigned (nth i w4 (RcIdentModel.zb 0)))).
{ intros i Hi. rewrite (w4t_aview_garr8 W mem _ _ _ Bw) by (rewrite length_map, length_app, HW; cbn [length]; lia).
  rewrite w4t_nth_map, app_nth1 by lia. reflexivity. }
split.
- intros H i Hi. specialize (H (Z.of_nat i) ltac:(lia)). rewrite (AN i Hi), (AW i Hi) in H. injection H as H. exact H.
- intros H i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite (AN (Z.to_nat i) ltac:(lia)), (AW (Z.to_nat i) ltac:(lia)). f_equal. apply H. lia.
Qed.

Section d.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp).
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis W4C : W4CPY.

(* ---- where things are ------------------------------------------------------------------------------------ *)
Lemma w4t_geo : forall (g : ectx) pos mf k ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
  ly2 S2 W2 mem2 md2 k ->
  frames S2 = [(4, pos)] -> ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  frame_addr ly2 4 pos = SFa g pos /\ 4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\
  SFa g pos mod 64 = 0 /\
  (SFa g pos + 1024 <= 2147446784 \/ 17594333495296 <= SFa g pos) /\
  shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8 /\
  0 <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= alloc_ceiling /\
  (SFa g pos + 1024 <= shadow_addr (SFa g pos) \/ shadow_addr (SFa g pos) + 128 <= SFa g pos) /\
  alloc_ceiling + 16384 <= mf /\ e_sp0 g - 336 <= mf <= e_sp0 g - 320 /\ mf mod 32 = 0 /\
  e_sp0 g mod 16 = 0 /\ e_sp0 g <= 2 ^ 47 /\ 336 + 16 + 16384 <= LLVMF_STK.
Proof.
intros g pos mf k ly2 S2 W2 regs2 mem2 md2 HJ Hfrs HC.
pose proof asan_consts as (C1 & _).
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'. assert (Has : ASTACK = 16384) by reflexivity.
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
destruct (j_geo B LLVMF_STK LAWS g pos k ly2 S2 W2 mem2 md2 HJ Hfrs)
  as (EFa & HSF0 & HSF1 & HSF64 & Hsh0 & Hsh1 & Hsfsh).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (_ & _ & HSFapp).
rewrite EFa in HSFapp. change (fs_frame_bytes 4) with 1024 in HSFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HSFapp.
pose proof HC as (_ & _ & _ & Hmfb & Hmf32 & _).
rewrite Has in HSTK'.
split; [exact EFa|]. split; [exact HSF0|]. split; [exact HSF1|]. split; [exact HSF64|].
split; [clear - HSFapp; lia|]. split; [reflexivity|]. split; [exact Hsh0|]. split; [exact Hsh1|].
split; [exact Hsfsh|].
split; [clear - Hmfb Hceil Hslo HSTK'; lia|]. split; [exact Hmfb|]. split; [exact Hmf32|].
split; [exact Hsp0al|]. split; [clear - Hshi H47; lia | exact HSTK'].
Qed.

(* ---- the memory facts across a run or the call ------------------------------------------------------------ *)
(* Every fact the cuts carry (ecommon, jkeep, the frame variables but exp_nm, the machine frame) speaks of
   bytes below alloc_ceiling or at or above mf, outside exp_nm: the bcmp wrapper writes only its own stack
   window below mf, the dash run only exp_nm[ln]. *)
Lemma w4t_move : forall (g : ectx) pos mf nm tk dp k ly2 S2 (W2 : world SEGS) regs2 mem2 md2 regs3 mem3 md3,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
  ly2 S2 W2 mem2 md2 k ->
  frames S2 = [(4, pos)] ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
  (forall a, 0 <= a < 2 ^ 64 -> (a < alloc_ceiling \/ mf <= a) ->
   ~ (SFa g pos + V_nm <= a < SFa g pos + V_nm + N_nm) ->
   aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 21%bv; 23%bv; 24%bv] -> getr regs3 r = getr regs2 r) ->
  m_fds md3 = m_fds md2 -> m_fs md3 = m_fs md2 ->
  ECOMMON g pos mf ly2 S2 W2 regs3 mem3 md3 /\ JKEEP g pos mf nm tk dp ly2 S2 W2 regs3 mem3 /\
  (forall off n, 0 <= off -> off + n <= 1024 -> 0 <= n ->
   sh_zero W2 mem2 (SFa g pos + off) n -> sh_zero W2 mem3 (SFa g pos + off) n) /\
  (forall off (l : list byte), 0 <= off -> off + Z.of_nat (length l) <= 1024 ->
   (off + Z.of_nat (length l) <= V_nm \/ V_nm + N_nm <= off) ->
   bytes_at8 W2 mem2 (SFa g pos + off) l -> bytes_at8 W2 mem3 (SFa g pos + off) l) /\
  (forall off (n : nat) v, 0 <= off -> off + Z.of_nat n <= 320 ->
   val_mem SEGS (rd W2 mem2) (mf + off) n v -> val_mem SEGS (rd W2 mem3) (mf + off) n v).
Proof.
intros g pos mf nm tk dp k ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HJ Hfrs HC HK KP RK Efd Efs.
pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR2 & _).
destruct (w4t_geo g pos mf k ly2 S2 W2 regs2 mem2 md2 HJ Hfrs HC)
  as (EFa & HSF0 & HSF1 & HSF64 & _ & Esh & Hsh0 & Hsh1 & Hsfsh & Hmf0 & _ & _ & _ & H47 & _).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
V24 & V32 & V40 & V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HK as (Hbl & Rs7 & R24 & R21 & V152 & V184 & V144 & V128 & V120 & V176 & V160 & V112 & Hid & Hbufs).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
set (sp0 := e_sp0 g) in *. set (SF := SFa g pos) in *.
(* the four kinds of kept bytes *)
assert (KFR : forall x, SF <= x < SF + 1024 -> ~ (SF + V_nm <= x < SF + V_nm + N_nm) ->
  aview SEGS (w_H W2) mem3 x = aview SEGS (w_H W2) mem2 x).
{ intros x Hx Hn. apply KP; [clear - Hx HSF0 HSF1 C1; lia | left; clear - Hx HSF1; lia | exact Hn]. }
assert (KSH : forall x, SHADOW_OFF + SF / 8 <= x < SHADOW_OFF + SF / 8 + 128 ->
  aview SEGS (w_H W2) mem3 x = aview SEGS (w_H W2) mem2 x).
{ intros x Hx. rewrite <- Esh in Hx.
  apply KP; [clear - Hx Hsh0 Hsh1 C1; lia | left; clear - Hx Hsh1; lia | clear - Hx Hsfsh; unfold V_nm, N_nm; lia]. }
assert (KMF : forall x, mf <= x < sp0 -> aview SEGS (w_H W2) mem3 x = aview SEGS (w_H W2) mem2 x).
{ intros x Hx. apply KP; [clear - Hx Hmf0 Hmfb H47 C1; lia | right; clear - Hx; lia
  | clear - Hx Hmf0 HSF1; unfold V_nm, N_nm; lia]. }
assert (KHB : forall p n x, In (p, n) (ablocks B ly2 S2) -> p <= x < p + req_size n ->
  aview SEGS (w_H W2) mem3 x = aview SEGS (w_H W2) mem2 x).
{ intros p n x Hin Hx.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n HAR2 Hin) as (_ & Hp4096 & Hpce & _).
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 p n 4 pos HAR2 Hin Hin4) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFa in Hd. change (fs_frame_bytes 4) with 1024 in Hd.
  apply KP; [clear - Hx Hp4096 Hpce C1; lia | left; clear - Hx Hpce; lia | clear - Hx Hd; unfold V_nm, N_nm; lia]. }
(* the moves *)
assert (VMS : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= sp0 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem3) a n v).
{ intros a n v H1 H2 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem3 a a n v); [|exact Hv].
  intros kk Hkk. apply KMF. clear - H1 H2 Hkk. lia. }
assert (VFR : forall off (n : nat) v, 0 <= off -> off + Z.of_nat n <= 1024 ->
  (off + Z.of_nat n <= V_nm \/ V_nm + N_nm <= off) ->
  val_mem SEGS (rd W2 mem2) (SF + off) n v -> val_mem SEGS (rd W2 mem3) (SF + off) n v).
{ intros off n v H0 H1 H2 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem3 (SF + off) (SF + off) n v); [|exact Hv].
  intros kk Hkk. apply KFR; clear - H0 H1 H2 Hkk; unfold V_nm, N_nm in *; lia. }
assert (GFR : forall off (l : list byte), 0 <= off -> off + Z.of_nat (length l) <= 1024 ->
  (off + Z.of_nat (length l) <= V_nm \/ V_nm + N_nm <= off) ->
  bytes_at8 W2 mem2 (SF + off) l -> bytes_at8 W2 mem3 (SF + off) l).
{ intros off l H0 H1 H2 Hg. unfold bytes_at8 in *.
  apply (j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem3 _ _); [|exact Hg].
  intros kk Hkk. rewrite length_map in Hkk. apply KFR; clear - H0 H1 H2 Hkk; unfold V_nm, N_nm in *; lia. }
assert (GHB : forall p n (l : list byte), In (p, n) (ablocks B ly2 S2) -> Z.of_nat (length l) <= req_size n ->
  bytes_at8 W2 mem2 p l -> bytes_at8 W2 mem3 p l).
{ intros p n l Hin Hl Hg. unfold bytes_at8 in *.
  apply (j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem3 _ _); [|exact Hg].
  intros kk Hkk. rewrite length_map in Hkk. apply (KHB p n); [exact Hin | clear - Hkk Hl; lia]. }
assert (SHZ : forall off n, 0 <= off -> off + n <= 1024 -> 0 <= n ->
  sh_zero W2 mem2 (SF + off) n -> sh_zero W2 mem3 (SF + off) n).
{ intros off n H0 H1 Hn Hz. unfold sh_zero in *.
  apply (j_zero_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) mem3) SHADOW_OFF (SF + off) n);
  [|exact Hz].
  intros ii Hii. apply KSH. unfold shadow_of_addr. clear - H0 H1 Hn Hii HSF64. lia. }
assert (SHB : forall off n, 0 <= off -> off + n + 8 <= 1024 -> 0 <= n ->
  sh_blk W2 mem2 (SF + off) n -> sh_blk W2 mem3 (SF + off) n).
{ intros off n H0 H1 Hn Hz. unfold sh_blk in *.
  apply (j_block_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) mem3) SHADOW_OFF (SF + off) n);
  [|exact Hz].
  intros ii Hii. apply KSH. unfold shadow_of_addr. clear - H0 H1 Hn Hii HSF64. lia. }
split.
{ unfold ecommon. change (e_sp0 g) with sp0. change (SFa g pos) with SF.
  split; [rewrite (RK 2%bv ltac:(w4t_in)); exact Rsp|].
  split; [rewrite (RK 9%bv ltac:(w4t_in)); exact Rs1|].
  split; [rewrite (RK 8%bv ltac:(w4t_in)); exact Rs0|].
  split; [exact Hmfb|]. split; [exact Hmf32|].
  split; [rewrite (RK 3%bv ltac:(w4t_in)); exact Rgp|].
  split; [rewrite (RK 4%bv ltac:(w4t_in)); exact Rtp|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V16]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V64]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V192]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V168]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vra]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vs0]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V24]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V32]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V40]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V48]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V56]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V64b]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V72]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V80]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V88]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V96]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V104]|].
  split; [apply (VFR 1016 8%nat); [clear; lia | clear; cbn; lia | right; unfold V_nm, N_nm; clear; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efd; exact (Hfds fd)|].
  split; [rewrite Efs; exact Hfs|].
  pose proof HPRE as (_ & _ & _ & _ & Hinp & Hlen & _).
  unfold bytes_at8 in *. apply (j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem3 _ _); [|exact Hinb].
  intros j Hj. rewrite length_map, <- Hlen in Hj.
  destruct Hinp as [[Hn0 _] | [[Hn0 Hn26] Hine]]; [clear - Hj Hn0; lia|].
  assert (Hine2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
  { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hine. }
  pose proof (req_size_pos (e_n g) ltac:(lia)) as [Hrq1 Hrq2].
  apply (KHB (e_p g) (e_n g)); [exact Hine2 | clear - Hj Hrq1 Hrq2; lia]. }
split.
{ unfold jkeep. split; [exact Hbl|].
  split; [unfold sh_reg in *; rewrite (RK 23%bv ltac:(w4t_in)); exact Rs7|].
  split; [rewrite (RK 24%bv ltac:(w4t_in)); exact R24|].
  split; [rewrite (RK 21%bv ltac:(w4t_in)); exact R21|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V152]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V184]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V144]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V128]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V120]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V176]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V160]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V112]|].
  split.
  { destruct Hid as (Hidb & Hidz & Hidk). unfold id_at. change (SFa g pos) with SF.
    assert (HL : Z.of_nat (length (m_id g (m_nrec g))) = 38).
    { unfold m_id. rewrite SlotModel.rec_id_length. unfold RcIdentModel.ID_SIZE. reflexivity. }
    split; [|split].
    - apply GFR; [unfold V_id; clear; lia | rewrite HL; unfold V_id; clear; lia
      | left; rewrite HL; unfold V_id, V_nm; clear; lia | exact Hidb].
    - apply SHZ; [unfold V_id; clear; lia | unfold V_id, N_id; clear; lia | unfold N_id; clear; lia | exact Hidz].
    - apply SHB; [unfold V_id; clear; lia | unfold V_id, N_id; clear; lia | unfold N_id; clear; lia | exact Hidk]. }
  intros Hr0. destruct (Hbufs Hr0) as (B1 & B2 & B3).
  destruct (W4TM.fits_lens (e_pl g) Hr0) as (L1 & L2 & L3).
  destruct Hbl as [Hperm _].
  assert (Hin : forall x, In x [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
    (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1); (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] ->
    In x (ablocks B ly2 S2)).
  { intros x Hx. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hx. }
  split; [|split].
  - apply (GHB nm (Z.max (SlotModel.t_cap_name (e_pl g)) 1)); [apply Hin; w4t_in | | exact B1].
    unfold req_size. destruct (Z.eqb_spec (Z.max (SlotModel.t_cap_name (e_pl g)) 1) 0) as [E0 | E0];
    clear - L1 E0; lia.
  - apply (GHB tk (Z.max (SlotModel.t_cap_tok (e_pl g)) 1)); [apply Hin; w4t_in | | exact B2].
    unfold req_size. destruct (Z.eqb_spec (Z.max (SlotModel.t_cap_tok (e_pl g)) 1) 0) as [E0 | E0];
    clear - L2 E0; lia.
  - apply (GHB dp (Z.max (SlotModel.t_cap_disp (e_pl g)) 1)); [apply Hin; w4t_in | | exact B3].
    unfold req_size. destruct (Z.eqb_spec (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) 0) as [E0 | E0];
    clear - L3 E0; lia. }
split; [exact SHZ|]. split; [exact GFR|].
intros off n v H0 H1 Hv. apply VMS; [clear - H0; lia | clear - H0 H1 Hmfb; lia | exact Hv].
Qed.

(* ---- the bcmp wrapper from the journal, keeping the fd table and the file system ------------------------- *)
Lemma w4t_bcmp_at : forall pc, abcmp_realizes SEGS B pc ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
  0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  src_ok SEGS W regsT memT x n -> src_ok SEGS W regsT memT y n ->
  (forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  (forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  amem_range x n -> amem_range y n ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) x n) ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) y n) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
   c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
   ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
   m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc /\
   aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
   (v = w64 0 <-> forall i, 0 <= i < n -> aview SEGS (w_H W) memT (x + i) = aview SEGS (w_H W) memT (y + i)) /\
   (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
    aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n o raw
HJ Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
pose proof pa_segs_low as Hsegs.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at with (o := o); try eassumption; try zlia. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
  by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x y n HPRE Hlo2 Hpres2E Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsx Hsy
  ltac:(rewrite Hsp'; exact Hbx) ltac:(rewrite Hsp'; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hcmp & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS Hsegs STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; zlia.
  - exact HAR2.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [rewrite (same_but_materialized_wvb mdc md2 Hsame); apply j_wvb_fds|].
split; [rewrite (same_but_materialized_wvb mdc md2 Hsame); apply j_wvb_fs|].
split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. exact Hfr.
Qed.

(* ---- +0x15c4 .. +0x15f8 or +0x1608: the tail test, the traps and the bcmp wrapper --------------------------- *)
Lemma w4t_L1 : forall (g : ectx) pos mf nm tk dp W2 c2, JC4 g pos mf nm tk dp W2 c2 ->
  SlotModel.n_wok (e_pl g) = true ->
  SRr SEGS W2 c2 (fun W3 c3 => w4t_c7c g pos mf nm tk dp W3 c3 \/ w4t_c6c g pos mf nm tk dp W3 c3).
Proof.
intros g pos mf nm tk dp W2 c2 Hstart Hwok.
pose proof (paj_run B LAWS) as RUN. pose proof (paj_run_to B LAWS) as RUNTO. pose proof (paj_branch (PI := PI)) as BR.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HK & R6 & R18 & R25 & R26 & R27 & SHnm & SHdp & SHw4 & Bw4 & Vn2 & Bnm).
pose proof HC as (Rsp & Rs1 & Rs0 & _ & _ & Rgp & Rtp & _).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (w4t_geo g pos mf _ ly2 S2 W2 regs2 mem2 md2 HJ Hfrs HC)
  as (EFa & HSF0 & HSF1 & HSF64 & HSFapp & Esh & Hsh0 & Hsh1 & Hsfsh & Hmf0 & Hmfb & Hmf32 & Hsp0al & H47 & HSTK').
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (Hln : 0 <= Z.of_nat (length (SlotModel.n_stem (e_pl g))) <= 16)
  by (pose proof (LLVMFuzzerTestOneInput_seg_J_model.m1_stem_len (e_pl g)) as Hs; clear - Hs; lia).
pose proof HJ as HJ0.
set (sp0 := e_sp0 g) in *. set (SF := SFa g pos) in *.
set (ln := Z.of_nat (length (SlotModel.n_stem (e_pl g)))) in *.
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs2 r)
  by (intros k' r Hk'; subst E; apply ew_Eimg_Ereg_nat; exact Hk').
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x15c4 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x15c4)) mem2 (seg_rom SEGS)))).
{ subst E. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (AGE : env_agree 32 (Ereg regs2 []) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (SHOK : sh_ok SEGS (SLit SB) [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (U25 : bv_unsigned (ew E 25) = SF + V_nm).
{ rewrite (EE 25%nat 25%bv eq_refl), R25. apply unsigned_lit_small. unfold V_nm. clear - HSF0 HSF1 C1. lia. }
assert (U27 : bv_unsigned (ew E 27) = ln).
{ rewrite (EE 27%nat 27%bv eq_refl), R27. apply unsigned_lit_small. clear - Hln. lia. }
assert (EV27 : U E (SOff 27 0) = ln).
{ rewrite U_SOff, U27, Z.add_0_r. apply zcanon_id. unfold M64. clear - Hln. lia. }
unfold cfg_at. change (w64 (BASE + 0x15c4)) with (Z_to_bv 64 (BASE + 0x15c4)).
(* 0x81d38 .. the test ln < 4 at 0x81d44 *)
paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_nil |].
rename ms into ms1. rename HFr into HFr1. clear HF HG.
assert (EQ1 : mrestrict (w_H W2) (ms_mem ms1) = mrestrict (w_H W2) mem2) by (w4t_ro HFr1).
clear HFr1.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* ln < 4: on to 0x81d7c *)
  assert (Hlt : ln < 4).
  { rewrite branch_ltu_U, EV27, U_SLit in Hc. change (zcanon 4) with 4 in Hc. apply Z.ltb_lt in Hc. exact Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x1608; [apply awr_ok_nil |].
  assert (EQ2 : mrestrict (w_H W2) (ms_mem ms) = mrestrict (w_H W2) (ms_mem ms1)) by (w4t_ro HFr).
  clear HFr HF HG.
  assert (EV : aview SEGS (w_H W2) (ms_mem ms) = aview SEGS (w_H W2) mem2)
    by (unfold aview; rewrite EQ2, EQ1; reflexivity).
  assert (RK : forall r, In r [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
    getr (ms_regs ms) r = getr regs2 r)
    by (eapply (regs_kept_of_st_ok_pi E _ (restrict (w_H W2) ms) regs2 _
          [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS AGE);
        vm_compute; reflexivity).
  w4t_reg HS (20%bv : bv 5) Q20. w4t_reg HS (22%bv : bv 5) Q22.
  rewrite (w4t_den_add E 25 27 0 0 (SF + V_nm) ln (SF + V_nm + ln) U25 U27) in Q20
    by (unfold V_nm; clear - HSF0 HSF1 C1 Hln; lia).
  rewrite (w4t_den_not E 25 (SF + V_nm) U25) in Q22 by (unfold V_nm; clear - HSF0 HSF1 C1; lia).
  pmkst HS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ =>
    destruct (w4t_move g pos mf nm tk dp _ ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) mdx HJ0 Hfrs HC HK
      ltac:(intros a _ _ _; rewrite EV; reflexivity)
      ltac:(intros r Hr; apply RK; w4t_sub Hr)
      ltac:(rewrite ?j_wvb_fds; reflexivity) ltac:(rewrite ?j_wvb_fs; reflexivity))
      as (HC3 & HK3 & MSZ & MGF & MVM)
  end.
  apply SRr_ret. left. unfold w4t_c7c, acut.
  exists ly2, S2, (ms_regs ms), (ms_mem ms). eexists.
  split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
  split; [exact MLE|]. split; [exact MOK|]. split; [exact HC3|]. split; [exact HK3|].
  change (SFa g pos) with SF. change (Z.of_nat (length (SlotModel.n_stem (e_pl g)))) with ln.
  split; [rewrite (RK 6%bv ltac:(w4t_in)); exact R6|].
  split; [rewrite (RK 18%bv ltac:(w4t_in)); exact R18|].
  split; [exact Q20|]. split; [exact Q22|].
  split; [rewrite (RK 25%bv ltac:(w4t_in)); exact R25|].
  split; [rewrite (RK 26%bv ltac:(w4t_in)); exact R26|].
  split; [rewrite (RK 27%bv ltac:(w4t_in)); exact R27|].
  split; [apply LLVMFuzzerTestOneInput_seg_J_model.m1_ends_w4_short; clear - Hlt; unfold ln in Hlt; lia|].
  split; [apply MSZ; [unfold V_nm; clear; lia | unfold V_nm, N_nm; clear; lia | unfold N_nm; clear; lia | exact SHnm]|].
  split; [apply MSZ; [unfold V_dp; clear; lia | unfold V_dp, N_dp; clear; lia | unfold N_dp; clear; lia | exact SHdp]|].
  split; [apply MSZ; [unfold V_w4; clear; lia | unfold V_w4, N_w4; clear; lia | unfold N_w4; clear; lia | exact SHw4]|].
  split.
  { apply MGF; [unfold V_w4; clear; lia | | | exact Bw4];
    rewrite length_app, (LLVMFuzzerTestOneInput_seg_J_model.m1_W4_len _ Hwok); cbn [length];
    [unfold V_w4; clear; lia | right; unfold V_w4, V_nm, N_nm; clear; lia]. }
  split; [apply MVM; [unfold M_n2; clear; lia | unfold M_n2; clear; lia | exact Vn2]|].
  unfold bytes_at8 in *. rewrite EQ2, EQ1. exact Bnm.
- (* ln >= 4: the traps, then the bcmp wrapper *)
  assert (Hge : 4 <= ln).
  { rewrite branch_ltu_U, EV27, U_SLit in Hc. change (zcanon 4) with 4 in Hc. apply Z.ltb_ge in Hc. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_nil |].
  rename ms into ms2. rename HFr into HFr2. clear HF HG.
  assert (EQ2 : mrestrict (w_H W2) (ms_mem ms2) = mrestrict (w_H W2) (ms_mem ms1)) by (w4t_ro HFr2).
  clear HFr2.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  1: { exfalso. rewrite branch_ltu_U, EV27, U_SLit in Hc. change (zcanon 32) with 32 in Hc.
       apply Z.ltb_lt in Hc. clear - Hc Hln. lia. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_nil |].
  rename ms into ms3. rename HFr into HFr3. clear HF HG.
  assert (EQ3 : mrestrict (w_H W2) (ms_mem ms3) = mrestrict (w_H W2) (ms_mem ms2)) by (w4t_ro HFr3).
  clear HFr3.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  1: { exfalso. rewrite branch_ltu_U, (w4t_U_not E 25 (SF + V_nm) U25), EV27 in Hc
         by (unfold V_nm; clear - HSF0 HSF1 C1; lia).
       rewrite w4t_lnot_mod in Hc by (unfold V_nm; clear - HSF0 HSF1 C1; lia).
       apply Z.ltb_lt in Hc. unfold V_nm in Hc. clear - Hc Hln HSF1 C1. lia. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_nil |].
  rename ms into ms4. rename HFr into HFr4. clear HF HG.
  assert (EQ4 : mrestrict (w_H W2) (ms_mem ms4) = mrestrict (w_H W2) (ms_mem ms3)) by (w4t_ro HFr4).
  clear HFr4.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  1: { exfalso. rewrite branch_ltu_U, (w4t_U_add E 25 27 0 0 (SF + V_nm) ln U25 U27), U_SLit in Hc
         by (unfold V_nm; clear - HSF0 HSF1 C1 Hln; lia).
       change (zcanon 5) with 5 in Hc. apply Z.ltb_lt in Hc. unfold V_nm in Hc. clear - Hc HSF0 Hln. lia. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_nil |].
  rename ms into ms5. rename HFr into HFr5. clear HF HG.
  assert (EQ5 : mrestrict (w_H W2) (ms_mem ms5) = mrestrict (w_H W2) (ms_mem ms4)) by (w4t_ro HFr5).
  clear HFr5.
  assert (EQT : mrestrict (w_H W2) (ms_mem ms5) = mrestrict (w_H W2) mem2) by (rewrite EQ5, EQ4, EQ3, EQ2, EQ1; reflexivity).
  assert (EV : aview SEGS (w_H W2) (ms_mem ms5) = aview SEGS (w_H W2) mem2) by (unfold aview; rewrite EQT; reflexivity).
  (* the registers at the wrapper's entry *)
  assert (RKT : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
    getr (ms_regs ms5) r = getr regs2 r)
    by (eapply (regs_kept_of_st_ok SEGS E _ (restrict (w_H W2) ms5) regs2 _
          [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS AGE);
        vm_compute; reflexivity).
  w4t_reg HS (10%bv : bv 5) Q10. w4t_reg HS (11%bv : bv 5) Q11. w4t_reg HS (12%bv : bv 5) Q12. w4t_reg HS (1%bv : bv 5) Q1.
  w4t_reg HS (20%bv : bv 5) Q20. w4t_reg HS (22%bv : bv 5) Q22.
  rewrite (w4t_den_add E 25 27 (-4) 0 (SF + V_nm) ln (SF + V_nm + ln - 4) U25 U27) in Q10
    by (unfold V_nm; clear - HSF0 HSF1 C1 Hln; lia).
  rewrite w4t_den_atom, (EE 18%nat 18%bv eq_refl), R18 in Q11.
  rewrite (w4t_den_lit E 4) in Q12 by (clear; lia).
  rewrite (w4t_den_add E 25 27 0 0 (SF + V_nm) ln (SF + V_nm + ln) U25 U27) in Q20
    by (unfold V_nm; clear - HSF0 HSF1 C1 Hln; lia).
  rewrite (w4t_den_not E 25 (SF + V_nm) U25) in Q22 by (unfold V_nm; clear - HSF0 HSF1 C1; lia).
  assert (Usp : spZ (ms_regs ms5) = mf).
  { unfold spZ. rewrite (RKT 2%bv ltac:(w4t_in)), Rsp. unfold w64. apply unsigned_lit_small.
    clear - Hmf0 Hmfb H47 C1. lia. }
  assert (HSFapp' : SF + 1024 <= 2147446784 \/ (17594333495296 <= SF /\ SF + 1024 <= alloc_ceiling))
    by (clear - HSFapp HSF1; lia).
  pmkst HS.
  pose proof (proj1 HJ) as HART.
  eapply SRr_bind.
  { eapply (w4t_bcmp_at (SIGMA IB___interceptor_trampoline_bcmp) ABCMP W2 (ms_regs ms5) (ms_mem ms5)
      LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ _
      (SF + V_nm + ln - 4) (SF + V_w4) 4 (mf - sp0) (Z_to_bv 64 (BASE + 0x15f8)) HJ).
    - exact Q10.
    - exact Q11.
    - exact Q12.
    - clear. lia.
    - unfold V_nm. clear - HSF0 Hge. lia.
    - unfold V_nm. clear - HSF1 C1 Hln. lia.
    - unfold V_w4. clear - HSF0. lia.
    - unfold V_w4. clear - HSF1 C1. lia.
    - rewrite Usp. clear. lia.
    - clear - Hmf32 Hsp0al. lia.
    - clear - Hmfb. lia.
    - rewrite Hes. clear - Hmfb HSTK'. lia.
    - rewrite (RKT 3%bv ltac:(w4t_in)). exact Rgp.
    - rewrite (RKT 4%bv ltac:(w4t_in)). exact Rtp.
    - rewrite Q1. exact (codeptr_val E 5624 HEI).
    - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
    - intros a Ha. split.
      + apply (aview_some_of_apresent SEGS).
        refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ _)).
        right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
        unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 4) with 1024.
        unfold V_nm in Ha. clear - Ha Hln Hge. lia.
      + rewrite Usp, Hes. unfold V_nm in Ha. clear - Ha HSF1 Hmf0 Hln. lia.
    - intros a Ha. split.
      + apply (aview_some_of_apresent SEGS).
        refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ _)).
        right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
        unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 4) with 1024.
        unfold V_w4 in Ha. clear - Ha. lia.
      + rewrite Usp, Hes. unfold V_w4 in Ha. clear - Ha HSF1 Hmf0. lia.
    - intros a Ha. rewrite Hes. unfold V_nm in Ha. clear - Ha HSF1 Hmf0 Hln. lia.
    - intros a Ha. rewrite Hes. unfold V_w4 in Ha. clear - Ha HSF1 Hmf0. lia.
    - apply amem_range_high; [clear; lia | unfold V_nm; clear - HSFapp' Hln; lia | unfold V_nm; clear - HSF1 Hln; lia].
    - apply amem_range_high; [clear; lia | unfold V_w4; clear - HSFapp'; lia | unfold V_w4; clear - HSF1; lia].
    - rewrite EV. apply (range_addressable_sub _ _ (SF + V_nm) N_nm).
      + apply zero_shadow_range; [unfold V_nm; clear - HSF64; lia | reflexivity | exact SHnm].
      + unfold V_nm. clear - Hge. lia.
      + unfold V_nm, N_nm. clear - Hln. lia.
    - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms5) _ 4 pos
        (SF + V_nm + ln - 4) 4 HART Hin4);
      [rewrite EFa; unfold V_nm; clear - Hge; lia
      | rewrite EFa; change (fs_frame_bytes 4) with 1024; unfold V_nm; clear - Hln; lia | clear; lia].
    - rewrite EV. apply (range_addressable_sub _ _ (SF + V_w4) N_w4).
      + apply zero_shadow_range; [unfold V_w4; clear - HSF64; lia | reflexivity | exact SHw4].
      + clear. lia.
      + unfold N_w4. clear. lia.
    - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms5) _ 4 pos
        (SF + V_w4) 4 HART Hin4);
      [rewrite EFa; unfold V_w4; clear; lia
      | rewrite EFa; change (fs_frame_bytes 4) with 1024; unfold V_w4; clear; lia | clear; lia]. }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v & -> & HJ3 & Efd3 & Efs3 & HP3 & Hv & Hcmp & Hfr3).
  assert (AP : forall r : Z, acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr (ms_regs ms5) (Z_to_bv 5 r))
    by exact HP3.
  assert (P18 : getr regs3 18 = getr (ms_regs ms5) 18) by exact (AP 18 ltac:(unfold acallee_saved; lia)).
  assert (P20 : getr regs3 20 = getr (ms_regs ms5) 20) by exact (AP 20 ltac:(unfold acallee_saved; lia)).
  assert (P22 : getr regs3 22 = getr (ms_regs ms5) 22) by exact (AP 22 ltac:(unfold acallee_saved; lia)).
  assert (P25 : getr regs3 25 = getr (ms_regs ms5) 25) by exact (AP 25 ltac:(unfold acallee_saved; lia)).
  assert (P26 : getr regs3 26 = getr (ms_regs ms5) 26) by exact (AP 26 ltac:(unfold acallee_saved; lia)).
  assert (P27 : getr regs3 27 = getr (ms_regs ms5) 27) by exact (AP 27 ltac:(unfold acallee_saved; lia)).
  assert (RK3 : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 21%bv; 23%bv; 24%bv] -> getr regs3 r = getr regs2 r).
  { intros r Hr. rewrite <- (RKT r ltac:(w4t_sub Hr)). cbn in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]];
    [ exact (AP 2 ltac:(unfold acallee_saved; lia))
    | exact (AP 3 ltac:(unfold acallee_saved; lia))
    | exact (AP 4 ltac:(unfold acallee_saved; lia))
    | exact (AP 8 ltac:(unfold acallee_saved; lia))
    | exact (AP 9 ltac:(unfold acallee_saved; lia))
    | exact (AP 21 ltac:(unfold acallee_saved; lia))
    | exact (AP 23 ltac:(unfold acallee_saved; lia))
    | exact (AP 24 ltac:(unfold acallee_saved; lia)) ]. }
  assert (KP : forall a, 0 <= a < 2 ^ 64 -> (a < alloc_ceiling \/ mf <= a) ->
    aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha Hlo. rewrite (Hfr3 a Ha) by (rewrite Hes; clear - Hlo Hmf0; lia). rewrite EV. reflexivity. }
  destruct (w4t_move g pos mf nm tk dp _ ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HJ0 Hfrs HC HK
    ltac:(intros a Ha Hlo _; exact (KP a Ha Hlo)) RK3
    ltac:(rewrite Efd3, ?j_wvb_fds; reflexivity) ltac:(rewrite Efs3, ?j_wvb_fs; reflexivity))
    as (HC3 & HK3 & MSZ & MGF & MVM).
  apply SRr_ret. right. unfold w4t_c6c, acut.
  exists ly2, S2, regs3, mem3, md3.
  split; [reflexivity|]. split; [exact HJ3|]. split; [exact Hfrs|]. split; [exact Hk|].
  split; [exact MLE|]. split; [exact MOK|]. split; [exact HC3|]. split; [exact HK3|].
  change (SFa g pos) with SF. change (Z.of_nat (length (SlotModel.n_stem (e_pl g)))) with ln.
  split.
  { rewrite Hv, Hcmp, EV. change ln with (Z.of_nat (length (SlotModel.n_stem (e_pl g)))).
    apply (w4t_cmp_iff g pos W2 mem2 Hwok); [unfold ln in Hge; clear - Hge; lia | exact Bnm | exact Bw4]. }
  split; [rewrite P18, (RKT 18%bv ltac:(w4t_in)); exact R18|].
  split; [rewrite P20; exact Q20|]. split; [rewrite P22; exact Q22|].
  split; [rewrite P25, (RKT 25%bv ltac:(w4t_in)); exact R25|].
  split; [rewrite P26, (RKT 26%bv ltac:(w4t_in)); exact R26|].
  split; [rewrite P27, (RKT 27%bv ltac:(w4t_in)); exact R27|].
  split; [apply MSZ; [unfold V_nm; clear; lia | unfold V_nm, N_nm; clear; lia | unfold N_nm; clear; lia | exact SHnm]|].
  split; [apply MSZ; [unfold V_dp; clear; lia | unfold V_dp, N_dp; clear; lia | unfold N_dp; clear; lia | exact SHdp]|].
  split; [apply MSZ; [unfold V_w4; clear; lia | unfold V_w4, N_w4; clear; lia | unfold N_w4; clear; lia | exact SHw4]|].
  split.
  { apply MGF; [unfold V_w4; clear; lia | | | exact Bw4];
    rewrite length_app, (LLVMFuzzerTestOneInput_seg_J_model.m1_W4_len _ Hwok); cbn [length];
    [unfold V_w4; clear; lia | right; unfold V_w4, V_nm, N_nm; clear; lia]. }
  split; [apply MVM; [unfold M_n2; clear; lia | unfold M_n2; clear; lia | exact Vn2]|].
  unfold bytes_at8 in *. apply (j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem3 _ _); [|exact Bnm].
  intros kk Hkk. rewrite length_map in Hkk. change (Z.of_nat (length (SlotModel.n_stem (e_pl g)))) with ln in Hkk.
  apply KP; [unfold V_nm; clear - Hkk HSF0 HSF1 C1 Hln; lia | left].
  unfold V_nm. clear - Hkk HSF1 Hln. lia.
Qed.

(* ---- +0x15f8 .. +0x16b8 or +0x1608: the wrapper's result ---------------------------------------------------- *)
Lemma w4t_L2 : forall (g : ectx) pos mf nm tk dp W2 c2, w4t_c6c g pos mf nm tk dp W2 c2 ->
  SlotModel.n_wok (e_pl g) = true ->
  SRr SEGS W2 c2 (fun W3 c3 => JC5 g pos mf nm tk dp W3 c3 \/ w4t_c7c g pos mf nm tk dp W3 c3).
Proof.
intros g pos mf nm tk dp W2 c2 Hstart Hwok.
pose proof (paj_run B LAWS) as RUN. pose proof (paj_run_to B LAWS) as RUNTO. pose proof (paj_branch (PI := PI)) as BR.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HK & Hiff & R18 & R20 & R22 & R25 & R26 & R27 & SHnm & SHdp & SHw4 & Bw4 & Vn2 & Bnm).
pose proof HC as (Rsp & Rs1 & _ & _ & _ & _ & _ & _ & _ & _ & V168 & _).
pose proof asan_consts as (C1 & _).
destruct (w4t_geo g pos mf _ ly2 S2 W2 regs2 mem2 md2 HJ Hfrs HC)
  as (EFa & HSF0 & HSF1 & HSF64 & HSFapp & Esh & Hsh0 & Hsh1 & Hsfsh & Hmf0 & Hmfb & Hmf32 & Hsp0al & H47 & HSTK').
assert (Hln : 0 <= Z.of_nat (length (SlotModel.n_stem (e_pl g))) <= 16)
  by (pose proof (LLVMFuzzerTestOneInput_seg_J_model.m1_stem_len (e_pl g)) as Hs; clear - Hs; lia).
pose proof HJ as HJ0.
set (sp0 := e_sp0 g) in *. set (SF := SFa g pos) in *.
set (ln := Z.of_nat (length (SlotModel.n_stem (e_pl g)))) in *.
remember (Eimg (Ereg regs2 [Z_to_bv 64 SHADOW_OFF])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs2 r)
  by (intros k' r Hk'; subst E; apply ew_Eimg_Ereg_nat; exact Hk').
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (ER : regs_ok E sr_atoms regs2) by (subst E; apply regs_ok_Eimg_Ereg).
assert (AGE : env_agree 32 (Ereg regs2 [Z_to_bv 64 SHADOW_OFF]) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 Hmfb H47 C1. lia. }
assert (U27 : bv_unsigned (ew E 27) = ln).
{ rewrite (EE 27%nat 27%bv eq_refl), R27. apply unsigned_lit_small. clear - Hln. lia. }
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x15f8 sr_atoms [w4t_mf] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x15f8)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold w4t_mf, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [clear - Hmf0 C1; lia|]. split; [clear - Hmfb H47; lia|]. split; [intros o Ho; clear - Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia
    | exact V168].
  - apply pairwise_disjoint_of_extents. unfold w4t_mf, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. split; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS (SLit SB) [] E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 (BASE + 0x15f8)) with (Z_to_bv 64 (BASE + 0x15f8)).
(* 0x81d6c beqz a0 *)
paj_run_tok RUN HS HJ SHOK Bspan;
[apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo w4t_mf]; apply Z.leb_le; reflexivity | apply awr_ok_nil] |].
rename ms into ms1. rename HFr into HFr1. clear HF HG.
assert (EQ1 : mrestrict (w_H W2) (ms_mem ms1) = mrestrict (w_H W2) mem2) by (w4t_ro HFr1).
clear HFr1.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* a0 = 0: the stem ends in the four digits; 0x81e28 reloads x6, on to the join 0x81e2c *)
  assert (Hend : SlotModel.n_ends_w4 (e_pl g) = true)
    by (apply Hiff; exact (w4t_br_eq0 E 10 (getr regs2 10) (EE 10%nat 10%bv eq_refl) Hc)).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x16b8;
  [apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo w4t_mf]; apply Z.leb_le; reflexivity | apply awr_ok_nil] |].
  assert (EQ2 : mrestrict (w_H W2) (ms_mem ms) = mrestrict (w_H W2) (ms_mem ms1)) by (w4t_ro HFr).
  clear HFr HF HG.
  assert (EV : aview SEGS (w_H W2) (ms_mem ms) = aview SEGS (w_H W2) mem2)
    by (unfold aview; rewrite EQ2, EQ1; reflexivity).
  assert (RK : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
    getr (ms_regs ms) r = getr regs2 r)
    by (eapply (regs_kept_of_st_ok_pi E _ (restrict (w_H W2) ms) regs2 _
          [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS AGE);
        vm_compute; reflexivity).
  w4t_reg HS (6%bv : bv 5) Q6. rewrite w4t_den_atom, E32 in Q6.
  pmkst HS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ =>
    destruct (w4t_move g pos mf nm tk dp _ ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) mdx HJ0 Hfrs HC HK
      ltac:(intros a _ _ _; rewrite EV; reflexivity)
      ltac:(intros r Hr; apply RK; w4t_sub Hr)
      ltac:(rewrite ?j_wvb_fds; reflexivity) ltac:(rewrite ?j_wvb_fs; reflexivity))
      as (HC3 & HK3 & MSZ & MGF & MVM)
  end.
  apply SRr_ret. left. unfold jc5, acut.
  exists ly2, S2, (ms_regs ms), (ms_mem ms). eexists.
  split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
  split; [exact MLE|]. split; [exact MOK|]. split; [exact HC3|]. split; [exact HK3|].
  change (SFa g pos) with SF.
  split; [exact Q6|].
  split; [rewrite (RK 22%bv ltac:(w4t_in)); exact R22|].
  split; [rewrite (RK 25%bv ltac:(w4t_in)); exact R25|].
  split; [rewrite (RK 26%bv ltac:(w4t_in)); exact R26|].
  split; [rewrite (LLVMFuzzerTestOneInput_seg_J_model.m1_n_ln_ends _ Hwok Hend), (RK 27%bv ltac:(w4t_in));
          exact R27|].
  split; [apply MSZ; [unfold V_nm; clear; lia | unfold V_nm, N_nm; clear; lia | unfold N_nm; clear; lia | exact SHnm]|].
  split; [apply MSZ; [unfold V_dp; clear; lia | unfold V_dp, N_dp; clear; lia | unfold N_dp; clear; lia | exact SHdp]|].
  split; [apply MVM; [unfold M_n2; clear; lia | unfold M_n2; clear; lia | exact Vn2]|].
  destruct (LLVMFuzzerTestOneInput_seg_J_model.m1_ends_w4_cases (e_pl g)) as [[_ Ex] | [Hf _]];
  [| rewrite Hend in Hf; discriminate Hf].
  rewrite Ex. unfold bytes_at8 in *. rewrite EQ2, EQ1. exact Bnm.
- (* a0 <> 0: the dash path; 0x81d74 reloads x6, the trap ln = 32 at 0x81d78 *)
  assert (Hend : SlotModel.n_ends_w4 (e_pl g) = false).
  { destruct (SlotModel.n_ends_w4 (e_pl g)) eqn:Ee; [|reflexivity]. exfalso.
    apply (w4t_br_ne0 E 10 (getr regs2 10) (EE 10%nat 10%bv eq_refl) Hc). apply Hiff. first [exact Ee | reflexivity]. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan;
  [apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo w4t_mf]; apply Z.leb_le; reflexivity | apply awr_ok_nil] |].
  rename ms into ms2. rename HFr into HFr2. clear HF HG.
  assert (EQ2 : mrestrict (w_H W2) (ms_mem ms2) = mrestrict (w_H W2) (ms_mem ms1)) by (w4t_ro HFr2).
  clear HFr2.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  1: { exfalso. rewrite branch_eq_U, U_SOff, U27, Z.add_0_r, U_SLit in Hc.
       rewrite (zcanon_id ln) in Hc by (unfold M64; clear - Hln; lia). change (zcanon 32) with 32 in Hc.
       apply Z.eqb_eq in Hc. clear - Hc Hln. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x1608;
  [apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo w4t_mf]; apply Z.leb_le; reflexivity | apply awr_ok_nil] |].
  assert (EQ3 : mrestrict (w_H W2) (ms_mem ms) = mrestrict (w_H W2) (ms_mem ms2)) by (w4t_ro HFr).
  clear HFr HF HG.
  assert (EV : aview SEGS (w_H W2) (ms_mem ms) = aview SEGS (w_H W2) mem2)
    by (unfold aview; rewrite EQ3, EQ2, EQ1; reflexivity).
  assert (RK : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv;
    27%bv] -> getr (ms_regs ms) r = getr regs2 r)
    by (eapply (regs_kept_of_st_ok_pi E _ (restrict (w_H W2) ms) regs2 _
          [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS AGE);
        vm_compute; reflexivity).
  w4t_reg HS (6%bv : bv 5) Q6. rewrite w4t_den_atom, E32 in Q6.
  pmkst HS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ =>
    destruct (w4t_move g pos mf nm tk dp _ ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) mdx HJ0 Hfrs HC HK
      ltac:(intros a _ _ _; rewrite EV; reflexivity)
      ltac:(intros r Hr; apply RK; w4t_sub Hr)
      ltac:(rewrite ?j_wvb_fds; reflexivity) ltac:(rewrite ?j_wvb_fs; reflexivity))
      as (HC3 & HK3 & MSZ & MGF & MVM)
  end.
  apply SRr_ret. right. unfold w4t_c7c, acut.
  exists ly2, S2, (ms_regs ms), (ms_mem ms). eexists.
  split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
  split; [exact MLE|]. split; [exact MOK|]. split; [exact HC3|]. split; [exact HK3|].
  change (SFa g pos) with SF. change (Z.of_nat (length (SlotModel.n_stem (e_pl g)))) with ln.
  split; [exact Q6|].
  split; [rewrite (RK 18%bv ltac:(w4t_in)); exact R18|].
  split; [rewrite (RK 20%bv ltac:(w4t_in)); exact R20|].
  split; [rewrite (RK 22%bv ltac:(w4t_in)); exact R22|].
  split; [rewrite (RK 25%bv ltac:(w4t_in)); exact R25|].
  split; [rewrite (RK 26%bv ltac:(w4t_in)); exact R26|].
  split; [rewrite (RK 27%bv ltac:(w4t_in)); exact R27|].
  split; [exact Hend|].
  split; [apply MSZ; [unfold V_nm; clear; lia | unfold V_nm, N_nm; clear; lia | unfold N_nm; clear; lia | exact SHnm]|].
  split; [apply MSZ; [unfold V_dp; clear; lia | unfold V_dp, N_dp; clear; lia | unfold N_dp; clear; lia | exact SHdp]|].
  split; [apply MSZ; [unfold V_w4; clear; lia | unfold V_w4, N_w4; clear; lia | unfold N_w4; clear; lia | exact SHw4]|].
  split.
  { apply MGF; [unfold V_w4; clear; lia | | | exact Bw4];
    rewrite length_app, (LLVMFuzzerTestOneInput_seg_J_model.m1_W4_len _ Hwok); cbn [length];
    [unfold V_w4; clear; lia | right; unfold V_w4, V_nm, N_nm; clear; lia]. }
  split; [apply MVM; [unfold M_n2; clear; lia | unfold M_n2; clear; lia | exact Vn2]|].
  unfold bytes_at8 in *. rewrite EQ3, EQ2, EQ1. exact Bnm.
Qed.

(* ---- +0x1608 .. +0x1644 (0x81d7c .. 0x81db8): the dash, then the digit copy to +0x16b8 ------------------- *)
Lemma w4t_L3 : forall (g : ectx) pos mf nm tk dp W2 c2, w4t_c7c g pos mf nm tk dp W2 c2 ->
  SlotModel.n_wok (e_pl g) = true -> SRr SEGS W2 c2 (JC5 g pos mf nm tk dp).
Proof.
intros g pos mf nm tk dp W2 c2 Hstart Hwok.
pose proof (SRr_run_pi_AJ B LAWS) as RUNP. pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof (paj_branch (PI := PI)) as BR.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HK & R6 & R18 & R20 & R22 & R25 & R26 & R27 & Hend & SHnm & SHdp & SHw4 & Bw4 & Vn2 & Bnm).
pose proof asan_consts as (C1 & _).
destruct (w4t_geo g pos mf _ ly2 S2 W2 regs2 mem2 md2 HJ Hfrs HC)
  as (EFa & HSF0 & HSF1 & HSF64 & HSFapp & Esh & Hsh0 & Hsh1 & Hsfsh & Hmf0 & Hmfb & Hmf32 & Hsp0al & H47 & HSTK').
assert (Hln : 0 <= Z.of_nat (length (SlotModel.n_stem (e_pl g))) <= 16)
  by (pose proof (LLVMFuzzerTestOneInput_seg_J_model.m1_stem_len (e_pl g)) as Hs; clear - Hs; lia).
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m1_W4_len _ Hwok) as HW4l.
(* w4[0], a digit, not NUL *)
assert (Vb0 : val_mem SEGS (rd W2 mem2) (SFa g pos + V_w4 + 0) 1
  (bv_unsigned (nth 0 (SlotModel.n_W4 (e_pl g)) (RcIdentModel.zb 0))) /\
  0 <= bv_unsigned (nth 0 (SlotModel.n_W4 (e_pl g)) (RcIdentModel.zb 0)) < 256).
{ unfold bytes_at8, garr8 in Bw4.
  pose proof (Bw4 0%nat ltac:(rewrite length_map, length_app, HW4l; cbn [length]; lia)) as Hb.
  rewrite w4t_nth_map, app_nth1 in Hb by (rewrite HW4l; lia). exact Hb. }
destruct Vb0 as [Vb0 Hb0r].
assert (Hb0 : bv_unsigned (nth 0 (SlotModel.n_W4 (e_pl g)) (RcIdentModel.zb 0)) <> 0).
{ apply (LLVMFuzzerTestOneInput_seg_J_model.m1_W4_nz _ Hwok). apply nth_In. rewrite HW4l. lia. }
pose proof HJ as HJ0.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
set (sp0 := e_sp0 g) in *. set (SF := SFa g pos) in *.
set (ln := Z.of_nat (length (SlotModel.n_stem (e_pl g)))) in *.
set (b0 := bv_unsigned (nth 0 (SlotModel.n_W4 (e_pl g)) (RcIdentModel.zb 0))) in *.
remember (Eimg (Ereg regs2 [Z_to_bv 64 (SHADOW_OFF + (SF + V_nm + ln) / 8); Z_to_bv 64 b0])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs2 r)
  by (intros k' r Hk'; subst E; apply ew_Eimg_Ereg_nat; exact Hk').
assert (E32 : ew E 32 = Z_to_bv 64 (SHADOW_OFF + (SF + V_nm + ln) / 8))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (ER : regs_ok E sr_atoms regs2) by (subst E; apply regs_ok_Eimg_Ereg).
assert (AGE : env_agree 32 (Ereg regs2 [Z_to_bv 64 (SHADOW_OFF + (SF + V_nm + ln) / 8); Z_to_bv 64 b0]) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (U20 : bv_unsigned (ew E 20) = SF + V_nm + ln).
{ rewrite (EE 20%nat 20%bv eq_refl), R20. apply unsigned_lit_small. unfold V_nm. clear - HSF0 HSF1 C1 Hln. lia. }
assert (U6 : bv_unsigned (ew E 6) = SHADOW_OFF).
{ rewrite (EE 6%nat 6%bv eq_refl), R6. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (U18 : bv_unsigned (ew E 18) = SF + V_w4).
{ rewrite (EE 18%nat 18%bv eq_refl), R18. apply unsigned_lit_small. unfold V_w4. clear - HSF0 HSF1 C1. lia. }
assert (U25 : bv_unsigned (ew E 25) = SF + V_nm).
{ rewrite (EE 25%nat 25%bv eq_refl), R25. apply unsigned_lit_small. unfold V_nm. clear - HSF0 HSF1 C1. lia. }
assert (U27 : bv_unsigned (ew E 27) = ln).
{ rewrite (EE 27%nat 27%bv eq_refl), R27. apply unsigned_lit_small. clear - Hln. lia. }
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF + (SF + V_nm + ln) / 8).
{ rewrite E32. apply unsigned_lit_small. unfold SHADOW_OFF, V_nm. clear - HSF0 HSF1 C1 Hln. lia. }
assert (U33 : bv_unsigned (ew E 33) = b0) by (rewrite E33; apply unsigned_lit_small; clear - Hb0r; lia).
assert (E22 : ew E 22 = Z_to_bv 64 (Z.lnot (SF + V_nm))) by (rewrite (EE 22%nat 22%bv eq_refl), R22; reflexivity).
(* the shadow byte of exp_nm[ln]: exp_nm's shadow is clear *)
assert (Hcell : aview SEGS (w_H W2) mem2 (SHADOW_OFF + (SF + V_nm + ln) / 8) = Some 0).
{ unfold sh_zero, zero_shadow in SHnm. specialize (SHnm (ln / 8) ltac:(unfold N_nm; clear - Hln; lia)).
  unfold shadow_of_addr in SHnm.
  replace (SHADOW_OFF + (SF + V_nm + ln) / 8) with (SHADOW_OFF + (SF + V_nm) / 8 + ln / 8)
    by (unfold V_nm; clear - HSF64 Hln HSF0; lia).
  exact SHnm. }
assert (HS : st_ok_pi SEGS VAL E ss_w4t3
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1608)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_w4t3. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold w4t_dash, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U20.
      split; [unfold V_nm; clear - HSF0 Hln; lia|]. split; [unfold V_nm; clear - HSF1 C1 Hln; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SF + V_nm + ln + o) HJ _)).
      right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 4) with 1024.
      unfold V_nm. clear - Ho Hln. lia.
    + unfold w4t_shc, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
      split; [unfold SHADOW_OFF, V_nm; clear - HSF0 Hln; lia|]. split; [unfold SHADOW_OFF, V_nm; clear - HSF1 C1 Hln; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (SHADOW_OFF + (SF + V_nm + ln) / 8) 0 1 (SLit 0) 0); [reflexivity | lia | lia |].
      rewrite Z.add_0_r. apply w4t_vm1. exact Hcell.
    + unfold w4t_w40, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U18.
      split; [unfold V_w4; clear - HSF0; lia|]. split; [unfold V_w4; clear - HSF1 C1; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (SF + V_w4) 0 1 (SOff 33 0) b0);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 1)) with 256; clear - Hb0r; lia | lia | exact Vb0].
  - apply pairwise_disjoint_of_extents. unfold w4t_dash, w4t_shc, w4t_w40, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U20, U32, U18.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite Esh in Hsfsh, Hsh0, Hsh1.
    clear - HSF0 HSF1 HSF64 Hsfsh Hsh0 Hsh1 Hln C1. unfold V_nm, V_w4, SHADOW_OFF in *.
    repeat split; lia.
  - unfold facts_ok, w4t_alias. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; [exact I|]]. split; [|exact I].
    apply U_inj. rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
    rewrite !U_SOff, U20, U6, U32, !Z.add_0_r.
    change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold zcanon, M64. clear - HSF0 HSF1 C1 Hln. unfold SHADOW_OFF, V_nm in *.
    rewrite !Z.mod_small by lia. lia. }
unfold cfg_at. change (w64 (BASE + 0x1608)) with (Z_to_bv 64 (BASE + 0x1608)).
(* 0x81d7c: the trap x22 < ln *)
paj_run_sh RUNP HS HJ.
{ intros a (rr & Hrr & Hra). cbn in Hrr.
  destruct Hrr as [<- | [<- | [<- | []]]]; cbn in Hra.
  - rewrite U20 in Hra. right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 4) with 1024.
    clear - Hra Hln. unfold V_nm in *. lia.
  - clear - Hra. lia.
  - clear - Hra. lia. }
rename ms into ms1. rename HFr into HFr1. clear HF HG.
psrr_branch_pi RUNP BR HS.
1: { exfalso. rewrite branch_ltu_U, (w4t_U_atom_w E 22 _ E22) in Hc.
     rewrite w4t_lnot_mod in Hc by (unfold V_nm; clear - HSF0 HSF1 C1; lia).
     rewrite U_SOff, U27, Z.add_0_r in Hc. rewrite (zcanon_id ln) in Hc by (unfold M64; clear - Hln; lia).
     apply Z.ltb_lt in Hc. unfold V_nm in Hc. clear - Hc Hln HSF1 C1. lia. }
clear Hc.
(* the shadow test (atom 32, an alias, no token), the dash, w4[0] and the test w4[0] = 0 at 0x81da0 *)
paj_run_sh RUNP HS HJ.
{ intros a (rr & Hrr & Hra). cbn in Hrr.
  destruct Hrr as [<- | [<- | [<- | []]]]; cbn in Hra.
  - rewrite U20 in Hra. right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 4) with 1024.
    clear - Hra Hln. unfold V_nm in *. lia.
  - clear - Hra. lia.
  - clear - Hra. lia. }
rename ms into ms2. rename HFr into HFr2. clear HF HG.
psrr_branch_pi RUNP BR HS.
1: { exfalso. rewrite branch_eq_U, (w4t_U_zext8 E 33 b0 U33 Hb0r), U_SLit in Hc. change (zcanon 0) with 0 in Hc.
     apply Z.eqb_eq in Hc. exact (Hb0 Hc). }
clear Hc.
(* the loop's registers, to its head 0x81db8 *)
paj_run_to_sh RUNTOP HS HJ 0x1644.
{ intros a (rr & Hrr & Hra). cbn in Hrr.
  destruct Hrr as [<- | [<- | [<- | []]]]; cbn in Hra.
  - rewrite U20 in Hra. right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 4) with 1024.
    clear - Hra Hln. unfold V_nm in *. lia.
  - clear - Hra. lia.
  - clear - Hra. lia. }
clear HF HG.
(* what the three runs kept: every byte but exp_nm[ln] *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> a <> SF + V_nm + ln ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hne.
  rewrite (kept_of_frame E _ (w_H W2) (ms_mem ms2) (ms_mem ms) (fun x => x = SF + V_nm + ln) HFr);
  [ | w4t_win U20 | exact Ha | exact Hne].
  rewrite (kept_of_frame E _ (w_H W2) (ms_mem ms1) (ms_mem ms2) (fun x => x = SF + V_nm + ln) HFr2);
  [ | w4t_win U20 | exact Ha | exact Hne].
  apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms1) (fun x => x = SF + V_nm + ln) HFr1);
  [w4t_win U20 | exact Ha | exact Hne]. }
clear HFr HFr1 HFr2.
assert (VD : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_nm + ln + 0) 1 45)
  by (w4t_ck HS 0%nat 0 (SF + V_nm + ln) U20; [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia]).
rewrite Z.add_0_r in VD.
assert (RK : forall r, In r [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv;
  26%bv] -> getr (ms_regs ms) r = getr regs2 r)
  by (eapply (regs_kept_of_st_ok_pi E _ (restrict (w_H W2) ms) regs2 _
        [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv] HS AGE);
      vm_compute; reflexivity).
w4t_reg HS (10%bv : bv 5) Q10. w4t_reg HS (11%bv : bv 5) Q11. w4t_reg HS (12%bv : bv 5) Q12. w4t_reg HS (13%bv : bv 5) Q13.
w4t_reg HS (14%bv : bv 5) Q14. w4t_reg HS (15%bv : bv 5) Q15. w4t_reg HS (27%bv : bv 5) Q27.
rewrite (w4t_den_lit E 0) in Q10 by (clear; lia).
rewrite (w4t_den_off E 20 1 (SF + V_nm + ln) (SF + V_nm + (ln + 1)) U20) in Q11
  by (unfold V_nm; clear - HSF0 HSF1 C1 Hln; lia).
rewrite (w4t_den_add E 25 27 1 0 (SF + V_nm) ln (SF + V_nm + (ln + 1)) U25 U27) in Q12
  by (unfold V_nm; clear - HSF0 HSF1 C1 Hln; lia).
rewrite (w4t_den_off E 18 1 (SF + V_w4) (SF + V_w4 + 1) U18) in Q13 by (unfold V_w4; clear - HSF0 HSF1 C1; lia).
rewrite (w4t_den_lit E 18446744073709551615), w4t_wm1 in Q14 by (clear; lia).
rewrite (w4t_den_zext8 E 33 b0 U33 Hb0r) in Q15.
rewrite (w4t_den_off E 27 1 ln (ln + 1) U27) in Q27 by (clear - Hln; lia).
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ =>
  destruct (w4t_move g pos mf nm tk dp _ ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) mdx HJ0 Hfrs HC HK
    ltac:(intros a Ha _ Hn; apply KEEP; [exact Ha | intros Ea; apply Hn; rewrite Ea; unfold V_nm, N_nm;
          clear - Hln; lia])
    ltac:(intros r Hr; apply RK; w4t_sub Hr)
    ltac:(rewrite ?j_wvb_fds; reflexivity) ltac:(rewrite ?j_wvb_fs; reflexivity))
    as (HC3 & HK3 & MSZ & MGF & MVM)
end.
(* the loop, from its head with i = 0, ld = ln + 1 and the stem and the dash in exp_nm *)
eapply SRr_mono.
{ apply (W4C LAWS g pos mf nm tk dp (ln + 1) 0 (SlotModel.n_stem (e_pl g) ++ [SlotModel.dash]) W2).
  unfold acut. exists ly2, S2, (ms_regs ms), (ms_mem ms). eexists.
  split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
  split; [exact MLE|]. split; [exact MOK|]. split; [exact HC3|].
  change (SFa g pos) with SF.
  split; [exact HK3|].
  split; [rewrite (RK 6%bv ltac:(w4t_in)); exact R6|].
  split; [rewrite (RK 18%bv ltac:(w4t_in)); exact R18|].
  split; [rewrite (RK 25%bv ltac:(w4t_in)); exact R25|].
  split; [rewrite (RK 26%bv ltac:(w4t_in)); exact R26|].
  split; [exact Q27|].
  split; [rewrite (RK 22%bv ltac:(w4t_in)); exact R22|].
  split; [apply MSZ; [unfold V_nm; clear; lia | unfold V_nm, N_nm; clear; lia | unfold N_nm; clear; lia | exact SHnm]|].
  split; [apply MSZ; [unfold V_dp; clear; lia | unfold V_dp, N_dp; clear; lia | unfold N_dp; clear; lia | exact SHdp]|].
  split; [apply MSZ; [unfold V_w4; clear; lia | unfold V_w4, N_w4; clear; lia | unfold N_w4; clear; lia | exact SHw4]|].
  split.
  { apply MGF; [unfold V_w4; clear; lia | | | exact Bw4];
    rewrite length_app, HW4l; cbn [length];
    [unfold V_w4; clear; lia | right; unfold V_w4, V_nm, N_nm; clear; lia]. }
  split; [exact Hwok|].
  split; [exact HW4l|].
  split; [exact (LLVMFuzzerTestOneInput_seg_J_model.m1_W4_nonul _ Hwok)|].
  split; [clear - Hln; lia|].
  split; [unfold N_nm; clear - Hln; lia|].
  split; [clear; lia|].
  split; [rewrite length_app; cbn [length]; change ln with (Z.of_nat (length (SlotModel.n_stem (e_pl g)))); lia|].
  split; [apply MVM; [unfold M_n2; clear; lia | unfold M_n2; clear; lia | exact Vn2]|].
  split.
  { cbn [Z.to_nat firstn]. rewrite app_nil_r. unfold bytes_at8. rewrite map_app. cbn [map].
    apply w4t_garr8_snoc.
    - unfold bytes_at8 in Bnm. apply (j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) _ _); [|exact Bnm].
      intros kk Hkk. rewrite length_map in Hkk. change (Z.of_nat (length (SlotModel.n_stem (e_pl g)))) with ln in Hkk.
      apply KEEP; [unfold V_nm; clear - Hkk HSF0 HSF1 C1 Hln; lia | clear - Hkk; lia].
    - rewrite length_map. exact VD.
    - pose proof (bv_unsigned_in_range 8 SlotModel.dash) as Hd. change (bv_modulus 8) with 256 in Hd. exact Hd. }
  split; [exact Q10|]. split; [exact Q11|]. split; [exact Q12|]. split; [exact Q13|]. split; [exact Q14|].
  exact Q15. }
(* the loop's exit is jc5 *)
cbv beta. intros W3 c3 _ Hx.
destruct Hx as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hfrs3 & Hk3 & MLE3 & MOK3 & HC3' & HP3).
destruct HP3 as (HK3' & X6 & X18 & X25 & X26 & X27 & X22 & Z1 & Z2 & V3 & B3).
unfold jc5, acut. exists ly3, S3, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact Hfrs3|]. split; [exact Hk3|].
split; [exact MLE3|]. split; [exact MOK3|]. split; [exact HC3'|]. split; [exact HK3'|].
split; [exact X6|]. split; [exact X22|]. split; [exact X25|]. split; [exact X26|].
split; [rewrite (LLVMFuzzerTestOneInput_seg_J_model.m1_n_ln_dash _ Hwok Hend), X27; f_equal;
        change ln with (Z.of_nat (length (SlotModel.n_stem (e_pl g)))); lia|].
split; [exact Z1|]. split; [exact Z2|]. split; [exact V3|].
destruct (LLVMFuzzerTestOneInput_seg_J_model.m1_ends_w4_cases (e_pl g)) as [[Hf _] | [_ Ex]];
[rewrite Hend in Hf; discriminate Hf|].
rewrite Ex. rewrite <- app_assoc in B3. exact B3.
Qed.

(* ---- the piece ------------------------------------------------------------------------------------------- *)
Lemma w4t_main : forall (g : ectx) pos mf nm tk dp W2 c2, JC4 g pos mf nm tk dp W2 c2 ->
  SlotModel.n_wok (e_pl g) = true -> SRr SEGS W2 c2 (JC5 g pos mf nm tk dp).
Proof.
intros g pos mf nm tk dp W2 c2 Hstart Hwok.
eapply SRr_bind; [exact (w4t_L1 g pos mf nm tk dp W2 c2 Hstart Hwok)|].
cbv beta. intros W3 c3 _ [H7 | H6].
- exact (w4t_L3 g pos mf nm tk dp W3 c3 H7 Hwok).
- eapply SRr_bind; [exact (w4t_L2 g pos mf nm tk dp W3 c3 H6 Hwok)|].
  cbv beta. intros W4 c4 _ [H5 | H7].
  + apply SRr_ret. exact H5.
  + exact (w4t_L3 g pos mf nm tk dp W4 c4 H7 Hwok).
Qed.
End d.

Lemma j_w4tail : j_w4tail_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS.
Proof.
unfold j_w4tail_stmt. intros LAWS ABCMP HSTK W4C.
exact (w4t_main LAWS ABCMP HSTK W4C).
Qed.
Check (j_w4tail : j_w4tail_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).

End c.
End b.
End a.
