(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC1i.v, with its module paths, module names and numbers changed; 643 of its 708 lines of code are new or changed and 637 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0s YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f YC1h YC44 YC88 YK0w YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma le_byte_bytes : forall (bs : list byte) j, (j < length bs)%nat ->
  YO0f.le_byte (bytes_le_to_Z bs) (length bs) j = bv_unsigned (nth j bs (Z_to_bv 8 0)).
Proof.
intros bs j Hj. unfold YO0f.le_byte.
pose proof (YK11.bytes_le_to_Z_bound bs) as Hb. pose proof (YK11.bytes_le_to_Z_nonneg bs) as Hn.
rewrite (Z.mod_small (bytes_le_to_Z bs) (2 ^ (8 * Z.of_nat (length bs)))) by (split; [exact Hn | exact Hb]).
rewrite Z.shiftr_div_pow2 by lia.
rewrite <- (zb_of_bytes bs j Hj). reflexivity.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma val_mem4_garr8 : forall (m : word -> option byte) b (L : list byte) k,
  garr8 SEGS m b (map bv_unsigned L) -> 0 <= k -> k + 4 <= Z.of_nat (length L) ->
  val_mem SEGS m (b + k) 4 (u_at L k 4).
Proof.
intros m b L k HG Hk Hkl j Hj. unfold u_at, sub.
set (bs := firstn 4 (skipn (Z.to_nat k) L)).
assert (Hlen : length bs = 4%nat) by (subst bs; rewrite length_firstn, length_skipn; lia).
replace (YO0f.le_byte (bytes_le_to_Z bs) 4 j) with (YO0f.le_byte (bytes_le_to_Z bs) (length bs) j) by (rewrite Hlen; reflexivity).
rewrite le_byte_bytes by lia.
assert (Hn : nth j bs (Z_to_bv 8 0) = nth (Z.to_nat k + j) L (Z_to_bv 8 0)).
{ subst bs. rewrite nth_firstn. replace (j <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_skipn. reflexivity. }
rewrite Hn.
assert (Hj2 : (Z.to_nat k + j < length (map bv_unsigned L))%nat) by (rewrite length_map; lia).
destruct (HG _ Hj2) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)).
replace (b + k + Z.of_nat j) with (b + Z.of_nat (Z.to_nat k + j) + Z.of_nat 0) by lia.
rewrite Hv. do 2 f_equal.
rewrite (nth_indep (map bv_unsigned L) 0 (bv_unsigned (Z_to_bv 8 0)) Hj2). rewrite map_nth.
apply le_byte_1_0. pose proof (bv_unsigned_in_range _ (nth (Z.to_nat k + j) L (Z_to_bv 8 0))) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.
Lemma u_at_n : forall T, length T = 400%nat -> tbl_T1 T -> u_at T 384 4 = n_of T.
Proof.
intros T LT T1. unfold tbl_T1, n_of, s32_at in *.
assert (R : 0 <= u_at T 384 4 < 2 ^ 32).
{ unfold u_at. pose proof (bytes_le_to_Z_bound (sub T 384 4)) as Hb. pose proof (bytes_le_to_Z_nonneg (sub T 384 4)) as Hn.
  assert (Hl : length (sub T 384 4) = 4%nat) by (unfold sub; rewrite length_firstn, length_skipn; lia).
  rewrite Hl in Hb. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hb. lia. }
set (u := u_at T 384 4) in *. unfold bv_swrap, bv_wrap in *.
change (bv_half_modulus 32) with (2 ^ 31) in *. change (bv_modulus 32) with (2 ^ 32) in *.
destruct (Z_lt_ge_dec u (2 ^ 31)).
- rewrite (Z.mod_small (u + 2 ^ 31)) in * by lia. lia.
- replace (u + 2 ^ 31) with ((u - 2 ^ 31) + 1 * 2 ^ 32) in T1 by lia.
  rewrite Z.mod_add, Z.mod_small in T1 by lia. lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Definition TFIND_ENTRY_STK : Z := 80 + 2 * ESTACK.
Definition tfind_entry_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md (T P : list byte)
  : world SEGS -> config -> Prop :=
  apost_base (fx := fq) SEGS B TFIND_ENTRY_STK [] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' _ => Permutation (ablocks B ly' S') (ablocks B ly S) /\ (exists r, getr regs' 10 = Z_to_bv 64 r /\ find_res T P r) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TFIND_ENTRY_STK <= a < spZ regs) ->
         aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a)).
Definition tfind_entry_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (t p : Z) (T P : list byte),
  afn_pre SEGS B TFIND_ENTRY_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 t -> getr regs 11 = w64 p ->
  0 < t -> t mod 8 = 0 -> t + 400 <= 2 ^ 63 -> 0 < p -> p + 6 <= 2 ^ 63 ->
  length T = 400%nat -> garr8 SEGS (mrestrict (w_H W) mem) t (map bv_unsigned T) ->
  length P = 6%nat -> garr8 SEGS (mrestrict (w_H W) mem) p (map bv_unsigned P) ->
  amem_range t 400 -> amem_range p 6 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t 400 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) t 400 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p 6 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) p 6 ->
  (t + 400 <= spZ regs - TFIND_ENTRY_STK \/ spZ regs <= t) ->
  off_img t 400 ->
  (p + 6 <= spZ regs - TFIND_ENTRY_STK \/ spZ regs <= p) ->
  tbl_T1 T ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_find_entry) regs mem md) (tfind_entry_post fq regs ly S W mem md T P).
Section w. Context {fx : YK11.FPState}.
Definition SB : Z := 0x7fff8000.
Definition FBx : sv := SOff 33 0.
Definition FBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition fe_regions : smem :=
  [ stack_region 80; got_regionP; bcell_regionP 33;
    YP09.mkRegion (Some 10%nat) 0 400 0 0 [YP09.mkChunk 384 (CVal 4 (SOff 32 0))] ].
Definition fe_facts : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 1 (2^47 - 401) 3); (32%nat, mkAF 0 8 0); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_fe : sstate := mkSS AF_both3_find_entry sr_atoms fe_regions None fe_facts.
Definition fe_SH : list shent := [ mkSHE 10 0 400 ].
Definition fe_extra (n : Z) : list word := map (Z_to_bv 64) [n; SB].
Definition akept (W : world SEGS) (m0 m1 : word -> option byte) (lo hi : Z) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a.
Lemma akept_refl : forall W m lo hi, akept W m m lo hi.
Proof. intros W m lo hi a _ _. reflexivity. Qed.
Lemma akept_trans : forall W m0 m1 m2 lo hi, akept W m0 m1 lo hi -> akept W m1 m2 lo hi -> akept W m0 m2 lo hi.
Proof. intros W m0 m1 m2 lo hi K1 K2 a Ha Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha Hn). Qed.
Lemma akept_widen : forall W m0 m1 lo hi lo' hi', akept W m0 m1 lo hi -> lo' <= lo -> hi <= hi' -> akept W m0 m1 lo' hi'.
Proof. intros W m0 m1 lo hi lo' hi' K Hl Hh a Ha Hn. apply K; [exact Ha | lia]. Qed.
Lemma akept_frame : forall E rs W m m' lo hi,
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r \/
     (lo <= base_val E (YP09.r_base r) + YP09.r_wlo r /\ base_val E (YP09.r_base r) + YP09.r_whi r <= hi)) ->
  akept W m m' lo hi.
Proof.
intros E rs W m m' lo hi HF Hr a Ha Hn. rewrite !(aview_mbyte SEGS). unfold YP09.mbyte.
rewrite (frame_of_outside E rs _ _ lo hi (Z_to_bv 64 a) HF Hr); [reflexivity|].
rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma branch_ge_U' : forall E a b, 0 <= U E a < 2 ^ 63 -> 0 <= U E b < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (U E a <? U E b).
Proof. intros E a b Ha Hb. rewrite YO0c.branch_ge. unfold U in *. rewrite !YO0b.s64_small by lia. reflexivity. Qed.
Lemma ra_kept_sub : forall (W : world SEGS) m0 m1 lo hi x n a' n',
  akept W m0 m1 lo hi -> range_addressable (aview SEGS (w_H W) m0) SHADOW_OFF x n ->
  0 <= x -> x + n <= 2 ^ 47 -> SHADOW_OFF + 2 ^ 45 <= lo -> x <= a' -> a' + n' <= x + n ->
  range_addressable (aview SEGS (w_H W) m1) SHADOW_OFF a' n'.
Proof.
intros W m0 m1 lo hi x n a' n' K H Hx Hn Hlo H1 H2 y Hy.
destruct (H y ltac:(lia)) as (s & Hs & Hok). exists s. split; [|exact Hok].
assert (D0 : 0 <= y / 8) by (apply Z.div_pos; lia).
assert (D1 : y / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
rewrite K; [exact Hs | unfold shadow_of_addr, SHADOW_OFF in *; lia | unfold shadow_of_addr, SHADOW_OFF in *; lia].
Qed.
Lemma shv_kept_sub : forall (W : world SEGS) m0 m1 lo hi x n a' n',
  akept W m0 m1 lo hi -> shadow_hull_vis (aview SEGS (w_H W) m0) x n ->
  0 <= x -> x + n <= 2 ^ 47 -> SHADOW_OFF + 2 ^ 45 <= lo -> x <= a' -> a' + n' <= x + n -> 0 < n' ->
  shadow_hull_vis (aview SEGS (w_H W) m1) a' n'.
Proof.
intros W m0 m1 lo hi x n a' n' K H Hx Hn Hlo H1 H2 H3 s Hs. unfold shadow_addr in *.
assert (M1 : (SHADOW_OFF + x / 8) / 8 * 8 <= (SHADOW_OFF + a' / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
assert (M2 : (SHADOW_OFF + (a' + n' - 1) / 8) / 8 * 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
assert (B1 : (SHADOW_OFF + (x + n - 1) / 8) / 8 * 8 <= SHADOW_OFF + (x + n - 1) / 8) by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
assert (B2 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (B3 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (B4 : 0 <= (SHADOW_OFF + x / 8) / 8 * 8) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos; unfold SHADOW_OFF; lia | lia]).
rewrite K; [apply H; unfold shadow_addr; lia | unfold SHADOW_OFF in *; lia | unfold SHADOW_OFF in *; lia].
Qed.
Lemma view_garr8 : forall (H : word -> bool) m b (L : list byte) j, garr8 SEGS (mrestrict H m) b (map bv_unsigned L) ->
  (j < length L)%nat -> aview SEGS H m (b + Z.of_nat j) = Some (bv_unsigned (nth j L (Z_to_bv 8 0))).
Proof.
intros H m b L j HG Hj. assert (Hj2 : (j < length (map bv_unsigned L))%nat) by (rewrite length_map; exact Hj).
destruct (HG j Hj2) as [Hv Hr]. rewrite (aview_of_val_mem1 SEGS _ _ _ _ Hv Hr). f_equal.
rewrite (nth_indep (map bv_unsigned L) 0 (bv_unsigned (Z_to_bv 8 0)) Hj2). apply map_nth.
Qed.
Lemma mac_iff : forall (W : world SEGS) (m : word -> option byte) t p (T P : list byte) i,
  garr8 SEGS (mrestrict (w_H W) m) t (map bv_unsigned T) -> length T = 400%nat ->
  garr8 SEGS (mrestrict (w_H W) m) p (map bv_unsigned P) -> length P = 6%nat -> 0 <= i < 8 ->
  ((forall k, 0 <= k < 6 -> aview SEGS (w_H W) m (t + 48 * i + k) = aview SEGS (w_H W) m (p + k)) <-> mac_of T i = P).
Proof.
intros W m t p T P i GT LT GP LP Hi.
assert (VT : forall k, 0 <= k < 6 -> aview SEGS (w_H W) m (t + 48 * i + k) = Some (bv_unsigned (nth (Z.to_nat (48 * i + k)) T (Z_to_bv 8 0)))).
{ intros k Hk. rewrite <- (view_garr8 _ m t T (Z.to_nat (48 * i + k)) GT) by lia. f_equal. lia. }
assert (VP : forall k, 0 <= k < 6 -> aview SEGS (w_H W) m (p + k) = Some (bv_unsigned (nth (Z.to_nat k) P (Z_to_bv 8 0)))).
{ intros k Hk. rewrite <- (view_garr8 _ m p P (Z.to_nat k) GP) by lia. f_equal. lia. }
assert (NM : forall k, (k < 6)%nat -> nth k (mac_of T i) (Z_to_bv 8 0) = nth (Z.to_nat (48 * i + Z.of_nat k)) T (Z_to_bv 8 0)).
{ intros k Hk. unfold mac_of, sub. rewrite nth_firstn. replace (k <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_skipn. f_equal. lia. }
assert (LM : length (mac_of T i) = 6%nat) by (unfold mac_of, sub; rewrite length_firstn, length_skipn; lia).
split.
- intros X. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [lia|]. intros k Hk. rewrite LM in Hk.
  specialize (X (Z.of_nat k) ltac:(lia)). rewrite VT, VP in X by lia. injection X as X.
  rewrite NM by exact Hk. apply bv_eq. rewrite X. f_equal. f_equal. lia.
- intros X k Hk. rewrite VT, VP by exact Hk. f_equal. f_equal.
  rewrite <- X. replace (Z.to_nat (48 * i + k)) with (Z.to_nat (48 * i + Z.of_nat (Z.to_nat k))) by (f_equal; lia).
  rewrite <- NM by lia. reflexivity.
Qed.
Lemma alu64_not : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_XOR (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small x) by lia. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite lxor_allones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma alu64_pos_mask : forall z, 1 <= z <= 8 ->
  alu64 ALU_AND (alu64 ALU_SUB (Z_to_bv 64 0) (alu64 ALU_SLT (Z_to_bv 64 0) (Z_to_bv 64 z))) (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
intros z Hz. assert (Hc : z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8) by lia.
destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; apply bv_eq; vm_compute; reflexivity.
Qed.
Definition FE_CLOB : list (bv 5) := [1; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 28; 29; 30; 31]%bv.
Definition A_FE_LOOP : Z := AF_both3_find_entry + 0x80.
Definition A_FE_EXIT : Z := AF_both3_find_entry + 0xb8.
Ltac rs_stack Usp :=
  intros r Hin; unfold ss_fe, fe_regions, stack_region, got_regionP, bcell_regionP in Hin; simpl in Hin;
  repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_whi YP09.r_wlo YP09.r_base base_val]; first [left; lia | right; rewrite Usp; lia] |]);
  try destruct Hin.
Ltac mk_kept K W lo hi Usp :=
  lazymatch goal with HFr : frame_of ?E ?rs (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    assert (K : akept W m0 m1 lo hi) by (apply (akept_frame E rs W m0 m1 lo hi HFr); rs_stack Usp);
    clear HFr; repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Definition FE_LSTK : Z := 2 * ESTACK.
Definition FE_KEPT : list (bv 5) := [2; 3; 4; 24; 25; 26; 27]%bv.
Definition fres_from (T P : list byte) (i res : Z) : Prop :=
  (res = -1 /\ forall j, i <= j < n_of T -> mac_of T j <> P) \/
  (i <= res < n_of T /\ mac_of T res = P /\ forall j, i <= j < res -> mac_of T j <> P).
Definition FLBx : sv := SLit SB.
Definition fl_facts : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF 1 (2^47 - 49) 0); (19%nat, mkAF 0 7 0); (20%nat, mkAF 0 336 0);
    (21%nat, mkAF (2^64 - 2^47) (2^64 - 2) 0); (22%nat, mkAF 1 8 0) ] [] [].
Definition ss_fl : sstate :=
  mkSS A_FE_LOOP (sr_set (sr_set sr_atoms 18%bv (SLit 18446744073709551615)) 23%bv (SLit 384)) [] None fl_facts.
Lemma fe_clob_kept : forall r : bv 5, reg_in r FE_CLOB = false -> r = 0%bv \/ In r FE_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
Lemma fe_loop : forall (k : nat) (i : Z) W (regs : bvmap 5 word) memc mdc sp1 mem0 md0 lyc Sc t p (T P : list byte),
  Z.of_nat k = n_of T - i -> 0 <= i < n_of T -> n_of T <= 8 ->
  ajournal SEGS B FE_LSTK sp1 [] lyc Sc W mem0 md0 [] lyc Sc W memc mdc 0 ->
  akept W mem0 memc (sp1 - FE_LSTK) sp1 ->
  0 < t -> length T = 400%nat -> garr8 SEGS (mrestrict (w_H W) mem0) t (map bv_unsigned T) ->
  0 < p -> length P = 6%nat -> garr8 SEGS (mrestrict (w_H W) mem0) p (map bv_unsigned P) ->
  amem_range t 400 -> amem_range p 6 ->
  range_addressable (aview SEGS (w_H W) mem0) SHADOW_OFF t 400 -> shadow_hull_vis (aview SEGS (w_H W) mem0) t 400 ->
  range_addressable (aview SEGS (w_H W) mem0) SHADOW_OFF p 6 -> shadow_hull_vis (aview SEGS (w_H W) mem0) p 6 ->
  (t + 400 <= sp1 - FE_LSTK \/ sp1 <= t) -> (p + 6 <= sp1 - FE_LSTK \/ sp1 <= p) ->
  spZ regs = sp1 -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = w64 (t + 48 * i) -> getr regs 9 = w64 p -> getr regs 18 = w64 18446744073709551615 ->
  getr regs 19 = w64 i -> getr regs 20 = w64 (48 * i) -> getr regs 21 = w64 (2 ^ 64 - 1 - t) ->
  getr regs 22 = w64 (n_of T - i) -> getr regs 23 = w64 384 ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_FE_LOOP)) memc (seg_rom SEGS)) mdc)
  (fun W' c' => W' = W /\ exists regs' mem' md',
     c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_FE_EXIT)) mem' (seg_rom SEGS)) md' /\
     ajournal SEGS B FE_LSTK sp1 [] lyc Sc W mem0 md0 [] lyc Sc W mem' md' 0 /\
     akept W mem0 mem' (sp1 - FE_LSTK) sp1 /\
     (forall r, In r FE_KEPT -> getr regs' r = getr regs r) /\
     exists res, getr regs' 18 = Z_to_bv 64 res /\ fres_from T P i res).
Proof.
induction k as [|k IH]; intros i W regs memc mdc sp1 mem0 md0 lyc Sc t p T P Hk Hi Hn8 HJ HK0 Ht0 LT GT Hp0 LP GP MRt MRp RAt SHt RAp SHp OWt OWp
  Hsp Hgp Htp H8 H9 H18 H19 H20 H21 H22 H23; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HLS : FE_LSTK = 8192) by reflexivity.
remember (Eimg (Ereg regs [])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = Z_to_bv 64 (t + 48 * i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact H8).
assert (E9 : ew E 9 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = Z_to_bv 64 i) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (E20 : ew E 20 = Z_to_bv 64 (48 * i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E21 : ew E 21 = Z_to_bv 64 (2 ^ 64 - 1 - t)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E22 : ew E 22 = Z_to_bv 64 (n_of T - i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (Usp : bv_unsigned (ew E 2) = sp1) by (rewrite E2; exact Hsp).
assert (HS : st_ok_pi SEGS VAL E ss_fl (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_FE_LOOP)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_fl. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H18] | intros X; discriminate X | cbn [sv_denot]; exact H23].
  - vm_compute. reflexivity.
  - constructor.
  - cbn [pairwise_disjoint]. exact I.
  - split; [|split; [exact I | exact I]].
    cbn [fl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E8, E19, E20, E21, E22, !unsigned_lit_small by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in MRt; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 HLS Hstk0 Hal16 Hi Hn8 Ht0 MRt. clear. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. intros.
    repeat match goal with |- _ /\ _ => split end; lia. }
clear HE.
assert (SHOK : sh_ok SEGS FLBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (Hshb : SHADOW_OFF + 2 ^ 45 <= sp1 - FE_LSTK) by (rewrite HLS; unfold SHADOW_OFF; lia).
assert (MRt' : 0 <= t /\ t + 400 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in MRt; lia).
assert (MRp' : 0 <= p /\ p + 6 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in MRp; lia).
paj_run_tok RUN HS HJ SHOK FBspan.
{ awr_ok_tac. }
mk_kept KR W (sp1 - FE_LSTK) sp1 Usp.
pose proof (akept_trans _ _ _ _ _ _ HK0 KR) as Kc. clear KR.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
eapply SRr_bind.
{ eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA AS___interceptor_trampoline_bcmp) (ABCMP fx) W _ _ FE_LSTK sp1 [] lyc Sc W mem0 md0 [] lyc Sc _ 0
    (t + 48 * i) p 6 0 (Z_to_bv 64 (BASE + 13812)) HJ).
  - rewrite Ra0, E8. reflexivity.
  - rewrite Ra1, E9. reflexivity.
  - exact Ra2.
  - lia. - lia. - lia. - lia. - lia.
  - unfold spZ. rewrite Rsp, Usp. lia.
  - reflexivity. - lia. - rewrite HLS. unfold ESTACK. lia.
  - rewrite Rgp, E3. exact Hgp.
  - rewrite Rtp, E4. exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split.
    + rewrite (Kc a ltac:(lia) ltac:(lia)). 
      destruct (GT (Z.to_nat (a - t)) ltac:(rewrite length_map; lia)) as [Hv1 Hr1].
      replace (t + Z.of_nat (Z.to_nat (a - t))) with a in Hv1 by lia.
      rewrite (aview_of_val_mem1 SEGS _ _ _ _ Hv1 Hr1). discriminate.
    + unfold spZ, ESTACK. rewrite Rsp, Usp. lia.
  - intros a Ha. split.
    + rewrite (Kc a ltac:(lia) ltac:(lia)).
      destruct (GP (Z.to_nat (a - p)) ltac:(rewrite length_map; lia)) as [Hv1 Hr1].
      replace (p + Z.of_nat (Z.to_nat (a - p))) with a in Hv1 by lia.
      rewrite (aview_of_val_mem1 SEGS _ _ _ _ Hv1 Hr1). discriminate.
    + unfold spZ, ESTACK. rewrite Rsp, Usp. lia.
  - intros a Ha. unfold ESTACK. lia.
  - intros a Ha. unfold ESTACK. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
  - exact MRp.
  - apply (ra_kept_sub W mem0 _ (sp1 - FE_LSTK) sp1 t 400); [exact Kc | exact RAt | lia | lia | exact Hshb | lia | lia].
  - intros _. apply (shv_kept_sub W mem0 _ (sp1 - FE_LSTK) sp1 t 400); [exact Kc | exact SHt | lia | lia | exact Hshb | lia | lia | lia].
  - apply (ra_kept_sub W mem0 _ (sp1 - FE_LSTK) sp1 p 6); [exact Kc | exact RAp | lia | lia | exact Hshb | lia | lia].
  - intros _. apply (shv_kept_sub W mem0 _ (sp1 - FE_LSTK) sp1 p 6); [exact Kc | exact SHp | lia | lia | exact Hshb | lia | lia | lia]. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpr2).
assert (Kc2 : akept W mem0 mem2 (sp1 - FE_LSTK) sp1).
{ intros a Ha Hn. rewrite (Hfr a Ha ltac:(unfold ESTACK in *; lia)). exact (Kc a Ha Hn). }
assert (Hmac : (v = w64 0) <-> mac_of T i = P).
{ rewrite Hcmp. rewrite <- (mac_iff W mem0 t p T P i GT LT GP LP ltac:(lia)).
  split; intros X kk Hkk.
  - rewrite <- (Kc (t + 48 * i + kk) ltac:(lia) ltac:(lia)), <- (Kc (p + kk) ltac:(lia) ltac:(lia)). apply X. exact Hkk.
  - rewrite (Kc (t + 48 * i + kk) ltac:(lia) ltac:(lia)), (Kc (p + kk) ltac:(lia) ltac:(lia)). apply X. exact Hkk. }
clear Hcmp Kc.
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc _ 40 _) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [assumption | cbv; lia]).
assert (OLD : forall n, (n < 40)%nat -> ew Eb n = ew E n) by (intros n Hn; rewrite HEb, ew_havoc_old by lia; reflexivity).
assert (HAEb : env_agree 32 (Ereg regs []) Eb) by (rewrite HEb; env_agree_chain HAE).
assert (Ea0 : ew Eb 44 = getr regs2 10) by (rewrite HEb; reflexivity).
clear HEb.
assert (SHOK2 : sh_ok SEGS FLBx [] Eb (mrestrict (w_H W) mem2)) by constructor. clear SHOK. rename SHOK2 into SHOK.
assert (U44 : U Eb (SOff 44 0) = bv_unsigned v).
{ apply U_atom; [rewrite Ea0, Hv; symmetry; apply Z_to_bv_bv_unsigned | pose proof (bv_unsigned_in_range 64 v) as Q; change (bv_modulus 64) with (2 ^ 64) in Q; lia]. }
assert (E19b : ew Eb 19 = Z_to_bv 64 i) by (rewrite OLD by lia; exact E19).
assert (E8b : ew Eb 8 = Z_to_bv 64 (t + 48 * i)) by (rewrite OLD by lia; exact E8).
assert (E20b : ew Eb 20 = Z_to_bv 64 (48 * i)) by (rewrite OLD by lia; exact E20).
assert (E22b : ew Eb 22 = Z_to_bv 64 (n_of T - i)) by (rewrite OLD by lia; exact E22).
psrr_branch_tok RUN BR HS SHOK FBspan.
- rewrite branch_eq_U, U44, U_lit in Hc by lia.
  assert (Hv0 : v = w64 0) by (apply Z.eqb_eq in Hc; apply bv_eq; rewrite Hc; reflexivity).
  pose proof (proj1 Hmac Hv0) as Hmi.
  paj_run_to_tok RUNTO HS HJ2 SHOK FBspan A_FE_EXIT.
  { awr_ok_tac. }
  mk_kept K3 W (sp1 - FE_LSTK) sp1 Usp.
  prreg HS (18%bv : bv 5) R18.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] FE_KEPT HS HAEb ltac:(vm_compute; reflexivity)) as HKr.
  cbn [ms_regs restrict] in HKr.
  pmkst HS.
  apply SRr_ret. split; [reflexivity|].
  lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists rg, m, d end.
  split; [reflexivity|]. split; [exact HJ2|]. split; [exact (akept_trans _ _ _ _ _ _ Kc2 K3)|].
  split; [intros r Hr; exact (HKr r Hr)|].
  exists i. split; [rewrite R18, E19b; reflexivity|].
  right. split; [lia|]. split; [exact Hmi|]. intros j Hj. lia.
- rewrite branch_eq_U, U44, U_lit in Hc by lia.
  assert (Hmn : mac_of T i <> P).
  { intros X. apply (proj2 Hmac) in X. rewrite X in Hc. cbv in Hc. discriminate Hc. }
  paj_run_tok RUN HS HJ2 SHOK FBspan.
  { awr_ok_tac. }
  mk_kept K3 W (sp1 - FE_LSTK) sp1 Usp.
  clear Hc.
  psrr_branch_tok RUN BR HS SHOK FBspan.
  + rewrite branch_ne_U, (U_atom_off Eb 22 (n_of T - i) (-1) E22b), U_lit in Hc by lia.
    assert (Hlt : i + 1 < n_of T) by (destruct (Z.eqb_spec (n_of T - i + -1) 0); [discriminate | lia]).
    paj_run_to_tok RUNTO HS HJ2 SHOK FBspan A_FE_LOOP.
    { awr_ok_tac. }
    mk_kept K4 W (sp1 - FE_LSTK) sp1 Usp.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] FE_KEPT HS HAEb ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    prreg HS (8%bv : bv 5) N8. prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19.
    prreg HS (20%bv : bv 5) N20. prreg HS (21%bv : bv 5) N21. prreg HS (22%bv : bv 5) N22. prreg HS (23%bv : bv 5) N23.
    pmkst HS.
    eapply SRr_mono.
    { eapply (IH (i + 1) W _ _ _ sp1 mem0 md0 lyc Sc t p T P);
      [ lia | lia | lia | exact HJ2 | exact (akept_trans _ _ _ _ _ _ (akept_trans _ _ _ _ _ _ Kc2 K3) K4)
      | exact Ht0 | exact LT | exact GT | exact Hp0 | exact LP | exact GP | exact MRt | exact MRp
      | exact RAt | exact SHt | exact RAp | exact SHp | exact OWt | exact OWp
      | unfold spZ; cbn [ms_regs]; rewrite (HKr 2%bv ltac:(cbv; tauto)); exact Hsp
      | cbn [ms_regs]; rewrite (HKr 3%bv ltac:(cbv; tauto)); exact Hgp
      | cbn [ms_regs]; rewrite (HKr 4%bv ltac:(cbv; tauto)); exact Htp
      | cbn [ms_regs]; rewrite N8, E8b, unsigned_lit_small by lia; unfold w64; f_equal; lia
      | cbn [ms_regs]; rewrite N9, OLD, E9 by lia; reflexivity
      | cbn [ms_regs]; rewrite N18; reflexivity
      | cbn [ms_regs]; rewrite N19, E19b, unsigned_lit_small by lia; reflexivity
      | cbn [ms_regs]; rewrite N20, E20b, unsigned_lit_small by lia; unfold w64; f_equal; lia
      | cbn [ms_regs]; rewrite N21, OLD, E21 by lia; reflexivity
      | cbn [ms_regs]; rewrite N22, E22b, unsigned_lit_small by lia; unfold w64; f_equal; lia
      | cbn [ms_regs]; rewrite N23; reflexivity ]. }
    cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ4 & HK4 & HKr3 & res & R3 & Hres).
    split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ4|]. split; [exact HK4|].
    split; [intros r Hr; rewrite (HKr3 r Hr); cbn [ms_regs]; exact (HKr r Hr)|].
    exists res. split; [exact R3|].
    destruct Hres as [(Hr1 & Hr2) | (Hr1 & Hr2 & Hr3)].
    * left. split; [exact Hr1|]. intros j Hj. destruct (Z.eq_dec j i) as [->|Hji]; [exact Hmn | apply Hr2; lia].
    * right. split; [lia|]. split; [exact Hr2|]. intros j Hj. destruct (Z.eq_dec j i) as [->|Hji]; [exact Hmn | apply Hr3; lia].
  + rewrite branch_ne_U, (U_atom_off Eb 22 (n_of T - i) (-1) E22b), U_lit in Hc by lia.
    assert (Heq : i + 1 = n_of T) by (destruct (Z.eqb_spec (n_of T - i + -1) 0); [lia | discriminate]).
    paj_run_to_tok RUNTO HS HJ2 SHOK FBspan A_FE_EXIT.
    { awr_ok_tac. }
    mk_kept K4 W (sp1 - FE_LSTK) sp1 Usp.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] FE_KEPT HS HAEb ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    prreg HS (18%bv : bv 5) N18.
    pmkst HS.
    apply SRr_ret. split; [reflexivity|].
    lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists rg, m, d end.
    split; [reflexivity|]. split; [exact HJ2|]. split; [exact (akept_trans _ _ _ _ _ _ (akept_trans _ _ _ _ _ _ Kc2 K3) K4)|].
    split; [intros r Hr; exact (HKr r Hr)|].
    exists (-1). split; [rewrite N18; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
    left. split; [reflexivity|]. intros j Hj. replace j with i by lia. exact Hmn.
Qed.
Lemma fe_entry : forall ly S W (regs : bvmap 5 word) mem md ch (t : Z) (T : list byte),
  afn_pre SEGS B TFIND_ENTRY_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  getr regs 10 = w64 t ->
  0 < t -> t mod 8 = 0 -> t + 400 <= 2 ^ 63 ->
  length T = 400%nat -> garr8 SEGS (mrestrict (w_H W) mem) t (map bv_unsigned T) ->
  amem_range t 400 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t 400 ->
  (t + 400 <= spZ regs - TFIND_ENTRY_STK \/ spZ regs <= t) ->
  off_img t 400 -> tbl_T1 T ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (fe_extra (n_of T)))) ss_fe
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_find_entry)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS FBx fe_SH (Eimg (Ereg regs (fe_extra (n_of T)))) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch t T HPRE H10 Ht0 Ht8 Ht63 LT GT MRt RAt OWt OIt T1.
assert (Esp : spZ (regupd regs 8 (Z_to_bv 64 0)) = spZ regs) by (unfold spZ; rewrite getr_other by reg_neq_tac; reflexivity).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite Esp in Hstk, Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TFIND_ENTRY_STK = 8272) by reflexivity.
pose proof (u_at_n T LT T1) as Hu. pose proof T1 as Hn. unfold tbl_T1 in Hn.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in OIt.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (fe_extra (n_of T)))).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (fe_extra (n_of T))) k)
by (intros k Hk; subst E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 (n_of T)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_fe. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold fe_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 FBx SB);
      [cbn [sv_denot FBx]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat t E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ t 384 4 (SOff 32 0) (n_of T));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      change (N.to_nat 4) with 4%nat. rewrite <- Hu. apply val_mem4_garr8; [exact GT | lia | rewrite LT; lia].
  + apply pairwise_disjoint_of_extents. unfold fe_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat t E10) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 WS Hstk0 HcellR HgcD HgotR OWt OIt Ht0 Ht63. clear. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP. intros.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [fe_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16 Hn Ht0 Ht8 Ht63 MRt. clear. unfold SB, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. intros.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, fe_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E FBx 10 t 400 t 0 400 RAt).
  + unfold U, FBx. cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + revert MRt. clear. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF. intros. lia.
Qed.
Theorem fe_walk : forall ly S W (regs : bvmap 5 word) mem md ch (t p : Z) (T P : list byte),
  afn_pre SEGS B TFIND_ENTRY_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 t -> getr regs 11 = w64 p ->
  0 < t -> t mod 8 = 0 -> t + 400 <= 2 ^ 63 -> 0 < p -> p + 6 <= 2 ^ 63 ->
  length T = 400%nat -> garr8 SEGS (mrestrict (w_H W) mem) t (map bv_unsigned T) ->
  length P = 6%nat -> garr8 SEGS (mrestrict (w_H W) mem) p (map bv_unsigned P) ->
  amem_range t 400 -> amem_range p 6 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t 400 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) t 400 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p 6 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) p 6 ->
  (t + 400 <= spZ regs - TFIND_ENTRY_STK \/ spZ regs <= t) ->
  off_img t 400 ->
  (p + 6 <= spZ regs - TFIND_ENTRY_STK \/ spZ regs <= p) ->
  tbl_T1 T ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_both3_find_entry) regs mem md) (tfind_entry_post fx regs ly S W mem md T P).
Proof.
intros ly S W regs mem md ch t p T P HPRE HRO H10 H11 Ht0 Ht8 Ht63 Hp0 Hp63 LT GT LP GP MRt MRp RAt SHt RAp SHp OWt OIt OWp T1.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (fe_entry ly S W regs mem md ch t T HPRE H10 Ht0 Ht8 Ht63 LT GT MRt RAt OWt OIt T1) as [HS SHOK].
assert (Esp : spZ (regupd regs 8 (Z_to_bv 64 0)) = spZ regs) by (unfold spZ; rewrite getr_other by reg_neq_tac; reflexivity).
pose proof (ajournal_init SEGS B TFIND_ENTRY_STK [] ly S W _ mem md ch HPRE) as HJ. rewrite Esp in HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
unfold raZ in Hra4. rewrite getr_other in Hra, Hra4, Hgp, Htp by reg_neq_tac. fold (raZ regs) in Hra4.
rewrite Esp in Hstk, Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TFIND_ENTRY_STK = 8272) by reflexivity.
pose proof (u_at_n T LT T1) as Hu. pose proof T1 as Hn. unfold tbl_T1 in Hn.
remember (Eimg (Ereg regs (fe_extra (n_of T)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (fe_extra (n_of T))) k)
by (intros k Hk; subst E; apply Eimg_low; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 (n_of T)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (fe_extra (n_of T))) E) by (split; [intros k Hk; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at. change (w64 (BASE + AF_both3_find_entry)) with (Z_to_bv 64 (BASE + AF_both3_find_entry)).
paj_run_tok RUN HS HJ SHOK FBspan.
{ awr_ok_tac; try exact Usp. }
mk_kept K1 W (spZ regs - 80) (spZ regs) Usp.
psrr_branch_tok RUN BR HS SHOK FBspan.
- rewrite branch_ge_U' in Hc by (rewrite ?U_lit, ?(U_atom E 32 (n_of T) E32) by lia; lia).
  rewrite U_lit, (U_atom E 32 (n_of T) E32) in Hc by lia.
  assert (Hn0 : n_of T = 0) by (destruct (Z.ltb_spec 0 (n_of T)); [discriminate | lia]).
  paj_run_tok RUN HS HJ SHOK FBspan.
  { awr_ok_tac; try exact Usp. }
  mk_kept K2 W (spZ regs - 80) (spZ regs) Usp.
  prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  unfold tfind_entry_post. apply apost_base_same_fx.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
  split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
  split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (fe_extra (n_of T)) HS); [exact HAE | vm_compute; reflexivity]|].
  split; [apply Permutation_refl|].
  split.
  + exists (-1). split; [cbn [ms_regs]; rewrite R10; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
    left. split; [reflexivity|]. intros j Hj. lia.
  + intros a Ha Hout. cbn [ms_mem].
    apply (akept_widen W mem _ (spZ regs - 80) (spZ regs) (spZ regs - TFIND_ENTRY_STK) (spZ regs) (akept_trans _ _ _ _ _ _ K1 K2)); [lia | lia | exact Ha | exact Hout].
- rewrite branch_ge_U' in Hc by (rewrite ?U_lit, ?(U_atom E 32 (n_of T) E32) by lia; lia).
  rewrite U_lit, (U_atom E 32 (n_of T) E32) in Hc by lia.
  assert (Hn1 : 0 < n_of T) by (destruct (Z.ltb_spec 0 (n_of T)); [lia | discriminate]).
  paj_run_to_tok RUNTO HS HJ SHOK FBspan A_FE_LOOP.
  { awr_ok_tac; try exact Usp. }
  mk_kept K3 W (spZ regs - 80) (spZ regs) Usp.
  prreg HS (2%bv : bv 5) L2. prreg HS (8%bv : bv 5) L8. prreg HS (9%bv : bv 5) L9. prreg HS (18%bv : bv 5) L18.
  prreg HS (19%bv : bv 5) L19. prreg HS (20%bv : bv 5) L20. prreg HS (21%bv : bv 5) L21. prreg HS (22%bv : bv 5) L22. prreg HS (23%bv : bv 5) L23.
  prreg HS (3%bv : bv 5) L3. prreg HS (4%bv : bv 5) L4.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) => rename msX into msL end.
  assert (Q2 : spZ (ms_regs msL) = spZ regs - 80) by (unfold spZ at 1; rewrite L2, Usp, unsigned_lit_small by lia; reflexivity).
  pose proof (akept_trans _ _ _ _ _ _ K1 K3) as K13. clear K1 K3.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdX) _ =>
    pose proof (ajournal_sub_init SEGS B _ _ _ _ _ _ _ _ _ _ _ W (ms_mem msL) mdX _ FE_LSTK (spZ regs - 80) [] (-80)
      HJ ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(unfold FE_LSTK, ESTACK; lia) ltac:(rewrite WS; unfold FE_LSTK, ESTACK; lia)) as HJL
  end.
  assert (Hshb : SHADOW_OFF + 2 ^ 45 <= spZ regs - 80) by (rewrite WS in Hslo; unfold SHADOW_OFF; lia).
  assert (MRt' : 0 <= t /\ t + 400 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in MRt; lia).
  assert (MRp' : 0 <= p /\ p + 6 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in MRp; lia).
  pmkst HS.
  eapply SRr_bind.
  { eapply (fe_loop (Z.to_nat (n_of T)) 0 W _ _ _ (spZ regs - 80) (ms_mem msL) _ ly S t p T P).
    - rewrite Z2Nat.id by lia. lia.
    - lia.
    - lia.
    - exact HJL.
    - apply akept_refl.
    - exact Ht0.
    - exact LT.
    - apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem (ms_mem msL) t _); [intros a Ha; rewrite length_map, LT in Ha; apply K13; lia | exact GT].
    - exact Hp0.
    - exact LP.
    - apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem (ms_mem msL) p _); [intros a Ha; rewrite length_map, LP in Ha; apply K13; lia | exact GP].
    - exact MRt.
    - exact MRp.
    - apply (ra_kept_sub W mem _ (spZ regs - 80) (spZ regs) t 400); [exact K13 | exact RAt | lia | lia | lia | lia | lia].
    - apply (shv_kept_sub W mem _ (spZ regs - 80) (spZ regs) t 400); [exact K13 | exact SHt | lia | lia | lia | lia | lia | lia].
    - apply (ra_kept_sub W mem _ (spZ regs - 80) (spZ regs) p 6); [exact K13 | exact RAp | lia | lia | lia | lia | lia].
    - apply (shv_kept_sub W mem _ (spZ regs - 80) (spZ regs) p 6); [exact K13 | exact SHp | lia | lia | lia | lia | lia | lia].
    - unfold FE_LSTK, ESTACK. lia.
    - unfold FE_LSTK, ESTACK. lia.
    - exact Q2.
    - rewrite L3, E3. exact Hgp.
    - rewrite L4, E4. exact Htp.
    - rewrite L8, E10. unfold w64. f_equal. lia.
    - rewrite L9, E11. reflexivity.
    - rewrite L18. reflexivity.
    - rewrite L19. reflexivity.
    - rewrite L20. reflexivity.
    - rewrite L21, E10, alu64_not by lia. reflexivity.
    - rewrite L22, E32, alu64_pos_mask by lia. unfold w64. f_equal. lia.
    - rewrite L23. reflexivity. }
  cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJL3 & KL & HKr3 & res & R18 & Hres).
  pose proof (ajournal_sub SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msL) _ 0 FE_LSTK (spZ regs - 80) [] [] ly S W mem3 md3 0
    HJ HJL3 ltac:(rewrite WS; unfold FE_LSTK, ESTACK; lia) ltac:(lia) ltac:(intros a (rg & [] & _))) as HJ3.
  cbn [app] in HJ3. change (0 + 0) with 0 in HJ3.
  pose proof (proj1 HJ) as HAR1. pose proof (proj1 HJ3) as HAR3.
  destruct (al_const _ _ LAWS _ _ _ _ _ HAR1) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
  destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell3 & _ & Kgot3 & _). rewrite HBgot, HBcell in Kgot3. rewrite HBcell in Kcell3.
  assert (KA : akept W mem mem3 (spZ regs - TFIND_ENTRY_STK) (spZ regs)).
  { apply (akept_trans _ _ (ms_mem msL)).
    - apply (akept_widen _ _ _ _ _ _ _ K13); lia.
    - apply (akept_widen _ _ _ _ _ _ _ KL); unfold FE_LSTK, ESTACK; lia. }
  jafter_stretch_pi HS 40%nat regs3 (mrestrict (w_H W) mem3) FE_CLOB A_FE_EXIT HS2.
  match type of HS2 with ?P -> ?Q -> _ => assert (HP : P); [|assert (HQ : Q); [|specialize (HS2 HP HQ); clear HP HQ]] end.
  { intros r0 Hr0. cbn [ms_regs restrict]. destruct (fe_clob_kept r0 Hr0) as [-> | Hin]; [rewrite !getr_zero; reflexivity | exact (HKr3 r0 Hin)]. }
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
    - eapply (region_kept_stack_sub SEGS B E); [exact HJL3 | exact HJ3 | exact Usp | lia | rewrite WS; lia | lia | lia | lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
      [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot3) | lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
      [exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell3) | lia].
    - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite E10, unsigned_lit_small by lia; intros a Ha; [|lia].
      apply (mbyte_of_aview SEGS). apply KL; [lia | unfold FE_LSTK, ESTACK; lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 40 _) as Et eqn:HEt in HS.
  assert (HEIt : img_env VAL A_LIM Et) by (rewrite HEt; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDt : forall k, (k < 40)%nat -> ew Et k = ew E k) by (intros k Hk; rewrite HEt; apply ew_havoc_old; exact Hk).
  assert (HAEt : env_agree 32 (Ereg regs (fe_extra (n_of T))) Et) by (rewrite HEt; apply env_agree_havoc_ge; [lia | exact HAE]).
  assert (E54 : ew Et 54 = getr regs3 18) by (rewrite HEt; reflexivity).
  clear HEt.
  assert (Usp3 : bv_unsigned (ew Et 2) = spZ regs) by (rewrite OLDt by lia; exact Usp).
  assert (SHOK3 : sh_ok SEGS FBx fe_SH Et (mrestrict (w_H W) mem3)).
  { unfold sh_ok, fe_SH. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W) mem3 Et FBx 10 t 400 t 0 400).
    - apply (ra_kept_sub W mem _ (spZ regs - TFIND_ENTRY_STK) (spZ regs) t 400); [exact KA | exact RAt | lia | lia | rewrite WS; unfold SHADOW_OFF; lia | lia | lia].
    - unfold U, FBx. cbn [sv_denot]. rewrite OLDt, E33 by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    - unfold U. cbn [sv_denot]. rewrite OLDt, E10 by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    - lia.
    - lia.
    - revert MRt. clear. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF. intros. lia. }
  clear SHOK.
  paj_run_tok RUN HS HJ3 SHOK3 FBspan.
  { awr_ok_tac; try exact Usp3. }
  mk_kept K5 W (spZ regs - 80) (spZ regs) Usp3.
  prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  unfold tfind_entry_post. apply apost_base_same_fx.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
  split; [cbn [ms_regs]; rewrite R1, OLDt, E1, Hra by lia; reflexivity|].
  split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ Et _ _ regs (fe_extra (n_of T)) HS); [exact HAEt | vm_compute; reflexivity]|].
  split; [apply Permutation_refl|].
  split.
  + exists res. split; [cbn [ms_regs]; rewrite R10, E54; exact R18|].
    unfold fres_from in Hres. unfold find_res. exact Hres.
  + intros a Ha Hout. cbn [ms_mem].
    apply (akept_trans _ _ mem3 _ _ _ KA (akept_widen W mem3 _ (spZ regs - 80) (spZ regs) (spZ regs - TFIND_ENTRY_STK) (spZ regs) K5 ltac:(lia) ltac:(lia))); [exact Ha | exact Hout].
Qed.
End w.
Theorem pb_find_entry : tfind_entry_spec.
Proof.
intros fq ly S W regs mem md ch t p T P HPRE HRO H10 H11 Ht0 Ht8 Ht63 Hp0 Hp63 LT GT LP GP MRt MRp RAt SHt RAp SHp OWt OIt OWp T1.
exact (@fe_walk fq ly S W regs mem md ch t p T P HPRE HRO H10 H11 Ht0 Ht8 Ht63 Hp0 Hp63 LT GT LP GP MRt MRp RAt SHt RAp SHp OWt OIt OWp T1).
Qed.
End h.
End f.
End d.
