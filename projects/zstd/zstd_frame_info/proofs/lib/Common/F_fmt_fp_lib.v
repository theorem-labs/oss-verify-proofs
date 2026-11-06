(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFW1_lemmas.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
Ltac showregs := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x2 := getreg 2%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "sp=" x2.

(* [comment removed for export] *)
Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. Local Ltac2 Set LiaHints.tbl := fun () => "0010=38557618280.2000004S2Hz".
rewrite unsigned_lit by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. Local Ltac2 Set LiaHints.tbl := fun () => "0010=38557618280.2000004S2Hz".
rewrite unsigned_lit by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac fix_litstore :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | _ => idtac
  end.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac zstep0 := zs.

(* [comment removed for export] *)
Ltac name_cb n H := match type of H with context [CB n ?l] => let j := fresh "jk" in set (j := l) in H; clearbody j end.

(* [comment removed for export] *)
Lemma shl52_land64 : forall f, (0 <= f)%Z -> Z.land (Z.shiftl f 52) 18446744073709551615 = (4503599627370496 * (f mod 4096))%Z.
Proof.
  intros f Hf. Local Ltac2 Set LiaHints.tbl := fun () => "0020=18926749090.245081153976.2000001002SS".
rewrite land_W64, Z.shiftl_mul_pow2 by lia. change (2^64)%Z with (4503599627370496 * 4096)%Z.
  change (2^52)%Z with 4503599627370496%Z. rewrite Z.mul_comm, Z.mul_mod_distr_l by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma land_bit11 : forall f, Z.land f 2048 = (2048 * ((f / 2048) mod 2))%Z.
Proof. intros. change 2048%Z with (2^11)%Z. Local Ltac2 Set LiaHints.tbl := fun () => "0010<6163401992.1000001S".
rewrite zb_land_pow2 by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma land_bit0 : forall f, Z.land f 1 = (f mod 2)%Z.
Proof. intros. change 1%Z with (2^1 - 1)%Z. Local Ltac2 Set LiaHints.tbl := fun () => "0010<6757322728.1000001S".
rewrite zb_land_mask by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma hi64_range : forall x, (0 <= hi64 x < 2^64)%Z.
Proof. intros. unfold hi64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. Local Ltac2 Set LiaHints.tbl := fun () => "0010=38955485601.1000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma lo64_range : forall x, (0 <= lo64 x < 2^64)%Z.
Proof. intros. unfold lo64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. Local Ltac2 Set LiaHints.tbl := fun () => "0010=38955485601.1000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma signbitl_range : forall x, (0 <= signbitl x <= 1)%Z.
Proof.
  intros. unfold signbitl. pose proof (hi64_range x). Local Ltac2 Set LiaHints.tbl := fun () => "0040=27055962958.232975921830.258246998422.268214771681.2000003004007008S1HSS1HS".
rewrite Z.shiftr_div_pow2 by lia.
  split; [apply Z.div_pos; lia|]. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma fpclassifyl_range : forall x, (0 <= fpclassifyl x <= 4)%Z.
Proof. intros. unfold fpclassifyl. repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. Qed.

(* [comment removed for export] *)
Lemma sx32_lit : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, swrap32_eq.
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Ltac unwrapK K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K.
Ltac mlia := OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].

Lemma fother : forall (F : bvmap 5 word) (v : word) (k : reg),
  bv_unsigned k <> 10%Z -> reg_get (bvmap_set 10 v F) k = reg_get F k.
Proof.
  intros F v k Hk. apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq.
  change (bv_unsigned (10 : reg)) with 10%Z. Local Ltac2 Set LiaHints.tbl := fun () => "0010=25330349198.4000004S2Hk".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.
Lemma zb_length : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
(* [comment removed for export] *)
Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
  Forall (fun iv => snd iv <= A \/ A + N <= fst iv)%Z W -> (A <= a)%Z -> (a + n <= A + N)%Z -> (0 <= n)%Z -> disjoint_from W a n.
Proof.
  intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. Local Ltac2 Set LiaHints.tbl := fun () => "0010>15083882462.1200000;S3Hiv2Ha2Hn".
split; [lia | exact IH].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
(* [comment removed for export] *)
Lemma zb_to_bytes_eq : forall l, zb l = Stdio.to_bytes l.
Proof. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof.
  Local Ltac2 Set LiaHints.tbl := fun () => "0060=33107249241.037009530087.538649584363.753892488832.763374555410.768399279967.400000100800900:00;00?SS2Hb2HsSSSS2IH".
induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
  split. { apply Z.lor_nonneg. lia. }
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
  2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  pose proof (bytes_le_to_Z_range bs) as HR.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
    Local Ltac2 Set LiaHints.tbl := fun () => "0040=15384169642.517508899659.829011858828.863368328716.500000400700:00;S2HbS1lS1nS".
rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
    replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z.
    2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
        destruct (Z.ltb_spec0 i 8).
        - rewrite Z.shiftl_spec_low by lia. reflexivity.
        - rewrite Z.ones_spec_high by lia. apply andb_false_r. }
    rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
    rewrite Z.lor_0_l. exact IH.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in HR.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010<1661189252.3000007S2HL2HR".
rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma u32arr_of_u8arr : forall segs m A bs k,
  u8arr segs m A bs -> length bs = (4 * k)%nat ->
  exists ws, length ws = k /\ u32arr segs m A ws.
Proof.
  intros segs m A bs k [Hb Hw] HL.
  assert (G : forall k bs, length bs = (4 * k)%nat -> exists ws, length ws = k /\ u32s ws = bs).
  { clear. induction k as [|k IH]; intros bs HL.
    - exists []. Local Ltac2 Set LiaHints.tbl := fun () => "0050>36433149040.7 36821012982.3 41147096472.125145515574.4  56582324531.7 00000900=00F00J00SS2HL4HlenS2HLS2HL4HlenS2HLS2HL4Hlen".
destruct bs; [split; reflexivity| cbn in HL; lia].
    - destruct (IH (skipn 4 bs) ltac:(rewrite length_skipn; lia)) as (ws & Hlen & Hu).
      exists (le_bytes_to_word (firstn 4 bs) :: ws). split; [cbn; lia|].
      cbn [u32s]. rewrite Hu, le4_of_bytes by (rewrite length_firstn; lia). apply firstn_skipn. }
  destruct (G k bs HL) as (ws & Hlen & Hu). exists ws. split; [exact Hlen|]. split.
  - rewrite Hu. exact Hb.
  - rewrite Hlen. replace (4 * Z.of_nat k)%Z with (Z.of_nat (length bs)) by lia. exact Hw.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma u8arr_of_u32arr : forall segs m A ws, u32arr segs m A ws -> u8arr segs m A (u32s ws).
Proof. intros segs m A ws [Hb Hw]. split; [exact Hb|]. rewrite u32s_length. Local Ltac2 Set LiaHints.tbl := fun () => "0010=17488400702.6000001S".
replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws))%Z by lia. exact Hw. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wnth (ws : list word) (i : Z) : word := nth (Z.to_nat i) ws (Z_to_bv 64 0).
Definition wval (ws : list word) (i : Z) : Z := (bv_unsigned (wnth ws i) mod 4294967296)%Z.

Lemma nth_error_wnth : forall ws i, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat -> nth_error ws (Z.to_nat i) = Some (wnth ws i).
Proof. intros ws i Hi Hl. unfold wnth. apply nth_error_nth'. exact Hl. Qed.

Lemma wval_upd_same : forall ws i v, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat ->
  wval (upd ws (Z.to_nat i) v) i = (bv_unsigned v mod 4294967296)%Z.
Proof.
  intros ws i v Hi Hl. unfold wval, wnth.
  pose proof (nth_error_upd_same ws (Z.to_nat i) v Hl) as E.
  apply nth_error_nth with (d := Z_to_bv 64 0) in E. rewrite E. reflexivity.
Qed.
Lemma wval_upd_other : forall ws i j v, (0 <= i)%Z -> (0 <= j)%Z -> i <> j ->
  wval (upd ws (Z.to_nat i) v) j = wval ws j.
Proof.
  intros ws i j v Hi Hj Hij. unfold wval, wnth.
  destruct (Nat.lt_ge_cases (Z.to_nat j) (length ws)) as [Hl|Hl].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0020=2293907673.8 36693294239.800000400BS2HlS2Hi2Hj3Hij2Hl".
pose proof (nth_error_upd_other ws (Z.to_nat i) (Z.to_nat j) v ltac:(lia)) as E.
    rewrite (nth_error_nth' ws (Z_to_bv 64 0) Hl) in E.
    apply nth_error_nth with (d := Z_to_bv 64 0) in E. rewrite E. reflexivity.
  - rewrite !nth_overflow by (rewrite ?upd_length; lia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wval_range : forall ws i, (0 <= wval ws i < 4294967296)%Z.
Proof. intros. unfold wval. apply Z.mod_pos_bound. Local Ltac2 Set LiaHints.tbl := fun () => "0010=18930413173.2000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma div1e9_magic : forall x, (0 <= x < 2^64)%Z ->
  Z.shiftr (Z.shiftr (Z.shiftr x 9 * 19342813113834067) 64) 11 = (x / 1000000000)%Z.
Proof.
  intros x Hx. Local Ltac2 Set LiaHints.tbl := fun () => "00:0=11054459580.211601619207.217935615974.235497640934.24392008886.2 47746555152.251860356214.256093676630.26160744982.2 63444950865.200000100200300400500900:00>00?00@SSSSSS2HxSS2HxSS".
rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
  change (2^64 * 2^11)%Z with (2^75)%Z. change 1000000000%Z with (512 * 1953125)%Z. rewrite <- Z.div_div by lia.
  change (2^9)%Z with 512%Z.
  set (y := (x / 512)%Z). assert (Hy : (0 <= y < 2^55)%Z) by (subst y; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  clearbody y. clear x Hx.
  Z.div_mod_to_equations. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma sx32_zero : forall w : word, bv_unsigned (sx32 w) = 0%Z <-> (bv_unsigned w mod 4294967296 = 0)%Z.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_modulus in R. change (2^64)%Z with 18446744073709551616%Z in *. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R.
  Local Ltac2 Set LiaHints.tbl := fun () => "0020=1456366856.3 33154001686.3000003006S1HS1H".
split; intros H; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma sx32_nonzero : forall w : word, bv_unsigned (sx32 w) <> 0%Z <-> (bv_unsigned w mod 4294967296 <> 0)%Z.
Proof. intros w. rewrite sx32_zero. tauto. Qed.

Lemma mulhu_M_range : forall x, (0 <= x < 2^62)%Z ->
  (0 <= Z.shiftr (Z.shiftr x 9 * 19342813113834067) 64 < 18446744073709551616)%Z.
Proof.
  intros x Hx. Local Ltac2 Set LiaHints.tbl := fun () => "0090=14528910095.225852676502.235497640934.238948407713.251860356214.256087383078.356093676630.267379879809.367381970929.200000400500600700800<00@00A00BS2HxSSSSS2HxS2HxSS".
rewrite !Z.shiftr_div_pow2 by lia.
  split. { apply Z.div_pos; [|lia]. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]. }
  apply Z.div_lt_upper_bound; [lia|].
  assert (x / 2^9 < 2^53)%Z by (apply Z.div_lt_upper_bound; lia). 
  assert (0 <= x / 2^9)%Z by (apply Z.div_pos; lia). nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
