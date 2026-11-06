(* The symbolic states, shadow entries and byte lemmas of the image-A walk of diginet_counter_encode
   (fuzz_codec.asan 0x86608; lib/A/Prog/diginet_counter_encode_A.v).
   Atoms: 0..31 the registers at entry (2 = sp, 10 = p, 11 = seg, 12 = dots, 13 = out), 32 = SB, 33..36 the
   four personality bytes p[16..20) (device, strips, chars, counter_addr), 37..44 seg[0..8).
   Regions: the 64-byte save area, the .got slot of the shadow-offset cell and the cell (cw_regs 64), the
   personality bytes (atom 10, [16, 20)), the eight segment bytes (atom 11, [0, 8)), and the bytes of out the
   function writes: [0, 4) before __asan_memcpy, [14, 15), [24, 26), [28, 32) after it; the ten payload bytes
   __asan_memcpy copies to out + 4 are a read-only region [4, 14) after the call. The personality and segment
   regions never meet in one state (the contract does not keep them apart), and neither meets the .got slot or
   the cell. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition A_CTR : Z := 0x86608.
Lemma T_counter_val : T_counter = 4160.
Proof. reflexivity. Qed.

(* ---------------------------------- atoms and regions ---------------------------------- *)
Definition ctr_xs (dev st ch dc : Z) (seg : list Z) : list Z :=
  [dev; st; ch; dc; nth 0 seg 0; nth 1 seg 0; nth 2 seg 0; nth 3 seg 0;
   nth 4 seg 0; nth 5 seg 0; nth 6 seg 0; nth 7 seg 0].
Definition ctr_AF : list (nat * afact) :=
  [(10%nat, mkAF 1 (2 ^ 47 - 21) 0); (11%nat, mkAF 1 (2 ^ 47 - 9) 0); (12%nat, mkAF 0 255 0);
   (13%nat, mkAF 1 (2 ^ 47 - 33) 0);
   (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0);
   (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0);
   (41%nat, mkAF 0 255 0); (42%nat, mkAF 0 255 0); (43%nat, mkAF 0 255 0); (44%nat, mkAF 0 255 0)].
Definition ss_ctr0 : sstate := mkSS A_CTR sr_atoms (cw_regs 64 ++ []) None (mkFacts (cw_atoms ++ ctr_AF) [] []).
Definition ctr_SH : list shent := [mkSHE 10 16 20; mkSHE 11 0 8; mkSHE 13 0 32].
Definition ctr_rpers : YP09.region := YP09.mkRegion (Some 10%nat) 16 20 0 0
  [YP09.mkChunk 16 (CVal 1 (SOff 33 0)); YP09.mkChunk 17 (CVal 1 (SOff 34 0));
   YP09.mkChunk 18 (CVal 1 (SOff 35 0)); YP09.mkChunk 19 (CVal 1 (SOff 36 0))].
Definition ctr_rseg : YP09.region := YP09.mkRegion (Some 11%nat) 0 8 0 0
  [YP09.mkChunk 0 (CVal 1 (SOff 37 0)); YP09.mkChunk 1 (CVal 1 (SOff 38 0));
   YP09.mkChunk 2 (CVal 1 (SOff 39 0)); YP09.mkChunk 3 (CVal 1 (SOff 40 0));
   YP09.mkChunk 4 (CVal 1 (SOff 41 0)); YP09.mkChunk 5 (CVal 1 (SOff 42 0));
   YP09.mkChunk 6 (CVal 1 (SOff 43 0)); YP09.mkChunk 7 (CVal 1 (SOff 44 0))].
Definition ctr_rout0 : YP09.region := YP09.mkRegion (Some 13%nat) 0 4 0 4 [].
(* the ten payload bytes at out + 4 after __asan_memcpy: counter_addr, dots, seg[7], ..., seg[0] *)
Definition ctr_rpl : YP09.region := YP09.mkRegion (Some 13%nat) 4 14 0 0
  [YP09.mkChunk 4 (CVal 1 (SOff 36 0)); YP09.mkChunk 5 (CVal 1 (SOff 12 0));
   YP09.mkChunk 6 (CVal 1 (SOff 44 0)); YP09.mkChunk 7 (CVal 1 (SOff 43 0));
   YP09.mkChunk 8 (CVal 1 (SOff 42 0)); YP09.mkChunk 9 (CVal 1 (SOff 41 0));
   YP09.mkChunk 10 (CVal 1 (SOff 40 0)); YP09.mkChunk 11 (CVal 1 (SOff 39 0));
   YP09.mkChunk 12 (CVal 1 (SOff 38 0)); YP09.mkChunk 13 (CVal 1 (SOff 37 0))].
Definition ctr_rout14 : YP09.region := YP09.mkRegion (Some 13%nat) 14 15 14 15 [].
Definition ctr_rout24 : YP09.region := YP09.mkRegion (Some 13%nat) 24 26 24 26 [].
Definition ctr_rout28 : YP09.region := YP09.mkRegion (Some 13%nat) 28 32 28 32 [].

(* ---------------------------------- byte lemmas ---------------------------------- *)
Lemma ctr_val1_kept : forall (H : word -> bool) (m m2 : word -> option byte) a v,
  aview tfibsegs H m2 a = aview tfibsegs H m a ->
  val_mem tfibsegs (mrestrict H m) a 1 v -> val_mem tfibsegs (mrestrict H m2) a 1 v.
Proof.
intros H m m2 a v Hk Hv i Hi. assert (i = 0%nat) as -> by lia. rewrite <- (Hv 0%nat ltac:(lia)).
apply (mbyte_of_aview tfibsegs). change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact Hk.
Qed.
Lemma ctr_garr8_kept : forall (H : word -> bool) (m m2 : word -> option byte) q l,
  (forall a, q <= a < q + Z.of_nat (length l) -> aview tfibsegs H m2 a = aview tfibsegs H m a) ->
  garr8 tfibsegs (mrestrict H m) q l -> garr8 tfibsegs (mrestrict H m2) q l.
Proof.
intros H m m2 q l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
apply (ctr_val1_kept H m m2); [apply Hk; lia | exact Hv].
Qed.
(* a one-byte chunk over atom k holding byte j of a byte array *)
Lemma ctr_chunk1 : forall E (m : word -> option byte) base off q l j k,
  garr8 tfibsegs m q l -> (j < length l)%nat -> base + off = q + Z.of_nat j ->
  ew E k = Z_to_bv 64 (nth j l 0) ->
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 1 (SOff k 0))).
Proof.
intros E m base off q l j k Hg Hj Ho Hk. destruct (Hg j Hj) as [Hv Hb].
apply (chunk_ok_val tfibsegs E m base off 1 (SOff k 0) (nth j l 0)).
- rewrite sv_denot_SOff0. exact Hk.
- change (2 ^ (8 * Z.of_N 1)) with 256. exact Hb.
- cbn. lia.
- rewrite Ho. exact Hv.
Qed.
(* the shadow band is kept when every byte of it is *)
Lemma ctr_ra_kept : forall (H : word -> bool) (m m2 : word -> option byte) q n,
  (forall a, SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44 -> aview tfibsegs H m2 a = aview tfibsegs H m a) ->
  0 <= q -> q + n <= 2 ^ 47 ->
  range_addressable (aview tfibsegs H m) SHADOW_OFF q n -> range_addressable (aview tfibsegs H m2) SHADOW_OFF q n.
Proof.
intros H m m2 q n Hk Hq Hqn Hra x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite Hk; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF in *.
assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia.
Qed.
(* the shadow window of a range that every byte of keeps *)
Lemma ctr_hull_kept : forall (H : word -> bool) (m m2 : word -> option byte) x n,
  (forall a, SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44 -> aview tfibsegs H m2 a = aview tfibsegs H m a) ->
  0 <= x -> x + n <= 2 ^ 47 -> 0 < n ->
  shadow_hull_vis (aview tfibsegs H m) x n -> shadow_hull_vis (aview tfibsegs H m2) x n.
Proof.
intros H m m2 x n Hk Hx Hxn Hn Hh s Hs. rewrite Hk; [exact (Hh s Hs)|].
unfold shadow_addr, SHADOW_OFF in *.
pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)) as M2.
pose proof (Z.div_mod (2147450880 + x / 8) 8 ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound (2147450880 + x / 8) 8 ltac:(lia)) as M3.
pose proof (Z.div_mod (2147450880 + (x + n - 1) / 8) 8 ltac:(lia)) as D4.
pose proof (Z.mod_pos_bound (2147450880 + (x + n - 1) / 8) 8 ltac:(lia)) as M4.
lia.
Qed.
(* a byte moved from a1 to a2 *)
Lemma ctr_val1_move : forall (H : word -> bool) (m m2 : word -> option byte) a1 a2 v,
  aview tfibsegs H m2 a2 = aview tfibsegs H m a1 ->
  val_mem tfibsegs (mrestrict H m) a1 1 v -> val_mem tfibsegs (mrestrict H m2) a2 1 v.
Proof.
intros H m m2 a1 a2 v E Hv i Hi. assert (i = 0%nat) as -> by lia.
pose proof (Hv 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0 |- *. rewrite Z.add_0_r in H0 |- *.
rewrite <- H0. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H m2) a2) as [b'|], (mbyte tfibsegs (mrestrict H m) a1) as [b|]; cbn in E;
  try discriminate; try reflexivity.
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
(* the low byte of a sign-extended byte *)
Lemma ctr_U_sext8_mod : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v < 256 ->
  bv_unsigned (sv_denot E (SExt true 8 (SOff k 0))) mod 2 ^ (8 * Z.of_N 1) = v.
Proof.
intros E k v Hk Hv. change (bv_unsigned (sv_denot E (SExt true 8 (SOff k 0)))) with (U E (SExt true 8 (SOff k 0))).
rewrite U_SExt, (cw_U_atom0 E k v Hk ltac:(lia)).
change (2 ^ Z.of_N 8) with 256. change (2 ^ (8 * Z.of_N 1)) with 256. rewrite (Z.mod_small v 256) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
destruct (Z.ltb_spec v 128) as [Hl|Hg].
- rewrite (Z.mod_small (v + 128) 256) by lia. replace (v + 128 - 128) with v by lia.
  rewrite (Z.mod_small v (2 ^ 64)) by lia. apply Z.mod_small. lia.
- replace (v + 128) with ((v - 256 + 128) + 1 * 256) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (v - 256 + 128) 256) by lia. replace (v - 256 + 128 - 128) with (v - 256) by lia.
  replace (v - 256) with ((v - 256 + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (v - 256 + 2 ^ 64)) by lia.
  replace (v - 256 + 2 ^ 64) with (v + (2 ^ 56 - 1) * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
(* a 4-byte field, read as its four bytes *)
Lemma ctr_val4_bytes : forall (m : word -> option byte) a v j, val_mem tfibsegs m a 4 v -> 0 <= v < 2 ^ 32 -> (j < 4)%nat ->
  val_mem tfibsegs m (a + Z.of_nat j) 1 (nth j (le4Z v) 0).
Proof.
intros m a v j Hv Hr Hj i Hi. assert (i = 0%nat) as -> by lia. replace (a + Z.of_nat j + Z.of_nat 0) with (a + Z.of_nat j) by lia.
rewrite (Hv j Hj).
assert (Hb : YO0f.le_byte v 4 j = YO0f.le_byte (nth j (le4Z v) 0) 1 0).
{ unfold YO0f.le_byte, le4Z. replace (8 * Z.of_nat 4) with 32 by reflexivity. replace (8 * Z.of_nat 1) with 8 by reflexivity.
  replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite (Z.mod_small v (2 ^ 32)) by lia. rewrite !Z.shiftr_0_r.
  destruct j as [|[|[|[|j]]]]; [ | | | | lia]; cbn [nth].
  - rewrite !Z.mod_mod by lia. reflexivity.
  - replace (8 * Z.of_nat 1) with 8 by reflexivity. rewrite Z.shiftr_div_pow2 by lia. rewrite !Z.mod_mod by lia. reflexivity.
  - replace (8 * Z.of_nat 2) with 16 by reflexivity. rewrite Z.shiftr_div_pow2 by lia. rewrite !Z.mod_mod by lia. reflexivity.
  - replace (8 * Z.of_nat 3) with 24 by reflexivity. rewrite Z.shiftr_div_pow2 by lia. rewrite !Z.mod_mod by lia. reflexivity. }
rewrite Hb. reflexivity.
Qed.
(* `lb` of a byte v then `bltz`: taken exactly when bit 7 of v is set *)
Lemma ctr_br_sext8 : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v < 256 ->
  branch_taken BC_LT (sv_denot E (SExt true 8 (SOff k 0))) (sv_denot E (SLit 0)) = (128 <=? v).
Proof.
intros E k v Hk Hv. cbn [branch_taken]. unfold bv_lts.
rewrite (denot_lit_U E (SExt true 8 (SOff k 0))), (denot_lit_U E (SLit 0)), !Z_to_bv_signed.
rewrite U_SExt, U_SLit, (cw_U_atom0 E k v Hk ltac:(lia)).
change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small v 256) by lia.
assert (Hsw : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_swrap 64 (zcanon z) = z).
{ intros z Hz. unfold zcanon, M64. unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63).
  change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia. }
unfold bv_swrap at 2. unfold bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
destruct (Z.ltb_spec v 128) as [Hl|Hg].
- rewrite (Z.mod_small (v + 128) 256) by lia. replace (v + 128 - 128) with v by lia.
  rewrite Hsw by lia. rewrite (Hsw 0) by lia.
  rewrite (proj2 (Z.ltb_ge v 0)) by lia. symmetry. apply Z.leb_gt. lia.
- replace (v + 128) with ((v - 256 + 128) + 1 * 256) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (v - 256 + 128) 256) by lia. replace (v - 256 + 128 - 128) with (v - 256) by lia.
  rewrite Hsw by lia. rewrite (Hsw 0) by lia.
  rewrite (proj2 (Z.ltb_lt (v - 256) 0)) by lia. symmetry. apply Z.leb_le. lia.
Qed.
(* the payload of counter_encode: pl[0] = counter_addr, pl[1] = dots, pl[2 + k] = seg[7 - k] *)
Definition ctr_pl (dc dots : Z) (seg : list Z) : list Z :=
  [dc; dots; nth 7 seg 0; nth 6 seg 0; nth 5 seg 0; nth 4 seg 0; nth 3 seg 0; nth 2 seg 0; nth 1 seg 0; nth 0 seg 0].
Lemma ctr_pl_eq : forall dc dots seg, (8 <= length seg)%nat ->
  [dc; dots] ++ rev (firstn 8 seg) = ctr_pl dc dots seg.
Proof.
intros dc dots seg Hl.
destruct seg as [|s0 [|s1 [|s2 [|s3 [|s4 [|s5 [|s6 [|s7 seg']]]]]]]]; cbn [length] in Hl; try lia.
reflexivity.
Qed.
Lemma ctr_spec_arg : forall d seg dots, 127 < d_dev d -> counter_spec (Some d) seg dots = (E_ARG, None).
Proof.
intros d seg dots H. unfold counter_spec, sysex_spec. rewrite (proj2 (Z.ltb_lt 127 (d_dev d)) H). reflexivity.
Qed.
Lemma ctr_testbit7 : forall x, 0 <= x < 256 -> Z.testbit x 7 = (128 <=? x).
Proof.
intros x Hx. pose proof (Z.testbit_spec' x 7 ltac:(lia)) as Hb. change (2 ^ 7) with 128 in Hb.
destruct (Z.leb_spec 128 x).
- replace (x / 128) with 1 in Hb by (apply Z.div_unique with (r := x - 128); lia).
  destruct (Z.testbit x 7); [reflexivity | vm_compute in Hb; discriminate Hb].
- rewrite Z.div_small in Hb by lia. destruct (Z.testbit x 7); [vm_compute in Hb; discriminate Hb | reflexivity].
Qed.
Lemma ctr_spec_range : forall d seg dots x, d_dev d <= 127 -> (8 <= length seg)%nat ->
  In x (ctr_pl (d_counter d) dots seg) -> 128 <= x < 256 -> counter_spec (Some d) seg dots = (E_RANGE, None).
Proof.
intros d seg dots x Hd Hl Hin Hx. unfold counter_spec, sysex_spec.
rewrite (proj2 (Z.ltb_ge 127 (d_dev d)) ltac:(lia)). rewrite (ctr_pl_eq _ _ _ Hl).
replace (existsb (fun x0 => Z.testbit x0 7) (ctr_pl (d_counter d) dots seg)) with true.
- replace (Z.of_nat (length (ctr_pl (d_counter d) dots seg)) + 5) with 15 by reflexivity. reflexivity.
- symmetry. apply existsb_exists. exists x. split; [exact Hin|]. rewrite ctr_testbit7 by lia. apply Z.leb_le. lia.
Qed.
Lemma ctr_spec_ok : forall d seg dots, d_dev d <= 127 -> (8 <= length seg)%nat ->
  Forall (fun x => 0 <= x < 128) (ctr_pl (d_counter d) dots seg) ->
  counter_spec (Some d) seg dots =
  (0, Some ([0xf0; 0x13; d_dev d; 0x30] ++ ctr_pl (d_counter d) dots seg ++ [0xf7], KEY 6 (d_counter d), 1)).
Proof.
intros d seg dots Hd Hl HF. unfold counter_spec, sysex_spec.
rewrite (proj2 (Z.ltb_ge 127 (d_dev d)) ltac:(lia)). rewrite (ctr_pl_eq _ _ _ Hl).
replace (existsb (fun x0 => Z.testbit x0 7) (ctr_pl (d_counter d) dots seg)) with false.
- replace (Z.of_nat (length (ctr_pl (d_counter d) dots seg)) + 5) with 15 by reflexivity. reflexivity.
- symmetry. apply Bool.not_true_iff_false. intros Ht. apply existsb_exists in Ht as (x & Hin & Hb).
  rewrite Forall_forall in HF. specialize (HF x Hin). rewrite ctr_testbit7 in Hb by lia. apply Z.leb_le in Hb. lia.
Qed.

(* the key of the counter command, KEY 6 counter_addr, as the walk computes it (`or` with 0x60000) *)
Lemma ctr_lor_key : forall v, 0 <= v < 256 -> Z.lor v 393216 = v + 393216.
Proof.
intros v Hv.
assert (Hin : In v (map Z.of_nat (seq 0 256))) by (apply in_map_iff; exists (Z.to_nat v); split; [lia | apply in_seq; lia]).
assert (R : forallb (fun x => Z.eqb (Z.lor x 393216) (x + 393216)) (map Z.of_nat (seq 0 256)) = true)
  by (vm_compute; reflexivity).
apply Z.eqb_eq. exact (proj1 (forallb_forall _ _) R v Hin).
Qed.
Lemma ctr_key : forall E v, ew E 36 = Z_to_bv 64 v -> 0 <= v < 256 ->
  bv_unsigned (sv_denot E (SAlu ALU_OR (SOff 36 0) (SLit 393216))) mod 2 ^ (8 * Z.of_N 4) = KEY 6 v.
Proof.
intros E v Hk Hv.
change (bv_unsigned (sv_denot E (SAlu ALU_OR (SOff 36 0) (SLit 393216)))) with (U E (SAlu ALU_OR (SOff 36 0) (SLit 393216))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (cw_U_atom0 E 36 v Hk) by lia. rewrite U_SLit. change (zcanon 393216) with 393216.
rewrite ctr_lor_key by lia. unfold KEY. change (6 * 65536) with 393216.
replace (Z.land v 65535) with v.
- rewrite Z.lor_comm, ctr_lor_key by lia. rewrite zcanon_small by lia. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
  apply Z.mod_small. lia.
- symmetry. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
(* the low byte of an atom that holds a byte *)
Lemma ctr_U_atom_mod : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v < 256 ->
  bv_unsigned (sv_denot E (SOff k 0)) mod 2 ^ (8 * Z.of_N 1) = v.
Proof.
intros E k v Hk Hv. change (bv_unsigned (sv_denot E (SOff k 0))) with (U E (SOff k 0)).
rewrite (cw_U_atom0 E k v Hk) by lia. change (2 ^ (8 * Z.of_N 1)) with 256. apply Z.mod_small. exact Hv.
Qed.
(* garr8 from its bytes *)
Lemma ctr_garr8_of : forall m q L,
  (forall j, (j < length L)%nat -> val_mem tfibsegs m (q + Z.of_nat j) 1 (nth j L 0)) ->
  Forall (fun b => 0 <= b < 256) L -> garr8 tfibsegs m q L.
Proof. intros m q L Hv Hb j Hj. split; [exact (Hv j Hj)|]. rewrite Forall_forall in Hb. apply Hb. apply nth_In. exact Hj. Qed.
(* the 32 bytes of the command after a successful counter_encode *)
Lemma ctr_cmd_out : forall before dev dc dots seg key, length before = 32%nat ->
  0 <= dev < 256 -> 0 <= dc < 256 -> 0 <= dots < 256 -> (forall j, (j < 8)%nat -> 0 <= nth j seg 0 < 256) ->
  cmd_outZ before (Some ([0xf0; 0x13; dev; 0x30] ++ ctr_pl dc dots seg ++ [0xf7], key, 1)) =
  [0xf0; 0x13; dev; 0x30; dc; dots; nth 7 seg 0; nth 6 seg 0; nth 5 seg 0; nth 4 seg 0;
   nth 3 seg 0; nth 2 seg 0; nth 1 seg 0; nth 0 seg 0; 0xf7;
   nth 15 before 0; nth 16 before 0; nth 17 before 0; nth 18 before 0; nth 19 before 0; nth 20 before 0;
   nth 21 before 0; nth 22 before 0; nth 23 before 0; 15; 1; nth 26 before 0; nth 27 before 0] ++ le4Z key.
Proof.
intros before dev dc dots seg key Hl Hd Hc Ho Hs.
pose proof (Hs 0%nat ltac:(lia)). pose proof (Hs 1%nat ltac:(lia)). pose proof (Hs 2%nat ltac:(lia)).
pose proof (Hs 3%nat ltac:(lia)). pose proof (Hs 4%nat ltac:(lia)). pose proof (Hs 5%nat ltac:(lia)).
pose proof (Hs 6%nat ltac:(lia)). pose proof (Hs 7%nat ltac:(lia)).
do 32 (destruct before as [|? before]; [cbn in Hl; discriminate Hl|]).
destruct before; [|cbn in Hl; discriminate Hl].
unfold cmd_outZ, ctr_pl, u8. cbn [app map length firstn skipn nth Z.of_nat Pos.of_succ_nat Pos.succ].
rewrite (Z.mod_small dev), (Z.mod_small dc), (Z.mod_small dots) by lia.
rewrite (Z.mod_small (nth 7 seg 0)), (Z.mod_small (nth 6 seg 0)), (Z.mod_small (nth 5 seg 0)), (Z.mod_small (nth 4 seg 0)),
  (Z.mod_small (nth 3 seg 0)), (Z.mod_small (nth 2 seg 0)), (Z.mod_small (nth 1 seg 0)), (Z.mod_small (nth 0 seg 0)) by lia.
reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

(* the walk's entry state (pd = Some d) and its shadow entries *)
Lemma ctr_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k regs
  (d : desk) p sg dots out seg,
  cdc_entry tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_counter ->
  getr regs 10 = w64 p -> getr regs 11 = w64 sg -> getr regs 12 = w64 dots -> 0 <= dots < 256 ->
  getr regs 13 = w64 out ->
  pers_argA tfibsegs B W memc (spZ regs) T_counter p (Some d) ->
  0 < sg -> (8 <= length seg)%nat ->
  crd_ok tfibsegs W memc (spZ regs) T_counter sg (Z.of_nat (length seg)) ->
  cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_counter out 32 ->
  garr8 tfibsegs (mrestrict (w_H W) memc) sg seg ->
  YP0l.st_ok tfibsegs (Ereg regs (cw_extra (ctr_xs (d_dev d) (d_strips d) (d_chars d) (d_counter d) seg))) ss_ctr0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_CTR) memc (seg_rom tfibsegs))) /\
  sh_ok tfibsegs CW_Bx ctr_SH (Ereg regs (cw_extra (ctr_xs (d_dev d) (d_strips d) (d_chars d) (d_counter d) seg)))
    (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs d p sg dots out seg
  HE H10 H11 H12 Hdots H13 HPA Hsg0 Hlen HCRD HCOUT HGseg.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_counter HE ltac:(unfold T_counter, ESTACK; lia))
  as (Hceil & H47 & H46 & Hal & Hpres).
pose proof HE as ((HAR & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTC : T_counter = 4160) by reflexivity. rewrite HTC in H46, Hceil, Hpres.
cbn [pers_argA] in HPA.
destruct HPA as (Hp0 & Hp1 & Hdv & Hst & Hch & Hdc & HGp & HCRp).
pose proof HCRp as (_ & _ & _ & HAMp0 & _ & _ & HUSp).
destruct (HUSp lyc Sc W memc mdc HAR) as [HRAp _].
pose proof HAMp0 as HAMp.
pose proof HCRD as (_ & Hsg1 & _ & HRAs & _ & HAMs & _).
pose proof HCOUT as (Hout0 & Hout1 & _ & _ & HRAo & _ & HAMo & _).
unfold amem_range in HAMp, HAMs, HAMo. rewrite C3, C4, C5 in HAMp, HAMs, HAMo.
set (xs := ctr_xs (d_dev d) (d_strips d) (d_chars d) (d_counter d) seg).
set (E := Ereg regs (cw_extra xs)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite (cw_ew_reg regs xs 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 sg) by (subst E; rewrite (cw_ew_reg regs xs 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 dots) by (subst E; rewrite (cw_ew_reg regs xs 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 out) by (subst E; rewrite (cw_ew_reg regs xs 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (EX : forall j, ew E (33 + j) = Z_to_bv 64 (nth j xs 0)) by (intros j; subst E; apply cw_ew_x).
assert (Hseg8 : forall j, (j < 8)%nat -> 0 <= nth j seg 0 < 256) by (intros j Hj; apply (HGseg j); lia).
split.
- unfold ss_ctr0. apply (cw_entry B TL LAWS A_CTR 64 xs [] ctr_AF lyc Sc W regs memc mdc HAR ltac:(lia) ltac:(lia) Hal
    ltac:(intros a Ha; apply Hpres; unfold T_counter, ESTACK; lia) eq_refl (Forall_nil _)).
  + rewrite app_nil_r. apply pairwise_disjoint_of_extents.
    unfold cw_regs, stack_region, got_region, bcell_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
    rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). change (bv_unsigned (getr regs 2)) with (spZ regs).
    unfold A_GOT_shadow, A_shadow_glob.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + change (Ereg regs (cw_extra xs)) with E. unfold ctr_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Z.pow_0_r. rewrite !Z.mod_1_r.
    rewrite E10, E11, E12, E13.
    assert (EXn : forall n, (33 <= n)%nat -> ew E n = Z_to_bv 64 (nth (n - 33) xs 0))
      by (intros n Hn; replace n with (33 + (n - 33))%nat at 1 by lia; apply EX).
    rewrite !EXn by lia. cbn [Nat.sub].
    subst xs. unfold ctr_xs. cbn [nth].
    pose proof (Hseg8 0%nat ltac:(lia)). pose proof (Hseg8 1%nat ltac:(lia)). pose proof (Hseg8 2%nat ltac:(lia)).
    pose proof (Hseg8 3%nat ltac:(lia)). pose proof (Hseg8 4%nat ltac:(lia)). pose proof (Hseg8 5%nat ltac:(lia)).
    pose proof (Hseg8 6%nat ltac:(lia)). pose proof (Hseg8 7%nat ltac:(lia)).
    rewrite !unsigned_lit_small by lia.
    repeat split; lia.
- unfold sh_ok, ctr_SH. repeat apply Forall_cons; try apply Forall_nil.
  + exact (cw_shent_ra_off W memc E 10 p 16 4 HRAp HAMp0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E10 E32).
  + apply (shent_ok_of_range tfibsegs (w_H W) memc E CW_Bx 11 sg (Z.of_nat (length seg)) sg 0 8 HRAs).
    * exact (cw_U_Bx E E32).
    * exact (cw_U_atom0 E 11 sg E11 ltac:(lia)).
    * lia.
    * lia.
    * cbn [Z.min Z.max]. intros x Hx. unfold SHADOW_OFF. lia.
  + exact (cw_shent_cdst B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_counter E 13 out 32 HCOUT E13 E32 ltac:(lia)).
Qed.
End d.
End b.
