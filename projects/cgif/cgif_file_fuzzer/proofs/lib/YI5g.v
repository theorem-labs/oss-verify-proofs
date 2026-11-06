(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02 YN3b YI06 YI5b YI09 YI08 YI0r
YI1w YI4l YI21 YI5o YI5r YI5l YI6b YL0g
YI3m YI5m YN0d
YI16 YI17 YI14 YI18 YI1a YI5c YI00 YI3u YI22 YI2u YI0l
YI5a YI23 YI0a YL00 YI05 YI5n.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5f YI5e YI5k.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition L_HDR0 : Z := Eval vm_compute in (src0_A_LLVMFuzzerTestOneInput + 0x50).
Definition lh_cnt (k : nat) : nat := nth k [0; 2; 4; 8; 12; 14]%nat 14%nat.
Definition lh_lo (k : nat) : Z := nth k [1; 2; 4; 8; 12; 14] 14.
Definition lh_hi (k : nat) : Z := nth k [1; 3; 7; 11; 13; CEIL_MAX] CEIL_MAX.
Definition lh_breg (k : nat) : list YP09.region :=
match k with O => [] | _ => [YP09.mkRegion (Some 10%nat) 0 (Z.of_nat (lh_cnt k)) 0 0 (byte_chunks 32 (lh_cnt k))] end.
Definition lh_bfacts (k : nat) : list (nat * afact) := map (fun i => ((32 + i)%nat, mkAF 0 255 0)) (seq 0 (lh_cnt k)).
Definition ss_lh (k : nat) : sstate :=
mkSS LLVM sr_atoms
([ YP09.mkRegion (Some 2%nat) (-192) (-128) (-192) (-128) [] ;
YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 [] ] ++ lh_breg k)
None
(mkFacts ([ (2%nat, mkAF (CEIL_MIN + LIB_STACK) (2^63) 4); (10%nat, mkAF 4096 CEIL_MAX 0);
(11%nat, mkAF (lh_lo k) (lh_hi k) 0) ] ++ lh_bfacts k) [] []).
Lemma byte_at_range_of : forall {E n m a}, ew E n = Z_to_bv 64 (byte_at m a) -> 0 <= byte_at m a < 256.
Proof. intros. apply byte_at_range. Qed.
Lemma land4_testbit : forall x, Z.land x 4 = if Z.testbit x 2 then 4 else 0.
Proof.
intros x. apply Z.bits_inj'. intros m Hm. rewrite Z.land_spec.
replace (Z.testbit 4 m) with (2 =? m) by (symmetry; apply (Z.pow2_bits_eqb 2 m); lia).
destruct (Z.eqb_spec 2 m) as [<-|Hne].
- destruct (Z.testbit x 2); [symmetry; apply (Z.pow2_bits_true 2); lia | rewrite Z.bits_0; reflexivity].
- rewrite andb_false_r. destruct (Z.testbit x 2); [symmetry; apply (Z.pow2_bits_false 2); lia | rewrite Z.bits_0; reflexivity].
Qed.
Lemma land4_mod32 : forall x, Z.land (x mod 2 ^ 32) 4 = Z.land x 4.
Proof. intros x. rewrite !land4_testbit. rewrite Z.mod_pow2_bits_low by lia. reflexivity. Qed.
Lemma denot_flag4 : forall E e,
sv_denot E (SAlu ALU_SLTU (SAlu ALU_AND e (SLit 4)) (SLit 1)) = Z_to_bv 64 (if Z.land (U E e mod 2 ^ 32) 4 =? 0 then 1 else 0).
Proof.
intros E e. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_and_lit by lia. rewrite U_SLit.
change (zcanon 1) with 1. rewrite land4_mod32, land4_testbit.
destruct (Z.testbit (U E e) 2); reflexivity.
Qed.
Lemma U_or_shl8 : forall E n1 n0 b1 b0,
ew E n1 = Z_to_bv 64 b1 -> ew E n0 = Z_to_bv 64 b0 -> 0 <= b1 < 256 -> 0 <= b0 < 256 ->
U E (SAlu ALU_OR (SAlu ALU_SLL (SOff n1 0) (SLit 8)) (SOff n0 0)) = b0 + 256 * b1.
Proof.
intros E n1 n0 b1 b0 H1 H0 R1 R0. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
change (Z.land (zcanon 8) 63) with 8. rewrite (U_atom E n1 b1 H1), (U_atom E n0 b0 H0) by lia.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (zcanon_id (b1 * 256)) by (unfold M64; lia). rewrite lor_shl8 by lia. apply zcanon_id. unfold M64; lia.
Qed.
Lemma denot_or_shl8 : forall E n1 n0 b1 b0,
ew E n1 = Z_to_bv 64 b1 -> ew E n0 = Z_to_bv 64 b0 -> 0 <= b1 < 256 -> 0 <= b0 < 256 ->
sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff n1 0) (SLit 8)) (SOff n0 0)) = Z_to_bv 64 (b0 + 256 * b1).
Proof. intros. rewrite denot_lit_U. f_equal. apply (U_or_shl8 E n1 n0 b1 b0); assumption. Qed.
Lemma st_chunk_low : forall E ss ms i rg p off (n : N) e a (k : nat) (m : Z),
st_ok src0segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p ->
In (mkChunk off (CVal n e)) (r_chunks rg) -> bv_unsigned (ew E p) = a -> Z.of_N n <= 8 ->
k = N.to_nat n -> m = 2 ^ (8 * Z.of_N n) ->
val_mem src0segs (ms_mem ms) (a + off) k (U E e mod m).
Proof.
intros E ss ms i rg p off n e a k m HS Hi Hb Hin Hp Hn -> ->.
pose proof (st_region_chunks src0segs E ss ms i rg p a HS Hi Hb Hp) as Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
unfold U. exact (val_mem_low_of_chunk src0segs E (ms_mem ms) a off n e Hc Hn).
Qed.
Lemma U_range : forall E e, 0 <= U E e < 2 ^ 64.
Proof. intros E e. unfold U. pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
Lemma lor_shl : forall k hi lo, 0 <= k -> 0 <= hi -> 0 <= lo < 2 ^ k -> Z.lor (hi * 2 ^ k) lo = lo + hi * 2 ^ k.
Proof.
intros k hi lo Hk Hhi Hlo.
assert (Hland : Z.land (hi * 2 ^ k) lo = 0).
{ destruct (Z.eq_dec lo 0) as [->|Hnz]; [apply Z.land_0_r|].
apply Z.bits_inj'. intros m Hm. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec m k) as [Hmk|Hmk].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- rewrite (Z.bits_above_log2 lo); [apply andb_false_r | lia |].
assert (Z.log2 lo < k); [apply Z.log2_lt_pow2; lia | lia]. }
rewrite <- (Z.lxor_lor _ _ Hland), <- (Z.add_nocarry_lxor _ _ Hland). lia.
Qed.
Lemma U_le4_mod32 : forall E (n3 n2 n1 n0 : nat) b3 b2 b1 b0,
ew E n3 = Z_to_bv 64 b3 -> ew E n2 = Z_to_bv 64 b2 -> ew E n1 = Z_to_bv 64 b1 -> ew E n0 = Z_to_bv 64 b0 ->
0 <= b3 < 256 -> 0 <= b2 < 256 -> 0 <= b1 < 256 -> 0 <= b0 < 256 ->
U E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SExt true 8 (SOff n3 0)) (SLit 24)) (SAlu ALU_SLL (SOff n2 0) (SLit 16)))
(SAlu ALU_OR (SAlu ALU_SLL (SOff n1 0) (SLit 8)) (SOff n0 0))) mod 2 ^ 32
= b0 + 256 * b1 + 65536 * b2 + 16777216 * b3.
Proof.
intros E n3 n2 n1 n0 b3 b2 b1 b0 H3 H2 H1 H0 R3 R2 R1 R0.
rewrite (U_SAlu E ALU_OR). cbn [zalu_raw]. rewrite (U_or_shl8 E n1 n0 b1 b0 H1 H0 R1 R0).
rewrite (U_SAlu E ALU_OR). cbn [zalu_raw].
rewrite (U_SAlu E ALU_SLL (SOff n2 0)). cbn [zalu_raw]. rewrite !U_SLit. change (Z.land (zcanon 16) 63) with 16.
rewrite (U_atom E n2 b2 H2) by lia. rewrite (Z.shiftl_mul_pow2 b2 16) by lia. rewrite (zcanon_id (b2 * 2 ^ 16)) by (unfold M64; lia).
rewrite (U_SAlu E ALU_SLL). cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 24) 63) with 24. rewrite U_SExt.
rewrite (U_atom E n3 b3 H3) by lia. change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small b3 256) by lia.
rewrite Z.shiftl_mul_pow2 by lia.
set (s := zcanon (bv_swrap 8 b3)).
assert (Hs : exists hi, zcanon (s * 2 ^ 24) = hi * 2 ^ 24 /\ (hi = b3 \/ hi = 2 ^ 40 - 256 + b3)).
{ subst s. unfold bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
destruct (Z_lt_le_dec b3 128) as [Hb|Hb].
- exists b3. split; [|left; reflexivity]. rewrite (Z.mod_small (b3 + 128) 256) by lia. replace (b3 + 128 - 128) with b3 by lia.
rewrite (zcanon_id b3) by (unfold M64; lia). apply zcanon_id. unfold M64; lia.
- exists (2 ^ 40 - 256 + b3). split; [|right; reflexivity].
replace ((b3 + 128) mod 256) with (b3 + 128 - 256) by (rewrite <- (Z.mod_small (b3 + 128 - 256) 256) by lia; rewrite <- (Z.mod_add _ 1 256) by lia; f_equal; lia).
replace (b3 + 128 - 256 - 128) with (b3 - 256) by lia.
replace (zcanon (b3 - 256)) with (2 ^ 64 + (b3 - 256)) by (unfold zcanon, M64; rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small by lia; lia).
unfold zcanon, M64. replace ((2 ^ 64 + (b3 - 256)) * 2 ^ 24) with ((2 ^ 40 - 256 + b3) * 2 ^ 24 + (2 ^ 24 - 1) * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
destruct Hs as (hi & -> & Hhi).
assert (Rhi : 0 <= hi /\ hi * 2 ^ 24 + 2 ^ 24 <= 2 ^ 64) by lia.
rewrite (lor_shl 24 hi (b2 * 2 ^ 16)) by lia. rewrite (zcanon_id (b2 * 2 ^ 16 + hi * 2 ^ 24)) by (unfold M64; lia).
replace (b2 * 2 ^ 16 + hi * 2 ^ 24) with ((b2 + 256 * hi) * 2 ^ 16) by lia.
rewrite (lor_shl 16 (b2 + 256 * hi) (b0 + 256 * b1)) by lia. rewrite (zcanon_id (b0 + 256 * b1 + (b2 + 256 * hi) * 2 ^ 16)) by (unfold M64; lia).
destruct Hhi as [-> | ->].
- rewrite Z.mod_small by lia. lia.
- replace (b0 + 256 * b1 + (b2 + 256 * (2 ^ 40 - 256 + b3)) * 2 ^ 16) with ((b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) + (2 ^ 32 - 1) * 2 ^ 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma hdr5_bytes : forall P, (14 <= length P)%nat ->
hdr5 P = (false, (nth 0 P 0 + 256 * nth 1 P 0, nth 2 P 0 + 256 * nth 3 P 0,
nth 4 P 0 + 256 * nth 5 P 0 + 65536 * nth 6 P 0 + 16777216 * nth 7 P 0,
nth 8 P 0 + 256 * nth 9 P 0 + 65536 * nth 10 P 0 + 16777216 * nth 11 P 0,
nth 12 P 0 + 256 * nth 13 P 0), skipn 14 P).
Proof.
intros P HP. rewrite hdr5_ok by lia.
do 14 (destruct P as [|? P]; [cbn in HP; lia|]). cbn [firstn skipn nth]. rewrite !le_bytes_2, !le_bytes_4. reflexivity.
Qed.
Lemma garr8_byte_at : forall m q (P : list Z) j, garr8 src0segs m q P -> (j < length P)%nat -> nth j P 0 = byte_at m (q + Z.of_nat j).
Proof.
intros m q P j H Hj. unfold byte_at. rewrite (garr8_mbyte _ m q P j H Hj). rewrite Z_to_bv_unsigned.
pose proof (proj2 (H j Hj)) as R. symmetry. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.
End c.
Ltac cfg_zero HS HU2 off len :=
lazymatch goal with |- val_mem _ _ (?b - 128 + ?k) ?n ?v =>
unify v 0;
let o := eval vm_compute in (-128 + k) in
replace (b - 128 + k) with (b + o) by lia;
eapply (st_chunk_zero_val src0segs _ _ _ 0%nat _ 2%nat off len b o n HS);
[ reflexivity | reflexivity | cbv; solve [auto 80] | ew_havocA; exact HU2 | lia | lia ]
end.
Ltac cfg_val2 HS HU2 n1 n0 H1 H0 :=
lazymatch goal with |- val_mem _ _ (?b - 128 + ?k) 2%nat ?v =>
let o := eval vm_compute in (-128 + k) in
replace (b - 128 + k) with (b + o) by lia;
eapply (st_chunk_val src0segs _ _ _ 0%nat _ 2%nat o 2%N _ b v HS);
[ reflexivity | reflexivity | cbv; solve [auto 80] | ew_havocA; exact HU2
| apply (denot_or_shl8 _ n1 n0); [ew_havocA; exact H1 | ew_havocA; exact H0 | apply byte_at_range | apply byte_at_range]
| pose proof (byte_at_range_of H1); pose proof (byte_at_range_of H0); cbn; lia | cbn; lia ]
end.
Ltac cfg_low4 HS HU2 :=
lazymatch goal with |- val_mem _ _ (?b - 128 + ?k) 4%nat ?v =>
let o := eval vm_compute in (-128 + k) in
replace (b - 128 + k) with (b + o) by lia;
eapply (st_chunk_low _ _ _ 0%nat _ 2%nat o 4%N _ b 4%nat (2 ^ 32) HS);
[ reflexivity | reflexivity | cbv; solve [auto 80] | ew_havocA; exact HU2 | cbn; lia | reflexivity | reflexivity ]
end.
Ltac untouched_tac HS HE G3 G4 G25 G26 G27 :=
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)|];
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)|];
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)|];
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)|];
reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27).
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Hypothesis CLOSE : close_specX API.
Hypothesis ADDF : addframe_specX API.
Hypothesis UNLINK : unlink_x src0_msyms MR src0_A_unlink.
Hypothesis RFC : rfc_specX API.
Hypothesis NEWGIF : newgif_x API.
Variables (regs : bvmap 5 word) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (b0 : rbound) (plen : Z) (K : lleaf -> TSet).
Hypothesis HSORT : Fs.fs_sorted (m_fs md) = true.
Hypothesis HK : forall fs' c', leaf_post API regs L A mem md (ff_delta plen b0) fs' c' -> realizes src0segs c' (K (LL 0 fs' [])).
Hypothesis HROOM : ff_room b0 plen.
Hypothesis HFD : fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None.
Definition lh_case_x (C : Z -> Prop) : Prop :=
forall (p n : Z) (PAYLOAD : list Z),
C n ->
fn_pre src0_msyms MR LIB_STACK L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> 0 < n -> In (p, n) (blocks L A) ->
sink_none src0_msyms mem md -> spZ regs <= 2 ^ 47 ->
garr8 src0segs mem p PAYLOAD -> Z.of_nat (length PAYLOAD) = n ->
res_ok A b0 ->
realizes src0segs (mkCfg (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom src0segs)) md) (ff_tree K (m_fs md) PAYLOAD).
Lemma lh_case_5 : lh_case_x (fun n => 14 <= n).
Proof.
intros p n PAYLOAD HC HPRE Hid G10 G11 Hn Hpn HSN0 Hsp47 HPL HPLn HRES0. apply realizes_via_SR.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HLSv : LIB_STACK = 16384) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
destruct (blocks_range _ _ LAWS L A mem md p n HH Hpn) as [Hp0 Hp1].
assert (Hpres : forall i, 0 <= i < n -> present mem (p + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS L A mem md p n i HH Hpn Hi)). }
set (bvals := map (fun i => byte_at mem (p + Z.of_nat i)) (seq 0 14)).
set (E := Ereg regs (map (Z_to_bv 64) bvals ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error bvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HB : forall j, (j < 14)%nat -> ew E (32 + j) = Z_to_bv 64 (byte_at mem (p + Z.of_nat j))).
{ intros j Hj. apply HX. subst bvals. rewrite nth_error_map, nth_error_seq. rewrite (proj2 (Nat.ltb_lt j 14) Hj). reflexivity. }
assert (HBr : forall j, (j < 14)%nat -> 0 <= bv_unsigned (ew E (32 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range mem (p + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = p) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = n) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HS : st_ok src0segs E (ss_lh 5) (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom src0segs))).
{ unfold ss_lh. replace src0_A_LLVMFuzzerTestOneInput with LLVM by reflexivity. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- cbn [lh_breg lh_cnt nth app]. constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. apply Hstw. lia.
+ apply (region_ok_stack src0segs _ mem 2 sp0); [exact HU2 | lia | lia |]. intros a Ha. apply Hstw. lia.
+ apply (region_ok_bytes _ mem 10 p 14 32); [exact HU10 | lia | lia |].
intros j Hj. split; [apply HB; exact Hj|]. apply Hpres. lia.
- cbn [lh_breg lh_cnt nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, ?HU10. repeat split; lia.
- cbn [f_atoms lh_bfacts lh_cnt lh_lo lh_hi nth map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1. pose proof (HBr 2%nat ltac:(lia)) as B2. pose proof (HBr 3%nat ltac:(lia)) as B3. pose proof (HBr 4%nat ltac:(lia)) as B4. pose proof (HBr 5%nat ltac:(lia)) as B5. pose proof (HBr 6%nat ltac:(lia)) as B6. pose proof (HBr 7%nat ltac:(lia)) as B7. pose proof (HBr 8%nat ltac:(lia)) as B8. pose proof (HBr 9%nat ltac:(lia)) as B9. pose proof (HBr 10%nat ltac:(lia)) as B10. pose proof (HBr 11%nat ltac:(lia)) as B11. pose proof (HBr 12%nat ltac:(lia)) as B12. pose proof (HBr 13%nat ltac:(lia)) as B13.
cbn [Nat.add] in B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13.
repeat split; try lia; assumption. }
pose proof (journal_init src0_msyms MR LIB_STACK [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom src0segs))) in HJ. fold sp0 in HJ.
jrun_to LAWS src0tbl_ok HS HJ src0_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ eapply (jmemset src0_msyms MR LAWS IMG src0_A_memset src0_memset_spec E _ _ LIB_STACK sp0 [] L A mem md L A _ (sp0 - 128) 0 48);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 128) with (sp0 + -128) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
jafter_stretch_keep HS 46%nat regs2 mem2 MEMSET_CLOB L_HDR0 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU10; lia | cbn [r_base r_hi base_val]; rewrite HU10; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU10; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
add_region HS (YP09.mkRegion (Some 2%nat) (-128) (-80) (-128) (-80) [mkChunk (-128) (CZero 48)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (writable_at_grows src0segs (ms_mem ms) mem2); [exact Hgr2|]. cbn [ms_mem mkst] in HG. apply (writable_at_grows src0segs mem (ms_mem ms)); [exact HG|]. apply Hstw. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off]. intros i Hi.
replace (sp0 + -128 + i) with (sp0 - 128 + i) by lia. apply Hzero2. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, ?HU10. repeat split; lia. }
jrun_to LAWS src0tbl_ok HS HJ2 L_TAIL.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (HB0 : ew E 32 = Z_to_bv 64 (byte_at mem (p + 0))) by (etransitivity; [apply (HB 0%nat); lia | f_equal; f_equal; lia]).
assert (HB1 : ew E 33 = Z_to_bv 64 (byte_at mem (p + 1))) by (etransitivity; [apply (HB 1%nat); lia | f_equal; f_equal; lia]).
assert (HB2 : ew E 34 = Z_to_bv 64 (byte_at mem (p + 2))) by (etransitivity; [apply (HB 2%nat); lia | f_equal; f_equal; lia]).
assert (HB3 : ew E 35 = Z_to_bv 64 (byte_at mem (p + 3))) by (etransitivity; [apply (HB 3%nat); lia | f_equal; f_equal; lia]).
assert (HB4 : ew E 36 = Z_to_bv 64 (byte_at mem (p + 4))) by (etransitivity; [apply (HB 4%nat); lia | f_equal; f_equal; lia]).
assert (HB5 : ew E 37 = Z_to_bv 64 (byte_at mem (p + 5))) by (etransitivity; [apply (HB 5%nat); lia | f_equal; f_equal; lia]).
assert (HB6 : ew E 38 = Z_to_bv 64 (byte_at mem (p + 6))) by (etransitivity; [apply (HB 6%nat); lia | f_equal; f_equal; lia]).
assert (HB7 : ew E 39 = Z_to_bv 64 (byte_at mem (p + 7))) by (etransitivity; [apply (HB 7%nat); lia | f_equal; f_equal; lia]).
assert (HB8 : ew E 40 = Z_to_bv 64 (byte_at mem (p + 8))) by (etransitivity; [apply (HB 8%nat); lia | f_equal; f_equal; lia]).
assert (HB9 : ew E 41 = Z_to_bv 64 (byte_at mem (p + 9))) by (etransitivity; [apply (HB 9%nat); lia | f_equal; f_equal; lia]).
assert (HB10 : ew E 42 = Z_to_bv 64 (byte_at mem (p + 10))) by (etransitivity; [apply (HB 10%nat); lia | f_equal; f_equal; lia]).
assert (HB11 : ew E 43 = Z_to_bv 64 (byte_at mem (p + 11))) by (etransitivity; [apply (HB 11%nat); lia | f_equal; f_equal; lia]).
assert (HB12 : ew E 44 = Z_to_bv 64 (byte_at mem (p + 12))) by (etransitivity; [apply (HB 12%nat); lia | f_equal; f_equal; lia]).
assert (HB13 : ew E 45 = Z_to_bv 64 (byte_at mem (p + 13))) by (etransitivity; [apply (HB 13%nat); lia | f_equal; f_equal; lia]).
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_tail_x API IMG CLOSE ADDF UNLINK RFC NEWGIF regs L A mem md b0 plen K HSORT HK HROOM HFD rg L A mm md p n 0 14 _ _ _ (byte_at mem (p + 0) + 256 * byte_at mem (p + 1)) (byte_at mem (p + 2) + 256 * byte_at mem (p + 3)) (byte_at mem (p + 12) + 256 * byte_at mem (p + 13)) _ _ PAYLOAD) end.
+ exact HJ2. + exact Hid. + exact Hra. + exact Htp. + exact Hal16. + exact Hpn. + exact Hn. + apply Permutation_refl.
+ reflexivity.
+ fold sp0. cbn [obj_at LAY_Config]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
try change (2 ^ (8 * 8)) with 18446744073709551616. try change (2 ^ (8 * 4)) with 4294967296.
try change (2 ^ (8 * 2)) with 65536.
try change (N.to_nat 8) with 8%nat. try change (N.to_nat 4) with 4%nat. try change (N.to_nat 2) with 2%nat.
pose proof (byte_at_range mem (p + 0)) as R0. pose proof (byte_at_range mem (p + 1)) as R1. pose proof (byte_at_range mem (p + 2)) as R2. pose proof (byte_at_range mem (p + 3)) as R3. pose proof (byte_at_range mem (p + 12)) as R12. pose proof (byte_at_range mem (p + 13)) as R13.
repeat match goal with |- _ /\ _ => split end;
first [ cfg_zero HS HU2 (-128) 16
| cfg_zero HS HU2 (-128) 24
| cfg_zero HS HU2 (-128) 48
| cfg_zero HS HU2 (-98) 18
| cfg_zero HS HU2 (-100) 20
| cfg_zero HS HU2 (-102) 22
| cfg_zero HS HU2 (-108) 4
| cfg_val2 HS HU2 33%nat 32%nat HB1 HB0
| cfg_val2 HS HU2 35%nat 34%nat HB3 HB2
| cfg_val2 HS HU2 45%nat 44%nat HB13 HB12
| cfg_low4 HS HU2
| lia
| match goal with |- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)); lia end
| match goal with |- ?G => idtac "CFGLEFT"; idtac G end ].
+ fold sp0. unfold saved_ok.
repeat match goal with |- _ /\ _ => split end;
first [ frame_wordI HS 2%nat HU2 HE 1%nat (1%bv:reg) | frame_wordI HS 2%nat HU2 HE 8%nat (8%bv:reg)
| frame_wordI HS 2%nat HU2 HE 9%nat (9%bv:reg) | frame_wordI HS 2%nat HU2 HE 18%nat (18%bv:reg)
| frame_wordI HS 2%nat HU2 HE 19%nat (19%bv:reg) | frame_wordI HS 2%nat HU2 HE 20%nat (20%bv:reg)
| frame_wordI HS 2%nat HU2 HE 21%nat (21%bv:reg) | frame_wordI HS 2%nat HU2 HE 22%nat (22%bv:reg)
| frame_wordI HS 2%nat HU2 HE 23%nat (23%bv:reg) | frame_wordI HS 2%nat HU2 HE 24%nat (24%bv:reg) ].
+ fold sp0. replace (sp0 - 184) with (sp0 + -184) by lia.
eapply (st_chunk_word _ _ _ 1%nat _ 2%nat (-184) (SOff 10 0) sp0 p HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HU10; reflexivity | lia].
+ fold sp0. replace (sp0 - 176) with (sp0 + -176) by lia.
eapply (st_chunk_word _ _ _ 1%nat _ 2%nat (-176) (SOff 11 0) sp0 n HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HU11; reflexivity | lia].
+ lia.
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ reg_nowF HS ltac:(rewrite HU11; reflexivity).
+ reg_nowF HS ltac:(rewrite HU10; reflexivity).
+ lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in pose proof (st_ok_reg src0segs Ec ssc msc 10%bv HS) as T; eval_sr_get_in T;
rewrite denot_flag4 in T; exact T end.
+ lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in pose proof (st_ok_reg src0segs Ec ssc msc 19%bv HS) as T; eval_sr_get_in T;
rewrite (denot_pal3 _ 45 44 (byte_at mem (p + 13)) (byte_at mem (p + 12))) in T;
[ exact T | ew_havocA; exact HB13 | ew_havocA; exact HB12 | apply byte_at_range | apply byte_at_range ] end.
+ lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in pose proof (st_ok_reg src0segs Ec ssc msc 20%bv HS) as T; eval_sr_get_in T;
rewrite (denot_or_shl8 _ 33 32 (byte_at mem (p + 1)) (byte_at mem (p + 0))) in T;
[ exact T | ew_havocA; exact HB1 | ew_havocA; exact HB0 | apply byte_at_range | apply byte_at_range ] end.
+ lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in pose proof (st_ok_reg src0segs Ec ssc msc 21%bv HS) as T; eval_sr_get_in T;
rewrite (denot_or_shl8 _ 35 34 (byte_at mem (p + 3)) (byte_at mem (p + 2))) in T;
[ exact T | ew_havocA; exact HB3 | ew_havocA; exact HB2 | apply byte_at_range | apply byte_at_range ] end.
+ reg_nowF HS ltac:(reflexivity).
+ split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ lia.
+ lia.
+ exact HSN0. + exact Hsp47. + exact HPL. + exact HPLn.
+ intros _ _. split; [reflexivity|].
rewrite hdr5_bytes by lia. rewrite !(garr8_byte_at mem p PAYLOAD) by (exact HPL || lia).
change (Z.of_nat 0) with 0. change (Z.of_nat 1) with 1. change (Z.of_nat 2) with 2. change (Z.of_nat 3) with 3.
change (Z.of_nat 4) with 4. change (Z.of_nat 5) with 5. change (Z.of_nat 6) with 6. change (Z.of_nat 7) with 7.
change (Z.of_nat 8) with 8. change (Z.of_nat 9) with 9. change (Z.of_nat 10) with 10. change (Z.of_nat 11) with 11.
change (Z.of_nat 12) with 12. change (Z.of_nat 13) with 13.
rewrite (U_le4_mod32 _ 39%nat 38%nat 37%nat 36%nat (byte_at mem (p + 7)) (byte_at mem (p + 6)) (byte_at mem (p + 5)) (byte_at mem (p + 4)));
[| ew_havocA; exact HB7 | ew_havocA; exact HB6 | ew_havocA; exact HB5 | ew_havocA; exact HB4 | apply byte_at_range | apply byte_at_range | apply byte_at_range | apply byte_at_range].
rewrite (U_le4_mod32 _ 43%nat 42%nat 41%nat 40%nat (byte_at mem (p + 11)) (byte_at mem (p + 10)) (byte_at mem (p + 9)) (byte_at mem (p + 8)));
[| ew_havocA; exact HB11 | ew_havocA; exact HB10 | ew_havocA; exact HB9 | ew_havocA; exact HB8 | apply byte_at_range | apply byte_at_range | apply byte_at_range | apply byte_at_range].
reflexivity.
+ intros _. split; reflexivity.
+ exact HRES0.
Qed.
Lemma lh_case_4 : lh_case_x (fun n => 12 <= n < 14).
Proof.
intros p n PAYLOAD HC HPRE Hid G10 G11 Hn Hpn HSN0 Hsp47 HPL HPLn HRES0. apply realizes_via_SR.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HLSv : LIB_STACK = 16384) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
destruct (blocks_range _ _ LAWS L A mem md p n HH Hpn) as [Hp0 Hp1].
assert (Hpres : forall i, 0 <= i < n -> present mem (p + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS L A mem md p n i HH Hpn Hi)). }
set (bvals := map (fun i => byte_at mem (p + Z.of_nat i)) (seq 0 12)).
set (E := Ereg regs (map (Z_to_bv 64) bvals ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error bvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HB : forall j, (j < 12)%nat -> ew E (32 + j) = Z_to_bv 64 (byte_at mem (p + Z.of_nat j))).
{ intros j Hj. apply HX. subst bvals. rewrite nth_error_map, nth_error_seq. rewrite (proj2 (Nat.ltb_lt j 12) Hj). reflexivity. }
assert (HBr : forall j, (j < 12)%nat -> 0 <= bv_unsigned (ew E (32 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range mem (p + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = p) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = n) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HS : st_ok src0segs E (ss_lh 4) (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom src0segs))).
{ unfold ss_lh. replace src0_A_LLVMFuzzerTestOneInput with LLVM by reflexivity. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- cbn [lh_breg lh_cnt nth app]. constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. apply Hstw. lia.
+ apply (region_ok_stack src0segs _ mem 2 sp0); [exact HU2 | lia | lia |]. intros a Ha. apply Hstw. lia.
+ apply (region_ok_bytes _ mem 10 p 12 32); [exact HU10 | lia | lia |].
intros j Hj. split; [apply HB; exact Hj|]. apply Hpres. lia.
- cbn [lh_breg lh_cnt nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, ?HU10. repeat split; lia.
- cbn [f_atoms lh_bfacts lh_cnt lh_lo lh_hi nth map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1. pose proof (HBr 2%nat ltac:(lia)) as B2. pose proof (HBr 3%nat ltac:(lia)) as B3. pose proof (HBr 4%nat ltac:(lia)) as B4. pose proof (HBr 5%nat ltac:(lia)) as B5. pose proof (HBr 6%nat ltac:(lia)) as B6. pose proof (HBr 7%nat ltac:(lia)) as B7. pose proof (HBr 8%nat ltac:(lia)) as B8. pose proof (HBr 9%nat ltac:(lia)) as B9. pose proof (HBr 10%nat ltac:(lia)) as B10. pose proof (HBr 11%nat ltac:(lia)) as B11.
cbn [Nat.add] in B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11.
repeat split; try lia; assumption. }
pose proof (journal_init src0_msyms MR LIB_STACK [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom src0segs))) in HJ. fold sp0 in HJ.
jrun_to LAWS src0tbl_ok HS HJ src0_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ eapply (jmemset src0_msyms MR LAWS IMG src0_A_memset src0_memset_spec E _ _ LIB_STACK sp0 [] L A mem md L A _ (sp0 - 128) 0 48);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 128) with (sp0 + -128) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
jafter_stretch_keep HS 46%nat regs2 mem2 MEMSET_CLOB L_HDR0 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU10; lia | cbn [r_base r_hi base_val]; rewrite HU10; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU10; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
add_region HS (YP09.mkRegion (Some 2%nat) (-128) (-80) (-128) (-80) [mkChunk (-128) (CZero 48)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (writable_at_grows src0segs (ms_mem ms) mem2); [exact Hgr2|]. cbn [ms_mem mkst] in HG. apply (writable_at_grows src0segs mem (ms_mem ms)); [exact HG|]. apply Hstw. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off]. intros i Hi.
replace (sp0 + -128 + i) with (sp0 - 128 + i) by lia. apply Hzero2. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, ?HU10. repeat split; lia. }
jrun_to LAWS src0tbl_ok HS HJ2 L_TAIL.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (HB0 : ew E 32 = Z_to_bv 64 (byte_at mem (p + 0))) by (etransitivity; [apply (HB 0%nat); lia | f_equal; f_equal; lia]).
assert (HB1 : ew E 33 = Z_to_bv 64 (byte_at mem (p + 1))) by (etransitivity; [apply (HB 1%nat); lia | f_equal; f_equal; lia]).
assert (HB2 : ew E 34 = Z_to_bv 64 (byte_at mem (p + 2))) by (etransitivity; [apply (HB 2%nat); lia | f_equal; f_equal; lia]).
assert (HB3 : ew E 35 = Z_to_bv 64 (byte_at mem (p + 3))) by (etransitivity; [apply (HB 3%nat); lia | f_equal; f_equal; lia]).
assert (HB4 : ew E 36 = Z_to_bv 64 (byte_at mem (p + 4))) by (etransitivity; [apply (HB 4%nat); lia | f_equal; f_equal; lia]).
assert (HB5 : ew E 37 = Z_to_bv 64 (byte_at mem (p + 5))) by (etransitivity; [apply (HB 5%nat); lia | f_equal; f_equal; lia]).
assert (HB6 : ew E 38 = Z_to_bv 64 (byte_at mem (p + 6))) by (etransitivity; [apply (HB 6%nat); lia | f_equal; f_equal; lia]).
assert (HB7 : ew E 39 = Z_to_bv 64 (byte_at mem (p + 7))) by (etransitivity; [apply (HB 7%nat); lia | f_equal; f_equal; lia]).
assert (HB8 : ew E 40 = Z_to_bv 64 (byte_at mem (p + 8))) by (etransitivity; [apply (HB 8%nat); lia | f_equal; f_equal; lia]).
assert (HB9 : ew E 41 = Z_to_bv 64 (byte_at mem (p + 9))) by (etransitivity; [apply (HB 9%nat); lia | f_equal; f_equal; lia]).
assert (HB10 : ew E 42 = Z_to_bv 64 (byte_at mem (p + 10))) by (etransitivity; [apply (HB 10%nat); lia | f_equal; f_equal; lia]).
assert (HB11 : ew E 43 = Z_to_bv 64 (byte_at mem (p + 11))) by (etransitivity; [apply (HB 11%nat); lia | f_equal; f_equal; lia]).
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_tail_x API IMG CLOSE ADDF UNLINK RFC NEWGIF regs L A mem md b0 plen K HSORT HK HROOM HFD rg L A mm md p n 0 n _ _ _ (byte_at mem (p + 0) + 256 * byte_at mem (p + 1)) (byte_at mem (p + 2) + 256 * byte_at mem (p + 3)) 0 _ _ PAYLOAD) end.
+ exact HJ2. + exact Hid. + exact Hra. + exact Htp. + exact Hal16. + exact Hpn. + exact Hn. + apply Permutation_refl.
+ reflexivity.
+ fold sp0. cbn [obj_at LAY_Config]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
try change (2 ^ (8 * 8)) with 18446744073709551616. try change (2 ^ (8 * 4)) with 4294967296.
try change (2 ^ (8 * 2)) with 65536.
try change (N.to_nat 8) with 8%nat. try change (N.to_nat 4) with 4%nat. try change (N.to_nat 2) with 2%nat.
pose proof (byte_at_range mem (p + 0)) as R0. pose proof (byte_at_range mem (p + 1)) as R1. pose proof (byte_at_range mem (p + 2)) as R2. pose proof (byte_at_range mem (p + 3)) as R3.
repeat match goal with |- _ /\ _ => split end;
first [ cfg_zero HS HU2 (-128) 16
| cfg_zero HS HU2 (-128) 24
| cfg_zero HS HU2 (-128) 48
| cfg_zero HS HU2 (-98) 18
| cfg_zero HS HU2 (-100) 20
| cfg_zero HS HU2 (-102) 22
| cfg_zero HS HU2 (-108) 4
| cfg_val2 HS HU2 33%nat 32%nat HB1 HB0
| cfg_val2 HS HU2 35%nat 34%nat HB3 HB2
| cfg_low4 HS HU2
| lia
| match goal with |- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)); lia end
| match goal with |- ?G => idtac "CFGLEFT"; idtac G end ].
+ fold sp0. unfold saved_ok.
repeat match goal with |- _ /\ _ => split end;
first [ frame_wordI HS 2%nat HU2 HE 1%nat (1%bv:reg) | frame_wordI HS 2%nat HU2 HE 8%nat (8%bv:reg)
| frame_wordI HS 2%nat HU2 HE 9%nat (9%bv:reg) | frame_wordI HS 2%nat HU2 HE 18%nat (18%bv:reg)
| frame_wordI HS 2%nat HU2 HE 19%nat (19%bv:reg) | frame_wordI HS 2%nat HU2 HE 20%nat (20%bv:reg)
| frame_wordI HS 2%nat HU2 HE 21%nat (21%bv:reg) | frame_wordI HS 2%nat HU2 HE 22%nat (22%bv:reg)
| frame_wordI HS 2%nat HU2 HE 23%nat (23%bv:reg) | frame_wordI HS 2%nat HU2 HE 24%nat (24%bv:reg) ].
+ fold sp0. replace (sp0 - 184) with (sp0 + -184) by lia.
eapply (st_chunk_word _ _ _ 1%nat _ 2%nat (-184) (SOff 10 0) sp0 p HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HU10; reflexivity | lia].
+ fold sp0. replace (sp0 - 176) with (sp0 + -176) by lia.
eapply (st_chunk_word _ _ _ 1%nat _ 2%nat (-176) (SOff 11 0) sp0 n HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HU11; reflexivity | lia].
+ lia.
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ reg_nowF HS ltac:(rewrite HU11; reflexivity).
+ reg_nowF HS ltac:(rewrite HU10; reflexivity).
+ lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in pose proof (st_ok_reg src0segs Ec ssc msc 10%bv HS) as T; eval_sr_get_in T;
rewrite denot_flag4 in T; exact T end.
+ reg_nowF HS ltac:(reflexivity).
+ lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in pose proof (st_ok_reg src0segs Ec ssc msc 20%bv HS) as T; eval_sr_get_in T;
rewrite (denot_or_shl8 _ 33 32 (byte_at mem (p + 1)) (byte_at mem (p + 0))) in T;
[ exact T | ew_havocA; exact HB1 | ew_havocA; exact HB0 | apply byte_at_range | apply byte_at_range ] end.
+ lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in pose proof (st_ok_reg src0segs Ec ssc msc 21%bv HS) as T; eval_sr_get_in T;
rewrite (denot_or_shl8 _ 35 34 (byte_at mem (p + 3)) (byte_at mem (p + 2))) in T;
[ exact T | ew_havocA; exact HB3 | ew_havocA; exact HB2 | apply byte_at_range | apply byte_at_range ] end.
+ reg_nowF HS ltac:(rewrite HU11; reflexivity).
+ split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ lia.
+ lia.
+ exact HSN0. + exact Hsp47. + exact HPL. + exact HPLn.
+ intros E1 E2. exfalso. lia.
+ intros Hge. exfalso. clear - Hge HC HPLn. lia.
+ exact HRES0.
Qed.
Lemma lh_case_3 : lh_case_x (fun n => 8 <= n < 12).
Proof.
intros p n PAYLOAD HC HPRE Hid G10 G11 Hn Hpn HSN0 Hsp47 HPL HPLn HRES0. apply realizes_via_SR.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HLSv : LIB_STACK = 16384) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
destruct (blocks_range _ _ LAWS L A mem md p n HH Hpn) as [Hp0 Hp1].
assert (Hpres : forall i, 0 <= i < n -> present mem (p + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS L A mem md p n i HH Hpn Hi)). }
set (bvals := map (fun i => byte_at mem (p + Z.of_nat i)) (seq 0 8)).
set (E := Ereg regs (map (Z_to_bv 64) bvals ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error bvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HB : forall j, (j < 8)%nat -> ew E (32 + j) = Z_to_bv 64 (byte_at mem (p + Z.of_nat j))).
{ intros j Hj. apply HX. subst bvals. rewrite nth_error_map, nth_error_seq. rewrite (proj2 (Nat.ltb_lt j 8) Hj). reflexivity. }
assert (HBr : forall j, (j < 8)%nat -> 0 <= bv_unsigned (ew E (32 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range mem (p + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = p) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = n) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HS : st_ok src0segs E (ss_lh 3) (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom src0segs))).
{ unfold ss_lh. replace src0_A_LLVMFuzzerTestOneInput with LLVM by reflexivity. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- cbn [lh_breg lh_cnt nth app]. constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. apply Hstw. lia.
+ apply (region_ok_stack src0segs _ mem 2 sp0); [exact HU2 | lia | lia |]. intros a Ha. apply Hstw. lia.
+ apply (region_ok_bytes _ mem 10 p 8 32); [exact HU10 | lia | lia |].
intros j Hj. split; [apply HB; exact Hj|]. apply Hpres. lia.
- cbn [lh_breg lh_cnt nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, ?HU10. repeat split; lia.
- cbn [f_atoms lh_bfacts lh_cnt lh_lo lh_hi nth map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1. pose proof (HBr 2%nat ltac:(lia)) as B2. pose proof (HBr 3%nat ltac:(lia)) as B3. pose proof (HBr 4%nat ltac:(lia)) as B4. pose proof (HBr 5%nat ltac:(lia)) as B5. pose proof (HBr 6%nat ltac:(lia)) as B6. pose proof (HBr 7%nat ltac:(lia)) as B7.
cbn [Nat.add] in B0, B1, B2, B3, B4, B5, B6, B7.
repeat split; try lia; assumption. }
pose proof (journal_init src0_msyms MR LIB_STACK [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom src0segs))) in HJ. fold sp0 in HJ.
jrun_to LAWS src0tbl_ok HS HJ src0_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ eapply (jmemset src0_msyms MR LAWS IMG src0_A_memset src0_memset_spec E _ _ LIB_STACK sp0 [] L A mem md L A _ (sp0 - 128) 0 48);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 128) with (sp0 + -128) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
jafter_stretch_keep HS 46%nat regs2 mem2 MEMSET_CLOB L_HDR0 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU10; lia | cbn [r_base r_hi base_val]; rewrite HU10; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU10; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
add_region HS (YP09.mkRegion (Some 2%nat) (-128) (-80) (-128) (-80) [mkChunk (-128) (CZero 48)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (writable_at_grows src0segs (ms_mem ms) mem2); [exact Hgr2|]. cbn [ms_mem mkst] in HG. apply (writable_at_grows src0segs mem (ms_mem ms)); [exact HG|]. apply Hstw. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off]. intros i Hi.
replace (sp0 + -128 + i) with (sp0 - 128 + i) by lia. apply Hzero2. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, ?HU10. repeat split; lia. }
jrun_to LAWS src0tbl_ok HS HJ2 L_TAIL.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (HB0 : ew E 32 = Z_to_bv 64 (byte_at mem (p + 0))) by (etransitivity; [apply (HB 0%nat); lia | f_equal; f_equal; lia]).
assert (HB1 : ew E 33 = Z_to_bv 64 (byte_at mem (p + 1))) by (etransitivity; [apply (HB 1%nat); lia | f_equal; f_equal; lia]).
assert (HB2 : ew E 34 = Z_to_bv 64 (byte_at mem (p + 2))) by (etransitivity; [apply (HB 2%nat); lia | f_equal; f_equal; lia]).
assert (HB3 : ew E 35 = Z_to_bv 64 (byte_at mem (p + 3))) by (etransitivity; [apply (HB 3%nat); lia | f_equal; f_equal; lia]).
assert (HB4 : ew E 36 = Z_to_bv 64 (byte_at mem (p + 4))) by (etransitivity; [apply (HB 4%nat); lia | f_equal; f_equal; lia]).
assert (HB5 : ew E 37 = Z_to_bv 64 (byte_at mem (p + 5))) by (etransitivity; [apply (HB 5%nat); lia | f_equal; f_equal; lia]).
assert (HB6 : ew E 38 = Z_to_bv 64 (byte_at mem (p + 6))) by (etransitivity; [apply (HB 6%nat); lia | f_equal; f_equal; lia]).
assert (HB7 : ew E 39 = Z_to_bv 64 (byte_at mem (p + 7))) by (etransitivity; [apply (HB 7%nat); lia | f_equal; f_equal; lia]).
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_tail_x API IMG CLOSE ADDF UNLINK RFC NEWGIF regs L A mem md b0 plen K HSORT HK HROOM HFD rg L A mm md p n 0 n _ _ _ (byte_at mem (p + 0) + 256 * byte_at mem (p + 1)) (byte_at mem (p + 2) + 256 * byte_at mem (p + 3)) 0 _ _ PAYLOAD) end.
+ exact HJ2. + exact Hid. + exact Hra. + exact Htp. + exact Hal16. + exact Hpn. + exact Hn. + apply Permutation_refl.
+ reflexivity.
+ fold sp0. cbn [obj_at LAY_Config]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
try change (2 ^ (8 * 8)) with 18446744073709551616. try change (2 ^ (8 * 4)) with 4294967296.
try change (2 ^ (8 * 2)) with 65536.
try change (N.to_nat 8) with 8%nat. try change (N.to_nat 4) with 4%nat. try change (N.to_nat 2) with 2%nat.
pose proof (byte_at_range mem (p + 0)) as R0. pose proof (byte_at_range mem (p + 1)) as R1. pose proof (byte_at_range mem (p + 2)) as R2. pose proof (byte_at_range mem (p + 3)) as R3.
repeat match goal with |- _ /\ _ => split end;
first [ cfg_zero HS HU2 (-128) 16
| cfg_zero HS HU2 (-128) 24
| cfg_zero HS HU2 (-128) 48
| cfg_zero HS HU2 (-98) 18
| cfg_zero HS HU2 (-100) 20
| cfg_zero HS HU2 (-102) 22
| cfg_zero HS HU2 (-108) 4
| cfg_val2 HS HU2 33%nat 32%nat HB1 HB0
| cfg_val2 HS HU2 35%nat 34%nat HB3 HB2
| cfg_low4 HS HU2
| lia
| match goal with |- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)); lia end
| match goal with |- ?G => idtac "CFGLEFT"; idtac G end ].
+ fold sp0. unfold saved_ok.
repeat match goal with |- _ /\ _ => split end;
first [ frame_wordI HS 2%nat HU2 HE 1%nat (1%bv:reg) | frame_wordI HS 2%nat HU2 HE 8%nat (8%bv:reg)
| frame_wordI HS 2%nat HU2 HE 9%nat (9%bv:reg) | frame_wordI HS 2%nat HU2 HE 18%nat (18%bv:reg)
| frame_wordI HS 2%nat HU2 HE 19%nat (19%bv:reg) | frame_wordI HS 2%nat HU2 HE 20%nat (20%bv:reg)
| frame_wordI HS 2%nat HU2 HE 21%nat (21%bv:reg) | frame_wordI HS 2%nat HU2 HE 22%nat (22%bv:reg)
| frame_wordI HS 2%nat HU2 HE 23%nat (23%bv:reg) | frame_wordI HS 2%nat HU2 HE 24%nat (24%bv:reg) ].
+ fold sp0. replace (sp0 - 184) with (sp0 + -184) by lia.
eapply (st_chunk_word _ _ _ 1%nat _ 2%nat (-184) (SOff 10 0) sp0 p HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HU10; reflexivity | lia].
+ fold sp0. replace (sp0 - 176) with (sp0 + -176) by lia.
eapply (st_chunk_word _ _ _ 1%nat _ 2%nat (-176) (SOff 11 0) sp0 n HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HU11; reflexivity | lia].
+ lia.
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ reg_nowF HS ltac:(rewrite HU11; reflexivity).
+ reg_nowF HS ltac:(rewrite HU10; reflexivity).
+ lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in pose proof (st_ok_reg src0segs Ec ssc msc 10%bv HS) as T; eval_sr_get_in T;
rewrite denot_flag4 in T; exact T end.
+ reg_nowF HS ltac:(reflexivity).
+ lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in pose proof (st_ok_reg src0segs Ec ssc msc 20%bv HS) as T; eval_sr_get_in T;
rewrite (denot_or_shl8 _ 33 32 (byte_at mem (p + 1)) (byte_at mem (p + 0))) in T;
[ exact T | ew_havocA; exact HB1 | ew_havocA; exact HB0 | apply byte_at_range | apply byte_at_range ] end.
+ lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in pose proof (st_ok_reg src0segs Ec ssc msc 21%bv HS) as T; eval_sr_get_in T;
rewrite (denot_or_shl8 _ 35 34 (byte_at mem (p + 3)) (byte_at mem (p + 2))) in T;
[ exact T | ew_havocA; exact HB3 | ew_havocA; exact HB2 | apply byte_at_range | apply byte_at_range ] end.
+ reg_nowF HS ltac:(rewrite HU11; reflexivity).
+ split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ lia.
+ lia.
+ exact HSN0. + exact Hsp47. + exact HPL. + exact HPLn.
+ intros E1 E2. exfalso. lia.
+ intros Hge. exfalso. clear - Hge HC HPLn. lia.
+ exact HRES0.
Qed.
Lemma lh_case_2 : lh_case_x (fun n => 4 <= n < 8).
Proof.
intros p n PAYLOAD HC HPRE Hid G10 G11 Hn Hpn HSN0 Hsp47 HPL HPLn HRES0. apply realizes_via_SR.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HLSv : LIB_STACK = 16384) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
destruct (blocks_range _ _ LAWS L A mem md p n HH Hpn) as [Hp0 Hp1].
assert (Hpres : forall i, 0 <= i < n -> present mem (p + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS L A mem md p n i HH Hpn Hi)). }
set (bvals := map (fun i => byte_at mem (p + Z.of_nat i)) (seq 0 4)).
set (E := Ereg regs (map (Z_to_bv 64) bvals ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error bvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HB : forall j, (j < 4)%nat -> ew E (32 + j) = Z_to_bv 64 (byte_at mem (p + Z.of_nat j))).
{ intros j Hj. apply HX. subst bvals. rewrite nth_error_map, nth_error_seq. rewrite (proj2 (Nat.ltb_lt j 4) Hj). reflexivity. }
assert (HBr : forall j, (j < 4)%nat -> 0 <= bv_unsigned (ew E (32 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range mem (p + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = p) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = n) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HS : st_ok src0segs E (ss_lh 2) (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom src0segs))).
{ unfold ss_lh. replace src0_A_LLVMFuzzerTestOneInput with LLVM by reflexivity. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- cbn [lh_breg lh_cnt nth app]. constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. apply Hstw. lia.
+ apply (region_ok_stack src0segs _ mem 2 sp0); [exact HU2 | lia | lia |]. intros a Ha. apply Hstw. lia.
+ apply (region_ok_bytes _ mem 10 p 4 32); [exact HU10 | lia | lia |].
intros j Hj. split; [apply HB; exact Hj|]. apply Hpres. lia.
- cbn [lh_breg lh_cnt nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, ?HU10. repeat split; lia.
- cbn [f_atoms lh_bfacts lh_cnt lh_lo lh_hi nth map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1. pose proof (HBr 2%nat ltac:(lia)) as B2. pose proof (HBr 3%nat ltac:(lia)) as B3.
cbn [Nat.add] in B0, B1, B2, B3.
repeat split; try lia; assumption. }
pose proof (journal_init src0_msyms MR LIB_STACK [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom src0segs))) in HJ. fold sp0 in HJ.
jrun_to LAWS src0tbl_ok HS HJ src0_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ eapply (jmemset src0_msyms MR LAWS IMG src0_A_memset src0_memset_spec E _ _ LIB_STACK sp0 [] L A mem md L A _ (sp0 - 128) 0 48);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 128) with (sp0 + -128) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
jafter_stretch_keep HS 46%nat regs2 mem2 MEMSET_CLOB L_HDR0 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU10; lia | cbn [r_base r_hi base_val]; rewrite HU10; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU10; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
add_region HS (YP09.mkRegion (Some 2%nat) (-128) (-80) (-128) (-80) [mkChunk (-128) (CZero 48)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (writable_at_grows src0segs (ms_mem ms) mem2); [exact Hgr2|]. cbn [ms_mem mkst] in HG. apply (writable_at_grows src0segs mem (ms_mem ms)); [exact HG|]. apply Hstw. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off]. intros i Hi.
replace (sp0 + -128 + i) with (sp0 - 128 + i) by lia. apply Hzero2. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, ?HU10. repeat split; lia. }
jrun_to LAWS src0tbl_ok HS HJ2 L_TAIL.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (HB0 : ew E 32 = Z_to_bv 64 (byte_at mem (p + 0))) by (etransitivity; [apply (HB 0%nat); lia | f_equal; f_equal; lia]).
assert (HB1 : ew E 33 = Z_to_bv 64 (byte_at mem (p + 1))) by (etransitivity; [apply (HB 1%nat); lia | f_equal; f_equal; lia]).
assert (HB2 : ew E 34 = Z_to_bv 64 (byte_at mem (p + 2))) by (etransitivity; [apply (HB 2%nat); lia | f_equal; f_equal; lia]).
assert (HB3 : ew E 35 = Z_to_bv 64 (byte_at mem (p + 3))) by (etransitivity; [apply (HB 3%nat); lia | f_equal; f_equal; lia]).
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_tail_x API IMG CLOSE ADDF UNLINK RFC NEWGIF regs L A mem md b0 plen K HSORT HK HROOM HFD rg L A mm md p n 0 n _ _ _ (byte_at mem (p + 0) + 256 * byte_at mem (p + 1)) (byte_at mem (p + 2) + 256 * byte_at mem (p + 3)) 0 _ _ PAYLOAD) end.
+ exact HJ2. + exact Hid. + exact Hra. + exact Htp. + exact Hal16. + exact Hpn. + exact Hn. + apply Permutation_refl.
+ reflexivity.
+ fold sp0. cbn [obj_at LAY_Config]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
try change (2 ^ (8 * 8)) with 18446744073709551616. try change (2 ^ (8 * 4)) with 4294967296.
try change (2 ^ (8 * 2)) with 65536.
try change (N.to_nat 8) with 8%nat. try change (N.to_nat 4) with 4%nat. try change (N.to_nat 2) with 2%nat.
pose proof (byte_at_range mem (p + 0)) as R0. pose proof (byte_at_range mem (p + 1)) as R1. pose proof (byte_at_range mem (p + 2)) as R2. pose proof (byte_at_range mem (p + 3)) as R3.
repeat match goal with |- _ /\ _ => split end;
first [ cfg_zero HS HU2 (-128) 16
| cfg_zero HS HU2 (-128) 24
| cfg_zero HS HU2 (-128) 48
| cfg_zero HS HU2 (-98) 18
| cfg_zero HS HU2 (-100) 20
| cfg_zero HS HU2 (-102) 22
| cfg_zero HS HU2 (-108) 4
| cfg_val2 HS HU2 33%nat 32%nat HB1 HB0
| cfg_val2 HS HU2 35%nat 34%nat HB3 HB2
| cfg_low4 HS HU2
| lia
| match goal with |- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)); lia end
| match goal with |- ?G => idtac "CFGLEFT"; idtac G end ].
+ fold sp0. unfold saved_ok.
repeat match goal with |- _ /\ _ => split end;
first [ frame_wordI HS 2%nat HU2 HE 1%nat (1%bv:reg) | frame_wordI HS 2%nat HU2 HE 8%nat (8%bv:reg)
| frame_wordI HS 2%nat HU2 HE 9%nat (9%bv:reg) | frame_wordI HS 2%nat HU2 HE 18%nat (18%bv:reg)
| frame_wordI HS 2%nat HU2 HE 19%nat (19%bv:reg) | frame_wordI HS 2%nat HU2 HE 20%nat (20%bv:reg)
| frame_wordI HS 2%nat HU2 HE 21%nat (21%bv:reg) | frame_wordI HS 2%nat HU2 HE 22%nat (22%bv:reg)
| frame_wordI HS 2%nat HU2 HE 23%nat (23%bv:reg) | frame_wordI HS 2%nat HU2 HE 24%nat (24%bv:reg) ].
+ fold sp0. replace (sp0 - 184) with (sp0 + -184) by lia.
eapply (st_chunk_word _ _ _ 1%nat _ 2%nat (-184) (SOff 10 0) sp0 p HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HU10; reflexivity | lia].
+ fold sp0. replace (sp0 - 176) with (sp0 + -176) by lia.
eapply (st_chunk_word _ _ _ 1%nat _ 2%nat (-176) (SOff 11 0) sp0 n HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HU11; reflexivity | lia].
+ lia.
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ reg_nowF HS ltac:(rewrite HU11; reflexivity).
+ reg_nowF HS ltac:(rewrite HU10; reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in pose proof (st_ok_reg src0segs Ec ssc msc 20%bv HS) as T; eval_sr_get_in T;
rewrite (denot_or_shl8 _ 33 32 (byte_at mem (p + 1)) (byte_at mem (p + 0))) in T;
[ exact T | ew_havocA; exact HB1 | ew_havocA; exact HB0 | apply byte_at_range | apply byte_at_range ] end.
+ lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in pose proof (st_ok_reg src0segs Ec ssc msc 21%bv HS) as T; eval_sr_get_in T;
rewrite (denot_or_shl8 _ 35 34 (byte_at mem (p + 3)) (byte_at mem (p + 2))) in T;
[ exact T | ew_havocA; exact HB3 | ew_havocA; exact HB2 | apply byte_at_range | apply byte_at_range ] end.
+ reg_nowF HS ltac:(rewrite HU11; reflexivity).
+ split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ lia.
+ lia.
+ exact HSN0. + exact Hsp47. + exact HPL. + exact HPLn.
+ intros E1 E2. exfalso. lia.
+ intros Hge. exfalso. clear - Hge HC HPLn. lia.
+ exact HRES0.
Qed.
Lemma lh_case_1 : lh_case_x (fun n => 2 <= n < 4).
Proof.
intros p n PAYLOAD HC HPRE Hid G10 G11 Hn Hpn HSN0 Hsp47 HPL HPLn HRES0. apply realizes_via_SR.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HLSv : LIB_STACK = 16384) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
destruct (blocks_range _ _ LAWS L A mem md p n HH Hpn) as [Hp0 Hp1].
assert (Hpres : forall i, 0 <= i < n -> present mem (p + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS L A mem md p n i HH Hpn Hi)). }
set (bvals := map (fun i => byte_at mem (p + Z.of_nat i)) (seq 0 2)).
set (E := Ereg regs (map (Z_to_bv 64) bvals ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error bvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HB : forall j, (j < 2)%nat -> ew E (32 + j) = Z_to_bv 64 (byte_at mem (p + Z.of_nat j))).
{ intros j Hj. apply HX. subst bvals. rewrite nth_error_map, nth_error_seq. rewrite (proj2 (Nat.ltb_lt j 2) Hj). reflexivity. }
assert (HBr : forall j, (j < 2)%nat -> 0 <= bv_unsigned (ew E (32 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range mem (p + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = p) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = n) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HS : st_ok src0segs E (ss_lh 1) (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom src0segs))).
{ unfold ss_lh. replace src0_A_LLVMFuzzerTestOneInput with LLVM by reflexivity. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- cbn [lh_breg lh_cnt nth app]. constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. apply Hstw. lia.
+ apply (region_ok_stack src0segs _ mem 2 sp0); [exact HU2 | lia | lia |]. intros a Ha. apply Hstw. lia.
+ apply (region_ok_bytes _ mem 10 p 2 32); [exact HU10 | lia | lia |].
intros j Hj. split; [apply HB; exact Hj|]. apply Hpres. lia.
- cbn [lh_breg lh_cnt nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, ?HU10. repeat split; lia.
- cbn [f_atoms lh_bfacts lh_cnt lh_lo lh_hi nth map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1.
cbn [Nat.add] in B0, B1.
repeat split; try lia; assumption. }
pose proof (journal_init src0_msyms MR LIB_STACK [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom src0segs))) in HJ. fold sp0 in HJ.
jrun_to LAWS src0tbl_ok HS HJ src0_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ eapply (jmemset src0_msyms MR LAWS IMG src0_A_memset src0_memset_spec E _ _ LIB_STACK sp0 [] L A mem md L A _ (sp0 - 128) 0 48);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 128) with (sp0 + -128) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
jafter_stretch_keep HS 46%nat regs2 mem2 MEMSET_CLOB L_HDR0 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU10; lia | cbn [r_base r_hi base_val]; rewrite HU10; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU10; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
add_region HS (YP09.mkRegion (Some 2%nat) (-128) (-80) (-128) (-80) [mkChunk (-128) (CZero 48)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (writable_at_grows src0segs (ms_mem ms) mem2); [exact Hgr2|]. cbn [ms_mem mkst] in HG. apply (writable_at_grows src0segs mem (ms_mem ms)); [exact HG|]. apply Hstw. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off]. intros i Hi.
replace (sp0 + -128 + i) with (sp0 - 128 + i) by lia. apply Hzero2. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, ?HU10. repeat split; lia. }
jrun_to LAWS src0tbl_ok HS HJ2 L_TAIL.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (HB0 : ew E 32 = Z_to_bv 64 (byte_at mem (p + 0))) by (etransitivity; [apply (HB 0%nat); lia | f_equal; f_equal; lia]).
assert (HB1 : ew E 33 = Z_to_bv 64 (byte_at mem (p + 1))) by (etransitivity; [apply (HB 1%nat); lia | f_equal; f_equal; lia]).
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_tail_x API IMG CLOSE ADDF UNLINK RFC NEWGIF regs L A mem md b0 plen K HSORT HK HROOM HFD rg L A mm md p n 0 n _ _ _ (byte_at mem (p + 0) + 256 * byte_at mem (p + 1)) 0 0 _ _ PAYLOAD) end.
+ exact HJ2. + exact Hid. + exact Hra. + exact Htp. + exact Hal16. + exact Hpn. + exact Hn. + apply Permutation_refl.
+ reflexivity.
+ fold sp0. cbn [obj_at LAY_Config]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
try change (2 ^ (8 * 8)) with 18446744073709551616. try change (2 ^ (8 * 4)) with 4294967296.
try change (2 ^ (8 * 2)) with 65536.
try change (N.to_nat 8) with 8%nat. try change (N.to_nat 4) with 4%nat. try change (N.to_nat 2) with 2%nat.
pose proof (byte_at_range mem (p + 0)) as R0. pose proof (byte_at_range mem (p + 1)) as R1.
repeat match goal with |- _ /\ _ => split end;
first [ cfg_zero HS HU2 (-128) 16
| cfg_zero HS HU2 (-128) 24
| cfg_zero HS HU2 (-128) 48
| cfg_zero HS HU2 (-98) 18
| cfg_zero HS HU2 (-100) 20
| cfg_zero HS HU2 (-102) 22
| cfg_zero HS HU2 (-108) 4
| cfg_val2 HS HU2 33%nat 32%nat HB1 HB0
| cfg_low4 HS HU2
| lia
| match goal with |- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)); lia end
| match goal with |- ?G => idtac "CFGLEFT"; idtac G end ].
+ fold sp0. unfold saved_ok.
repeat match goal with |- _ /\ _ => split end;
first [ frame_wordI HS 2%nat HU2 HE 1%nat (1%bv:reg) | frame_wordI HS 2%nat HU2 HE 8%nat (8%bv:reg)
| frame_wordI HS 2%nat HU2 HE 9%nat (9%bv:reg) | frame_wordI HS 2%nat HU2 HE 18%nat (18%bv:reg)
| frame_wordI HS 2%nat HU2 HE 19%nat (19%bv:reg) | frame_wordI HS 2%nat HU2 HE 20%nat (20%bv:reg)
| frame_wordI HS 2%nat HU2 HE 21%nat (21%bv:reg) | frame_wordI HS 2%nat HU2 HE 22%nat (22%bv:reg)
| frame_wordI HS 2%nat HU2 HE 23%nat (23%bv:reg) | frame_wordI HS 2%nat HU2 HE 24%nat (24%bv:reg) ].
+ fold sp0. replace (sp0 - 184) with (sp0 + -184) by lia.
eapply (st_chunk_word _ _ _ 1%nat _ 2%nat (-184) (SOff 10 0) sp0 p HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HU10; reflexivity | lia].
+ fold sp0. replace (sp0 - 176) with (sp0 + -176) by lia.
eapply (st_chunk_word _ _ _ 1%nat _ 2%nat (-176) (SOff 11 0) sp0 n HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HU11; reflexivity | lia].
+ lia.
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ reg_nowF HS ltac:(rewrite HU11; reflexivity).
+ reg_nowF HS ltac:(rewrite HU10; reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in pose proof (st_ok_reg src0segs Ec ssc msc 20%bv HS) as T; eval_sr_get_in T;
rewrite (denot_or_shl8 _ 33 32 (byte_at mem (p + 1)) (byte_at mem (p + 0))) in T;
[ exact T | ew_havocA; exact HB1 | ew_havocA; exact HB0 | apply byte_at_range | apply byte_at_range ] end.
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(rewrite HU11; reflexivity).
+ split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ lia.
+ lia.
+ exact HSN0. + exact Hsp47. + exact HPL. + exact HPLn.
+ intros E1 E2. exfalso. lia.
+ intros Hge. exfalso. clear - Hge HC HPLn. lia.
+ exact HRES0.
Qed.
Lemma lh_case_0 : lh_case_x (fun n => n < 2).
Proof.
intros p n PAYLOAD HC HPRE Hid G10 G11 Hn Hpn HSN0 Hsp47 HPL HPLn HRES0. apply realizes_via_SR.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HLSv : LIB_STACK = 16384) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
destruct (blocks_range _ _ LAWS L A mem md p n HH Hpn) as [Hp0 Hp1].
assert (Hpres : forall i, 0 <= i < n -> present mem (p + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS L A mem md p n i HH Hpn Hi)). }
set (bvals := map (fun i => byte_at mem (p + Z.of_nat i)) (seq 0 0)).
set (E := Ereg regs (map (Z_to_bv 64) bvals ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error bvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = p) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = n) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HS : st_ok src0segs E (ss_lh 0) (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom src0segs))).
{ unfold ss_lh. replace src0_A_LLVMFuzzerTestOneInput with LLVM by reflexivity. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- cbn [lh_breg lh_cnt nth app]. constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. apply Hstw. lia.
+ apply (region_ok_stack src0segs _ mem 2 sp0); [exact HU2 | lia | lia |]. intros a Ha. apply Hstw. lia.
- cbn [lh_breg lh_cnt nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, ?HU10. repeat split; lia.
- cbn [f_atoms lh_bfacts lh_cnt lh_lo lh_hi nth map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
pose proof (journal_init src0_msyms MR LIB_STACK [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom src0segs))) in HJ. fold sp0 in HJ.
jrun_to LAWS src0tbl_ok HS HJ src0_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ eapply (jmemset src0_msyms MR LAWS IMG src0_A_memset src0_memset_spec E _ _ LIB_STACK sp0 [] L A mem md L A _ (sp0 - 128) 0 48);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 128) with (sp0 + -128) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
jafter_stretch_keep HS 46%nat regs2 mem2 MEMSET_CLOB L_HDR0 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
add_region HS (YP09.mkRegion (Some 2%nat) (-128) (-80) (-128) (-80) [mkChunk (-128) (CZero 48)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (writable_at_grows src0segs (ms_mem ms) mem2); [exact Hgr2|]. cbn [ms_mem mkst] in HG. apply (writable_at_grows src0segs mem (ms_mem ms)); [exact HG|]. apply Hstw. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off]. intros i Hi.
replace (sp0 + -128 + i) with (sp0 - 128 + i) by lia. apply Hzero2. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, ?HU10. repeat split; lia. }
jrun_to LAWS src0tbl_ok HS HJ2 L_TAIL.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_nil. }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_tail_x API IMG CLOSE ADDF UNLINK RFC NEWGIF regs L A mem md b0 plen K HSORT HK HROOM HFD rg L A mm md p n 0 n _ _ _ 0 0 0 _ _ PAYLOAD) end.
+ exact HJ2. + exact Hid. + exact Hra. + exact Htp. + exact Hal16. + exact Hpn. + exact Hn. + apply Permutation_refl.
+ reflexivity.
+ fold sp0. cbn [obj_at LAY_Config]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
try change (2 ^ (8 * 8)) with 18446744073709551616. try change (2 ^ (8 * 4)) with 4294967296.
try change (2 ^ (8 * 2)) with 65536.
try change (N.to_nat 8) with 8%nat. try change (N.to_nat 4) with 4%nat. try change (N.to_nat 2) with 2%nat.
repeat match goal with |- _ /\ _ => split end;
first [ cfg_zero HS HU2 (-128) 16
| cfg_zero HS HU2 (-128) 24
| cfg_zero HS HU2 (-128) 48
| cfg_zero HS HU2 (-98) 18
| cfg_zero HS HU2 (-100) 20
| cfg_zero HS HU2 (-102) 22
| cfg_zero HS HU2 (-108) 4
| cfg_low4 HS HU2
| lia
| match goal with |- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)); lia end
| match goal with |- ?G => idtac "CFGLEFT"; idtac G end ].
+ fold sp0. unfold saved_ok.
repeat match goal with |- _ /\ _ => split end;
first [ frame_wordI HS 2%nat HU2 HE 1%nat (1%bv:reg) | frame_wordI HS 2%nat HU2 HE 8%nat (8%bv:reg)
| frame_wordI HS 2%nat HU2 HE 9%nat (9%bv:reg) | frame_wordI HS 2%nat HU2 HE 18%nat (18%bv:reg)
| frame_wordI HS 2%nat HU2 HE 19%nat (19%bv:reg) | frame_wordI HS 2%nat HU2 HE 20%nat (20%bv:reg)
| frame_wordI HS 2%nat HU2 HE 21%nat (21%bv:reg) | frame_wordI HS 2%nat HU2 HE 22%nat (22%bv:reg)
| frame_wordI HS 2%nat HU2 HE 23%nat (23%bv:reg) | frame_wordI HS 2%nat HU2 HE 24%nat (24%bv:reg) ].
+ fold sp0. replace (sp0 - 184) with (sp0 + -184) by lia.
eapply (st_chunk_word _ _ _ 1%nat _ 2%nat (-184) (SOff 10 0) sp0 p HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HU10; reflexivity | lia].
+ fold sp0. replace (sp0 - 176) with (sp0 + -176) by lia.
eapply (st_chunk_word _ _ _ 1%nat _ 2%nat (-176) (SOff 11 0) sp0 n HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HU11; reflexivity | lia].
+ lia.
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ reg_nowF HS ltac:(rewrite HU11; reflexivity).
+ reg_nowF HS ltac:(rewrite HU10; reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(rewrite HU11; reflexivity).
+ split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)|].
reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ lia.
+ lia.
+ exact HSN0. + exact Hsp47. + exact HPL. + exact HPLn.
+ intros E1 E2. exfalso. lia.
+ intros Hge. exfalso. clear - Hge HC HPLn. lia.
+ exact HRES0.
Qed.
Definition ss_le : sstate :=
mkSS LLVM (sr_set sr_atoms 11%bv (SLit 0))
[ YP09.mkRegion (Some 2%nat) (-192) (-128) (-192) (-128) [] ;
YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 [] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK) (2^63) 4) ] [] []).
Lemma lh_empty_x :
fn_pre src0_msyms MR LIB_STACK L A regs mem md -> st_init_done A = true ->
getr regs 11 = Z_to_bv 64 0 ->
sink_none src0_msyms mem md ->
res_ok A b0 ->
realizes src0segs (mkCfg (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom src0segs)) md) (ff_tree K (m_fs md) []).
Proof.
intros HPRE Hid G11 HSN0 HRES0. apply realizes_via_SR.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HLSv : LIB_STACK = 16384) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
assert (Hspm : (sp0 - 192) mod 16 = 0) by (replace (sp0 - 192) with (sp0 + (-12) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
set (E := Ereg regs []).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HS : st_ok src0segs E ss_le (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom src0segs))).
{ unfold ss_le. replace src0_A_LLVMFuzzerTestOneInput with LLVM by reflexivity. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros H0; discriminate H0 |]. cbn [sv_denot]. exact G11.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. apply Hstw. lia.
+ apply (region_ok_stack src0segs _ mem 2 sp0); [exact HU2 | lia | lia |]. intros a Ha. apply Hstw. lia.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2. repeat split; lia.
- split; [| split; constructor].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. repeat split; try lia; assumption. }
pose proof (journal_init src0_msyms MR LIB_STACK [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom src0segs))) in HJ. fold sp0 in HJ.
jrun_to LAWS src0tbl_ok HS HJ src0_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ eapply (jmemset src0_msyms MR LAWS IMG src0_A_memset src0_memset_spec E _ _ LIB_STACK sp0 [] L A mem md L A _ (sp0 - 128) 0 48);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 128) with (sp0 + -128) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
jafter_stretch_keep HS 46%nat regs2 mem2 MEMSET_CLOB L_HDR0 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
add_region HS (YP09.mkRegion (Some 2%nat) (-128) (-80) (-128) (-80) [mkChunk (-128) (CZero 48)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (writable_at_grows src0segs (ms_mem ms) mem2); [exact Hgr2|]. cbn [ms_mem mkst] in HG. apply (writable_at_grows src0segs mem (ms_mem ms)); [exact HG|]. apply Hstw. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off]. intros i Hi.
replace (sp0 + -128 + i) with (sp0 - 128 + i) by lia. apply Hzero2. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2. repeat split; lia. }
jrun_to LAWS src0tbl_ok HS HJ2 src0_A_malloc.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hm10.
jreg HS (2%bv:reg) as Hm2. rewrite HU2 in Hm2. replace (sp0 + -192) with (sp0 - 192) in Hm2 by lia.
jreg HS (4%bv:reg) as Hm4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hm4.
jreg HS (1%bv:reg) as Hm1.
eapply SR_bind.
{ eapply (jmalloc_at_res API IMG) with (n := 0) (spc := sp0 - 192);
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact Hid | exact Hm10 | exact HRES0 | apply (hdr_pal_room b0 plen HROOM); unfold PALMAX; lia
| exact Hm2 | lia | exact Hspm | lia | lia | exact Hm4 | exact Hm1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L2 & A2 & regs3 & mem3 & md3 & res & -> & HJ3 & Hid3 & HP3 & Hres10 & Hres & Hkeep3 & Hhi3 & HR3). clear HJ2.
change (ms_segs src0_msyms) with src0segs in Hkeep3, Hhi3. cbn [ms_regs ms_mem mkst] in HP3, Hkeep3, Hhi3, HJ3, Hres10.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HH3.
jafter_call_keep HS 52%nat regs3 mem3 HP3 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK2 : P); [|specialize (HS2 HK2); clear HK2] end.
{ constructor; [|constructor; [|constructor; [|constructor]]];
(eapply (region_kept_stack src0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi3 | lia | lia | lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq56. cbn [ms_regs mkst] in Hq56. rewrite Hres10 in Hq56. symmetry in Hq56.
pose proof (HE 3%nat 3%bv eq_refl) as G3. pose proof (HE 4%nat 4%bv eq_refl) as G4.
pose proof (HE 25%nat 25%bv eq_refl) as G25. pose proof (HE 26%nat 26%bv eq_refl) as G26. pose proof (HE 27%nat 27%bv eq_refl) as G27.
destruct Hres as (Hnz & Hres16 & (b1 & b2 & Hbl2 & Hblc) & Hwr).
assert (Hpin : In (res, 0) (blocks L2 A2)) by (rewrite Hbl2; apply in_app_iff; right; left; reflexivity).
destruct (blocks_range _ _ LAWS L2 A2 mem3 md3 res 0 HH3 Hpin) as [Hr0 Hr1].
assert (HB2 : Permutation (blocks L2 A2) ((res, 0) :: blocks L A)).
{ rewrite Hbl2. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip. rewrite <- Hblc. apply Permutation_refl. }
add_fact HS 56%nat (mkAF 4096 CEIL_MAX 4).
2:{ rewrite Hq56, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
jrun_to LAWS src0tbl_ok HS HJ3 src0_A_memcpy.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as M10. rewrite Hq56 in M10.
jreg HS (11%bv:reg) as M11. jreg HS (12%bv:reg) as M12. jreg HS (1%bv:reg) as M1.
pose proof (u64_range' (ew E 10)) as Rp.
eapply SR_bind.
{ eapply (jmemcpy_rd API IMG _ src0_memcpy) with (d := res) (src := bv_unsigned (ew E 10)) (n := 0);
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact M10 | rewrite M11, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity | exact M12 | exact M1
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia
| intros i Hi; exfalso; lia | intros i Hi; exfalso; lia | lia | intros a Ha; exfalso; lia ]. }
cbv beta. intros c' (regs4 & mem4 & -> & HJ4 & Hd10' & Hfr4 & Hout4 & Hgr4 & Hcp4). clear HJ3.
jafter_stretch_keep HS 68%nat regs4 mem4 MEMCPY_CLOB L_CPYRET [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr4. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]];
(eapply region_kept_out; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_havocA; rewrite HU2; lia
| cbn [r_base r_hi base_val]; ew_havocA; rewrite HU2; lia
| cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
jrun_to LAWS src0tbl_ok HS HJ4 L_PALFREE.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
unfold ff_tree. rewrite (ff_cfg_hdr_short [] (hdr5_short [] ltac:(cbn; lia))). unfold ff_leaf.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ => eapply (llvm_freeret_x API IMG regs L A mem md b0 plen K HK rg L2 A2 mm md3 res 0 (rb_malloc b0 0)) end.
+ exact HJ4. + exact Hid3. + exact Hra. + exact Htp. + exact Hal16.
+ right. split; [exact HB2 | intros _; lia].
+ fold sp0. unfold saved_ok.
repeat match goal with |- _ /\ _ => split end;
first [ frame_wordI HS 2%nat HU2 HE 1%nat (1%bv:reg) | frame_wordI HS 2%nat HU2 HE 8%nat (8%bv:reg)
| frame_wordI HS 2%nat HU2 HE 9%nat (9%bv:reg) | frame_wordI HS 2%nat HU2 HE 18%nat (18%bv:reg)
| frame_wordI HS 2%nat HU2 HE 19%nat (19%bv:reg) | frame_wordI HS 2%nat HU2 HE 20%nat (20%bv:reg)
| frame_wordI HS 2%nat HU2 HE 21%nat (21%bv:reg) | frame_wordI HS 2%nat HU2 HE 22%nat (22%bv:reg)
| frame_wordI HS 2%nat HU2 HE 23%nat (23%bv:reg) | frame_wordI HS 2%nat HU2 HE 24%nat (24%bv:reg) ].
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ reg_nowF HS ltac:(rewrite Hq56, Z_to_bv_bv_unsigned; reflexivity).
+ untouched_tac HS HE (eq_sym G3) (eq_sym G4) (eq_sym G25) (eq_sym G26) (eq_sym G27).
+ exact HSN0.
+ exact HR3.
+ apply (main_bud_fin b0 plen). apply (hdr_pal_bud b0). unfold PALMAX. lia.
Qed.
End S.
End f.
