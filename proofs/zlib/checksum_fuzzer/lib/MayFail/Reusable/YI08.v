(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI08.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN32.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition MAGIC255 : Z := 9259542125412876288.
Lemma magic255_div : forall x, 0 <= x < 2 ^ 32 -> (x * 2155905153) / 2 ^ 39 = x / 255.
Proof.
intros x Hx.
pose proof (Z.div_mod x 255 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 255 ltac:(lia)) as Hmb.
set (q := x / 255) in *. set (r := x mod 255) in *.
symmetry. apply (Z.div_unique _ _ _ ((r * 2 ^ 39 + 127 * x) / 255)).
- left. split.
+ apply Z.div_pos; lia.
+ apply Z.div_lt_upper_bound; [lia|]. nia.
- assert (E : x * 2155905153 * 255 = 2 ^ 39 * q * 255 + (r * 2 ^ 39 + 127 * x)) by nia.
apply (Z.mul_cancel_r _ _ 255); [lia|].
rewrite E, Z.mul_add_distr_r.
rewrite <- (Z.mul_comm 255 ((r * 2 ^ 39 + 127 * x) / 255)).
rewrite <- (proj2 (Z.div_exact (r * 2 ^ 39 + 127 * x) 255 ltac:(lia))); [lia|].
apply Z.mod_divide; [lia|]. exists (x * 2155905153 - 2 ^ 39 * q). nia.
Qed.
Section g.
Variable E : env.
Variable x : Z.
Hypothesis Hx12 : ew E 12 = Z_to_bv 64 x.
Hypothesis Hx : 0 <= x < 2 ^ 28.
Definition sv_q : sv := SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_SLL (SOff 12 0) (SLit 32)) (SLit MAGIC255)) (SLit 39).
Definition sv_q256 : sv := SAluw ALU_SLL sv_q (SLit 8).
Definition sv_rem : sv := SAluw ALU_SUB (SAlu ALU_ADD (SOff 12 0) sv_q) sv_q256.
Lemma U_sv_q : U E sv_q = x / 255.
Proof.
unfold sv_q. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 12 x Hx12) by lia. rewrite !U_SLit.
change (zcanon 32) with 32. change (zcanon 39) with 39. change (zcanon MAGIC255) with MAGIC255.
change (Z.land 32 63) with 32. change (Z.land 39 63) with 39.
rewrite (zcanon_id (Z.shiftl x 32)). 2:{ rewrite Z.shiftl_mul_pow2 by lia. unfold M64. nia. }
rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia. change (Z.of_N 64) with 64.
replace (x * 2 ^ 32 * MAGIC255) with (x * 2155905153 * 2 ^ 64) by (unfold MAGIC255; lia).
rewrite Z.div_mul by lia.
rewrite (zcanon_id (x * 2155905153)) by (unfold M64; nia).
rewrite magic255_div by lia. apply zcanon_id. unfold M64.
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
Lemma U_sv_q256 : U E sv_q256 = 256 * (x / 255).
Proof.
unfold sv_q256. rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite U_sv_q, U_SLit. change (zcanon 8 mod 2 ^ 32) with 8.
change (Z.land 8 31) with 8.
assert (Hq : 0 <= x / 255 < 2 ^ 21) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (Z.mod_small (x / 255)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
replace (bv_modulus 32) with (2 ^ 32) by reflexivity. replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
rewrite (Z.mod_small (x / 255 * 2 ^ 8 + 2 ^ 31)) by lia.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma U_sv_rem : U E sv_rem = x mod 255.
Proof.
unfold sv_rem. rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 12 x Hx12) by lia. rewrite U_sv_q. fold sv_q256. rewrite U_sv_q256.
pose proof (Z.div_mod x 255 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 255 ltac:(lia)) as Hmb.
assert (Hq : 0 <= x / 255 < 2 ^ 21) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id (x + x / 255)) by (unfold M64; lia).
rewrite !Z.mod_small by lia.
unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
replace (bv_modulus 32) with (2 ^ 32) by reflexivity. replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
rewrite (Z.mod_small (x + x / 255 - 256 * (x / 255) + 2 ^ 31)) by lia.
rewrite Z.mod_small by lia. lia.
Qed.
End g.
Lemma alu64_add_lit : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. rewrite alu_add. unfold v_add. apply Z_to_bv64_eq_mod.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity.
Qed.
Section h.
Variable segs : list Segment.
Lemma val_mem1 : forall (mem : word -> option byte) a,
present mem a -> exists v, 0 <= v < 2 ^ 8 /\ val_mem segs mem a 1 v.
Proof.
intros mem a [b Hb]. exists (bv_unsigned b). pose proof (bv_unsigned_in_range _ b) as Hr.
change (bv_modulus 8) with (2 ^ 8) in Hr. split; [lia|].
intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. unfold mbyte. rewrite Hb. f_equal.
unfold le_byte. replace (8 * Z.of_nat 0) with 0 by reflexivity. replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite Z.mod_small by lia.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma val_mem2 : forall (mem : word -> option byte) a,
present mem a -> present mem (a + 1) -> exists v, 0 <= v < 2 ^ 16 /\ val_mem segs mem a 2 v.
Proof.
intros mem a [b0 Hb0] [b1 Hb1]. exists (bv_unsigned b0 + 256 * bv_unsigned b1).
pose proof (bv_unsigned_in_range _ b0) as Hr0. pose proof (bv_unsigned_in_range _ b1) as Hr1.
change (bv_modulus 8) with 256 in Hr0, Hr1. split; [lia|].
assert (Hm : (bv_unsigned b0 + 256 * bv_unsigned b1) mod 2 ^ (8 * Z.of_nat 2) = bv_unsigned b0 + 256 * bv_unsigned b1).
{ apply Z.mod_small. replace (2 ^ (8 * Z.of_nat 2)) with 65536 by reflexivity. lia. }
intros k Hk. unfold le_byte. rewrite Hm. destruct k as [|[|k]]; [| |lia]; unfold mbyte.
- replace (a + Z.of_nat 0) with a by lia. rewrite Hb0. f_equal. replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
replace (bv_unsigned b0 + 256 * bv_unsigned b1) with (bv_unsigned b0 + bv_unsigned b1 * 256) by lia.
rewrite Z_mod_plus_full, Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
- replace (a + Z.of_nat 1) with (a + 1) by lia. rewrite Hb1. f_equal. replace (8 * Z.of_nat 1) with 8 by reflexivity.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
replace (bv_unsigned b0 + 256 * bv_unsigned b1) with (bv_unsigned b0 + bv_unsigned b1 * 256) by lia.
rewrite Z.div_add, Z.div_small, Z.add_0_l, Z.mod_small by lia.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma frame_of_cons_ro : forall E r rs (m m' : word -> option byte),
frame_of E (r :: rs) m m' -> r_whi r <= r_wlo r -> frame_of E rs m m'.
Proof.
intros E r rs m m' H Hro x Hx. apply H. intros (r' & [<-|Hin] & Hr'); [lia|]. apply Hx. exists r'. auto.
Qed.
Lemma st_ok_set_reg : forall E ss ms (r : reg) e,
st_ok segs E ss ms -> r <> 0%bv -> getr (ms_regs ms) r = sv_denot E e ->
st_ok segs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hr He.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|split; assumption].
apply regs_ok_pin; assumption.
Qed.
End h.
Lemma land7_split : forall t, 0 <= t -> exists m, t = 8 * m + Z.land t 7 /\ 0 <= Z.land t 7 < 8.
Proof.
intros t Ht. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
exists (t / 8). pose proof (Z.div_mod t 8 ltac:(lia)). pose proof (Z.mod_pos_bound t 8 ltac:(lia)). lia.
Qed.
Lemma land255_small : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof. intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma U_and255 : forall E n c L, ew E n = Z_to_bv 64 L -> 0 <= L < 256 -> 0 <= L + c < 256 ->
U E (SAlu ALU_AND (SOff n c) (SLit 255)) = L + c.
Proof.
intros E n c L Hn HL HLc. rewrite U_and_lit by lia. rewrite (U_atom_off E n L c Hn) by lia. apply land255_small. lia.
Qed.
Lemma U_t6 : forall E n c L m b, ew E n = Z_to_bv 64 L -> ew E m = Z_to_bv 64 b -> 0 <= L < 256 -> 0 <= L + c < 256 -> 0 <= b < 256 ->
U E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_AND (SOff n c) (SLit 255))) = b + (L + c).
Proof.
intros E n c L m b Hn Hm HL HLc Hb. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_and255 E n c L Hn HL HLc).
rewrite (U_atom E m b Hm) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma alu64_sll1 : forall D, 0 <= D < 2 ^ 62 -> alu64 ALU_SLL (Z_to_bv 64 D) (Z_to_bv 64 1) = Z_to_bv 64 (2 * D).
Proof.
intros D HD. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small D), (Z.mod_small 1) by lia. change (Z.land 1 63) with 1.
rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia.
Qed.
Lemma lxor_allones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx.
assert (E : 2 ^ 64 - 1 - x = Z.lnot x mod 2 ^ 64).
{ rewrite Z.lnot_eq_pred_opp. apply Z.mod_unique_pos with (q := -1); lia. }
rewrite E. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec. replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity.
rewrite Z.testbit_mod_pow2, Z.lnot_spec by lia.
destruct (Z.ltb_spec i 64).
- rewrite Z.ones_spec_low by lia. replace (i <? 64) with true by (symmetry; apply Z.ltb_lt; lia).
destruct (Z.testbit x i); reflexivity.
- rewrite Z.ones_spec_high by lia. replace (i <? 64) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite (Z_testbit_high 64 x i) by lia. reflexivity.
Qed.
Lemma U_not : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
U E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = 2 ^ 64 - 1 - x.
Proof.
intros E n x Hn Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hn Hx), U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma U_not_off : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
U E (SAlu ALU_XOR (SOff n c) (SLit (-1))) = 2 ^ 64 - 1 - (x + c).
Proof.
intros E n x c Hn Hx Hc. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E n x c Hn Hx Hc), U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma lit_m1 : Z_to_bv 64 18446744073709551615 = Z_to_bv 64 (-1).
Proof. apply bv_eq. reflexivity. Qed.
Lemma mem_grows_of_eq : forall (m m' : word -> option byte), (forall x, m' x = m x) -> mem_grows m m'.
Proof. intros m m' H x Hx. rewrite H. exact Hx. Qed.
Lemma atoms_ok_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[n f] l1 IH]; [exact H2|]. destruct H1 as [Hf H1]. split; [exact Hf | apply IH; exact H1]. Qed.
Section j.
Variable segs : list Segment.
Lemma st_ok_reg_U : forall E ss ms (r : reg),
st_ok segs E ss ms -> getr (ms_regs ms) r = Z_to_bv 64 (U E (sr_get (ss_regs ss) r)).
Proof. intros E ss ms r HS. unfold U. rewrite Z_to_bv_bv_unsigned. apply (st_ok_reg _ _ _ _ _ HS). Qed.
Lemma entry_st_ok_any : forall E pc sr regs (rs : smem) (G : facts) mem,
regs_ok E sr regs -> regions_wf rs = true -> Forall (region_ok segs E mem) rs ->
pairwise_disjoint E rs -> facts_ok E G ->
st_ok segs E (mkSS pc sr rs None G) (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)).
Proof.
intros E pc sr regs rs G mem Hsr Hwf Hrs Hpd HG.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact Hsr|]. split; [| exact HG].
split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.
End j.
End d.
Ltac lia0 := repeat match goal with H : _ |- _ => clear H end; lia.
Ltac kreg HK :=
lazymatch goal with |- getr _ ?r = _ => rewrite (HK r) by (cbv; tauto); first [assumption | reflexivity] end.
Ltac cnorm H HE28 HE30 :=
first [ rewrite branch_ltu_U in H | rewrite branch_geu_U in H | rewrite branch_eq_U in H | rewrite branch_ne_U in H ];
rewrite ?(U_t6 _ 28 _ _ 30 _ HE28 HE30) in H by lia;
rewrite ?(U_and255 _ 28 _ _ HE28) in H by lia;
rewrite ?U_lit in H by lia0;
first [ apply Z.ltb_lt in H | apply Z.ltb_ge in H | apply Z.eqb_eq in H | apply Z.eqb_neq in H
| apply (proj1 (Bool.negb_true_iff _)) in H; first [apply Z.ltb_ge in H | apply Z.eqb_neq in H]
| apply (proj1 (Bool.negb_false_iff _)) in H; first [apply Z.ltb_lt in H | apply Z.eqb_eq in H] ].
Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition CBB_STK : Z := 96.
Definition cbb_len (n : Z) : Z := 256 * (n / 255) + (if n mod 255 =? 0 then 1 else n mod 255 + 2).
Lemma cbb_len_bounds : forall n, 0 <= n -> 1 <= cbb_len n <= n + n / 255 + 2.
Proof.
intros n Hn. unfold cbb_len.
pose proof (Z.div_mod n 255 ltac:(lia)). pose proof (Z.mod_pos_bound n 255 ltac:(lia)).
destruct (Z.eqb_spec (n mod 255) 0); lia.
Qed.
Definition cbb_aliases : list (sv * sv) :=
[ (sv_q, SOff 32%nat 0);
(SAlu ALU_SUB (SOff 12%nat 0) (SMd M_MUL (SOff 32%nat 0) (SLit 255)), SOff 33%nat 0);
(SAlu ALU_ADD (SOff 11%nat 0) (SMd M_MUL (SOff 32%nat 0) (SLit 256)), SOff 34%nat 0);
(SAlu ALU_ADD (SOff 10%nat 0) (SMd M_MUL (SOff 32%nat 0) (SLit 255)), SOff 35%nat 0);
(SAlu ALU_ADD (SOff 11%nat 0) (SAlu ALU_ADD (SAlu ALU_ADD (SOff 33%nat 0) (SMd M_MUL (SOff 32%nat 0) (SLit 256))) (SLit 1)), SOff 36%nat 0) ].
Definition cbb_facts (rzero : bool) : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + CBB_STK) (2^63) 4); (10%nat, mkAF 4096 CEIL_MAX 4);
(11%nat, mkAF 4096 CEIL_MAX 4); (12%nat, mkAF 0 (2^28) 0); (32%nat, mkAF 0 (2^21) 0);
(33%nat, if rzero then mkAF 0 0 0 else mkAF 1 254 0);
(34%nat, mkAF 4096 CEIL_MAX 0); (35%nat, mkAF 4096 CEIL_MAX 0) ]
++ (if rzero then [] else [(36%nat, mkAF 4096 CEIL_MAX 0)]).
Definition reg_stack96 : YP09.region := YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 [].
Definition reg_at (n : nat) : YP09.region := YP09.mkRegion (Some n) 0 1 0 1 [].
Lemma cbb_aliases_ok : forall E n q r bl bb,
ew E 12 = Z_to_bv 64 n -> 0 <= n < 2 ^ 28 -> n = 255 * q + r -> 0 <= r < 255 ->
ew E 32 = Z_to_bv 64 q -> ew E 33 = Z_to_bv 64 r ->
ew E 10 = Z_to_bv 64 bl -> ew E 11 = Z_to_bv 64 bb -> 4096 <= bl <= alloc_ceiling -> 4096 <= bb <= alloc_ceiling ->
ew E 34 = Z_to_bv 64 (bb + 256 * q) -> ew E 35 = Z_to_bv 64 (bl + 255 * q) -> ew E 36 = Z_to_bv 64 (bb + 256 * q + r + 1) ->
alias_ok E cbb_aliases.
Proof.
intros E n q r bl bb H12 Hn Hdm Hmb H32 H33 H10 H11 Hbl Hbb H34 H35 H36.
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (Hq : q = n / 255) by (apply (Z.div_unique n 255 q r); [left; lia | lia]).
assert (Hqr : 0 <= q < 2 ^ 21) by (subst q; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
cbn [alias_ok cbb_aliases]. repeat split.
- apply U_inj. rewrite (U_sv_q E n H12 Hn). rewrite (U_atom E 32 q H32) by lia. lia.
- apply U_inj. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite (U_atom E 12 n H12), (U_atom E 32 q H32), (U_atom E 33 r H33), U_SLit by lia.
change (zcanon 255) with 255. rewrite (zcanon_id (q * 255)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
- apply U_inj. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite (U_atom E 11 bb H11), (U_atom E 32 q H32), (U_atom E 34 _ H34), U_SLit by lia.
change (zcanon 256) with 256. rewrite (zcanon_id (q * 256)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
- apply U_inj. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite (U_atom E 10 bl H10), (U_atom E 32 q H32), (U_atom E 35 _ H35), U_SLit by lia.
change (zcanon 255) with 255. rewrite (zcanon_id (q * 255)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
- apply U_inj. rewrite !U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom E 11 bb H11), (U_atom E 32 q H32), (U_atom E 33 r H33), (U_atom E 36 _ H36), !U_SLit by lia.
change (zcanon 256) with 256. change (zcanon 1) with 1.
rewrite (zcanon_id (q * 256)) by (unfold M64; lia). rewrite (zcanon_id (r + q * 256)) by (unfold M64; lia).
rewrite (zcanon_id (r + q * 256 + 1)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma alu64_sll_lit : forall q k, 0 <= k < 64 -> 0 <= q -> q * 2 ^ k < 2 ^ 64 ->
alu64 ALU_SLL (Z_to_bv 64 q) (Z_to_bv 64 k) = Z_to_bv 64 (q * 2 ^ k).
Proof.
intros q k Hk Hq Hqk. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
assert (Hq' : q < 2 ^ 64) by (pose proof (Z.pow_pos_nonneg 2 k); nia).
rewrite (Z.mod_small q), (Z.mod_small k) by lia.
replace (Z.land k 63) with k.
2:{ change 63 with (Z.ones 6). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. lia. }
rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Definition CBL_STK : Z := 32.
Definition sr_cbl : list sv := sr_set (sr_set (sr_set sr_atoms 17%bv (SLit 11)) 5%bv (SLit 8)) 7%bv (SLit 16).
Lemma regs_ok_cbl : forall regs extra,
getr regs 17 = Z_to_bv 64 11 -> getr regs 5 = Z_to_bv 64 8 -> getr regs 7 = Z_to_bv 64 16 ->
regs_ok (Ereg regs extra) sr_cbl regs.
Proof.
intros regs extra H17 H5 H7. unfold sr_cbl.
repeat (apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; assumption]).
apply regs_ok_Ereg.
Qed.
Definition cbl_facts_core : list (nat * afact) :=
[ (10%nat, mkAF 4096 CEIL_MAX 4); (12%nat, mkAF 4096 CEIL_MAX 0); (6%nat, mkAF 4096 CEIL_MAX 0);
(13%nat, mkAF 0 65535 0); (14%nat, mkAF 0 12 0); (16%nat, mkAF 0 131070 0);
(15%nat, mkAF 0 (2^29) 0); (28%nat, mkAF 0 12 0) ].
Definition cbl_facts_AB : list (nat * afact) :=
cbl_facts_core ++ [ (30%nat, mkAF 0 7 0); (32%nat, mkAF 4096 CEIL_MAX 0); (33%nat, mkAF 0 65535 0);
(34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0) ].
Definition cbl_facts_C : list (nat * afact) :=
cbl_facts_core ++ [ (31%nat, mkAF 0 31 0); (33%nat, mkAF 0 65535 0) ].
Definition R12 : YP09.region := YP09.mkRegion (Some 12%nat) 0 2 0 0 [mkChunk 0 (CVal 2 (SOff 33%nat 0))].
Definition R32 : YP09.region :=
YP09.mkRegion (Some 32%nat) 0 3 0 3 [mkChunk 0 (CVal 1 (SOff 34%nat 0)); mkChunk 1 (CVal 1 (SOff 35%nat 0)); mkChunk 2 (CVal 1 (SOff 36%nat 0))].
Definition cbl_alias : list (sv * sv) := [ (SAlu ALU_ADD (SOff 10%nat 0) (SOff 15%nat 0), SOff 32%nat 0) ].
Definition cbl_regs_fix (regs : bvmap 5 word) (bl lz lzwPos D C0 : Z) : Prop :=
getr regs 10 = Z_to_bv 64 bl /\ getr regs 6 = Z_to_bv 64 (lz + 2 * lzwPos) /\
getr regs 13 = Z_to_bv 64 D /\ getr regs 14 = Z_to_bv 64 C0 /\ getr regs 16 = Z_to_bv 64 (2 * D) /\
getr regs 17 = Z_to_bv 64 11 /\ getr regs 5 = Z_to_bv 64 8 /\ getr regs 7 = Z_to_bv 64 16.
Definition cbl_fix (Lby Llz lzwPos D C0 : Z) : Prop :=
0 < lzwPos < 2 ^ 28 /\ 2 * lzwPos <= Llz /\ 3 * lzwPos + 5 <= 2 * Lby /\ 0 <= D <= 65535 /\ 0 <= C0 <= 12.
Definition REGS_FIX : list reg := [10; 6; 13; 14; 16; 17; 5; 7]%bv.
Lemma cbl_regs_fix_kept : forall regs regs' bl lz lzwPos D C0,
cbl_regs_fix regs bl lz lzwPos D C0 -> (forall r, In r REGS_FIX -> getr regs' r = getr regs r) ->
cbl_regs_fix regs' bl lz lzwPos D C0.
Proof.
intros regs regs' bl lz lzwPos D C0 (H10 & H6 & H13 & H14 & H16 & H17 & H5 & H7) HK.
unfold cbl_regs_fix. rewrite !HK by (cbv; tauto). repeat split; assumption.
Qed.
Definition KEPT : list reg := [1; 2; 3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
End l.
