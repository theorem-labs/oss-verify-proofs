(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements
   are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_qdisc's ASan harness walk from
   proofs/libreac/fuzz_knock/lib/A/APgLoop0.v (its part 0, the walk helpers a9's lib/A framework set does
   not carry: lines 73-270) and proofs/libreac/fuzz_knock/lib/A/APgMain1.v (its local part, lines 120-260:
   the region-move lemmas, in_region, rd_run, br_go, pin_reg, in_bytes and the byte-bound lemmas) and
   lines 98-112 of APgMain3.v (in_region_keep), at origin/ossv/recipes 6ebe35ba632, with their module paths
   changed and knock's frame arguments (fpos, F, EFA) dropped from every tactic, because fuzz_qdisc's
   harness owns no fake frame (lib/A/QPgRt.v, change Q1). This file adds fuzz_qdisc's own Z-level model of
   the harness loop: the frame-rate table and the selector's magic division by 6. rule 24 (reuse): no
   function is proved here; helpers, two model lemmas, the walk states and the loop invariants only. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep AWalkFw1 AWalkFw2 ACfm QPgRt.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Prog Require Import qdisc_spec qdisc_div.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================== 0. the walk helpers a9's set does not carry ===================== *)
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* [knock A/APgLoop0.v:86-99, the donor's A/ACf1.v:112-123] *)
Lemma rt_chunk1_of_val : forall E (m : word -> option byte) base off k v,
val_mem tfibsegs m (base + off) 1 v -> 0 <= v < 256 -> ew E k = Z_to_bv 64 v ->
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 1 (SOff k 0))).
Proof.
intros E m base off k v Hv Hr Hk i Hi. cbn [YP09.c_len YP09.c_val YP09.cv_len Z.of_N] in Hi.
assert (i = 0) as -> by lia.
exists (Z_to_bv 8 (YO0f.le_byte v 1 0)). split.
- cbn [YP09.c_off YP09.c_val YP09.cbyte]. rewrite sv_denot_SOff0, Hk. f_equal. unfold YP09.byte_of_word.
rewrite unsigned_lit_small by lia. f_equal. unfold YO0f.le_byte. change (Z.of_nat 1) with 1. cbn [Z.of_nat].
rewrite ?Z.mul_0_r, ?Z.shiftr_0_r.
change (2 ^ (8 * 1)) with 256. rewrite !(Z.mod_small v 256) by lia. reflexivity.
- cbn [YP09.c_off]. rewrite Z.add_0_r. pose proof (Hv 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0.
rewrite Z.add_0_r in H0. exact H0.
Qed.
(* [knock A/APgLoop0.v:101-102, the donor's A/ACf9.v:339-340] *)
Lemma denot_havoc_win : forall E k ws e, sv_atoms_on (win_free k (length ws)) e = true -> sv_denot (havoc E k ws) e = sv_denot E e.
Proof. intros E k ws e He. apply (sv_denot_agree_on (win_free k (length ws)) E); [apply env_agree_on_havoc | exact He]. Qed.
(* [knock A/APgLoop0.v:122-153, the donor's A/ACf1.v:192-223]: move one region to the head *)
Lemma rt_ad_split : forall E x pre r post, all_disjoint E x (pre ++ r :: post) -> extent_disjoint E x r /\ all_disjoint E x (pre ++ post).
Proof. intros E x pre r post. induction pre as [|y pre IH]; cbn [app all_disjoint]; [tauto|]. intros [Hy Hr]. destruct (IH Hr) as [A B']. tauto. Qed.
Lemma rt_ed_sym : forall E a b, extent_disjoint E a b -> extent_disjoint E b a.
Proof. unfold extent_disjoint. intros E a b H. lia. Qed.
Lemma rt_pd_move : forall E pre r post, pairwise_disjoint E (pre ++ r :: post) -> all_disjoint E r (pre ++ post) /\ pairwise_disjoint E (pre ++ post).
Proof.
intros E pre r post. induction pre as [|x pre IH]; cbn [app pairwise_disjoint all_disjoint]; [tauto|].
intros [Hx Hrest]. destruct (IH Hrest) as [Hr Hp]. destruct (rt_ad_split E x pre r post Hx) as [Hxr Hxa].
split; [split; [apply rt_ed_sym; exact Hxr | exact Hr] | split; [exact Hxa | exact Hp]].
Qed.
Lemma rt_wf_move : forall pre r post, regions_wf (pre ++ r :: post) = true -> regions_wf (r :: pre ++ post) = true.
Proof.
intros pre r post. induction pre as [|x pre IH]; cbn [app regions_wf]; [tauto|]. intros H.
apply andb_prop in H as [Hx H]. specialize (IH H). cbn [regions_wf] in IH. apply andb_prop in IH as [Hr Hp].
rewrite Hr, Hx, Hp. reflexivity.
Qed.
Lemma rt_forall_move : forall {A} (P : A -> Prop) pre r post, Forall P (pre ++ r :: post) -> Forall P (r :: pre ++ post).
Proof.
intros A P pre r post H. rewrite Forall_forall in *. intros x Hx. apply H.
destruct Hx as [<- | Hx]; [apply in_or_app; right; left; reflexivity|].
apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx].
Qed.
Lemma rt_st_ok_move : forall E ss ms pre r post,
st_ok tfibsegs E ss ms -> ss_mem ss = pre ++ r :: post ->
st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (r :: pre ++ post) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms pre r post (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (W & O & D) & H9) Hm.
rewrite Hm in W, O, D.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [exact (rt_wf_move pre r post W)|]. split; [exact (rt_forall_move _ pre r post O)|].
destruct (rt_pd_move E pre r post D) as [A B']. split; [exact A | exact B'].
Qed.
(* [knock A/APgMain1.v:181-190]: the byte bounds the join needs *)
Lemma U_lit0 : forall E, U E (SLit 0) = 0.
Proof. intros E. rewrite U_SLit. reflexivity. Qed.
Lemma U_zext8_lt : forall E x, 0 <= U E (SExt false 8 x) < 2 ^ 16.
Proof. intros E x. rewrite U_zext. change (2 ^ Z.of_N 8) with 256. pose proof (Z.mod_pos_bound (U E x) 256 ltac:(lia)). lia. Qed.
Lemma U_sll8_zext8_lt : forall E x, 0 <= U E (SAlu ALU_SLL (SExt false 8 x) (SLit 8)) < 2 ^ 16.
Proof.
intros E x. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_zext, U_SLit. change (2 ^ Z.of_N 8) with 256.
change (Z.land (zcanon 8) 63) with 8. pose proof (Z.mod_pos_bound (U E x) 256 ltac:(lia)).
rewrite Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* [knock A/APgLoop0.v:309-320]: the two bytes of the u16 lead do not overlap *)
Lemma lor_byte_pair : forall hib lo, 0 <= hib < 256 -> 0 <= lo < 256 -> Z.lor (hib * 256) lo = hib * 256 + lo.
Proof.
intros hib lo Hh Hl.
assert (Hd : Z.land (hib * 256) lo = 0).
{ apply Z.bits_inj_0. intros i. rewrite Z.land_spec. destruct (Z_lt_le_dec i 8) as [Hi|Hi].
- destruct (Z_lt_le_dec i 0) as [Hn|Hn]; [rewrite Z.testbit_neg_r by exact Hn; reflexivity|].
replace (hib * 256) with (Z.shiftl hib 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
rewrite Z.shiftl_spec_low by exact Hi. reflexivity.
- rewrite <- (Z.mod_small lo 256) by exact Hl. change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_high by lia.
apply Bool.andb_false_r. }
rewrite <- (Z.lxor_lor _ _ Hd). rewrite <- (Z.add_nocarry_lxor _ _ Hd). reflexivity.
Qed.
(* [knock A/APgLoop0.v:291-298]: `lw` of a small non-negative field sign-extends to itself *)
Lemma U_sext32_small : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> U E (SExt true 32 (SOff n 0)) = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt. rewrite (U_atom E n v Hn) by lia.
rewrite (Z.mod_small v (2 ^ Z.of_N 32)) by (change (2 ^ Z.of_N 32) with (2 ^ 32); lia).
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia.
apply zcanon_id. unfold M64. lia.
Qed.
End h.

(* ===================== 1. fuzz_qdisc's own Z-level model of the loop =====================
   The harness reads [u8 budgets mod 8] then, per budget, [u16 lead][u8 selector], and indexes the
   6-entry frame-rate table with selector mod 6 (fuzz_qdisc.c:94-99). The image computes the modulus
   without a division: `mul a1,a0,s8` with s8 = 0xab = 171, `srli a1,a1,0xa`, then a0 - 6 * a1 through
   `slli a2,a1,3 / slli a1,a1,1 / subw a1,a1,a2 / add a0,a0,a1` (0x7e78c-0x7e7a0). *)
Definition qd_fps (s : Z) : Z := nth (Z.to_nat s) fps_table 0.
(* 171 * b / 1024 is b / 6 on a byte: checked on every one of the 256 values. *)
Lemma qd_div6 : forall b, 0 <= b < 256 -> b * 171 / 1024 = b / 6.
Proof.
intros b Hb.
assert (Hin : In b (map Z.of_nat (seq 0 256))).
{ apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia. }
assert (R : forallb (fun x => Z.eqb (x * 171 / 1024) (x / 6)) (map Z.of_nat (seq 0 256)) = true)
by (vm_compute; reflexivity).
apply Z.eqb_eq. exact (proj1 (forallb_forall _ _) R b Hin).
Qed.
(* `andi s4, a2, 7` of the first input byte: the budget count is in [0, 7] *)
Lemma qd_land7 : forall a, 0 <= a -> 0 <= Z.land a 7 <= 7.
Proof.
intros a Ha. replace 7 with (Z.ones 3) by reflexivity. rewrite Z.land_ones by lia.
pose proof (Z.mod_pos_bound a (2 ^ 3) ltac:(lia)). change (2 ^ 3) with 8 in *.
change (Z.ones 3) with 7. lia.
Qed.
Lemma qd_mod6_range : forall b, 0 <= b < 256 -> 0 <= b mod 6 <= 5.
Proof. intros b Hb. pose proof (Z.mod_pos_bound b 6 ltac:(lia)). lia. Qed.
Lemma qd_fps_range : forall s, - 2 ^ 31 <= qd_fps s < 2 ^ 31.
Proof.
intros s. unfold qd_fps, fps_table.
change (2 ^ 31) with 2147483648.
destruct (Z.to_nat s) as [|[|[|[|[|[|m]]]]]]; cbn [nth]; [lia|lia|lia|lia|lia|lia|destruct m; lia].
Qed.

(* ===================== 2. the ported walk tactics ===================== *)
(* [knock A/APgLoop0.v:156-157, the donor's A/ACf9.v:347-348] *)
Ltac ewpeel := repeat (first [ rewrite ew_havoc_old by nat_side | rewrite ew_havoc_above by nat_side | rewrite ew_ewset_other by nat_side ]).
Ltac ewpeel_in H := repeat (first [ rewrite ew_havoc_old in H by nat_side | rewrite ew_havoc_above in H by nat_side | rewrite ew_ewset_other in H by nat_side ]).
(* [knock A/APgLoop0.v:159-164, the donor's A/ACf9.v:246-251] *)
Ltac add_atom_win HS n w En :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc_win tfibsegs n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
(* [knock A/APgLoop0.v:166-193, the donor's A/ACf9.v:252-279] *)
Ltac ra_join_win HS target N deads hook :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem tfibsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc_win tfibsegs N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl end;
norm_ss HS;
hook;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] end.
(* [knock A/APgLoop0.v:195-199, the donor's A/ACf9.v:389-393] *)
Ltac vkeep V H2 m2 etac :=
lazymatch type of V with val_mem _ (mrestrict ?Hh ?m) ?a ?n ?v =>
let V2 := fresh "V" in
assert (V2 : val_mem tfibsegs (mrestrict H2 m2) a n v) by (apply (val_mem_kept Hh H2 m m2 a n v V); intros i Hi; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; etac);
clear V; rename V2 into V end.
(* [knock A/APgMain1.v:226-234, the donor's A/ACf1.v:243-251] *)
Ltac move_region HS i :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let pre := eval vm_compute in (firstn i rs) in
let r := eval vm_compute in (nth i rs got_region) in
let post := eval vm_compute in (skipn (S i) rs) in
let HS3 := fresh "HS3" in
pose proof (rt_st_ok_move Ex ssx msx pre r post HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* [knock A/APgMain1.v:193-207, the donor's A/ACf1.v:124-161]: a read-only one-byte region over an
   input-block address.  knock's version unfolds the UAR cells too; qdisc has none. *)
Ltac in_region HS R E10x AG :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region tfibsegs Ev ssv msv R HS eq_refl) as HS3;
specialize (HS3 ltac:(
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
ewpeel; rewrite E10x, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros oo Hoo; lia|];
repeat (apply Forall_cons; [ eapply rt_chunk1_of_val; [ apply val_mem1_of_aview; eassumption | eassumption | ewpeel; eassumption ] | ]); apply Forall_nil));
specialize (HS3 ltac:(
lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob;
repeat split; zone_lia));
clear HS; rename HS3 into HS; norm_ss HS end.
(* the same, with the disjointness goals cut to the bounds they use first [knock A/APgMain3.v:98-112] *)
Ltac in_region_keep HS R E10x AG keep :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region tfibsegs Ev ssv msv R HS eq_refl) as HS3;
specialize (HS3 ltac:(
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
ewpeel; rewrite E10x, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros oo Hoo; lia|];
repeat (apply Forall_cons; [ eapply rt_chunk1_of_val; [ apply val_mem1_of_aview; eassumption | eassumption | ewpeel; eassumption ] | ]); apply Forall_nil));
specialize (HS3 ltac:(
lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob;
repeat split; first [keep; zones; req_lits; lia | zone_lia]));
clear HS; rename HS3 into HS; norm_ss HS end.
(* the shadow obligation of an input byte at a MOVING cursor [knock A/APgLoop0.v:230-239] *)
Ltac obl_cur HJx HEcur HEbx Hin Hrq :=
let L := rnLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff ?n ?c)) ?len =>
lazymatch type of HEcur with _ = Z_to_bv 64 ?cv =>
lazymatch type of Hin with In (?pb, ?sz) _ =>
first [ rewrite (U_atom_off Ex n cv c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEcur | lia | lia]
| rewrite (U_atom Ex n cv); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEcur | lia] ];
eapply (obl_of_block tfibsegs _ L _ _ _ _ _ Ex (SOff bx 0) _ len pb sz (proj1 HJx) Hin);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEbx | unfold SB; lia]
| lia | rewrite Hrq; lia ] end end end.
(* the four runners [knock A/APgMain1.v:208-219 and A/APgLoop0.v:241-263], without the frame arguments *)
Ltac rd_run HS HJ AG E10x E32x Hpin3 Hrq :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok tfibtbl_lib_ok HS HJ SH RTBspan;
try (lazymatch goal with |- range_addressable _ _ _ _ => first [obl_pay HJ E10x E32x Hpin3 Hrq | obl_cur HJ E10x E32x Hpin3 Hrq] end);
try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG end) end.
Ltac rd_run_to HS HJ AG E10x E32x Hpin3 Hrq stop :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok tfibtbl_lib_ok HS HJ SH RTBspan stop;
try (lazymatch goal with |- range_addressable _ _ _ _ => first [obl_pay HJ E10x E32x Hpin3 Hrq | obl_cur HJ E10x E32x Hpin3 Hrq] end);
try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG end) end.
Ltac pl_run HS HJ AG :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok tfibtbl_lib_ok HS HJ SH RTBspan;
try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG end) end.
Ltac pl_run_to HS HJ AG stop :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok tfibtbl_lib_ok HS HJ SH RTBspan stop;
try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG end) end.
(* [knock A/APgLoop0.v:265-268]: the branch the engine could not decide, with its condition named *)
Ltac br_split HS Hc :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok tfibtbl_lib_ok HS SH RTBspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
Ltac rb HS AG E10 E11 E32 E10n E11n E32n :=
let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv; relowRT HS AG E10 E11 E32 E10n E11n E32n.
(* [knock A/APgMain1.v:235-246, the donor's A/ACf1.v:267-281]: point a register at a fresh atom *)
Ltac pin_reg HS rr a v Hv Ea :=
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) rr) in
remember (U Ev e) as v eqn:Hv;
let Q := fresh "Q" in
assert (Q : getr (ms_regs ms) rr = sv_denot Ev e) by exact (st_ok_restrict_reg tfibsegs Hh Ev ssx ms rr HS);
add_atom_win HS a (Z_to_bv 64 v) Ea;
lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msv2 =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pin_rege Ev2 ssx2 msv2 rr (SOff a 0) HS ltac:(intros X; discriminate X)
ltac:(rewrite sv_denot_SOff0, Ea; cbn [ms_regs restrict mkst]; rewrite Q, Hv; symmetry; apply denot_lit_U)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end; clear Q end.
(* [knock A/APgMain3.v:63-75]: point a register at a fresh atom whose value a tactic proves *)
Ltac pin_by HS r e dtac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let eo := eval vm_compute in (sr_get (ss_regs ssx) r) in
let Hv := fresh "Hv" in
assert (Hv : sv_denot Ev e = sv_denot Ev eo) by dtac;
let HS3 := fresh "HS3" in
pose proof (st_ok_pin_rege Ev ssx msx r e HS ltac:(intros X; discriminate X)
(eq_trans Hv (eq_sym (st_ok_reg tfibsegs Ev ssx msx r HS)))) as HS3;
clear HS Hv; rename HS3 into HS; norm_ss HS end.
Ltac pin_tac :=
rewrite sv_denot_SOff0; cbn [sv_denot];
repeat match goal with H : ew ?Ex ?m = Z_to_bv 64 _ |- context [ew ?Ex ?m] => rewrite H end;
rewrite ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia].
(* [knock A/APgMain1.v:247-258, the donor's A/ACf1.v:396-407]: n0 input bytes from index i0 *)
Ltac in_bytes HJ cx LAWS HAR Hpin Hpin3 Hrq FP0 i0 n0 :=
let HJc := fresh "HJc" in pose proof HJ as HJc; rewrite FP0 in HJc;
let rec go j k :=
lazymatch k with
| O => idtac
| S ?k' =>
let bj := fresh "b" in let PBj := fresh "PB" in let Aj := fresh "A" in let Rj := fresh "R" in
destruct (PB_at_now _ _ cx _ _ _ _ _ _ _ j LAWS HAR HJc Hpin Hpin3 Hrq ltac:(cbn [c_n]; lia)) as (bj & PBj & Aj);
cbn [c_p] in Aj; pose proof (proj1 PBj) as Rj;
let j' := eval vm_compute in (j + 1) in go j' k'
end in
go i0 n0; clear HJc.

(* ===================== 3. the env slots, the four states and their invariants =====================
   The harness loop (0x7e710 .. 0x7e7e0, back edge `bnez s4` at 0x7e7e0) runs at most `budgets` times,
   and `budgets` is the first input byte & 7, so 1 <= budgets <= 7 at the head and the body decrements it
   by one (`addiw s4,s4,-1` at 0x7e7dc). The closure is therefore an induction on a nat `fuel` with
   Z.to_nat budgets <= fuel, the shape the released plain proof uses
   (lib/Prog/LLVMFuzzerTestOneInput.v). *)
Notation N_cur := 300%nat.  Notation N_rem := 301%nat.  Notation N_bud := 302%nat.
Notation N_cur2 := 303%nat. Notation N_rem2 := 304%nat. Notation N_lead := 305%nat.
Notation N_sel := 306%nat.  Notation N_fps := 307%nat.
Notation RT_LN := 760%nat.
Notation RT_JN := 700%nat.
Notation RT_CN := 720%nat.
Notation RT_XN := 600%nat.
(* The registers the loop does not keep live. x26 (s10) and x27 (s11) are never written by the harness
   and the two callees preserve them, so they stay SOff 26 0 / SOff 27 0 and are NOT dead. *)
Definition ql_deads : list nat := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 28; 29; 30; 31]%nat.
(* at the join 0x7e7a8 the lead is live in s1 (x9) and the selector in a1 (x11) *)
Definition ql_deadsJ : list nat := [1; 5; 6; 7; 10; 12; 13; 14; 15; 16; 17; 18; 28; 29; 30; 31]%nat.
(* at 0x7e7c4 the lead is live in s1 and the frame rate in s2 (x18) *)
Definition ql_deadsC : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
(* at the exit 0x7e81c only sp, gp, tp, s10, s11 and the save area are live *)
Definition ql_deadsX : list nat := [1; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 28; 29; 30; 31]%nat.
Definition ql_deads_bv : list (bv 5) := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 28; 29; 30; 31]%bv.
Definition ql_deadsJ_bv : list (bv 5) := [1; 5; 6; 7; 10; 12; 13; 14; 15; 16; 17; 18; 28; 29; 30; 31]%bv.
Definition ql_deadsC_bv : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition ql_deadsX_bv : list (bv 5) := [1; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 28; 29; 30; 31]%bv.
(* the eleven callee-saved words the prologue wrote at sp0-88 .. sp0-8 (0x7e690-0x7e6b8) *)
Definition ql_saves : list YP09.chunk :=
[ YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
  YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
  YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
  YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
  YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
  YP09.mkChunk (-8) (CVal 8 (SOff 1 0)) ].
Definition ql_stack : YP09.region := YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 ql_saves.
Definition ql_mem : smem := [ ql_stack; got_region; bcell_region 32 ].
Definition ql_atoms0 : list (nat * afact) := [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0) ].
Definition ql_atomsL : list (nat * afact) :=
(N_cur, mkAF 4096 140737479966720 0) :: (N_rem, mkAF 0 (2 ^ 26 - 1) 0) :: (N_bud, mkAF 0 7 0) :: ql_atoms0.
Definition ql_atomsJ : list (nat * afact) :=
(N_cur2, mkAF 4096 140737479966720 0) :: (N_rem2, mkAF 0 (2 ^ 26 - 1) 0) :: (N_bud, mkAF 0 7 0)
:: (N_lead, mkAF 0 65535 0) :: (N_sel, mkAF 0 5 0) :: ql_atoms0.
Definition ql_atomsC : list (nat * afact) :=
(N_cur2, mkAF 4096 140737479966720 0) :: (N_rem2, mkAF 0 (2 ^ 26 - 1) 0) :: (N_bud, mkAF 0 7 0)
:: (N_lead, mkAF 0 65535 0) :: ql_atoms0.
(* ss_L, pc 0x7e710: the loop head. s0 = cursor, s9 = rem, s4 = budgets left, s3 = SB, s5 = 1, s6 = 2,
   s7 = 0x20c80 (the frame-rate table), s8 = 171 (the magic multiplier of the mod-6). *)
Definition ss_L_0 : sstate :=
mkSS 0x7e710
[SLit 0; SOff 1 0; SOff 2 (-96); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff N_cur 0; SOff 9 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff 18 0; SOff 32 0; SOff N_bud 0; SLit 1; SLit 2; SLit 134272;
 SLit 171; SOff N_rem 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
ql_mem None (mkFacts ql_atomsL [] []).
Definition ss_L : sstate := Eval vm_compute in ss_havoc_regs ss_L_0 RT_LN ql_deads.
(* ss_J, pc 0x7e7a8: the four byte-reading paths join. s1 = lead, a1 = selector, s0 / s9 advanced. *)
Definition ss_J_0 : sstate :=
mkSS 0x7e7a8
[SLit 0; SOff 1 0; SOff 2 (-96); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff N_cur2 0; SOff N_lead 0; SOff 10 0; SOff N_sel 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff 18 0; SOff 32 0; SOff N_bud 0; SLit 1; SLit 2; SLit 134272;
 SLit 171; SOff N_rem2 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
ql_mem None (mkFacts ql_atomsJ [] []).
Definition ss_J : sstate := Eval vm_compute in ss_havoc_regs ss_J_0 RT_JN ql_deadsJ.
(* ss_C, pc 0x7e7c4: the frame rate has been read into s2. *)
Definition ss_C_0 : sstate :=
mkSS 0x7e7c4
[SLit 0; SOff 1 0; SOff 2 (-96); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff N_cur2 0; SOff N_lead 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff N_fps 0; SOff 32 0; SOff N_bud 0; SLit 1; SLit 2; SLit 134272;
 SLit 171; SOff N_rem2 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
ql_mem None (mkFacts ql_atomsC [] []).
Definition ss_C : sstate := Eval vm_compute in ss_havoc_regs ss_C_0 RT_CN ql_deadsC.
(* ss_X, pc 0x7e81c: the exit block. Only sp, gp, tp, s10, s11 and the save area are live; the eleven
   `ld` of 0x7e820-0x7e848 put the callee-saved registers back and `ret` leaves at the caller's ra. *)
Definition ss_X_0 : sstate :=
mkSS 0x7e81c
[SLit 0; SOff 1 0; SOff 2 (-96); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 8 0; SOff 9 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0;
 SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
[ql_stack] None (mkFacts ql_atoms0 [] []).
Definition ss_X : sstate := Eval vm_compute in ss_havoc_regs ss_X_0 RT_XN ql_deadsX.
Section inv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Definition inv_cursor (cx : rtcx) (cur rem c : Z) : Prop :=
cur = c_p cx + c /\ 0 <= c /\ c + rem = c_n cx /\ 0 <= rem /\ 4096 <= cur /\ cur <= 140737479966720.
Definition INV_L (B : asyms) (MT : ameter_ops) (fuel : nat)
: rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 =>
k <= EV_LIB /\ acc <= ACC0 /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\
In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)) /\ req_size (c_n cx) = c_n cx /\
exists (cur rem bud c : Z),
ew E N_cur = Z_to_bv 64 cur /\ ew E N_rem = Z_to_bv 64 rem /\ ew E N_bud = Z_to_bv 64 bud /\
inv_cursor cx cur rem c /\ 1 <= bud <= 7 /\ (Z.to_nat bud <= fuel)%nat.
Definition INV_J (B : asyms) (MT : ameter_ops) (fuel : nat)
: rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 =>
k <= EV_LIB /\ acc <= ACC0 /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\
In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)) /\ req_size (c_n cx) = c_n cx /\
exists (cur rem bud c lead sel : Z),
ew E N_cur2 = Z_to_bv 64 cur /\ ew E N_rem2 = Z_to_bv 64 rem /\ ew E N_bud = Z_to_bv 64 bud /\
ew E N_lead = Z_to_bv 64 lead /\ ew E N_sel = Z_to_bv 64 sel /\
inv_cursor cx cur rem c /\ 1 <= bud <= 7 /\ (Z.to_nat bud <= fuel)%nat /\
0 <= lead <= 65535 /\ 0 <= sel <= 5.
Definition INV_C (B : asyms) (MT : ameter_ops) (fuel : nat)
: rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 =>
k <= EV_LIB /\ acc <= ACC0 /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\
In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)) /\ req_size (c_n cx) = c_n cx /\
exists (cur rem bud c lead sel : Z),
ew E N_cur2 = Z_to_bv 64 cur /\ ew E N_rem2 = Z_to_bv 64 rem /\ ew E N_bud = Z_to_bv 64 bud /\
ew E N_lead = Z_to_bv 64 lead /\ ew E N_fps = Z_to_bv 64 (qd_fps sel) /\
inv_cursor cx cur rem c /\ 1 <= bud <= 7 /\ (Z.to_nat bud <= fuel)%nat /\
0 <= lead <= 65535 /\ 0 <= sel <= 5.
Definition INV_X (B : asyms) (MT : ameter_ops)
: rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 =>
k <= EV_LIB /\ acc <= c_T cx /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)).
End inv.
