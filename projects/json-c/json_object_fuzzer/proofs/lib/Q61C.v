(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition SH (a : Z) : Z := a / 8 + A_SHADOW_OFS.

Definition gran (n k : Z) : Z := if 8 * k + 8 <=? n then 0 else n - 8 * k.

Lemma gran_cases n k : 0 <= k -> 8 * k < n ->
gran n k = 0 \/ (0 < gran n k < 8 /\ gran n k = n - 8 * k).
Proof. intros Hk Hn. unfold gran. destruct (Z.leb_spec0 (8 * k + 8) n); lia. Qed.

Lemma gran_range n k : 0 <= k -> 8 * k < n -> 0 <= gran n k < 8.
Proof. intros Hk Hn. destruct (gran_cases n k Hk Hn); lia. Qed.

Lemma gran_full n k : 8 * k + 8 <= n -> gran n k = 0.
Proof. intros H. unfold gran. destruct (Z.leb_spec0 (8 * k + 8) n); lia. Qed.

Lemma SH_add A k : A mod 8 = 0 -> SH (A + 8 * k) = SH A + k.
Proof. intros HA. unfold SH. Z.div_mod_to_equations. lia. Qed.

Lemma SH_of x A : A mod 8 = 0 -> A <= x -> SH x = SH A + (x / 8 - A / 8).
Proof. intros HA Hx. unfold SH. lia. Qed.

Lemma shadow_check_arith A n x s :
A mod 8 = 0 -> A <= x -> 1 <= s -> x + s <= A + n ->
let k := x / 8 - A / 8 in
0 <= k /\ 8 * k < n /\ SH x = SH A + k /\
(gran n k = 0 \/ (0 < gran n k < 8 /\ x mod 8 + s <= gran n k)).
Proof.
intros HA Hx Hs Hn. cbv zeta.
assert (K0 : 0 <= x / 8 - A / 8) by (Z.div_mod_to_equations; lia).
assert (K1 : 8 * (x / 8 - A / 8) < n) by (Z.div_mod_to_equations; lia).
split; [exact K0|]. split; [exact K1|]. split; [apply SH_of; assumption|].
unfold gran. destruct (Z.leb_spec0 (8 * (x / 8 - A / 8) + 8) n); [left; reflexivity| right].
Z.div_mod_to_equations. lia.
Qed.

Section WithSegs.
Variable segs : list Segment.
Implicit Types (m : word -> option byte).

Definition blk_shadow m (A n : Z) : Prop :=
0 <= A /\ A mod 8 = 0 /\ 0 <= n /\ SH A + (n + 7) / 8 <= KHI /\
forall k, 0 <= k -> 8 * k < n -> bytes_at segs m (SH A + k) [Z_to_bv 8 (gran n k)].

Definition tbl_shadow m : Prop :=
blk_shadow m 0x20efa 92 /\ blk_shadow m 0x20f7a 29952 /\ blk_shadow m 0x2a0e0 8704 /\
blk_shadow m 0x2cb80 1024 /\ blk_shadow m 0x2d080 2048 /\ blk_shadow m 0x2da80 1792 /\
blk_shadow m 0x2e340 4608.

Definition shadow_base m : Prop :=
ro_cells segs m A_SHADOW_GOT [C8 (Z_to_bv 64 A_SHADOW_CELL)] /\
ro_cells segs m A_SHADOW_CELL [C8 (Z_to_bv 64 A_SHADOW_OFS)].

Definition sh_lo (A : Z) : Z := SH A.
Definition sh_hi (A n : Z) : Z := SH A + (n + 7) / 8.

Lemma blk_shadow_facts m A n : blk_shadow m A n -> 0 <= A /\ A mod 8 = 0 /\ 0 <= n /\ SH A + (n + 7) / 8 <= KHI.
Proof. intros (H1 & H2 & H3 & H4 & _). auto. Qed.

Lemma SH_ge (a : Z) : 0 <= a -> 0x7fff8000 <= SH a.
Proof. intros H. unfold SH, A_SHADOW_OFS. pose proof (Z.div_pos a 8 H ltac:(lia)). lia. Qed.

Lemma disjoint_from_sub W B L b l :
disjoint_from W B L -> B <= b -> b + l <= B + L -> disjoint_from W b l.
Proof.
intros HD H1 H2. induction W as [|[lo hi] W IH]; cbn in *; [exact I|].
destruct HD as [HD1 HD2]. split; [lia| apply IH; exact HD2].
Qed.

Lemma blk_shadow_munch W m0 m A n :
blk_shadow m0 A n -> munch W m0 m -> disjoint_from W (SH A) ((n + 7) / 8) -> blk_shadow m A n.
Proof.
intros (HA0 & HA & Hn & HK & H) MU HD. split; [exact HA0|]. split; [exact HA|]. split; [exact Hn|]. split; [exact HK|].
intros k Hk Hkn. eapply bytes_at_transport; [apply H; assumption| exact MU|].
eapply disjoint_from_sub; [exact HD| lia|]. cbn. Z.div_mod_to_equations. lia.
Qed.

Lemma blk_shadow_read m A n x a :
blk_shadow m A n -> A <= x -> x < A + n -> a = wa (SH x) ->
ov_read_bytes segs m a 1 = Some [Z_to_bv 8 (gran n (x / 8 - A / 8))].
Proof.
intros (HA0 & HA & Hn & HK & H) H1 H2 ->.
pose proof (shadow_check_arith A n x 1 HA H1 ltac:(lia) ltac:(lia)) as (K0 & K1 & E & _).
rewrite E. replace (SH A + (x / 8 - A / 8)) with (SH A + (x / 8 - A / 8) + 0) by lia.
rewrite (bytes_at_read segs m (SH A + (x / 8 - A / 8)) [Z_to_bv 8 (gran n (x / 8 - A / 8))] 0 1);
[reflexivity| apply H; assumption| lia| cbn; lia].
Qed.

Lemma blk_shadow_read_munch W m0 m A n x a :
blk_shadow m0 A n -> munch W m0 m -> disjoint_from W (SH A) ((n + 7) / 8) ->
A <= x -> x < A + n -> a = wa (SH x) ->
ov_read_bytes segs m a 1 = Some [Z_to_bv 8 (gran n (x / 8 - A / 8))].
Proof. intros SHD MU HD H1 H2 Ha. eapply blk_shadow_read; [eapply blk_shadow_munch; eassumption| assumption..]. Qed.

End WithSegs.

Lemma sxb_small v : 0 <= v < 8 -> sxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof. intros Hv. apply sxb_b8. lia. Qed.

Lemma zxb_small v : 0 <= v < 8 -> zxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof. intros Hv. rewrite zxb_b8. f_equal. apply Z.mod_small. lia. Qed.

Lemma land_7 x : Z.land x 7 = x mod 8.
Proof. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma bv_signed_lit v : -2^63 <= v < 2^63 -> bv_signed (Z_to_bv 64 v) = v.
Proof.
intros Hv. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64) with 18446744073709551616 in *. change (Z.of_N 64 - 1) with 63.
change (2^63) with 9223372036854775808 in *. Z.div_mod_to_equations. lia.
Qed.

Ltac reg_key n := eval vm_compute in (bv_key (Z_to_bv 5 n)).

Ltac join1 ru pcj :=
lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
let pu := reg_key ru in
let R' := constr:(fun vu : word => tset pu vu R) in
let R'' := eval cbv beta iota delta [tset mkR] in R' in
apply (evt_cut segs (fun ms' : machine_state => exists vu : word, ms' = MS (R'' vu) F (Z_to_bv 64 pcj) fc rv m ro) Q)
end.
Ltac join2 r1 r2 pcj :=
lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
let p1 := reg_key r1 in let p2 := reg_key r2 in
let R' := constr:(fun v1 v2 : word => tset p2 v2 (tset p1 v1 R)) in
let R'' := eval cbv beta iota delta [tset mkR] in R' in
apply (evt_cut segs (fun ms' : machine_state => exists v1 v2 : word, ms' = MS (R'' v1 v2) F (Z_to_bv 64 pcj) fc rv m ro) Q)
end.
Ltac join3 r1 r2 r3 pcj :=
lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
let p1 := reg_key r1 in let p2 := reg_key r2 in let p3 := reg_key r3 in
let R' := constr:(fun v1 v2 v3 : word => tset p3 v3 (tset p2 v2 (tset p1 v1 R))) in
let R'' := eval cbv beta iota delta [tset mkR] in R' in
apply (evt_cut segs (fun ms' : machine_state => exists v1 v2 v3 : word, ms' = MS (R'' v1 v2 v3) F (Z_to_bv 64 pcj) fc rv m ro) Q)
end.

Ltac join3_set rS vS r1 r2 r3 pcj :=
lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
let pS := reg_key rS in let p1 := reg_key r1 in let p2 := reg_key r2 in let p3 := reg_key r3 in
let R' := constr:(fun v1 v2 v3 : word => tset p3 v3 (tset p2 v2 (tset p1 v1 (tset pS vS R)))) in
let R'' := eval cbv beta iota delta [tset mkR] in R' in
apply (evt_cut segs (fun ms' : machine_state => exists v1 v2 v3 : word, ms' = MS (R'' v1 v2 v3) F (Z_to_bv 64 pcj) fc rv m ro) Q)
end.
Ltac join_done := apply evt_done; repeat eexists; reflexivity.

Ltac join_k := let ms := fresh "ms" in let JH := fresh "JH" in
intros ms JH;
repeat (lazymatch type of JH with ex _ => let w := fresh "jw" in destruct JH as [w JH] end);
subst ms.

Ltac shadow_addr_tac :=
unfold wa, SH, A_SHADOW_OFS; f_equal; rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; tbl_lia.

Ltac shadow_read SHD rt x :=
let a := tbl_getreg rt in
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
lazymatch type of SHD with blk_shadow _ ?m0 ?A ?n =>
let H := fresh "RD" in
assert (H : ov_read_bytes segs m a 1 = Some [Z_to_bv 8 (gran n (x / 8 - A / 8))]);
[ lazymatch goal with
| MU : munch ?W m0 m |- _ =>
apply (blk_shadow_read_munch segs W m0 m A n x a SHD MU);
[ let SFx := fresh "SFx" in pose proof (blk_shadow_facts _ _ _ _ SHD) as SFx; pose proof (SH_ge _ (proj1 SFx));
cbn [disjoint_from]; unfold KHI in *; lia
| tbl_lia | tbl_lia | shadow_addr_tac ]
| _ => fail "shadow_read: no hypothesis munch W m0 m linking" m0 "to" m
end
| ]
end end.

Ltac shadow_lb SHD rt x s v GC :=
shadow_read SHD rt x;
step; tbl_clear;
lazymatch type of SHD with blk_shadow _ _ ?A ?n =>
let F := fresh "SF" in
pose proof (blk_shadow_facts _ _ _ _ SHD) as F;
pose proof (shadow_check_arith A n x s ltac:(apply F) ltac:(tbl_lia) ltac:(lia) ltac:(tbl_lia)) as GC;
clear F;
cbv zeta in GC;
let VR := fresh "VR" v in
assert (VR := gran_range n (x / 8 - A / 8) ltac:(apply GC) ltac:(apply GC));
apply proj2 in GC; apply proj2 in GC; apply proj2 in GC;
generalize dependent (gran n (x / 8 - A / 8)); intros v GC VR;
rewrite ?(sxb_small v VR), ?(zxb_small v VR)
end.

Ltac shadow_bnez ru pcj GC :=
join1 ru pcj;
[ step;
let Kb := fresh "Kb" in
if_cases Kb; zify_cond Kb;
[
step; step;
let K2 := fresh "Ks" in
first [ if_cases K2 | step; if_cases K2 ];
zify_cond K2; rewrite ?land_7, ?bv_signed_lit in K2 by lia;
first [ join_done | step; join_done | exfalso; lia ]
| join_done ]
| join_k; clear GC ].

Ltac shadow_bnez8 GC :=
step;
let Kb := fresh "Kb" in
if_cases Kb; zify_cond Kb; [ exfalso; lia | clear Kb GC ].
