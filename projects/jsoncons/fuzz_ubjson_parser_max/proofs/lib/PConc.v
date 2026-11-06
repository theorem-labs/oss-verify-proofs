(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BigLinkZA.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan AsanPlanCore
BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
intros A Pz. rewrite (BG.word_of_unsigned (edenot E e) (z mod BL.MM) (L5KA.zpolyA_sound E Vz e z A Pz)).
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, BL.MM. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma u64_of_KWord8a segs E M b off e a v a' : kentry_ok segs E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at segs M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u64_of_KWord8; eauto. Qed.
Lemma u32_of_KWord4a segs E M b off e a v a' : kentry_ok segs E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at segs M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u32_of_KWord4; eauto. Qed.
Lemma u8_of_KWord1a segs E M b off e a v a' : kentry_ok segs E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at segs M a' v.
Proof. intros K Ha Hv Hr ->. eapply L5K.u8_of_KWord1; eauto. Qed.
Lemma u8x2_of_KWord2a segs E M b off e a v a' v0 v1 : kentry_ok segs E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
L5.u8_at segs M a' v0 /\ L5.u8_at segs M (a' + 1) v1.
Proof.
intros K Ha Hv -> -> ->. cbn [kentry_ok] in K. destruct K as (_ & _ & Rd).
rewrite L5K.adenot_e, Ha in Rd. rewrite (BG.word_of_unsigned _ _ Hv) in Rd.
pose proof (bv_unsigned_in_range 64 (edenot E e)) as Rg. rewrite Hv in Rg. change (bv_modulus 64) with (2 ^ 64) in Rg.
unfold word_to_le_bytes in Rd. rewrite Z_to_bv_unsigned in Rd. unfold bv_wrap in Rd. change (bv_modulus 64) with (2 ^ 64) in Rd.
rewrite (Z.mod_small v (2 ^ 64)) in Rd by (clear - Rg; lia). cbn [Z_to_le_bytes rdn] in Rd. unfold L5.u8_at.
assert (E1 : (Z_to_bv 64 (a + off) + 1 = Z_to_bv 64 (a + off + 1))%bv).
{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (bv_unsigned (1 : bv 64)) with 1. apply Z.add_mod_idemp_l. clear; lia. }
rewrite E1 in Rd.
destruct (match M (Z_to_bv 64 (a + off)) with Some b0 => Some b0 | None => seg_rom segs (Z_to_bv 64 (a + off)) end) as [x|] eqn:X; [|discriminate].
destruct (match M (Z_to_bv 64 (a + off + 1)) with Some b0 => Some b0 | None => seg_rom segs (Z_to_bv 64 (a + off + 1)) end) as [y|] eqn:Y; [|discriminate].
injection Rd as Ex Ey. split.
- cbn [rdn]. rewrite X. subst x. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_mod by (clear; lia). reflexivity.
- cbn [rdn]. rewrite Y. subst y. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 8) with 256. rewrite Z.mod_mod by (clear; lia). reflexivity.
Qed.
Lemma defined_of_KUnka segs E M b off ne a n a' : kentry_ok segs E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof. intros K Ha Hn ->. eapply L5K.defined_of_KUnk; eauto. Qed.
Lemma u8_of_KWord1ma segs E M b off e a v a' v' : kentry_ok segs E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at segs M a' v'.
Proof. intros K Ha Hv -> ->. eapply L5KA.u8_of_KWord1_mod; eauto. Qed.
Lemma zeros_of_KZeroa segs E M b off ne a n a' : kentry_ok segs E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof. intros K Ha Hn ->. eapply L5KA.zeros_of_KZero; eauto. Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof. intros Ha Hm. pose proof (L5K.land_le_r a m Ha ltac:(lia)). lia. Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
intros Ha Hb. split. apply Z.lor_nonneg; lia.
destruct (Z.eq_dec a 0) as [->|Na]. rewrite Z.lor_0_l. lia. destruct (Z.eq_dec b 0) as [->|Nb]. rewrite Z.lor_0_r. lia.
apply (Z.log2_lt_cancel). rewrite Z.log2_lor by lia.
apply Z.max_lub_lt; apply Z.log2_lt_pow2; try lia; change (2 ^ Z.log2 256) with 256; lia.
Qed.
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof. intros Ha Hm. rewrite Z.land_comm. exact (proj2 (L5K.land_le_r m a Hm Ha)). Qed.
Ltac zfacts :=
repeat (match goal with |- context [Z.land ?a ?m] =>
lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
repeat (match goal with |- context [?a / ?c] =>
lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
intros Ha. assert (E : forallb (fun i => let x := Z.of_nat i in (0 <=? (Z.land x 18446744073709551613 + 2) mod 2 ^ 64) && ((Z.land x 18446744073709551613 + 2) mod 2 ^ 64 <? 256)) (seq 0 256) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in E. specialize (E (Z.to_nat a) ltac:(apply in_seq; lia)). cbn zeta in E. rewrite Z2Nat.id in E by lia. apply andb_prop in E as [E1 E2]. lia.
Qed.
Ltac byte_go :=
lazymatch goal with
| |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
| |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
| |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
| _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
end.
Ltac byte_tac0 k := k; byte_go.
Tactic Notation "byte_tac" tactic(k) := byte_tac0 k.
Ltac solve_modk k :=
repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (k; zfacts; lia) end;
first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
| symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
| symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
L5K.norm_expr; eapply L5KA.zpolyA_val;
[ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Ltac exactA H :=
first [ exact H
| lazymatch goal with
| |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
| |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
| |- L5.u32_at _ _ ?a _ => lazymatch type of H with L5.u32_at _ _ ?b _ => replace a with b by (clear; lia) end
| |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
| |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
| |- L5KA.zeros_at _ ?a _ => lazymatch type of H with L5KA.zeros_at _ ?b _ => replace a with b by (clear; lia) end
end; exact H ].
Ltac den_tac := first [reflexivity | lia | idtac].
Ltac apc_norm :=
repeat match goal with
| |- context [APC.eadd ?a ?b] => let t := eval vm_compute in (APC.eadd a b) in change (APC.eadd a b) with t
| |- context [APC.esub ?a ?b] => let t := eval vm_compute in (APC.esub a b) in change (APC.esub a b) with t
| |- context [APC.escale ?c ?e] => let t := eval vm_compute in (APC.escale c e) in change (APC.escale c e) with t
| |- context [APC.eaddz ?a ?z] => let t := eval vm_compute in (APC.eaddz a z) in change (APC.eaddz a z) with t
end.
Ltac zp_norm := repeat (match goal with |- context [(?a <=? ?b) && (?c <? ?d)] => let r := eval vm_compute in ((a <=? b) && (c <? d)) in change ((a <=? b) && (c <? d)) with r end);
repeat (match goal with |- context [2 ^ ?s] => let r := eval vm_compute in (2 ^ s) in change (2 ^ s) with r end); lazy beta iota zeta.
Ltac zp_mods := repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia) end.
Ltac slotP ZA :=
first [ assumption | reflexivity
| (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].
Ltac wordP' ZA AG :=
eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
| cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].
Tactic Notation "qpsp" hyp(X) ident(A) ident(B) :=
pose proof (proj1 X) as A; move A before X; pose proof (proj2 X) as B; move B before X; clear X.
Tactic Notation "qZA" hyp(E) hyp(V) := assert (ZA : forall j, bv_unsigned (ev E j) = V j).
Tactic Notation "qHR" hyp(E) hyp(R) constr(r) hyp(Z) :=
assert (HR : regs_ok E r R); [ apply BG.regs_ok_of_slots; [ reflexivity | cbn [BG.slots tl r nth]; apc_norm; repeat split; slotP Z ] | ].
Tactic Notation "qHK" constr(sg) hyp(E) hyp(M) constr(k) := assert (HK : know_ok sg E M k).
Ltac qkopen := lazymatch goal with |- know_ok _ _ _ ?k => unfold know_ok, k end.
Ltac qknil := apply Forall_nil.
Ltac qkKRange := apply Forall_cons; [ eapply L5K.kentry_KRange | ].
Ltac qkKRange_andlit := apply Forall_cons; [ eapply L5K.kentry_KRange_andlit | ].
Ltac qkKAlign := apply Forall_cons; [ eapply L5K.kentry_KAlign | ].
Ltac qkKWr := apply Forall_cons; [ eapply L5K.kentry_KWr | ].
Ltac qkKUnk := apply Forall_cons; [ eapply L5K.kentry_KUnk | ].
Ltac qkKDisj := apply Forall_cons; [ eapply L5K.kentry_KDisj | ].
Ltac qkKImg := apply Forall_cons; [ eapply L5K.kentry_KImg | ].
Ltac qkKWord8 := apply Forall_cons; [ eapply L5K.kentry_KWord8 | ].
Ltac qkKWord4 := apply Forall_cons; [ eapply L5K.kentry_KWord4 | ].
Ltac qkKWord1 := apply Forall_cons; [ eapply L5K.kentry_KWord1 | ].
Tactic Notation "qe" hyp(Z) "(" hyp_list(l) ")" := evalEk Z ltac:(clear - l).
Tactic Notation "qx" hyp(Z) hyp(A) "(" hyp_list(l) ")" := evalEk' Z A ltac:(clear - l).
Tactic Notation "ql" "(" hyp_list(l) ")" := clear - l; lia.
Tactic Notation "qa" hyp(H) := exactA H.
Tactic Notation "qc" hyp(A) hyp(B) := exact (conj A B).
Tactic Notation "qg" hyp(H) := generalize H; clear; intro; lia.
Tactic Notation "qb" "(" hyp_list(l) ")" := byte_tac ltac:(clear - l).
Tactic Notation "qh" hyp(H) constr(n) := apply H; apply (nth_error_In _ n); reflexivity.
Tactic Notation "qdss" constr(ax) hyp(fx) hyp(E) hyp(R) hyp(M) hyp(HR) hyp(HK) :=
pvz_hg ltac:(idtac; destruct (ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
Tactic Notation "qnx" hyp(H) constr(n) := let v := eval vm_compute in n in change n with v in H.
Tactic Notation "qps1" hyp(Hms) hyp(Hregs) :=
lazymatch type of Hms with context [SR.ps_pc ?p] =>
let b := eval red in p in lazymatch b with SR.PS ?pc ?rg _ _ => change (SR.ps_pc p) with pc in Hms; change (SR.ps_regs p) with rg in Hregs end end.
Tactic Notation "qps2" hyp(Hc) :=
lazymatch type of Hc with context [SR.ps_cells ?p] =>
let b := eval red in p in lazymatch b with SR.PS _ _ _ ?cl => change (SR.ps_cells p) with cl in Hc end end.
Tactic Notation "qfr" hyp(H) := apply H; lazymatch goal with |- SGP.outside _ ?f _ => unfold f end.
Ltac qocons := eapply L5K.outside_cons_e.
Ltac qonil := apply L5K.outside_nil_e.
Tactic Notation "qfrz" hyp(F) hyp(Hi) := apply F; rewrite ?BG.unsigned_lit by exact Hi; assumption.
Tactic Notation "qn1" hyp(H) hyp(p) := apply L5K.nth_error_single in H; subst p.
Tactic Notation "qn2" hyp(H) := apply L5K.nth_error_pair in H; destruct H as [[-> ->] | [-> ->]].
Tactic Notation "qkept" hyp(E) hyp(E') hyp(R) hyp(R') constr(K) hyp(HR) hyp(Ha) hyp(Hr) hyp(j) hyp(Hj) :=
apply (BG.kept_regs E E' R R' _ _ _ _ K HR Ha Hr j Hj).
Tactic Notation "qor" hyp(E') hyp(R') hyp(Hr) hyp(Z) hyp(Ha) :=
lazymatch type of Hr with context [nth _ ?ro (ELit 0)] =>
lazymatch goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?i)) = _ =>
rewrite (BG.out_reg ro E' R' i Hr) by (clear; lia); cbn [nth ro]; first [reflexivity | wordP' Z Ha] end end.
Ltac qW8 := eapply u64_of_KWord8a.
Ltac qW4 := eapply u32_of_KWord4a.
Ltac qW1 := eapply u8_of_KWord1a.
Ltac qfrw := lazymatch goal with
| |- ?A /\ _ => assert (FRW : A)
| |- ?T => let b := eval red in T in lazymatch b with ?A /\ _ => assert (FRW : A) end end.
Tactic Notation "qD" hyp(Z) "(" hyp_list(a) ")" "(" hyp_list(c) ")" hyp(H) :=
qkKDisj; [qe Z (a) | qe Z ( ) | qe Z (c) | qe Z ( ) | qg H | ].
Tactic Notation "q8" hyp(Z) "(" hyp_list(a) ")" "(" hyp_list(b) ")" hyp(H) :=
qkKWord8; [qe Z (a) | qe Z (b) | ql (a) | ql (a) | qa H | ].
Tactic Notation "q4" hyp(Z) "(" hyp_list(a) ")" "(" hyp_list(b) ")" hyp(H) :=
qkKWord4; [qe Z (a) | qe Z (b) | ql (a) | ql (a) | qa H | ].
Tactic Notation "qWr" hyp(Z) "(" hyp_list(a) ")" hyp(H) :=
qkKWr; [qe Z (a) | qe Z ( ) | ql (a) | ql (a) | ql (a) | qa H | ].
Tactic Notation "qUk" hyp(Z) "(" hyp_list(a) ")" hyp(H) :=
qkKUnk; [qe Z (a) | qe Z ( ) | ql (a) | ql (a) | ql (a) | qa H | ].
Tactic Notation "qA" hyp(Z) "(" hyp_list(a) ")" hyp(H) :=
qkKAlign; [qe Z (a) | ql ( ) | exact H | ].
Tactic Notation "qR" hyp(Z) "(" hyp_list(a) ")" hyp(L) hyp(R) :=
qkKRange; [qe Z (a) | qc L R | ].
Tactic Notation "q1" hyp(Z) "(" hyp_list(a) ")" hyp(H) :=
qkKWord1; [qe Z (a) | qe Z ( ) | ql (a) | ql (a) | qb ( ) | qa H | ].
Tactic Notation "qI" hyp(H) := qkKImg; [ql ( ) | ql ( ) | exact H | ].
Tactic Notation "qr8" hyp(Hc) hyp(Z) hyp(A) constr(k) "(" hyp_list(a) ")" "(" hyp_list(b) ")" :=
qW8; [qh Hc k | qx Z A (a) | qx Z A (b) | ql ( )].
Tactic Notation "qr4" hyp(Hc) hyp(Z) hyp(A) constr(k) "(" hyp_list(a) ")" "(" hyp_list(b) ")" :=
qW4; [qh Hc k | qx Z A (a) | qx Z A (b) | ql ( )].
Tactic Notation "qr1" hyp(Hc) hyp(Z) hyp(A) constr(k) "(" hyp_list(a) ")" "(" hyp_list(b) ")" :=
qW1; [qh Hc k | qx Z A (a) | qx Z A (b) | qb ( ) | ql ( )].
Ltac qkKZero := apply Forall_cons; [ eapply L5KA.kentry_KZero | ].
Ltac qW1m := eapply u8_of_KWord1ma.
Ltac qU := eapply defined_of_KUnka.
Ltac qZz := eapply zeros_of_KZeroa.
Ltac qW2x := eapply u8x2_of_KWord2a.
Tactic Notation "qZ" hyp(Z) "(" hyp_list(a) ")" hyp(H) :=
qkKZero; [qe Z (a) | qe Z ( ) | ql (a) | ql (a) | ql (a) | qa H | ].
Tactic Notation "qr1m" hyp(Hc) hyp(Z) hyp(A) constr(k) "(" hyp_list(a) ")" "(" hyp_list(b) ")" :=
qW1m; [qh Hc k | qx Z A (a) | qx Z A (b) | ql ( ) | vm_compute; reflexivity].
Tactic Notation "qrU" hyp(Hc) hyp(Z) hyp(A) constr(k) "(" hyp_list(a) ")" "(" hyp_list(b) ")" :=
qU; [qh Hc k | qx Z A (a) | qx Z A (b) | ql ( )].
