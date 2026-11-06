(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcR.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PStmt. Import PStmt.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BigLinkZA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ja0PlanKit AsanPlanCore
BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_arvCW LibSegJa_arvCK1 LibSegJa_arvCK2 LibSegJa_arvSG0 LibSegJa_arvSGe LibSegJa_arvSF LibSegJa_arvHG0 LibSegJa_arvHGe LibSegJa_arvHF LibSegJa_arvSW LibSegJa_arvSK.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMARVP6.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
intros A Pz. rewrite (BG.word_of_unsigned (edenot E e) (z mod BL.MM) (L5KA.zpolyA_sound E Vz e z A Pz)).
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, BL.MM. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u64_of_KWord8; eauto. Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u32_of_KWord4; eauto. Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof. intros K Ha Hv Hr ->. eapply L5K.u8_of_KWord1; eauto. Qed.
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
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
destruct (match M (Z_to_bv 64 (a + off)) with Some b0 => Some b0 | None => seg_rom RSEGS (Z_to_bv 64 (a + off)) end) as [x|] eqn:X; [|discriminate].
destruct (match M (Z_to_bv 64 (a + off + 1)) with Some b0 => Some b0 | None => seg_rom RSEGS (Z_to_bv 64 (a + off + 1)) end) as [y|] eqn:Y; [|discriminate].
injection Rd as Ex Ey. split.
- cbn [rdn]. rewrite X. subst x. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_mod by (clear; lia). reflexivity.
- cbn [rdn]. rewrite Y. subst y. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 8) with 256. rewrite Z.mod_mod by (clear; lia). reflexivity.
Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof. intros K Ha Hn ->. eapply L5K.defined_of_KUnk; eauto. Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof. intros K Ha Hv -> ->. eapply L5KA.u8_of_KWord1_mod; eauto. Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
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
Local Ltac zfacts :=
repeat (match goal with |- context [Z.land ?a ?m] =>
lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
repeat (match goal with |- context [?a / ?c] =>
lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
intros Ha. assert (E : forallb (fun i => let x := Z.of_nat i in (0 <=? (Z.land x 18446744073709551613 + 2) mod 2 ^ 64) && ((Z.land x 18446744073709551613 + 2) mod 2 ^ 64 <? 256)) (seq 0 256) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in E. specialize (E (Z.to_nat a) ltac:(apply in_seq; lia)). cbn zeta in E. rewrite Z2Nat.id in E by lia. apply andb_prop in E as [E1 E2]. lia.
Qed.
Local Ltac byte_go :=
lazymatch goal with
| |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
| |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
| |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
| _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
end.
Local Ltac byte_tac0 k := k; byte_go.
Tactic Notation "byte_tac" tactic(k) := byte_tac0 k.
Local Ltac solve_modk k :=
repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (k; zfacts; lia) end;
first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
| symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
| symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
L5K.norm_expr; eapply L5KA.zpolyA_val;
[ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Local Ltac exactA H :=
first [ exact H
| lazymatch goal with
| |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
| |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
| |- L5.u32_at _ _ ?a _ => lazymatch type of H with L5.u32_at _ _ ?b _ => replace a with b by (clear; lia) end
| |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
| |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
| |- L5KA.zeros_at _ ?a _ => lazymatch type of H with L5KA.zeros_at _ ?b _ => replace a with b by (clear; lia) end
end; exact H ].
Local Ltac den_tac := first [reflexivity | lia | idtac].
Local Ltac apc_norm :=
repeat match goal with
| |- context [APC.eadd ?a ?b] => let t := eval vm_compute in (APC.eadd a b) in change (APC.eadd a b) with t
| |- context [APC.esub ?a ?b] => let t := eval vm_compute in (APC.esub a b) in change (APC.esub a b) with t
| |- context [APC.escale ?c ?e] => let t := eval vm_compute in (APC.escale c e) in change (APC.escale c e) with t
| |- context [APC.eaddz ?a ?z] => let t := eval vm_compute in (APC.eaddz a z) in change (APC.eaddz a z) with t
end.
Local Ltac zp_norm := repeat (match goal with |- context [(?a <=? ?b) && (?c <? ?d)] => let r := eval vm_compute in ((a <=? b) && (c <? d)) in change ((a <=? b) && (c <? d)) with r end);
repeat (match goal with |- context [2 ^ ?s] => let r := eval vm_compute in (2 ^ s) in change (2 ^ s) with r end); lazy beta iota zeta.
Local Ltac zp_mods := repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia) end.
Local Ltac slotP ZA :=
first [ assumption | reflexivity
| (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].
Local Ltac wordP' ZA AG :=
eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
| cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].
Definition KS_arvCW_0 : list nat := Eval vm_compute in (BG.kept_list 72 LibSegJa_arvCW.regs0 LibSegJa_arvCW.regs_out0).
Lemma KS_arvCW_0_ok : BG.kept_ok 72 LibSegJa_arvCW.regs0 LibSegJa_arvCW.regs_out0 KS_arvCW_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arvCW_1 : list nat := Eval vm_compute in (BG.kept_list 72 LibSegJa_arvCW.regs0 LibSegJa_arvCW.regs_out1).
Lemma KS_arvCW_1_ok : BG.kept_ok 72 LibSegJa_arvCW.regs0 LibSegJa_arvCW.regs_out1 KS_arvCW_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition arvCW_conc_s := ",4?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v33p#2#40S,2_v2#80S,8v2S,9_v2#80S,;v33S,12+/v2?#8#7???8000S,13v2?S,14v24S,15v26S,16v25S,17+v2?#;0S,18#1S,1:#7???8000S,1;v2?O#10000#134000La#13:<?8#7???8000Ma#13:=00#1La#134648#124=;0B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#691000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#80#80v24#180B#691000v26#7??????????0Hv26#8P#7???7000#100000001000v26#10Ka+/v26#8#7???8000#2Iv26#10P_v2#80#80v26#10Pv24#180v26#10B#691000v2?#7????????>00Hv2?#20Jav2?#200Iv2?#200P#7???7000#100000001000v2?#200I+/v2?#8#7???8000#40La+v2?#1?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#200v30#1P_v2#80#80v2?#200P_v2#80#80v30#1Pv24#180v2?#200Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#40Pv26#10v2?#200Pv26#10v30#1P+/v26#8#7???8000#2+/v2?#8#7???8000#40Pv2?#200#10000#124000P+/v2?#8#7???8000#40#134648#8B#691000v25#7??????????8Hv25#8P#7???7000#100000001000v25#8Ka+/v25#8#7???8000#1Iv25#8P_v2#80#80v25#8Lav25#12<940Ka#8001=928#10Na+v24#10#Pv24#180v25#8Pv26#10v25#8P+/v2?#8#7???8000#40#8001=928#10Pv2?#200v25#8Pv30#1v25#8P+/v2?#8#7???8000#40+/v25#8#7???8000#1Mav26#,,2,2X#:=7<8#:>468Y,,6X#:=7<8#:>974Y,1T,1#:=7>0T,:v26T,;#7T,18#7"%pstring.
Lemma arvCW_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arvCW_0; KS_arvCW_1] fx R M V arvCW_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arvCW_0; KS_arvCW_1] LibSegJa_arvCW.regs0 LibSegJa_arvCW.kn0 LibSegJa_arvCW.BR LibSegJa_arvCW.PSS LibSegJa_arvCW.NX0 LibSegJa_arvCW.F0 710600 LibSegJa_arvCW.seg_sound_ax fx R M V arvCW_conc_s. Qed.
Definition KS_arvCK1 : list nat := Eval vm_compute in (BG.kept_list 72 LibSegJa_arvCK1.regs0 LibSegJa_arvCK1.regs_out0).
Lemma KS_arvCK1_ok : BG.kept_ok 72 LibSegJa_arvCK1.regs0 LibSegJa_arvCK1.regs_out0 KS_arvCK1 = true. Proof. vm_compute. reflexivity. Qed.
Definition arvCK1_conc_s := ",4=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40S,2_v2#80S,8v2S,9_v2#80S,12+/v2?#8#7???8000S,13v2?S,14v24S,15v26S,16v25S,17+v2?#;0S,18#1S,1:#7???8000S,1;v2?O#10000#134000La#13:<?8#7???8000Ma#13:=00#1La#134648#124=;0B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#691000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#80#80v24#180B#691000v26#7??????????0Hv26#8P#7???7000#100000001000v26#10Ka+/v26#8#7???8000#2Iv26#10P_v2#80#80v26#10Pv24#180v26#10B#691000v2?#7????????>00Hv2?#20Jav2?#200Iv2?#200P#7???7000#100000001000v2?#200I+/v2?#8#7???8000#40La+v2?#1?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#200v30#1P_v2#80#80v2?#200P_v2#80#80v30#1Pv24#180v2?#200Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#40Pv26#10v2?#200Pv26#10v30#1P+/v26#8#7???8000#2+/v2?#8#7???8000#40Pv2?#200#10000#124000P+/v2?#8#7???8000#40#134648#8B#691000v25#7??????????8Hv25#8P#7???7000#100000001000v25#8Ka+/v25#8#7???8000#1Iv25#8P_v2#80#80v25#8Lav25#12<940Ka#8001=928#10Na+v24#10#Pv24#180v25#8Pv26#10v25#8P+/v2?#8#7???8000#40#8001=928#10Pv2?#200v25#8Pv30#1v25#8P+/v2?#8#7???8000#40+/v25#8#7???8000#1Mav26#,1++/v2?#8#7???8000##40,1,5X#:>468#:>474Y,T,;+v2?#<0Nb+/v2?#8#7???8019#Nb+/v2?#8#7???8018#"%pstring.
Lemma arvCK1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arvCK1] fx R M V arvCK1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arvCK1] LibSegJa_arvCK1.regs0 LibSegJa_arvCK1.kn0 LibSegJa_arvCK1.BR LibSegJa_arvCK1.PSS LibSegJa_arvCK1.NX0 LibSegJa_arvCK1.F0 713832 LibSegJa_arvCK1.seg_sound_ax fx R M V arvCK1_conc_s. Qed.
Definition KS_arvCK2 : list nat := Eval vm_compute in (BG.kept_list 72 LibSegJa_arvCK2.regs0 LibSegJa_arvCK2.regs_out0).
Lemma KS_arvCK2_ok : BG.kept_ok 72 LibSegJa_arvCK2.regs0 LibSegJa_arvCK2.regs_out0 KS_arvCK2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvCK2_conc (fx : FPState) (R : bvmap 5 (bv 64)) (M : word -> option byte) (V : nat -> Z) :
ltac:(PStmt.mk RSEGS aligned srl_range L5KA.zeros_at [KS_arvCK2] fx R M V ",4?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40S,2_v2#80S,8v2S,9_v2#80S,;+v2?#<0S,12+/v2?#8#7???8000S,13v2?S,14v24S,15v26S,16v25S,17+v2?#;0S,18#1S,1:#7???8000S,1;v2?O#10000#134000La#13:<?8#7???8000Ma#13:=00#1La#134648#124=;0B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#691000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#80#80v24#180B#691000v26#7??????????0Hv26#8P#7???7000#100000001000v26#10Ka+/v26#8#7???8000#2Iv26#10P_v2#80#80v26#10Pv24#180v26#10B#691000v2?#7????????>00Hv2?#20Jav2?#200Iv2?#200P#7???7000#100000001000v2?#200I+/v2?#8#7???8000#40La+v2?#1?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#200v30#1P_v2#80#80v2?#200P_v2#80#80v30#1Pv24#180v2?#200Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#40Pv26#10v2?#200Pv26#10v30#1P+/v26#8#7???8000#2+/v2?#8#7???8000#40Pv2?#200#10000#124000P+/v2?#8#7???8000#40#134648#8B#691000v25#7??????????8Hv25#8P#7???7000#100000001000v25#8Ka+/v25#8#7???8000#1Iv25#8P_v2#80#80v25#8Lav25#12<940Ka#8001=928#10Na+v24#10#Pv24#180v25#8Pv26#10v25#8P+/v2?#8#7???8000#40#8001=928#10Pv2?#200v25#8Pv30#1v25#8P+/v2?#8#7???8000#40+/v25#8#7???8000#1Mav26#Ka+/+v2?#<0#8#7???8000#2,3+v24#8#1++/v2?#8#7???8000##40+v2?#<0#10,1,12X#:>474#:>110Y,T,1#:>4<<T,:^#?#??????????????8T,;#1T,<#T,=v24T,>v26T,?#:8810Nb+/v2?#8#7???8016#?8Nb+v24#8#1Nb+/v2?#8#7???8019#?8Nb+/v2?#8#7???8018#?8Lb+v2?#<8#1Lb+v2?#<0+v2?#;0Jbv2?#<0Jb+v2?#=0#130Kb+/v2?#8#7???801:_+*-1/v2?#8/+v2?#<0#8#18"%pstring).
Proof.
intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G11 G18 G19 G20 G21 G22 G23 G24 G26 G27 K0 K1 K2 K3 pvzI7 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13 K14 pvzI9 K16 K17 K18 K19 K20 K21 pvzI10 K23 K24 K25 K26 K27 K28 pvzI11 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 pvzI12 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59.
pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K15l; move K15l before pvzI9; pose proof (proj2 pvzI9) as K15r; move K15r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K22l; move K22l before pvzI10; pose proof (proj2 pvzI10) as K22r; move K22r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K29l; move K29l before pvzI11; pose proof (proj2 pvzI11) as K29r; move K29r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K43l; move K43l before pvzI12; pose proof (proj2 pvzI12) as K43r; move K43r before pvzI12; clear pvzI12.
set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
{ unfold VzN. BigLinkZA.za_tac0 49%nat. }
assert (HR: regs_ok E LibSegJa_arvCK2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl LibSegJa_arvCK2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
assert (HK: know_ok RSEGS E M LibSegJa_arvCK2.kn0).
{ unfold know_ok, LibSegJa_arvCK2.kn0.
apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K3]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K4l K4r) | exact (conj K4l K4r)]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K4l K4r) | clear; lia | exact K5]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K4l K4r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K4l K4r; lia | clear - HV2l HV2r K4l K4r; lia | clear - HV2l HV2r K4l K4r; lia | exactA K6]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | exact (conj K7l K7r)]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | clear; lia | exact K8]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r; lia | clear - HV36l HV36r K7l K7r; lia | clear - HV36l HV36r K7l K7r; lia | exactA K10]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r; lia | clear - HV36l HV36r K7l K7r; lia | clear - HV36l HV36r K7l K7r; lia | exactA K11]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r; lia | clear - HV36l HV36r K7l K7r; lia | clear - HV36l HV36r K7l K7r; lia | exactA K12]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r; lia | clear - HV36l HV36r K7l K7r; lia | clear - HV36l HV36r K7l K7r; lia | exactA K13]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K4l K4r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K15l K15r) | exact (conj K15l K15r)]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K15l K15r) | clear; lia | exact K16]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K15l K15r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K15l K15r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K15l K15r; lia | clear - HV38l HV38r K15l K15r; lia | clear - HV38l HV38r K15l K15r; lia | exactA K18]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K15l K15r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K15l K15r; lia | clear - HV38l HV38r K15l K15r; lia | clear - HV38l HV38r K15l K15r; lia | exactA K19]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K4l K4r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K15l K15r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K15l K15r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | exact (conj K22l K22r)]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | clear; lia | exact K23]. }
apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K22l K22r; lia | clear - HV47l HV47r K22l K22r; lia | clear - HV47l HV47r K22l K22r; lia | exactA K24]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K22l K22r; lia | clear - HV47l HV47r K22l K22r; lia | clear - HV47l HV47r K22l K22r; lia | exactA K25]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K22l K22r; lia | clear - HV47l HV47r K22l K22r; lia | clear - HV47l HV47r K22l K22r; lia | exactA K27]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | clear - HV47l HV47r K22l K22r; lia | clear - HV47l HV47r K22l K22r; lia | exactA K28]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | exact (conj K29l K29r)]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K29l K29r; lia | clear - HV48l HV48r K29l K29r; lia | clear - HV48l HV48r K29l K29r; lia | exactA K30]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K4l K4r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K4l K4r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K15l K15r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K15l K15r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K15l K15r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K43l K43r) | exact (conj K43l K43r)]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K43l K43r) | clear; lia | exact K44]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K43l K43r; lia | clear - HV37l HV37r K43l K43r; lia | clear - HV37l HV37r K43l K43r; lia | exactA K46]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K43l K43r; lia | clear - HV37l HV37r K43l K43r; lia | clear - HV37l HV37r K43l K43r; lia | exactA K47]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K4l K4r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K43l K43r; lia | clear - HV37l HV37r K43l K43r; lia | exactA K49]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K50]. }
apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K7l K7r; lia | clear - HV36l HV36r K7l K7r; lia | byte_tac ltac:(clear) | exactA K51]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K15l K15r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | generalize K53; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K54; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | generalize K55; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | generalize K56; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | generalize K57; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV38l HV38r K15l K15r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K15l K15r; lia | clear - HV38l HV38r K15l K15r; lia | exactA K58]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K22l K22r; lia | clear - HV47l HV47r K22l K22r; lia | clear - HV47l HV47r K22l K22r; lia | exactA K59]. }
apply Forall_nil. }
pvz_hg ltac:(idtac; destruct (LibSegJa_arvCK2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
change LibSegJa_arvCK2.NX0 with 72%nat in Hag.
exists fx', R', M'. pvz_linconj. split. exact Hgr.
assert (FRW: forall a : word, ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 64) -> ~ ((vz_47 + 192) <= bv_unsigned a < (vz_47 + 192) + 16) -> M' a = M a).
{ intros a Hn0 Hn1 Hn2. apply Hfr. unfold LibSegJa_arvCK2.F0.
eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K7l K7r Hn0; lia |].
eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K22l K22r Hn1; lia |].
eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K22l K22r Hn2; lia |].
apply L5K.outside_nil_e. }
split. exact FRW.
split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
apply L5K.nth_error_single in Hnth. subst ps.
change (SR.ps_pc LibSegJa_arvCK2.ps0) with 0xae110 in Hms. change (SR.ps_regs LibSegJa_arvCK2.ps0) with (map (fun i => (i, nth i LibSegJa_arvCK2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
change (SR.ps_cells LibSegJa_arvCK2.ps0) with LibSegJa_arvCK2.cells0 in Hcells.
split. { exact Hms. }
split. { intros j Hj. apply (BG.kept_regs E E' R R' LibSegJa_arvCK2.regs0 LibSegJa_arvCK2.regs_out0 72 KS_arvCK2 KS_arvCK2_ok HR Hag Hregs j Hj). }
split. { rewrite (BG.out_reg LibSegJa_arvCK2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth LibSegJa_arvCK2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_arvCK2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth LibSegJa_arvCK2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_arvCK2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth LibSegJa_arvCK2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_arvCK2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth LibSegJa_arvCK2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_arvCK2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth LibSegJa_arvCK2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_arvCK2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth LibSegJa_arvCK2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_arvCK2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth LibSegJa_arvCK2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K7l K7r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | clear; lia]. }
split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | clear; lia].
Qed.
Definition KS_arvSG0 : list nat := Eval vm_compute in (BG.kept_list 72 LibSegJa_arvSG0.regs0 LibSegJa_arvSG0.regs_out0).
Lemma KS_arvSG0_ok : BG.kept_ok 72 LibSegJa_arvSG0.regs0 LibSegJa_arvSG0.regs_out0 KS_arvSG0 = true. Proof. vm_compute. reflexivity. Qed.
Definition arvSG0_conc_s := ",3>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12+/v2?#8#7???8000S,13v2?S,14v24S,15v26S,16v25S,1:#7???8000S,1;v2?O#10000#134000La#13:<?8#7???8000Ma#13:=00#1La#134648#124=;0B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#691000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#80#80v24#180B#691000v26#7??????????0Hv26#8P#7???7000#100000001000v26#10Ka+/v26#8#7???8000#2Iv26#10P_v2#80#80v26#10Pv24#180v26#10B#691000v2?#7????????>00Hv2?#20Jav2?#200Iv2?#200P#7???7000#100000001000v2?#200I+/v2?#8#7???8000#40La+v2?#1?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#200v30#1P_v2#80#80v2?#200P_v2#80#80v30#1Pv24#180v2?#200Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#40Pv26#10v2?#200Pv26#10v30#1P+/v26#8#7???8000#2+/v2?#8#7???8000#40Pv2?#200#10000#124000P+/v2?#8#7???8000#40#134648#8Mav26#,,1,7X#:=8?<#;0428Y,T,1#:=928T,:+v24#18T,;v31T,<+v24#150T,17v31"%pstring.
Lemma arvSG0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arvSG0] fx R M V arvSG0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arvSG0] LibSegJa_arvSG0.regs0 LibSegJa_arvSG0.kn0 LibSegJa_arvSG0.BR LibSegJa_arvSG0.PSS LibSegJa_arvSG0.NX0 LibSegJa_arvSG0.F0 710908 LibSegJa_arvSG0.seg_sound_ax fx R M V arvSG0_conc_s. Qed.
Definition KS_arvSGe : list nat := Eval vm_compute in (BG.kept_list 72 LibSegJa_arvSGe.regs0 LibSegJa_arvSGe.regs_out0).
Lemma KS_arvSGe_ok : BG.kept_ok 72 LibSegJa_arvSGe.regs0 LibSegJa_arvSGe.regs_out0 KS_arvSGe = true. Proof. vm_compute. reflexivity. Qed.
Definition arvSGe_conc_s := ",40A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12+/v2?#8#7???8000S,13v2?S,14v24S,15v26S,16v25S,1:#7???8000S,1;v2?O#10000#134000La#13:<?8#7???8000Ma#13:=00#1La#134648#124=;0B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#691000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#80#80v24#180B#691000v26#7??????????0Hv26#8P#7???7000#100000001000v26#10Ka+/v26#8#7???8000#2Iv26#10P_v2#80#80v26#10Pv24#180v26#10B#691000v2?#7????????>00Hv2?#20Jav2?#200Iv2?#200P#7???7000#100000001000v2?#200I+/v2?#8#7???8000#40La+v2?#1?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#200v30#1P_v2#80#80v2?#200P_v2#80#80v30#1Pv24#180v2?#200Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#40Pv26#10v2?#200Pv26#10v30#1P+/v26#8#7???8000#2+/v2?#8#7???8000#40Pv2?#200#10000#124000P+/v2?#8#7???8000#40#134648#8Mav26v32B#1v32#40,1+v2?##8,1,8X#:=8?<#7:?;4Y,T,1#:>144T,:+/v2?#8#7???8000T,;#40T,17v31Lbv2?#45>0360>Jb+v2?#8#1?8"%pstring.
Lemma arvSGe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arvSGe] fx R M V arvSGe_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arvSGe] LibSegJa_arvSGe.regs0 LibSegJa_arvSGe.kn0 LibSegJa_arvSGe.BR LibSegJa_arvSGe.PSS LibSegJa_arvSGe.NX0 LibSegJa_arvSGe.F0 710908 LibSegJa_arvSGe.seg_sound_ax fx R M V arvSGe_conc_s. Qed.
Definition KS_arvSF_0 : list nat := Eval vm_compute in (BG.kept_list 72 LibSegJa_arvSF.regs0 LibSegJa_arvSF.regs_out0).
Lemma KS_arvSF_0_ok : BG.kept_ok 72 LibSegJa_arvSF.regs0 LibSegJa_arvSF.regs_out0 KS_arvSF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arvSF_1 : list nat := Eval vm_compute in (BG.kept_list 72 LibSegJa_arvSF.regs0 LibSegJa_arvSF.regs_out1).
Lemma KS_arvSF_1_ok : BG.kept_ok 72 LibSegJa_arvSF.regs0 LibSegJa_arvSF.regs_out1 KS_arvSF_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition arvSF_conc_s := ",42A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v33p#2#40A#v34p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v33S,;v34S,12+/v2?#8#7???8000S,13v2?S,14v24S,15v26S,16v25S,17v31S,1:#7???8000S,1;v2?O#10000#134000La#13:<?8#7???8000Ma#13:=00#1La#134648#124=;0B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#691000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#80#80v24#180B#691000v26#7??????????0Hv26#8P#7???7000#100000001000v26#10Ka+/v26#8#7???8000#2Iv26#10P_v2#80#80v26#10Pv24#180v26#10B#691000v2?#7????????>00Hv2?#20Jav2?#200Iv2?#200P#7???7000#100000001000v2?#200I+/v2?#8#7???8000#40La+v2?#1?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#200v30#1P_v2#80#80v2?#200P_v2#80#80v30#1Pv24#180v2?#200Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#40Pv26#10v2?#200Pv26#10v30#1P+/v26#8#7???8000#2+/v2?#8#7???8000#40Pv2?#200#10000#124000P+/v2?#8#7???8000#40#134648#8Mav26#,,2,6X#:=928#:?:88Y,T,1#:=938T,;v31T,18v33C%_v34v31p#2#40#1,6X#:=928#:>974Y,1T,1#:>2<<T,:v26T,;#1D#1%_v34v31p#2#40"%pstring.
Lemma arvSF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arvSF_0; KS_arvSF_1] fx R M V arvSF_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arvSF_0; KS_arvSF_1] LibSegJa_arvSF.regs0 LibSegJa_arvSF.kn0 LibSegJa_arvSF.BR LibSegJa_arvSF.PSS LibSegJa_arvSF.NX0 LibSegJa_arvSF.F0 710952 LibSegJa_arvSF.seg_sound_ax fx R M V arvSF_conc_s. Qed.
Definition KS_arvHG0 : list nat := Eval vm_compute in (BG.kept_list 72 LibSegJa_arvHG0.regs0 LibSegJa_arvHG0.regs_out0).
Lemma KS_arvHG0_ok : BG.kept_ok 72 LibSegJa_arvHG0.regs0 LibSegJa_arvHG0.regs_out0 KS_arvHG0 = true. Proof. vm_compute. reflexivity. Qed.
Definition arvHG0_conc_s := ",3>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12+/v2?#8#7???8000S,13v2?S,14v24S,15v26S,16v25S,1:#7???8000S,1;v2?O#10000#134000La#13:<?8#7???8000Ma#13:=00#1La#134648#124=;0B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#691000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#80#80v24#180B#691000v26#7??????????0Hv26#8P#7???7000#100000001000v26#10Ka+/v26#8#7???8000#2Iv26#10P_v2#80#80v26#10Pv24#180v26#10B#691000v2?#7????????>00Hv2?#20Jav2?#200Iv2?#200P#7???7000#100000001000v2?#200I+/v2?#8#7???8000#40La+v2?#1?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#200v30#1P_v2#80#80v2?#200P_v2#80#80v30#1Pv24#180v2?#200Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#40Pv26#10v2?#200Pv26#10v30#1P+/v26#8#7???8000#2+/v2?#8#7???8000#40Pv2?#200#10000#124000P+/v2?#8#7???8000#40#134648#8Mav26#,,1,7X#:=978#;0428Y,T,1#:=9:4T,:+v24#18T,;v31T,<+v24#150T,19v31"%pstring.
Lemma arvHG0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arvHG0] fx R M V arvHG0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arvHG0] LibSegJa_arvHG0.regs0 LibSegJa_arvHG0.kn0 LibSegJa_arvHG0.BR LibSegJa_arvHG0.PSS LibSegJa_arvHG0.NX0 LibSegJa_arvHG0.F0 711032 LibSegJa_arvHG0.seg_sound_ax fx R M V arvHG0_conc_s. Qed.
Definition KS_arvHGe : list nat := Eval vm_compute in (BG.kept_list 72 LibSegJa_arvHGe.regs0 LibSegJa_arvHGe.regs_out0).
Lemma KS_arvHGe_ok : BG.kept_ok 72 LibSegJa_arvHGe.regs0 LibSegJa_arvHGe.regs_out0 KS_arvHGe = true. Proof. vm_compute. reflexivity. Qed.
Definition arvHGe_conc_s := ",40A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12+/v2?#8#7???8000S,13v2?S,14v24S,15v26S,16v25S,1:#7???8000S,1;v2?O#10000#134000La#13:<?8#7???8000Ma#13:=00#1La#134648#124=;0B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#691000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#80#80v24#180B#691000v26#7??????????0Hv26#8P#7???7000#100000001000v26#10Ka+/v26#8#7???8000#2Iv26#10P_v2#80#80v26#10Pv24#180v26#10B#691000v2?#7????????>00Hv2?#20Jav2?#200Iv2?#200P#7???7000#100000001000v2?#200I+/v2?#8#7???8000#40La+v2?#1?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#200v30#1P_v2#80#80v2?#200P_v2#80#80v30#1Pv24#180v2?#200Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#40Pv26#10v2?#200Pv26#10v30#1P+/v26#8#7???8000#2+/v2?#8#7???8000#40Pv2?#200#10000#124000P+/v2?#8#7???8000#40#134648#8Mav26v32B#1v32#40,1+v2?##8,1,8X#:=978#7:?;4Y,T,1#:>144T,:+/v2?#8#7???8000T,;#40T,19v31Lbv2?#45>0360>Jb+v2?#8#1?8"%pstring.
Lemma arvHGe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arvHGe] fx R M V arvHGe_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arvHGe] LibSegJa_arvHGe.regs0 LibSegJa_arvHGe.kn0 LibSegJa_arvHGe.BR LibSegJa_arvHGe.PSS LibSegJa_arvHGe.NX0 LibSegJa_arvHGe.F0 711032 LibSegJa_arvHGe.seg_sound_ax fx R M V arvHGe_conc_s. Qed.
Definition KS_arvHF_0 : list nat := Eval vm_compute in (BG.kept_list 72 LibSegJa_arvHF.regs0 LibSegJa_arvHF.regs_out0).
Lemma KS_arvHF_0_ok : BG.kept_ok 72 LibSegJa_arvHF.regs0 LibSegJa_arvHF.regs_out0 KS_arvHF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arvHF_1 : list nat := Eval vm_compute in (BG.kept_list 72 LibSegJa_arvHF.regs0 LibSegJa_arvHF.regs_out1).
Lemma KS_arvHF_1_ok : BG.kept_ok 72 LibSegJa_arvHF.regs0 LibSegJa_arvHF.regs_out1 KS_arvHF_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition arvHF_conc_s := ",42A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v33p#2#40A#v34p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v33S,;v34S,12+/v2?#8#7???8000S,13v2?S,14v24S,15v26S,16v25S,19v31S,1:#7???8000S,1;v2?O#10000#134000La#13:<?8#7???8000Ma#13:=00#1La#134648#124=;0B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#691000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#80#80v24#180B#691000v26#7??????????0Hv26#8P#7???7000#100000001000v26#10Ka+/v26#8#7???8000#2Iv26#10P_v2#80#80v26#10Pv24#180v26#10B#691000v2?#7????????>00Hv2?#20Jav2?#200Iv2?#200P#7???7000#100000001000v2?#200I+/v2?#8#7???8000#40La+v2?#1?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#200v30#1P_v2#80#80v2?#200P_v2#80#80v30#1Pv24#180v2?#200Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#40Pv26#10v2?#200Pv26#10v30#1P+/v26#8#7???8000#2+/v2?#8#7???8000#40Pv2?#200#10000#124000P+/v2?#8#7???8000#40#134648#8Mav26#,,2,6X#:=9:4#;071<Y,T,1#:=9;4T,;v31T,17v33C%_v34v31p#2#40#1,6X#:=9:4#:>974Y,1T,1#:>2?8T,:v26T,;#1D#1%_v34v31p#2#40"%pstring.
Lemma arvHF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arvHF_0; KS_arvHF_1] fx R M V arvHF_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arvHF_0; KS_arvHF_1] LibSegJa_arvHF.regs0 LibSegJa_arvHF.kn0 LibSegJa_arvHF.BR LibSegJa_arvHF.PSS LibSegJa_arvHF.NX0 LibSegJa_arvHF.F0 711076 LibSegJa_arvHF.seg_sound_ax fx R M V arvHF_conc_s. Qed.
Definition KS_arvSW_0 : list nat := Eval vm_compute in (BG.kept_list 72 LibSegJa_arvSW.regs0 LibSegJa_arvSW.regs_out0).
Lemma KS_arvSW_0_ok : BG.kept_ok 72 LibSegJa_arvSW.regs0 LibSegJa_arvSW.regs_out0 KS_arvSW_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arvSW_1 : list nat := Eval vm_compute in (BG.kept_list 72 LibSegJa_arvSW.regs0 LibSegJa_arvSW.regs_out1).
Lemma KS_arvSW_1_ok : BG.kept_ok 72 LibSegJa_arvSW.regs0 LibSegJa_arvSW.regs_out1 KS_arvSW_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition arvSW_conc_s := ",51A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v33p#2#40A#v35p#2#40S,2_v2#80S,8v2S,9_v2#80S,;v35S,12+/v2?#8#7???8000S,13v2?S,14v24S,15v26S,16v25S,17v31S,18v33S,1:#7???8000S,1;v2?O#10000#134000La#13:<?8#7???8000Ma#13:=00#1La#134648#124=;0B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#691000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#80#80v24#180B#691000v26#7??????????0Hv26#8P#7???7000#100000001000v26#10Ka+/v26#8#7???8000#2Iv26#10P_v2#80#80v26#10Pv24#180v26#10B#691000v2?#7????????>00Hv2?#20Jav2?#200Iv2?#200P#7???7000#100000001000v2?#200I+/v2?#8#7???8000#40La+v2?#1?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#200v30#1P_v2#80#80v2?#200P_v2#80#80v30#1Pv24#180v2?#200Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#40Pv26#10v2?#200Pv26#10v30#1P+/v26#8#7???8000#2+/v2?#8#7???8000#40Pv2?#200#10000#124000P+/v2?#8#7???8000#40#134648#8B#691000v25#7??????????8Hv25#8P#7???7000#100000001000v25#8Ka+/v25#8#7???8000#1Iv25#8P_v2#80#80v25#8Lav25#12<940Ka#8001=928#10Na+v24#10#Pv24#180v25#8Pv26#10v25#8P+/v2?#8#7???8000#40#8001=928#10Pv2?#200v25#8Pv30#1v25#8P+/v2?#8#7???8000#40+/v25#8#7???8000#1Mav26#,,2,2X#:=938#:>51<Y,,5X#:=938#:>974Y,1T,1#:=94<T,:v26T,;#7"%pstring.
Lemma arvSW_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arvSW_0; KS_arvSW_1] fx R M V arvSW_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arvSW_0; KS_arvSW_1] LibSegJa_arvSW.regs0 LibSegJa_arvSW.kn0 LibSegJa_arvSW.BR LibSegJa_arvSW.PSS LibSegJa_arvSW.NX0 LibSegJa_arvSW.F0 710968 LibSegJa_arvSW.seg_sound_ax fx R M V arvSW_conc_s. Qed.
Definition KS_arvSK : list nat := Eval vm_compute in (BG.kept_list 72 LibSegJa_arvSK.regs0 LibSegJa_arvSK.regs_out0).
Lemma KS_arvSK_ok : BG.kept_ok 72 LibSegJa_arvSK.regs0 LibSegJa_arvSK.regs_out0 KS_arvSK = true. Proof. vm_compute. reflexivity. Qed.
Definition arvSK_conc_s := ",4?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v33p#2#40S,2_v2#80S,8v2S,9_v2#80S,12+/v2?#8#7???8000S,13v2?S,14v24S,15v26S,16v25S,17v31S,18v33S,1:#7???8000S,1;v2?O#10000#134000La#13:<?8#7???8000Ma#13:=00#1La#134648#124=;0B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#691000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#80#80v24#180B#691000v26#7??????????0Hv26#8P#7???7000#100000001000v26#10Ka+/v26#8#7???8000#2Iv26#10P_v2#80#80v26#10Pv24#180v26#10B#691000v2?#7????????>00Hv2?#20Jav2?#200Iv2?#200P#7???7000#100000001000v2?#200I+/v2?#8#7???8000#40La+v2?#1?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#200v30#1P_v2#80#80v2?#200P_v2#80#80v30#1Pv24#180v2?#200Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#40Pv26#10v2?#200Pv26#10v30#1P+/v26#8#7???8000#2+/v2?#8#7???8000#40Pv2?#200#10000#124000P+/v2?#8#7???8000#40#134648#8B#691000v25#7??????????8Hv25#8P#7???7000#100000001000v25#8Ka+/v25#8#7???8000#1Iv25#8P_v2#80#80v25#8Lav25#12<940Ka#8001=928#10Na+v24#10#Pv24#180v25#8Pv26#10v25#8P+/v2?#8#7???8000#40#8001=928#10Pv2?#200v25#8Pv30#1v25#8P+/v2?#8#7???8000#40+/v25#8#7???8000#1Mav26#,3+v24#8#1++/v2?#8#7???8000##40+v2?#>0#10,1,10X#:>51<#:>110Y,T,1#:>56<T,:+v24#8T,;#1T,<#T,=v24T,>v26T,?#:8810Nb+v24#8#1Nb+/v2?#8#7???801=#?8Nb+/v2?#8#7???801<#?8Lb+v2?#>8v31Lb+v2?#>0v33Jbv2?#>0Jb+v2?#?0#110"%pstring.
Lemma arvSK_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arvSK] fx R M V arvSK_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arvSK] LibSegJa_arvSK.regs0 LibSegJa_arvSK.kn0 LibSegJa_arvSK.BR LibSegJa_arvSK.PSS LibSegJa_arvSK.NX0 LibSegJa_arvSK.F0 714012 LibSegJa_arvSK.seg_sound_ax fx R M V arvSK_conc_s. Qed.
End PMARVP6.
