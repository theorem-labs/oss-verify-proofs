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
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Jb0PlanKit AsanPlanCore
BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_bsrM1eq LibSegJb_bsrM1ne LibSegJb_bsrF0 LibSegJb_bsrFge LibSegJb_bsrFlt LibSegJb_bsrFlt2 LibSegJb_bsrM2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBSRP2.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
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
Definition KS_bsrM1eq : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_bsrM1eq.regs0 LibSegJb_bsrM1eq.regs_out0).
Lemma KS_bsrM1eq_ok : BG.kept_ok 80 LibSegJb_bsrM1eq.regs0 LibSegJb_bsrM1eq.regs_out0 KS_bsrM1eq = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition bsrM1eq_conc_s := ",45A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v32p#2#40S,2v32S,8v2S,9v32S,12+/+v24#120#8#7???8000S,13v24S,14v26S,15+/+v24#118#8#7???8000S,16v26S,17+v24#120S,18+v24#118S,19+/v2?#8#7???8000S,1:v2?S,1;#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801000v32#7?????????60Hv32#20Iv32#38La+v32#18v25B#1000v25#7???????<000La+v32#8+v2?#20La+v32#10v2?La+v32#30v2?B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128Pv32#38v24#128La+v24#108v22La+v24#110#4000Ja+v24#100#8La+v24#118v23La+v24#120v21B#693000v2?#7?????????80Hv2?#20Jav2?#80Iv2?#80P#7???7000#100000001000v2?#80I+/v2?#8#7???8000#10La+v2?#78v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#80v30#1Pv24#128v2?#80Pv24#128v30#1P+/v24#8#7???8000#25+/v2?#8#7???8000#10Pv32#38v2?#80Pv32#38v30#1Pv2?#80#10000#126000La+v2?#20v26Na+/v2?#8#7???8004#Na+/v2?#8#7???8008#?8B#1v21#4000B#1v26#4000B#_v21v26#3???B#1000v23#7???????<000,1+v24#100#28,1,8X#;07>4#;0;3<Y,T,:+v24#100T,<#Lb+v24#120_v21v26Lb+v24#118+v23v26Lb+v24#108v22Lb+v24#110#4000"%pstring.
Lemma bsrM1eq_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsrM1eq] fx R M V bsrM1eq_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsrM1eq] LibSegJb_bsrM1eq.regs0 LibSegJb_bsrM1eq.kn0 LibSegJb_bsrM1eq.BR LibSegJb_bsrM1eq.PSS LibSegJb_bsrM1eq.NX0 LibSegJb_bsrM1eq.F0 722916 LibSegJb_bsrM1eq.seg_sound_ax fx R M V bsrM1eq_conc_s. Qed.
Definition KS_bsrM1ne : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_bsrM1ne.regs0 LibSegJb_bsrM1ne.regs_out0).
Lemma KS_bsrM1ne_ok : BG.kept_ok 80 LibSegJb_bsrM1ne.regs0 LibSegJb_bsrM1ne.regs_out0 KS_bsrM1ne = true. Proof. vm_compute. reflexivity. Qed.
Definition bsrM1ne_conc_s := ",45A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v32p#2#40S,2v32S,8v2S,9v32S,12+/+v24#120#8#7???8000S,13v24S,14v21S,15+/+v24#118#8#7???8000S,16v26S,17+v24#120S,18+v24#118S,19+/v2?#8#7???8000S,1:v2?S,1;#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801000v32#7?????????60Hv32#20Iv32#38La+v32#18v25B#1000v25#7???????<000La+v32#8+v2?#20La+v32#10v2?La+v32#30v2?B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128Pv32#38v24#128La+v24#108v22La+v24#110#4000Ja+v24#100#8La+v24#118v23La+v24#120v21B#693000v2?#7?????????80Hv2?#20Jav2?#80Iv2?#80P#7???7000#100000001000v2?#80I+/v2?#8#7???8000#10La+v2?#78v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#80v30#1Pv24#128v2?#80Pv24#128v30#1P+/v24#8#7???8000#25+/v2?#8#7???8000#10Pv32#38v2?#80Pv32#38v30#1Pv2?#80#10000#126000La+v2?#20v26Na+/v2?#8#7???8004#Na+/v2?#8#7???8008#?8B#1v21#3???B#2v26#4000B#1+*-1v21v26#3???B#1000v23#7???????<000,1+v24#100#28,1,<X#;07>4#;0>58Y,T,1#;08:<T,:v24T,;v22T,<#4000T,=#4000T,16+v24#118Lb+v24#118v22Lb+v24#120#Lb+v24#108v22Lb+v24#110#4000"%pstring.
Lemma bsrM1ne_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsrM1ne] fx R M V bsrM1ne_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsrM1ne] LibSegJb_bsrM1ne.regs0 LibSegJb_bsrM1ne.kn0 LibSegJb_bsrM1ne.BR LibSegJb_bsrM1ne.PSS LibSegJb_bsrM1ne.NX0 LibSegJb_bsrM1ne.F0 722916 LibSegJb_bsrM1ne.seg_sound_ax fx R M V bsrM1ne_conc_s. Qed.
Definition KS_bsrF0 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_bsrF0.regs0 LibSegJb_bsrF0.regs_out0).
Lemma KS_bsrF0_ok : BG.kept_ok 80 LibSegJb_bsrF0.regs0 LibSegJb_bsrF0.regs_out0 KS_bsrF0 = true. Proof. vm_compute. reflexivity. Qed.
Definition bsrF0_conc_s := ",42A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40A#v28p#2#40A#v2?p#2#40A#v30p#2#40A#v32p#2#40S,2v32S,8v2S,9v32S,:#S,12+/+v24#120#8#7???8000S,13v24S,14v27S,15+/+v24#118#8#7???8000S,16+v24#118S,17+v24#120S,19+/v2?#8#7???8000S,1:v2?S,1;#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801000v32#7?????????60Hv32#20Iv32#38La+v32#18v25B#1000v25#7???????<000La+v32#8+v2?#20La+v32#10v2?La+v32#30v2?B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128Pv32#38v24#128La+v24#108v22La+v24#110#4000Ja+v24#100#8La+v24#118v22La+v24#120#B#693000v2?#7?????????80Hv2?#20Jav2?#80Iv2?#80P#7???7000#100000001000v2?#80I+/v2?#8#7???8000#10La+v2?#78v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#80v30#1Pv24#128v2?#80Pv24#128v30#1P+/v24#8#7???8000#25+/v2?#8#7???8000#10Pv32#38v2?#80Pv32#38v30#1Pv2?#80#10000#126000La+v2?#20+v28v27Na+/v2?#8#7???8004#Na+/v2?#8#7???8008#?8B#v27#3???B#1v28#4000,1+v24#100#28,1,9X#;08:<#;0;3<Y,T,;#T,16v27Lb+v24#120#Lb+v24#108v22Lb+v24#110#4000Jb+v24#100#8Lb+v24#118v22"%pstring.
Lemma bsrF0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsrF0] fx R M V bsrF0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsrF0] LibSegJb_bsrF0.regs0 LibSegJb_bsrF0.kn0 LibSegJb_bsrF0.BR LibSegJb_bsrF0.PSS LibSegJb_bsrF0.NX0 LibSegJb_bsrF0.F0 723116 LibSegJb_bsrF0.seg_sound_ax fx R M V bsrF0_conc_s. Qed.
Definition KS_bsrFge : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_bsrFge.regs0 LibSegJb_bsrFge.regs_out0).
Lemma KS_bsrFge_ok : BG.kept_ok 80 LibSegJb_bsrFge.regs0 LibSegJb_bsrFge.regs_out0 KS_bsrFge = true. Proof. vm_compute. reflexivity. Qed.
Definition bsrFge_conc_s := ",46A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40A#v28p#2#40A#v2?p#2#40A#v30p#2#40A#v32p#2#40S,2v32S,8v2S,9v32S,:v21S,12+/+v24#120#8#7???8000S,13v24S,14v27S,15+/+v24#118#8#7???8000S,16+v24#118S,17+v24#120S,19+/v2?#8#7???8000S,1:v2?S,1;#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801000v32#7?????????60Hv32#20Iv32#38La+v32#18v25B#1000v25#7???????<000La+v32#8+v2?#20La+v32#10v2?La+v32#30v2?B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128Pv32#38v24#128La+v24#108v22La+v24#110#4000Ja+v24#100#8La+v24#118v22La+v24#120#B#693000v2?#7?????????80Hv2?#20Jav2?#80Iv2?#80P#7???7000#100000001000v2?#80I+/v2?#8#7???8000#10La+v2?#78v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#80v30#1Pv24#128v2?#80Pv24#128v30#1P+/v24#8#7???8000#25+/v2?#8#7???8000#10Pv32#38v2?#80Pv32#38v30#1Pv2?#80#10000#126000La+v2?#20+v28v27Na+/v2?#8#7???8004#Na+/v2?#8#7???8008#?8B#1v21#4000B#v27#3???B#1v28#4000B#+*-1v21v28#3???B#1000v22#7???????<000,3+v2?#40#8++/v2?#8#7???8000#8#1+v24#100#28,1,10X#;08:<#7760<Y,T,1#;092<T,:+v25v27T,;v22T,<v21T,18v21Nb+/v2?#8#7???8008#?8Lb+v2?#40v28Lb+v24#120v21Lb+v24#108v22Lb+v24#110#4000Jb+v24#100#8Lb+v24#118v22Jbv2?#40Jb+v2?#48#38"%pstring.
Lemma bsrFge_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsrFge] fx R M V bsrFge_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsrFge] LibSegJb_bsrFge.regs0 LibSegJb_bsrFge.kn0 LibSegJb_bsrFge.BR LibSegJb_bsrFge.PSS LibSegJb_bsrFge.NX0 LibSegJb_bsrFge.F0 723116 LibSegJb_bsrFge.seg_sound_ax fx R M V bsrFge_conc_s. Qed.
Definition KS_bsrFlt : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_bsrFlt.regs0 LibSegJb_bsrFlt.regs_out0).
Lemma KS_bsrFlt_ok : BG.kept_ok 80 LibSegJb_bsrFlt.regs0 LibSegJb_bsrFlt.regs_out0 KS_bsrFlt = true. Proof. vm_compute. reflexivity. Qed.
Definition bsrFlt_conc_s := ",45A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40A#v28p#2#40A#v2?p#2#40A#v30p#2#40A#v32p#2#40S,2v32S,8v2S,9v32S,:v21S,12+/+v24#120#8#7???8000S,13v24S,14v27S,15+/+v24#118#8#7???8000S,16+v24#118S,17+v24#120S,19+/v2?#8#7???8000S,1:v2?S,1;#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801000v32#7?????????60Hv32#20Iv32#38La+v32#18v25B#1000v25#7???????<000La+v32#8+v2?#20La+v32#10v2?La+v32#30v2?B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128Pv32#38v24#128La+v24#108v22La+v24#110#4000Ja+v24#100#8La+v24#118v22La+v24#120#B#693000v2?#7?????????80Hv2?#20Jav2?#80Iv2?#80P#7???7000#100000001000v2?#80I+/v2?#8#7???8000#10La+v2?#78v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#80v30#1Pv24#128v2?#80Pv24#128v30#1P+/v24#8#7???8000#25+/v2?#8#7???8000#10Pv32#38v2?#80Pv32#38v30#1Pv2?#80#10000#126000La+v2?#20+v28v27Na+/v2?#8#7???8004#Na+/v2?#8#7???8008#?8B#2v21#4000B#v27#3???B#1v28#3???B#1_v21v28#3???,3+v2?#40#8++/v2?#8#7???8000#8#1+v24#100#28,1,=X#;08:<#;08=<Y,T,;+v2?#40T,<v28Lb+v2?#40v28Nb+/v2?#8#7???8008#Lb+v24#120v21Lb+v24#108v22Lb+v24#110#4000Jb+v24#100#8Lb+v24#118v22Jbv2?#40Jb+v2?#48#38"%pstring.
Lemma bsrFlt_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsrFlt] fx R M V bsrFlt_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsrFlt] LibSegJb_bsrFlt.regs0 LibSegJb_bsrFlt.kn0 LibSegJb_bsrFlt.BR LibSegJb_bsrFlt.PSS LibSegJb_bsrFlt.NX0 LibSegJb_bsrFlt.F0 723116 LibSegJb_bsrFlt.seg_sound_ax fx R M V bsrFlt_conc_s. Qed.
Definition KS_bsrFlt2 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_bsrFlt2.regs0 LibSegJb_bsrFlt2.regs_out0).
Lemma KS_bsrFlt2_ok : BG.kept_ok 80 LibSegJb_bsrFlt2.regs0 LibSegJb_bsrFlt2.regs_out0 KS_bsrFlt2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bsrFlt2_conc (fx : FPState) (R : bvmap 5 (bv 64)) (M : word -> option byte) (V : nat -> Z) :
ltac:(PStmt.mk RSEGS aligned srl_range L5KA.zeros_at [KS_bsrFlt2] fx R M V ",48A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40A#v28p#2#40A#v2?p#2#40A#v30p#2#40A#v32p#2#40S,2v32S,8v2S,9v32S,:v21S,;+v2?#40S,<v28S,12+/+v24#120#8#7???8000S,13v24S,14v27S,15+/+v24#118#8#7???8000S,16+v24#118S,17+v24#120S,19+/v2?#8#7???8000S,1:v2?S,1;#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801000v32#7?????????60Hv32#20Iv32#38La+v32#18v25B#1000v25#7???????<000La+v32#8+v2?#20La+v32#10v2?La+v32#30v2?B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128Pv32#38v24#128La+v24#108v22La+v24#110#4000Ja+v24#100#8La+v24#118v22La+v24#120v21B#693000v2?#7?????????80Hv2?#20Jav2?#80Iv2?#80P#7???7000#100000001000v2?#80I+/v2?#8#7???8000#10La+v2?#78v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#80v30#1Pv24#128v2?#80Pv24#128v30#1P+/v24#8#7???8000#25+/v2?#8#7???8000#10Pv32#38v2?#80Pv32#38v30#1Pv2?#80#10000#126000La+v2?#20+v28v27La+v2?#40v28Ka+/+v2?#40#8#7???8000#1B#2v21#4000B#v27#3???B#1v28#3???B#1_v21v28#3???B#1000v22#7???????<000,3+v2?#40#8++/v2?#8#7???8000#8#1+v24#100#28,1,>X#;08=<#7760<Y,T,1#;092<T,:+v25v27T,;v22T,18v28Nb+/v2?#8#7???8008#?8Lb+v24#108v22Lb+v24#110#4000Jb+v24#100#8Lb+v24#118v22Lb+v24#120v21Lb+v2?#40v28Kb+/v2?#8#7???8009_+*-1/v2?#8/+v2?#40#8#8"%pstring).
Proof.
intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G23 G25 G26 G27 K0 K1 K2 pvzI11 K4 K5 K6 pvzI12 K8 K9 K10 pvzI13 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 pvzI14 K23 K24 K25 K26 K27 K28 pvzI15 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20.
pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV47l; move HV47l before pvzI8; pose proof (proj2 pvzI8) as HV47r; move HV47r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV48l; move HV48l before pvzI9; pose proof (proj2 pvzI9) as HV48r; move HV48r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV50l; move HV50l before pvzI10; pose proof (proj2 pvzI10) as HV50r; move HV50r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K7l; move K7l before pvzI12; pose proof (proj2 pvzI12) as K7r; move K7r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K11l; move K11l before pvzI13; pose proof (proj2 pvzI13) as K11r; move K11r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K22l; move K22l before pvzI14; pose proof (proj2 pvzI14) as K22r; move K22r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K29l; move K29l before pvzI15; pose proof (proj2 pvzI15) as K29r; move K29r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K42l; move K42l before pvzI16; pose proof (proj2 pvzI16) as K42r; move K42r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K43l; move K43l before pvzI17; pose proof (proj2 pvzI17) as K43r; move K43r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K44l; move K44l before pvzI18; pose proof (proj2 pvzI18) as K44r; move K44r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K45l; move K45l before pvzI19; pose proof (proj2 pvzI19) as K45r; move K45r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K46l; move K46l before pvzI20; pose proof (proj2 pvzI20) as K46r; move K46r before pvzI20; clear pvzI20.
set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | 39%nat => vz_39 | 40%nat => vz_40 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
{ unfold VzN. BigLinkZA.za_tac0 51%nat. }
assert (HR: regs_ok E LibSegJb_bsrFlt2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl LibSegJb_bsrFlt2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
assert (HK: know_ok RSEGS E M LibSegJb_bsrFlt2.kn0).
{ unfold know_ok, LibSegJb_bsrFlt2.kn0.
apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | exact (conj K3l K3r)]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | clear; lia | exact K4]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r; lia | clear - HV50l HV50r K3l K3r; lia | clear - HV50l HV50r K3l K3r; lia | exactA K5]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | clear - HV50l HV50r K3l K3r; lia | clear - HV50l HV50r K3l K3r; lia | exactA K6]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | exact (conj K7l K7r)]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | clear - HV50l HV50r K3l K3r; lia | clear - HV50l HV50r K3l K3r; lia | exactA K8]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | clear - HV50l HV50r K3l K3r; lia | clear - HV50l HV50r K3l K3r; lia | exactA K9]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | clear - HV50l HV50r K3l K3r; lia | clear - HV50l HV50r K3l K3r; lia | exactA K10]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | exact (conj K11l K11r)]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | clear; lia | exact K12]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r; lia | clear - HV36l HV36r K11l K11r; lia | clear - HV36l HV36r K11l K11r; lia | exactA K14]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r; lia | clear - HV36l HV36r K11l K11r; lia | clear - HV36l HV36r K11l K11r; lia | exactA K15]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | evalEk ZA ltac:(clear - HV34l HV34r K46l K46r) | clear - HV36l HV36r K11l K11r; lia | clear - HV36l HV36r K11l K11r; lia | exactA K17]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r; lia | clear - HV36l HV36r K11l K11r; lia | exactA K18]. }
apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r; lia | clear - HV36l HV36r K11l K11r; lia | clear - HV36l HV36r K11l K11r; lia | exactA K19]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | evalEk ZA ltac:(clear - HV34l HV34r K46l K46r) | clear - HV36l HV36r K11l K11r; lia | clear - HV36l HV36r K11l K11r; lia | exactA K20]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | evalEk ZA ltac:(clear - HV33l HV33r K42l K42r K45l K45r) | clear - HV36l HV36r K11l K11r; lia | clear - HV36l HV36r K11l K11r; lia | exactA K21]. }
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
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear - HV39l HV39r K43l K43r HV40l HV40r K44l K44r K45l K45r) | clear - HV47l HV47r K22l K22r; lia | clear - HV47l HV47r K22l K22r; lia | exactA K39]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear - HV40l HV40r K44l K44r K45l K45r) | clear - HV47l HV47r K22l K22r; lia | clear - HV47l HV47r K22l K22r; lia | exactA K40]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K22l K22r; lia | clear - HV47l HV47r K22l K22r; lia | clear - HV47l HV47r K22l K22r; lia | exactA K41]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K42l K42r K45l K45r) | exact (conj K42l K42r)]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K43l K43r) | exact (conj K43l K43r)]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K44l K44r K45l K45r) | exact (conj K44l K44r)]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K42l K42r K45l K45r HV40l HV40r K44l K44r) | exact (conj K45l K45r)]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K46l K46r) | exact (conj K46l K46r)]. }
apply Forall_nil. }
pvz_hg ltac:(idtac; destruct (LibSegJb_bsrFlt2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
change LibSegJb_bsrFlt2.NX0 with 80%nat in Hag.
exists fx', R', M'. pvz_linconj. split. exact Hgr.
assert (FRW: forall a : word, ~ ((vz_47 + 64) <= bv_unsigned a < (vz_47 + 64) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 8) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 8) + 1) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
{ intros a Hn0 Hn1 Hn2. apply Hfr. unfold LibSegJb_bsrFlt2.F0.
eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K22l K22r Hn0; lia |].
eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K22l K22r Hn1; lia |].
eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K11l K11r Hn2; lia |].
apply L5K.outside_nil_e. }
split. exact FRW.
split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
apply L5K.nth_error_single in Hnth. subst ps.
change (SR.ps_pc LibSegJb_bsrFlt2.ps0) with 0x7760c in Hms. change (SR.ps_regs LibSegJb_bsrFlt2.ps0) with (map (fun i => (i, nth i LibSegJb_bsrFlt2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
change (SR.ps_cells LibSegJb_bsrFlt2.ps0) with LibSegJb_bsrFlt2.cells0 in Hcells.
split. { exact Hms. }
split. { intros j Hj. apply (BG.kept_regs E E' R R' LibSegJb_bsrFlt2.regs0 LibSegJb_bsrFlt2.regs_out0 80 KS_bsrFlt2 KS_bsrFlt2_ok HR Hag Hregs j Hj). }
split. { rewrite (BG.out_reg LibSegJb_bsrFlt2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth LibSegJb_bsrFlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJb_bsrFlt2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth LibSegJb_bsrFlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJb_bsrFlt2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth LibSegJb_bsrFlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJb_bsrFlt2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth LibSegJb_bsrFlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K46l K46r) | clear; lia]. }
split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K46l K46r) | clear; lia]. }
split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K42l K42r K45l K45r) | clear; lia]. }
split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K44l K44r K45l K45r) | clear; lia]. }
eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K22l K22r) | clear; lia].
Qed.
Definition KS_bsrM2 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_bsrM2.regs0 LibSegJb_bsrM2.regs_out0).
Lemma KS_bsrM2_ok : BG.kept_ok 80 LibSegJb_bsrM2.regs0 LibSegJb_bsrM2.regs_out0 KS_bsrM2 = true. Proof. vm_compute. reflexivity. Qed.
Definition bsrM2_conc_s := ",43A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40A#v28p#2#40A#v2?p#2#40A#v30p#2#40A#v32p#2#40S,2v32S,8v2S,9v32S,12+/+v24#120#8#7???8000S,13v24S,14v27S,15+/+v24#118#8#7???8000S,16+v24#118S,17+v24#120S,18v28S,19+/v2?#8#7???8000S,1:v2?S,1;#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801000v32#7?????????60Hv32#20Iv32#38La+v32#18v25B#1000v25#7???????<000La+v32#8+v2?#20La+v32#10v2?La+v32#30v2?B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128Pv32#38v24#128La+v24#108v22La+v24#110#4000Ja+v24#100#8La+v24#118v22La+v24#120v21B#693000v2?#7?????????80Hv2?#20Jav2?#80Iv2?#80P#7???7000#100000001000v2?#80I+/v2?#8#7???8000#10La+v2?#78v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#80v30#1Pv24#128v2?#80Pv24#128v30#1P+/v24#8#7???8000#25+/v2?#8#7???8000#10Pv32#38v2?#80Pv32#38v30#1Pv2?#80#10000#126000B#1v21#4000B#v27#3???B#1v28#4000B#_v21v28#3???B#1000v22#7???????<000,1+v24#100#28,1,9X#;092<#;0;3<Y,T,:+v24#100T,<#T,16+v27v28Lb+v24#120_v21v28Lb+v24#118+v22v28Lb+v24#108v22Lb+v24#110#4000"%pstring.
Lemma bsrM2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsrM2] fx R M V bsrM2_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsrM2] LibSegJb_bsrM2.regs0 LibSegJb_bsrM2.kn0 LibSegJb_bsrM2.BR LibSegJb_bsrM2.PSS LibSegJb_bsrM2.NX0 LibSegJb_bsrM2.F0 723244 LibSegJb_bsrM2.seg_sound_ax fx R M V bsrM2_conc_s. Qed.
End PMBSRP2.
