(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCkd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACkc.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition boxed (P : Prop) : Prop := P.
Ltac box H := lazymatch type of H with ?T => change T with (boxed T) in H end.
Ltac unbox := unfold boxed in *.
Ltac rwEFA := repeat match goal with H : forall c p, frame_addr ?l3 c p = frame_addr ?l c p |- context [frame_addr ?l3 _ _] =>
tryif constr_eq l3 l then fail else rewrite !H end.
Definition ss_clear_conds (s : sstate) : sstate :=
mkSS (ss_pc s) (ss_regs s) (ss_mem s) (ss_resv s) (mkFacts (f_atoms (ss_facts s)) [] (f_alias (ss_facts s))).
Ltac ra_join HS target N deads hook :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_pi_submem Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem _ Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end;
norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_pi_havoc_hi N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc _ N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl  end;
norm_ss HS;
hook;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_pi_facts_incl3 Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 _ Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS  end;
norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] | st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg]  end.
Ltac ra_join_val HS N i R En :=
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
lazymatch Ev with havoc _ _ ?vals =>
lazymatch type of R with _ = ?v =>
let n := eval vm_compute in (N + i)%nat in
assert (En : ew Ev n = v);
[ change n with (N + i)%nat; rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; exact R | ] end end | st_ok _ ?Ev _ _ =>
lazymatch Ev with havoc _ _ ?vals =>
lazymatch type of R with _ = ?v =>
let n := eval vm_compute in (N + i)%nat in
assert (En : ew Ev n = v);
[ change n with (N + i)%nat; rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; exact R | ] end end  end.
Ltac ra_join_fact HS n af tac :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_fact Ev ssx msx n af HS ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; tac)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_fact Ev ssx msx n af HS ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; tac)) as HS3;
clear HS; rename HS3 into HS  end.
Ltac prSS tag HS := lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in idtac tag; idtac v | st_ok _ _ ?ss _ => let v := eval vm_compute in ss in idtac tag; idtac v  end.
Ltac ws_pin HS r e Hr dtac :=
let HS3 := fresh "HS3" in
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msv =>
pose proof (st_ok_pin_rege Ev ssx msv r e HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Hr; cbn [sv_denot]; dtac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS | st_ok _ ?Ev ?ssx ?msv =>
pose proof (st_ok_pin_rege Ev ssx msv r e HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Hr; cbn [sv_denot]; dtac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
Ltac add_atom_win HS n w En :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_havoc_hi n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) | st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_havoc_hi n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia)))  end.
Ltac nat_side := first [ apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (Nat.eqb_neq _ _)); vm_compute; reflexivity
| cbn [length Nat.add]; apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity ].
Ltac hc_atom H n v En rtac :=
lazymatch type of H with context [U ?E' (SOff n 0)] =>
rewrite (U_atom E' n v ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact En)) in H by rtac end.
Ltac rebaseF HS AG HEv :=
let AG2 := fresh "AG" in let Ev := fresh "E" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
first [ pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as HEIv | pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as HEIv ];
rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by nat_side; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by nat_side; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG | st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
first [ pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as HEIv | pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as HEIv ];
rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by nat_side; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by nat_side; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG  end end.
Ltac rebase_goal := lazymatch goal with HS0 : st_ok_pi _ _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ =>
let HEv0 := fresh "HEv" in rebaseF HS0 AG0 HEv0; clear HEv0 end.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma land_low8 : forall x m, 0 <= x -> 0 <= m < 256 -> Z.land (x mod 256) m = Z.land x m.
Proof.
intros x m Hx Hm. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
destruct (Z_lt_le_dec n 8) as [Hl|Hge].
- change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit m n) with false; [rewrite !andb_false_r; reflexivity|].
symmetry. destruct (Z.eq_dec m 0) as [->|Hm0]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
apply (Z.le_lt_trans _ (Z.log2 255)); [apply Z.log2_le_mono; lia|]. cbn. lia.
Qed.
Lemma gen_test8 : forall E n v m, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= m < 256 ->
Z.land (U E (SExt false 8 (SOff n 0))) m = Z.land v m.
Proof.
intros E n v m Hn Hv Hm. rewrite U_zext. change (2 ^ Z.of_N 8) with 256.
rewrite (U_atom E n v Hn Hv). apply land_low8; lia.
Qed.
Lemma reg_and1_zero0 : forall (Hw : word -> bool) E ss ms (r : bv 5) n v,
st_ok SEGS E ss (restrict Hw ms) -> sr_get (ss_regs ss) r = SAlu ALU_AND (SOff n 0) (SLit 1) ->
ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> Z.land v 1 = 0 -> getr (ms_regs ms) r = Z_to_bv 64 0.
Proof.
intros Hw E ss ms r n v HS Hsr Hn Hv Hand.
rewrite (st_ok_restrict_reg SEGS Hw E ss ms r HS), Hsr.
rewrite <- (lit_of_word (sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 1)))). f_equal.
change (bv_unsigned (sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 1)))) with (U E (SAlu ALU_AND (SOff n 0) (SLit 1))).
rewrite U_and_lit by lia. rewrite (U_atom E n v Hn Hv). exact Hand.
Qed.
Lemma reg_and1_zero : forall (Hw : word -> bool) E ss ms (r : bv 5) n v,
st_ok_pi SEGS VAL E ss (restrict Hw ms) -> sr_get (ss_regs ss) r = SAlu ALU_AND (SOff n 0) (SLit 1) ->
ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> Z.land v 1 = 0 -> getr (ms_regs ms) r = Z_to_bv 64 0.
Proof.
intros Hw E ss ms r n v HS Hsr Hn Hv Hand. destruct ss as [pc0 sr0 fr0 sm0 rv0 fs0]. exact (reg_and1_zero0 Hw E _ ms r n v HS Hsr Hn Hv Hand).
Qed.
End b.
End a.
