(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhQ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UhQ1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uwbh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uwbh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UB5o.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UB5o. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJtP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJtP. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U5CJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U5CJ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Local Open Scope Z_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma gw_code : CodeAt.code_at rsegs 0x5958c QVbl.divtf3_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x5958c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x5958c /\ 0x5958c + 2308 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Definition saved12 (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) (j : list byte) : list cell :=
[CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma gw_eq_saved12 : @saved12 = ltac:(GwInst.gw_term (@QkTt.saved12) (@saved12)). Proof. unfold saved12, QkTt.saved12; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_saved12 : gw_eqs.

Definition DRr (signHi absHi absLo r3Hi r3Lo bHi bLo gt1 : Z) : Z :=
let abs1Lo := add64 absLo gt1 in
let b2Hi := shl64 bHi 1 in
let ca := b2z (Z.ltb abs1Lo absLo) in
let b3Hi0 := mulhu bLo 3 in
let abs1Hi := add64 absHi ca in
let b3Hi1 := add64 b3Hi0 bHi in
let b3Hi := add64 b3Hi1 b2Hi in
let ltInf1 := b2z (Z.ltb abs1Hi INF_HI) in
let gt3 := b2z (if Z.eqb r3Hi b3Hi then Z.ltb (add64 (shl64 bLo 1) bLo) r3Lo else Z.ltb b3Hi r3Hi) in
let inc2 := Z.land ltInf1 gt3 in
let b5Hi0 := mulhu bLo 5 in
let b5Hi1 := add64 b5Hi0 bHi in
let b4Hi := shl64 bHi 2 in
let abs2Lo := add64 abs1Lo inc2 in
let cb := b2z (Z.ltb abs2Lo abs1Lo) in
let abs2Hi := add64 abs1Hi cb in
let b5Hi := add64 b5Hi1 b4Hi in
let ltInf2 := b2z (Z.ltb abs2Hi INF_HI) in
let gt5 := b2z (if Z.eqb r3Hi b5Hi then Z.ltb (add64 (shl64 bLo 2) bLo) r3Lo else Z.ltb b5Hi r3Hi) in
let inc3 := Z.land ltInf2 gt5 in
let resLo := add64 abs2Lo inc3 in
let cc := b2z (Z.ltb resLo abs2Lo) in
let resHi := Z.lor (add64 abs2Hi cc) signHi in
mk128 resHi resLo.
Lemma gw_eq_DRr : @DRr = ltac:(GwInst.gw_term (@QkTt.DRr) (@DRr)). Proof. unfold DRr, QkTt.DRr; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_DRr : gw_eqs.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QkTt.divtf3_post) (@UB5o.divtf3_post) (Q6nq.gwt_def (@QVbl.divtf3_post) (@UB5o.divtf3_post) Q6nq.gwt_nil)).
Lemma div_round_DRr : ltac2:(Q6nq.tyx '(@QkTt.div_round_DRr rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32) [[@gw_eq_saved12__3; @gw_eq_saved12__2; @gw_eq_saved12]; [@gw_eq_DRr__3; @gw_eq_DRr__2; @gw_eq_DRr]] '(@nil Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.div_round_DRr rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.

Lemma subw_amt : forall wE, -2^30 < wE < 2^30 ->
bv_swrap 32 (1 - Z.land wE 18446744073709551615) = 1 - wE.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.subw_amt rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.

Section IfLemmas.
Context {T : Type}.
#[using="Type"] Lemma if_ltb_t x y (A B : T) : x < y -> (if x <? y then A else B) = A.   Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.if_ltb_t rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.
#[using="Type"] Lemma if_ltb_f x y (A B : T) : y <= x -> (if x <? y then A else B) = B.  Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.if_ltb_f rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.
#[using="Type"] Lemma if_leb_t x y (A B : T) : x <= y -> (if x <=? y then A else B) = A. Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.if_leb_t rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.
#[using="Type"] Lemma if_leb_f x y (A B : T) : y < x -> (if x <=? y then A else B) = B.  Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.if_leb_f rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.
#[using="Type"] Lemma if_eqb_t x y (A B : T) : x = y -> (if x =? y then A else B) = A.   Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.if_eqb_t rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.
#[using="Type"] Lemma if_eqb_f x y (A B : T) : x <> y -> (if x =? y then A else B) = B.  Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.if_eqb_f rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.
#[using="Type"] Lemma if_nltb_t x y (A B : T) : x < y -> (if negb (x <? y) then A else B) = B.   Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.if_nltb_t rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.
#[using="Type"] Lemma if_nltb_f x y (A B : T) : y <= x -> (if negb (x <? y) then A else B) = A.  Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.if_nltb_f rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.
#[using="Type"] Lemma if_nleb_t x y (A B : T) : x <= y -> (if negb (x <=? y) then A else B) = B. Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.if_nleb_t rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.
#[using="Type"] Lemma if_nleb_f x y (A B : T) : y < x -> (if negb (x <=? y) then A else B) = A.  Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.if_nleb_f rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.
#[using="Type"] Lemma if_neqb_t x y (A B : T) : x = y -> (if negb (x =? y) then A else B) = B.   Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.if_neqb_t rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.
#[using="Type"] Lemma if_neqb_f x y (A B : T) : x <> y -> (if negb (x =? y) then A else B) = A.  Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.if_neqb_f rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.
End IfLemmas.
Ltac decide_ifs ::=
repeat (match goal with
| |- context [if (?x <? ?y) then ?A else ?B] => first [rewrite (if_ltb_t x y A B) by lia | rewrite (if_ltb_f x y A B) by lia]
| |- context [if negb (?x <? ?y) then ?A else ?B] => first [rewrite (if_nltb_t x y A B) by lia | rewrite (if_nltb_f x y A B) by lia]
| |- context [if (?x <=? ?y) then ?A else ?B] => first [rewrite (if_leb_t x y A B) by lia | rewrite (if_leb_f x y A B) by lia]
| |- context [if negb (?x <=? ?y) then ?A else ?B] => first [rewrite (if_nleb_t x y A B) by lia | rewrite (if_nleb_f x y A B) by lia]
| |- context [if (?x =? ?y) then ?A else ?B] => first [rewrite (if_eqb_t x y A B) by lia | rewrite (if_eqb_f x y A B) by lia]
| |- context [if negb (?x =? ?y) then ?A else ?B] => first [rewrite (if_neqb_t x y A B) by lia | rewrite (if_neqb_f x y A B) by lia]
end). Ltac mkr__decide_ifs_6 := repeat (match goal with
| |- context [if (?x <? ?y) then ?A else ?B] => first [rewrite (if_ltb_t x y A B) by lia | rewrite (if_ltb_f x y A B) by lia]
| |- context [if negb (?x <? ?y) then ?A else ?B] => first [rewrite (if_nltb_t x y A B) by lia | rewrite (if_nltb_f x y A B) by lia]
| |- context [if (?x <=? ?y) then ?A else ?B] => first [rewrite (if_leb_t x y A B) by lia | rewrite (if_leb_f x y A B) by lia]
| |- context [if negb (?x <=? ?y) then ?A else ?B] => first [rewrite (if_nleb_t x y A B) by lia | rewrite (if_nleb_f x y A B) by lia]
| |- context [if (?x =? ?y) then ?A else ?B] => first [rewrite (if_eqb_t x y A B) by lia | rewrite (if_eqb_f x y A B) by lia]
| |- context [if negb (?x =? ?y) then ?A else ?B] => first [rewrite (if_neqb_t x y A B) by lia | rewrite (if_neqb_f x y A B) by lia]
end).

Section Walk.
Variables (sp sgw w6 : word).

#[using="Type"] Lemma Lepi : ltac2:(Q6nq.tyx '(@QkTt.Lepi rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32) [[@gw_eq_saved12__3; @gw_eq_saved12__2; @gw_eq_saved12]; [@gw_eq_DRr__3; @gw_eq_DRr__2; @gw_eq_DRr]; [@gw_eq_divtf3_post__3; @gw_eq_divtf3_post__2; @gw_eq_divtf3_post]; [@gw_eq_w0__3; @gw_eq_w0__2; @gw_eq_w0]] '([(-112); 4096; 367876]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.Lepi rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.

#[using="Type"] Lemma Lzero : ltac2:(Q6nq.tyx '(@QkTt.Lzero rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32) [[@gw_eq_saved12__3; @gw_eq_saved12__2; @gw_eq_saved12]; [@gw_eq_DRr__3; @gw_eq_DRr__2; @gw_eq_DRr]; [@gw_eq_divtf3_post__3; @gw_eq_divtf3_post__2; @gw_eq_divtf3_post]] '([(-112); 4096; 367308]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.Lzero rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.

#[using="Type"] Lemma Linf : ltac2:(Q6nq.tyx '(@QkTt.Linf rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32) [[@gw_eq_saved12__3; @gw_eq_saved12__2; @gw_eq_saved12]; [@gw_eq_DRr__3; @gw_eq_DRr__2; @gw_eq_DRr]; [@gw_eq_divtf3_post__3; @gw_eq_divtf3_post__2; @gw_eq_divtf3_post]] '([(-112); 4096; 367116]%Z : list Z) '(Q6nq.gwt_zc INF_HI gwt_X)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.Linf rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.

#[using="Type"] Lemma Lround : ltac2:(Q6nq.tyx '(@QkTt.Lround rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32) [[@gw_eq_saved12__3; @gw_eq_saved12__2; @gw_eq_saved12]; [@gw_eq_DRr__3; @gw_eq_DRr__2; @gw_eq_DRr]; [@gw_eq_divtf3_post__3; @gw_eq_divtf3_post__2; @gw_eq_divtf3_post]] '([(-112); 4096; 367724]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QkTt.Lround rsegs 0x5958c gw_code gw_base4 gw_baser mulhu_shl32). Qed.

End Walk.
