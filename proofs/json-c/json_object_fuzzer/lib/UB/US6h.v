(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QROt.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UjdK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UjdK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzHs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzHs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTIW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTIW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxrO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxrO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um2h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um2h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDgQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDgQ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8Ie.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8Ie.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzOj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzOj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSCw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSCw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qbz7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qbz7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qqmw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qqmw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTru.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTru.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations.
Import QlEo.Mq0.Exc. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x55624%Z.
Definition w_22 := 0x00010517%Z.
Definition w_25 := 0x35453603%Z.
Definition w_81 := 0xfb8ff0ef%Z.
Definition w_281 := 0xfffc1697%Z.
Definition w_282 := 0xc9068693%Z.
Definition w_332 := 0xfffc1597%Z.
Definition w_333 := 0xa7c58593%Z.
Definition w_360 := 0xfffbb597%Z.
Definition w_362 := 0x92f58593%Z.
Definition w_371 := 0xfffbb517%Z.
Definition w_372 := 0x90350513%Z.
Definition w_378 := 0xfffbd517%Z.
Definition w_379 := 0x76f50b93%Z.
Definition w_381 := 0xf49fa0ef%Z.
Definition w_383 := 0xf4dfa0ef%Z.
Definition w_389 := 0x1ec0a0ef%Z.
Definition w_395 := 0xfffbb617%Z.
Definition w_396 := 0x8a360613%Z.
Definition w_412 := 0xfffbb597%Z.
Definition w_413 := 0x85f58593%Z.
Definition w_426 := 0xfffc1597%Z.
Definition w_427 := 0x9e458593%Z.
Definition w_438 := 0xfffba597%Z.
Definition w_439 := 0x7f758893%Z.
Definition w_453 := 0xfffba517%Z.
Definition w_454 := 0x7bb50513%Z.
Definition w_467 := 0xfffba597%Z.
Definition w_468 := 0x78358713%Z.
Definition w_473 := 0xfffbd697%Z.
Definition w_474 := 0x71868693%Z.
Definition w_530 := 0x8b4ff0ef%Z.
Definition w_533 := 0xfffba597%Z.
Definition w_534 := 0x67b58593%Z.
Definition w_543 := 0xfffba597%Z.
Definition w_545 := 0x65358893%Z.
Definition w_627 := 0x1c9090ef%Z.
Definition w_639 := 0xf01fe0ef%Z.
Definition w_648 := 0xeddfe0ef%Z.
Definition w_655 := 0xec1fe0ef%Z.
Definition w_668 := 0x125090ef%Z.
Definition w_680 := 0xe5dfe0ef%Z.
Definition w_689 := 0xe39fe0ef%Z.
Definition w_701 := 0x0a1090ef%Z.
Definition w_713 := 0xdd9fe0ef%Z.
Definition w_722 := 0xdb5fe0ef%Z.
Definition w_729 := 0xd99fe0ef%Z.
Definition w_742 := 0x7fc090ef%Z.
Definition w_754 := 0xd35fe0ef%Z.
Definition w_762 := 0xd15fe0ef%Z.
Definition w_798 := 0x8c5fa0ef%Z.
Definition w_883 := 0xf70fa0ef%Z.
Definition w_907 := 0xbd5fa0ef%Z.
Definition hi_22 := (Z_to_bv 20 16).
Definition hi_281 := (Z_to_bv 20 1048513).
Definition hi_332 := (Z_to_bv 20 1048513).
Definition hi_360 := (Z_to_bv 20 1048507).
Definition hi_371 := (Z_to_bv 20 1048507).
Definition hi_378 := (Z_to_bv 20 1048509).
Definition hi_395 := (Z_to_bv 20 1048507).
Definition hi_412 := (Z_to_bv 20 1048507).
Definition hi_426 := (Z_to_bv 20 1048513).
Definition hi_438 := (Z_to_bv 20 1048506).
Definition hi_453 := (Z_to_bv 20 1048506).
Definition hi_467 := (Z_to_bv 20 1048506).
Definition hi_473 := (Z_to_bv 20 1048509).
Definition hi_533 := (Z_to_bv 20 1048506).
Definition hi_543 := (Z_to_bv 20 1048506).
Definition lo_25 := (Z_to_bv 12 852).
Definition lo_282 := (Z_to_bv 12 3216).
Definition lo_333 := (Z_to_bv 12 2684).
Definition lo_362 := (Z_to_bv 12 2351).
Definition lo_372 := (Z_to_bv 12 2307).
Definition lo_379 := (Z_to_bv 12 1903).
Definition lo_396 := (Z_to_bv 12 2211).
Definition lo_413 := (Z_to_bv 12 2143).
Definition lo_427 := (Z_to_bv 12 2532).
Definition lo_439 := (Z_to_bv 12 2039).
Definition lo_454 := (Z_to_bv 12 1979).
Definition lo_468 := (Z_to_bv 12 1923).
Definition lo_474 := (Z_to_bv 12 1816).
Definition lo_534 := (Z_to_bv 12 1659).
Definition lo_545 := (Z_to_bv 12 1619).
Definition joff_81 := (Z_to_bv 21 2095032).
Definition joff_381 := (Z_to_bv 21 2076488).
Definition joff_383 := (Z_to_bv 21 2076492).
Definition joff_389 := (Z_to_bv 21 41452).
Definition joff_530 := (Z_to_bv 21 2093236).
Definition joff_627 := (Z_to_bv 21 39368).
Definition joff_639 := (Z_to_bv 21 2092800).
Definition joff_648 := (Z_to_bv 21 2092764).
Definition joff_655 := (Z_to_bv 21 2092736).
Definition joff_668 := (Z_to_bv 21 39204).
Definition joff_680 := (Z_to_bv 21 2092636).
Definition joff_689 := (Z_to_bv 21 2092600).
Definition joff_701 := (Z_to_bv 21 39072).
Definition joff_713 := (Z_to_bv 21 2092504).
Definition joff_722 := (Z_to_bv 21 2092468).
Definition joff_729 := (Z_to_bv 21 2092440).
Definition joff_742 := (Z_to_bv 21 38908).
Definition joff_754 := (Z_to_bv 21 2092340).
Definition joff_762 := (Z_to_bv 21 2092308).
Definition joff_798 := (Z_to_bv 21 2074820).
Definition joff_883 := (Z_to_bv 21 2074480).
Definition joff_907 := (Z_to_bv 21 2075604).
Definition G_102fd := 0x104f3%Z.
Definition G_10741 := 0x1337b%Z.
Definition G_107e0 := 0x134a0%Z.
Definition G_11778 := 0x165d0%Z.
Definition G_11858 := 0x166b0%Z.
Definition G_118c0 := 0x16718%Z.
Definition got_ssp := got_ssp.
Definition GLOBALS_TOP := GLOBALS_TOP.
Definition STATIC_SPLIT := STATIC_SPLIT.
Definition ssp_guard := ssp_guard.
Definition e_194bc := 0x50b60%Z.
Definition e_194c8 := 0x50b6c%Z.
Definition e_197bc := 0x51024%Z.
Definition e_fwritex := 0x54f20%Z.
Definition e_memset := 0x5f9b8%Z.
Definition e_2596c := 0x5fe24%Z.
Definition e_memchr := 0x5f33c%Z.
Definition jt_11778_o1504 := 259636%Z.
Definition jt_11778_o1432 := 259564%Z.
Definition jt_11778_o1800 := 259932%Z.
Definition jt_11778_o1744 := 259876%Z.
Definition jt_11778_o1864 := 259996%Z.
Definition jt_11778_o1352 := 259484%Z.
Lemma CODE : CodeAt.code_at rsegs 0x55624 (Q8l1.Mq1.printf_core_code 0x00010517%Z 0x35453603%Z 0xfb8ff0ef%Z 0xfffc1697%Z 0xc9068693%Z 0xfffc1597%Z 0xa7c58593%Z 0xfffbb597%Z 0x92f58593%Z 0xfffbb517%Z 0x90350513%Z 0xfffbd517%Z 0x76f50b93%Z 0xf49fa0ef%Z 0xf4dfa0ef%Z 0x1ec0a0ef%Z 0xfffbb617%Z 0x8a360613%Z 0xfffbb597%Z 0x85f58593%Z 0xfffc1597%Z 0x9e458593%Z 0xfffba597%Z 0x7f758893%Z 0xfffba517%Z 0x7bb50513%Z 0xfffba597%Z 0x78358713%Z 0xfffbd697%Z 0x71868693%Z 0x8b4ff0ef%Z 0xfffba597%Z 0x67b58593%Z 0xfffba597%Z 0x65358893%Z 0x1c9090ef%Z 0xf01fe0ef%Z 0xeddfe0ef%Z 0xec1fe0ef%Z 0x125090ef%Z 0xe5dfe0ef%Z 0xe39fe0ef%Z 0x0a1090ef%Z 0xdd9fe0ef%Z 0xdb5fe0ef%Z 0xd99fe0ef%Z 0x7fc090ef%Z 0xd35fe0ef%Z 0xd15fe0ef%Z 0x8c5fa0ef%Z 0xf70fa0ef%Z 0xbd5fa0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x55624 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x55624 /\ 0x55624 + 3632 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition strnlen_spec := @strnlen_spec.
Definition va_area_bound := @va_area_bound.
Definition pop_arg_spec := @pop_arg_spec.
Lemma ROM_G_118c0 : ltac2:(GwEq.gw_fact_ty 'segs '(@QROt.Mq0.gw_all) @ROM_G_118c0). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_G_102fd : ltac2:(GwEq.gw_fact_ty 'segs '(@QROt.Mq0.gw_all) @ROM_G_102fd). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_G_107e0 : ltac2:(GwEq.gw_fact_ty 'segs '(@QROt.Mq0.gw_all) @ROM_G_107e0). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac show_goal := match goal with |- ?G => idtac "GOAL:" G end.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac plia := unfold zlength, got_ssp, ssp_guard, PC_DEPTH, OUT_DEPTH, GLOBALS_TOP, FMT_FP_DEPTH, INT_MAX in *; lia.

Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.

Tactic Notation "callw" tactic3(tac) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ tac | post_call segs m ]
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac br K := brf K; try (exfalso; lia).

Ltac fixr := try (rewrite !swrap32_small by lia); try (rewrite !Z.add_0_r).

Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end.

Definition hide (P : Prop) := P.
Lemma gw_eq_hide : @hide = ltac:(GwInst.gw_term (@QROt.Mq0.hide) (@hide)). Proof. unfold hide, QROt.Mq0.hide; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_hide : gw_eqs.
Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

Ltac ienter := lazymatch goal with |- Ql2m.Mq3.implM _ _ _ _ _ => unfold Ql2m.Mq3.implM; apply impl_from_evt | |- QlEo.Mq0.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
lazymatch goal with |- QlEo.Mq0.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Ql2m.Mq3.implM rsegs c s Q ms) | _ => idtac end.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [GwInst.gw_exact (@QROt.Mq0.zb_length) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.zb_length)]. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [GwInst.gw_exact (@QROt.Mq0.zb_app) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.zb_app)]. Qed.
Lemma nth_error_zb : forall l i c, nth_error l i = Some c -> nth_error (zb l) i = Some (Z_to_bv 8 c).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [GwInst.gw_exact (@QROt.Mq0.nth_error_zb) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.nth_error_zb)]. Qed.
Lemma znth_nth_error : forall l i, (0 <= i < zlength l)%Z -> nth_error l (Z.to_nat i) = Some (znth l i).
Proof. first [GwInst.gw_exact (@QROt.Mq0.znth_nth_error) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.znth_nth_error)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QQRC.Mq0.zb) (@UDgQ.zb) (Q6nq.gwt_def (@QROt.Mq0.wfile) (@UxrO.wfile) (Q6nq.gwt_def (@QQLG.Mq7.wfile) (@UxrO.wfile) (Q6nq.gwt_def (@QROt.Mq0.va_area) (@UzOj.va_area) (Q6nq.gwt_def (@Q91D.Mq3.va_area) (@UzOj.va_area) (Q6nq.gwt_def (@Q8l1.Mq1.topok_stmt) (@UTru.topok_stmt) (Q6nq.gwt_def (@Q91D.Mq6.strnlen_post) (@UTIW.strnlen_post) (Q6nq.gwt_def (@QROt.Mq0.strnlen_post) (@UTIW.strnlen_post) (Q6nq.gwt_def (@QROt.Mq0.ssp_cells) (@Um2h.ssp_cells) (Q6nq.gwt_def (@Q91D.Mq2.ssp_cells) (@Um2h.ssp_cells) (Q6nq.gwt_def (@Q8l1.Mq1.sink_frame_stmt) (@UTru.sink_frame_stmt) (Q6nq.gwt_def (@QROt.Mq0.sink_frame_stmt) (@UTru.sink_frame_stmt) (Q6nq.gwt_def (@Q8l1.Mq1.sink_flags_stmt) (@UTru.sink_flags_stmt) (Q6nq.gwt_def (@QROt.Mq0.sink_flags_stmt) (@UTru.sink_flags_stmt) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_loop) (@QSCw.printf_loop) (Q6nq.gwt_def (@QROt.Mq0.pop_arg_post) (@UzOj.pop_arg_post) (Q6nq.gwt_def (@Q91D.Mq3.pop_arg_post) (@UzOj.pop_arg_post) (Q6nq.gwt_def (@Q91D.Mq3.pop_arg_lo) (@UzOj.pop_arg_lo) (Q6nq.gwt_def (@Q91D.Mq3.pop_arg_hi) (@UzOj.pop_arg_hi) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pass1_ok) (@QSCw.pass1_ok) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.parse_flags) (@QSCw.parse_flags) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.parse_dir) (@QSCw.parse_dir) (Q6nq.gwt_def (@Q8l1.Mq1.out_stmt) (@UTru.out_stmt) (Q6nq.gwt_def (@QROt.Mq0.out_stmt) (@UTru.out_stmt) (Q6nq.gwt_def (@Q8l1.Mq1.out_post) (@UTru.out_post) (Q6nq.gwt_def (@QROt.Mq0.out_post) (@UTru.out_post) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.mpad) (@QSCw.mpad) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.lit_run) (@QSCw.lit_run) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.is_digit) (@QSCw.is_digit) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.hex_digits) (@QSCw.hex_digits) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.getint) (@QSCw.getint) (Q6nq.gwt_def (@Q8l1.Mq1.fpcall_stmt) (@UTru.fpcall_stmt) (Q6nq.gwt_def (@QROt.Mq0.fpcall_stmt) (@UTru.fpcall_stmt) (Q6nq.gwt_def (@Q8l1.Mq1.fpcall_post) (@UTru.fpcall_post) (Q6nq.gwt_def (@QROt.Mq0.fpcall_post) (@UTru.fpcall_post) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.fp_calls) (@QSCw.fp_calls) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.flag_bit) (@QSCw.flag_bit) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.dir_ty_ok) (@QSCw.dir_ty_ok) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.digits_aux) (@QSCw.digits_aux) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.dec_digits) (@QSCw.dec_digits) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.d_ps) (@QSCw.d_ps) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_type_l) (@QSCw.conv_type_l) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_type) (@QSCw.conv_type) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_tail) (@QSCw.conv_tail) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_int) (@QSCw.conv_int) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv) (@QSCw.conv) (Q6nq.gwt_def (@Q8l1.Mq1.args_ok) (@UTru.args_ok) (Q6nq.gwt_def (@QROt.Mq0.args_ok) (@UTru.args_ok) (Q6nq.gwt_def (@Q8l1.Mq1.arg_ok) (@UTru.arg_ok) (Q6nq.gwt_def (@QROt.Mq0.arg_ok) (@UTru.arg_ok) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.XDIGITS) (@QSCw.XDIGITS) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.T_PTR) (@QSCw.T_PTR) (Q6nq.gwt_def (@Q91D.Mq3.T_PTR) (@QSCw.T_PTR) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.T_LONG) (@QSCw.T_LONG) (Q6nq.gwt_def (@Q91D.Mq3.T_LONG) (@QSCw.T_LONG) (Q6nq.gwt_def (@QFau.STATES1) (@Qqmw.STATES1) (Q6nq.gwt_def (@QFau.STATES0) (@Qqmw.STATES0) (Q6nq.gwt_def (@Q8l1.Mq1.PC_DEPTH) (@UTru.PC_DEPTH) (Q6nq.gwt_def (@Q8l1.Mq1.OUT_DEPTH) (@UTru.OUT_DEPTH) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_shp.F_fmt_fp.FMT_FP_DEPTH) (@Q8Ie.FMT_FP_DEPTH) Q6nq.gwt_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Lemma zbytes_read : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.zbytes_read) [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.zbytes_read) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.zbytes_read)]. Qed.
Lemma Forall_znth : forall (P : Z -> Prop) l i, Forall P l -> (0 <= i < zlength l)%Z -> P (znth l i).
Proof. first [GwInst.gw_exact (@QROt.Mq0.Forall_znth) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.Forall_znth)]. Qed.

Lemma land_lxor_distr : forall a b m, Z.land (Z.lxor a b) m = Z.lxor (Z.land a m) (Z.land b m).
Proof. first [GwInst.gw_exact (@QROt.Mq0.land_lxor_distr) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.land_lxor_distr)]. Qed.

Section Sfx.
Variable fmt : list Z.
Definition sfx (k : Z) : list Z := skipn (Z.to_nat k) fmt.
Lemma gw_eq_sfx : @sfx = ltac:(GwInst.gw_term (@QROt.Mq0.sfx) (@sfx)). Proof. unfold sfx, QROt.Mq0.sfx; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_sfx : gw_eqs.
#[using="Type"] Lemma sfx_cons : forall k, (0 <= k < zlength fmt)%Z -> sfx k = znth fmt k :: sfx (k + 1).
Proof. rewrite ?gw_eq_sfx; first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.sfx_cons) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.sfx_cons)]. Qed.
#[using="Type"] Lemma sfx_nil : forall k, (zlength fmt <= k)%Z -> sfx k = [].
Proof. rewrite ?gw_eq_sfx; first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.sfx_nil) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.sfx_nil)]. Qed.
#[using="Type"] Lemma sfx_skipn : forall n k, (0 <= k)%Z -> skipn n (sfx k) = sfx (k + Z.of_nat n).
Proof. rewrite ?gw_eq_sfx; first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.sfx_skipn) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.sfx_skipn)]. Qed.
#[using="Type"] Lemma sfx_length : forall k, (0 <= k <= zlength fmt)%Z -> zlength (sfx k) = (zlength fmt - k)%Z.
Proof. rewrite ?gw_eq_sfx; first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.sfx_length) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.sfx_length)]. Qed.
#[using="Type"] Lemma sfx_cons_inv : forall k c s, (0 <= k)%Z -> sfx k = c :: s -> (k < zlength fmt)%Z /\ c = znth fmt k /\ s = sfx (k + 1).
Proof. rewrite ?gw_eq_sfx; first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.sfx_cons_inv) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.sfx_cons_inv)]. Qed.

#[using="Type"] Lemma lit_run_firstn : forall s, lit_run s = firstn (length (lit_run s)) s.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_lit_run__3; @gw_eq_lit_run__2; @gw_eq_lit_run]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.lit_run_firstn) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.lit_run_firstn)]. Qed.
#[using="Type"] Lemma lit_run_length : forall s, (length (lit_run s) <= length s)%nat.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_lit_run__3; @gw_eq_lit_run__2; @gw_eq_lit_run]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.lit_run_length) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.lit_run_length)]. Qed.
#[using="Type"] Lemma lit_run_in : forall s j c, nth_error (lit_run s) j = Some c -> c <> 0%Z /\ c <> 37%Z.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_lit_run__3; @gw_eq_lit_run__2; @gw_eq_lit_run]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.lit_run_in) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.lit_run_in)]. Qed.
#[using="Type"] Lemma lit_run_stop : forall s c s', skipn (length (lit_run s)) s = c :: s' -> c = 0%Z \/ c = 37%Z.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_lit_run__3; @gw_eq_lit_run__2; @gw_eq_lit_run]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.lit_run_stop) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.lit_run_stop)]. Qed.

#[using="Type"] Lemma lit_run_sfx : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.lit_run_sfx) [[@gw_eq_lit_run__3; @gw_eq_lit_run__2; @gw_eq_lit_run]; [@gw_eq_sfx]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_sfx; ltac2:(GwEq.gw_rw [[@gw_eq_lit_run__3; @gw_eq_lit_run__2; @gw_eq_lit_run]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.lit_run_sfx) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.lit_run_sfx)]. Qed.
End Sfx.
Lemma gw_eq_sfx__2 : @sfx = ltac:(GwInst.gw_term (@QROt.Mq0.sfx) (@sfx)). Proof. unfold sfx, QROt.Mq0.sfx; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_sfx__2 : gw_eqs.

Lemma land_M64_id : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551615 = x.
Proof. first [GwInst.gw_exact (@QROt.Mq0.land_M64_id) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.land_M64_id)]. Qed.

Lemma landM64_zero : forall p, (-2^63 <= p < 2^63)%Z -> (Z.land p 18446744073709551615 = 0 <-> p = 0)%Z.
Proof. first [GwInst.gw_exact (@QROt.Mq0.landM64_zero) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.landM64_zero)]. Qed.
Lemma if_false_Z : forall a b : Z, (if false then a else b) = b. Proof. first [GwInst.gw_exact (@QROt.Mq0.if_false_Z) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.if_false_Z)]. Qed.
Lemma if_true_Z : forall a b : Z, (if true then a else b) = a. Proof. first [GwInst.gw_exact (@QROt.Mq0.if_true_Z) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.if_true_Z)]. Qed.

Lemma div10_magic : forall x, (0 <= x < 2^64)%Z ->
Z.shiftr (Z.shiftr (x * 14757395258967641293) 64) 3 = (x / 10)%Z.
Proof. first [GwInst.gw_exact (@QROt.Mq0.div10_magic) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.div10_magic)]. Qed.
Lemma lor48_digit : forall d, (0 <= d < 10)%Z -> Z.lor d 48 = (48 + d)%Z.
Proof. first [GwInst.gw_exact (@QROt.Mq0.lor48_digit) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.lor48_digit)]. Qed.
Lemma le1_small : forall v, (0 <= v < 256)%Z -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. first [GwInst.gw_exact (@QROt.Mq0.le1_small) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.le1_small)]. Qed.

Lemma digits_aux_S : ltac2:(Q6nq.tyx '(@QROt.Mq0.digits_aux_S) [[@gw_eq_digits_aux__3; @gw_eq_digits_aux__2; @gw_eq_digits_aux]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_digits_aux__3; @gw_eq_digits_aux__2; @gw_eq_digits_aux]]); first [GwInst.gw_exact (@QROt.Mq0.digits_aux_S) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.digits_aux_S)]. Qed.
Lemma digits_aux_acc : forall f b d y acc, digits_aux f b d y acc = digits_aux f b d y [] ++ acc.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_digits_aux__3; @gw_eq_digits_aux__2; @gw_eq_digits_aux]]); first [GwInst.gw_exact (@QROt.Mq0.digits_aux_acc) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.digits_aux_acc)]. Qed.
Lemma digits_aux_fuel : ltac2:(Q6nq.tyx '(@QROt.Mq0.digits_aux_fuel) [[@gw_eq_digits_aux__3; @gw_eq_digits_aux__2; @gw_eq_digits_aux]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_digits_aux__3; @gw_eq_digits_aux__2; @gw_eq_digits_aux]]); first [GwInst.gw_exact (@QROt.Mq0.digits_aux_fuel) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.digits_aux_fuel)]. Qed.
Lemma dec_digits_0 : dec_digits 0 = [].
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]]); first [GwInst.gw_exact (@QROt.Mq0.dec_digits_0) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.dec_digits_0)]. Qed.
Lemma dec_digits_small : forall x, (1 <= x <= 9)%Z -> dec_digits x = [48 + x]%Z.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]]); first [GwInst.gw_exact (@QROt.Mq0.dec_digits_small) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.dec_digits_small)]. Qed.
Lemma dec_digits_step : forall x, (10 <= x < 2^64)%Z -> dec_digits x = dec_digits (x / 10) ++ [48 + x mod 10]%Z.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]]); first [GwInst.gw_exact (@QROt.Mq0.dec_digits_step) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.dec_digits_step)]. Qed.
Lemma digits_aux_length : forall f b d y acc, (length (digits_aux f b d y acc) <= f + length acc)%nat.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_digits_aux__3; @gw_eq_digits_aux__2; @gw_eq_digits_aux]]); first [GwInst.gw_exact (@QROt.Mq0.digits_aux_length) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.digits_aux_length)]. Qed.
Lemma dec_digits_length : forall x, (length (dec_digits x) <= 20)%nat.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]]); first [GwInst.gw_exact (@QROt.Mq0.dec_digits_length) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.dec_digits_length)]. Qed.
Lemma dec_digits_range : forall x, Forall (fun c => 48 <= c < 58)%Z (dec_digits x).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]]); first [GwInst.gw_exact (@QROt.Mq0.dec_digits_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.dec_digits_range)]. Qed.

Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells rsegs m A [CB n bs] -> length bs = n.
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.rw_CB_length) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.rw_CB_length)]. Qed.
Lemma upd_firstn_part : forall {X} (l : list X) i x n, (n <= i < length l)%nat -> firstn n (upd l i x) = firstn n l.
Proof. first [GwInst.gw_exact (@QROt.Mq0.upd_firstn_part) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.upd_firstn_part)]. Qed.
Lemma upd_skipn_at : forall {X} (l : list X) i x, (i < length l)%nat -> skipn i (upd l i x) = x :: skipn (S i) l.
Proof. first [GwInst.gw_exact (@QROt.Mq0.upd_skipn_at) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.upd_skipn_at)]. Qed.

Lemma hex_digits_0 : forall l, hex_digits l 0 = [].
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_hex_digits__3; @gw_eq_hex_digits__2; @gw_eq_hex_digits]]); first [GwInst.gw_exact (@QROt.Mq0.hex_digits_0) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.hex_digits_0)]. Qed.
Lemma hex_digits_step : ltac2:(Q6nq.tyx '(@QROt.Mq0.hex_digits_step) [[@gw_eq_XDIGITS__3; @gw_eq_XDIGITS__2; @gw_eq_XDIGITS]; [@gw_eq_hex_digits__3; @gw_eq_hex_digits__2; @gw_eq_hex_digits]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_XDIGITS__3; @gw_eq_XDIGITS__2; @gw_eq_XDIGITS]; [@gw_eq_hex_digits__3; @gw_eq_hex_digits__2; @gw_eq_hex_digits]]); first [GwInst.gw_exact (@QROt.Mq0.hex_digits_step) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.hex_digits_step)]. Qed.
Lemma hex_digits_length : forall l x, (length (hex_digits l x) <= 16)%nat.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_hex_digits__3; @gw_eq_hex_digits__2; @gw_eq_hex_digits]]); first [GwInst.gw_exact (@QROt.Mq0.hex_digits_length) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.hex_digits_length)]. Qed.
Lemma hexchar_ok0 : ltac2:(Q6nq.tyx '(@QROt.Mq0.hexchar_ok0) [[@gw_eq_XDIGITS__3; @gw_eq_XDIGITS__2; @gw_eq_XDIGITS]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]] '([103]%Z : list Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_XDIGITS__3; @gw_eq_XDIGITS__2; @gw_eq_XDIGITS]]); first [GwInst.gw_exact (@QROt.Mq0.hexchar_ok0) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.hexchar_ok0)]. Qed.
Lemma hexchar_ok32 : ltac2:(Q6nq.tyx '(@QROt.Mq0.hexchar_ok32) [[@gw_eq_XDIGITS__3; @gw_eq_XDIGITS__2; @gw_eq_XDIGITS]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]] '([103]%Z : list Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_XDIGITS__3; @gw_eq_XDIGITS__2; @gw_eq_XDIGITS]]); first [GwInst.gw_exact (@QROt.Mq0.hexchar_ok32) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.hexchar_ok32)]. Qed.
Lemma hexchar_range : forall l v, (l = 0 \/ l = 32)%Z -> (0 <= v < 16)%Z -> (48 <= Z.lor (znth XDIGITS v) l < 103)%Z.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_XDIGITS__3; @gw_eq_XDIGITS__2; @gw_eq_XDIGITS]]); first [GwInst.gw_exact (@QROt.Mq0.hexchar_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.hexchar_range)]. Qed.
Lemma hex_digits_range : forall l x, (l = 0 \/ l = 32)%Z -> Forall (fun c => 48 <= c < 103)%Z (hex_digits l x).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_hex_digits__3; @gw_eq_hex_digits__2; @gw_eq_hex_digits]]); first [GwInst.gw_exact (@QROt.Mq0.hex_digits_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.hex_digits_range)]. Qed.

Lemma ift : forall (X : Type) (a b : X), (if true then a else b) = a. Proof. first [GwInst.gw_exact (@QROt.Mq0.ift) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.ift)]. Qed.
Lemma iff : forall (X : Type) (a b : X), (if false then a else b) = b. Proof. first [GwInst.gw_exact (@QROt.Mq0.iff) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.iff)]. Qed.

Lemma lo64_range : forall y, (0 <= lo64 y < 2^64)%Z.
Proof. first [GwInst.gw_exact (@QROt.Mq0.lo64_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.lo64_range)]. Qed.
Lemma hi64_range : forall y, (0 <= hi64 y < 2^64)%Z.
Proof. first [GwInst.gw_exact (@QROt.Mq0.hi64_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.hi64_range)]. Qed.
Lemma lo64_hi64 : forall y, (0 <= y < 2^128)%Z -> (lo64 y + 2^64 * hi64 y)%Z = y.
Proof. first [GwInst.gw_exact (@QROt.Mq0.lo64_hi64) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.lo64_hi64)]. Qed.

Section Ranges128.
Local Open Scope Z_scope.
#[using="Type"] Lemma mk128_range : forall hi lo, 0 <= hi < 2^64 -> 0 <= lo < 2^64 -> 0 <= mk128 hi lo < 2^128.
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.mk128_range) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.mk128_range)]. Qed.
#[using="Type"] Lemma shr64_range64 : forall a k, 0 <= a < 2^64 -> 0 <= k -> 0 <= Z.shiftr a k < 2^64.
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.shr64_range64) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.shr64_range64)]. Qed.
#[using="Type"] Lemma sra63_range : forall x, 0 <= sra63 x < 2^64.
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.sra63_range) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.sra63_range)]. Qed.
#[using="Type"] Lemma f128_of_d_range : forall d, 0 <= f128_of_d d < 2^128.
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.f128_of_d_range) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.f128_of_d_range)]. Qed.
End Ranges128.

Lemma sx32_int : ltac2:(Q6nq.tyx '(@QROt.Mq0.sx32_int) [[@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]] '(@nil Z) 'gwt_X).
Proof. first [GwInst.gw_exact (@QROt.Mq0.sx32_int) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.sx32_int)]. Qed.
Lemma zx32_uint : forall (slot : word) u, (bv_unsigned slot mod 2^32 = u)%Z -> zx32 slot = Z_to_bv 64 u.
Proof. first [GwInst.gw_exact (@QROt.Mq0.zx32_uint) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.zx32_uint)]. Qed.

Lemma land_land_same : forall a m, Z.land (Z.land a m) m = Z.land a m.
Proof. first [GwInst.gw_exact (@QROt.Mq0.land_land_same) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.land_land_same)]. Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof. first [GwInst.gw_exact (@QROt.Mq0.le8_of_bytes) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.le8_of_bytes)]. Qed.
Lemma cb8_c8_in : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.cb8_c8_in) [[@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]] '(@nil Z) 'gwt_X).
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.cb8_c8_in) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.cb8_c8_in)]. Qed.
Ltac c8ify H := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
let rec go pre l := lazymatch l with
| CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
| ?c :: ?l' => go constr:(pre ++ [c]) l'
| [] => idtac end in
go constr:(@nil cell) cs end.

Lemma printf_loop_S : ltac2:(Q6nq.tyx '(@QROt.Mq0.printf_loop_S) [[@gw_eq_conv__3; @gw_eq_conv__2; @gw_eq_conv]; [@gw_eq_lit_run__3; @gw_eq_lit_run__2; @gw_eq_lit_run]; [@gw_eq_parse_dir__3; @gw_eq_parse_dir__2; @gw_eq_parse_dir]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]] '(@nil Z) '(Q6nq.gwt_zc INT_MAX gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_conv__3; @gw_eq_conv__2; @gw_eq_conv]; [@gw_eq_lit_run__3; @gw_eq_lit_run__2; @gw_eq_lit_run]; [@gw_eq_parse_dir__3; @gw_eq_parse_dir__2; @gw_eq_parse_dir]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [GwInst.gw_exact (@QROt.Mq0.printf_loop_S) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.printf_loop_S)]. Qed.
Lemma fp_calls_S : ltac2:(Q6nq.tyx '(@QROt.Mq0.fp_calls_S) [[@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_lit_run__3; @gw_eq_lit_run__2; @gw_eq_lit_run]; [@gw_eq_parse_dir__3; @gw_eq_parse_dir__2; @gw_eq_parse_dir]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]] '(@nil Z) '(Q6nq.gwt_zc ZERO_PAD (Q6nq.gwt_zc LEFT_ADJ gwt_X))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_lit_run__3; @gw_eq_lit_run__2; @gw_eq_lit_run]; [@gw_eq_parse_dir__3; @gw_eq_parse_dir__2; @gw_eq_parse_dir]]); first [GwInst.gw_exact (@QROt.Mq0.fp_calls_S) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.fp_calls_S)]. Qed.

Lemma In_firstn_w : forall {A} (x : A) n l, In x (firstn n l) -> In x l.
Proof. first [GwInst.gw_exact (@QROt.Mq0.In_firstn_w) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.In_firstn_w)]. Qed.
Lemma In_skipn_w : forall {A} (x : A) n l, In x (skipn n l) -> In x l.
Proof. first [GwInst.gw_exact (@QROt.Mq0.In_skipn_w) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.In_skipn_w)]. Qed.
Lemma Forall_sub : forall {A} (P : A -> Prop) (l : list A) n k, Forall P l -> Forall P (firstn n (skipn k l)).
Proof. first [GwInst.gw_exact (@QROt.Mq0.Forall_sub) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.Forall_sub)]. Qed.
Lemma zb_firstn : forall n l, zb (firstn n l) = firstn n (zb l).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [GwInst.gw_exact (@QROt.Mq0.zb_firstn) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.zb_firstn)]. Qed.
Lemma zb_skipn : forall n l, zb (skipn n l) = skipn n (zb l).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [GwInst.gw_exact (@QROt.Mq0.zb_skipn) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.zb_skipn)]. Qed.
Lemma bytes_at_sub : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.bytes_at_sub) [[@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]] '(@nil Z) 'gwt_X).
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.bytes_at_sub) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.bytes_at_sub)]. Qed.

Lemma parse_dir_conv_type : forall s d rest, parse_dir s = Some (d, rest) -> dir_ty_ok d.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_dir_ty_ok__3; @gw_eq_dir_ty_ok__2; @gw_eq_dir_ty_ok]; [@gw_eq_parse_dir__3; @gw_eq_parse_dir__2; @gw_eq_parse_dir]]); first [GwInst.gw_exact (@QROt.Mq0.parse_dir_conv_type) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.parse_dir_conv_type)]. Qed.

Lemma parse_dir_xp : ltac2:(Q6nq.tyx '(@QROt.Mq0.parse_dir_xp) [[@gw_eq_parse_dir__3; @gw_eq_parse_dir__2; @gw_eq_parse_dir]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]] '(@nil Z) '(Q6nq.gwt_zc INT_MAX gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_parse_dir__3; @gw_eq_parse_dir__2; @gw_eq_parse_dir]]); first [GwInst.gw_exact (@QROt.Mq0.parse_dir_xp) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq0.parse_dir_xp)]. Qed.

Lemma c8_read4 : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.c8_read4) [[@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]] '(@nil Z) 'gwt_X).
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.c8_read4) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.c8_read4)]. Qed.

Lemma bytes_at_nil : forall m a, (0 <= a)%Z -> (a <= 2^64)%Z -> bytes_at rsegs m a [].
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.bytes_at_nil) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.bytes_at_nil)]. Qed.

Section PrintfCore.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Context {St : Type}.
Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 401408)%Z.

Hypothesis SEP_F : ((416216 <= Fp /\ Fp + 232 <= 622192) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((622200 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Notation sfx := (sfx fmt).
Definition ctx_all : unit :=
let _ := (ra, q, gp, tp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, F, fc0, m0,
lo, canary, A, fmt, AP, VA, slots, nla, nlt) in tt.
Lemma gw_eq_ctx_all : @ctx_all = ltac:(GwInst.gw_term (@QROt.Mq0.ctx_all) (@ctx_all)). Proof. unfold ctx_all, QROt.Mq0.ctx_all; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_ctx_all : gw_eqs.

Definition W : list (Z * Z) := [(lo, q); (AP, AP + 8); (Fp, Fp + 232); (B, B + BS)]%Z.
Lemma gw_eq_W : @W = ltac:(GwInst.gw_term (@QROt.Mq0.W) (@W)). Proof. unfold W, QROt.Mq0.W; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_W : gw_eqs.
Notation SPv := (Z_to_bv 64 (q + -544)).
Notation FPv := (Z_to_bv 64 Fp).

Definition Fokd (F1 F2 : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k.
Lemma gw_eq_Fokd : @Fokd = ltac:(GwInst.gw_term (@QROt.Mq0.Fokd) (@Fokd)). Proof. unfold Fokd, QROt.Mq0.Fokd; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_Fokd : gw_eqs.
Definition Fok (Ft : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k.
Lemma gw_eq_Fok : @Fok = ltac:(GwInst.gw_term (@QROt.Mq0.Fok) (@Fok)). Proof. unfold Fok, QROt.Mq0.Fok; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_Fok : gw_eqs.
#[using="Type"] Lemma Fok_refl : Fok F. Proof. rewrite ?gw_eq_Fok; first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.Fok_refl) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.Fok_refl)]. Qed.
#[using="Type"] Lemma Fok_trans : forall F1 F2, Fok F1 -> (forall k : reg, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k) -> Fok F2.
Proof. rewrite ?gw_eq_Fok; first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.Fok_trans) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.Fok_trans)]. Qed.

Definition POST : Z -> St -> machine_state -> Prop :=
fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (apv : word) (m' : word -> option byte),
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ Fok Ft
/\ stk rsegs m' lo q
/\ SINK m' st'
/\ ssp_cells m' canary
/\ rw_cells rsegs m' AP [C8 apv]
/\ (0 <= r <= INT_MAX)%Z.
Lemma gw_eq_POST : @POST = ltac:(GwInst.gw_term (@QROt.Mq0.POST rsegs got_ssp ssp_guard) (@POST)). Proof. unfold POST, QROt.Mq0.POST; rewrite ?gw_eq_W, ?gw_eq_Fok; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_POST : gw_eqs.

Definition hi_cells : list cell :=
[C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].
Lemma gw_eq_hi_cells : @hi_cells = ltac:(GwInst.gw_term (@QROt.Mq0.hi_cells) (@hi_cells)). Proof. unfold hi_cells, QROt.Mq0.hi_cells; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_hi_cells : gw_eqs.

Definition lo_cells (pfx s2s za pl plp l10n alo ahi : word) (j128 : list byte) : list cell :=
[C8 pfx; C8 s2s; C8 za; C8 pl; C8 plp; C8 (Z_to_bv 64 18446744072850558157); C8 (Z_to_bv 64 18446744073709486079);
C8 nla; C8 nlt; C8 (Z_to_bv 64 AP); C8 (Z_to_bv 64 75913); C8 l10n; C8 (Z_to_bv 64 ssp_guard); C8 (Z_to_bv 64 214748364);
C8 alo; C8 ahi; CB 24 j128].
Lemma gw_eq_lo_cells : @lo_cells = ltac:(GwInst.gw_term (@QROt.Mq0.lo_cells ssp_guard) (@lo_cells)). Proof. unfold lo_cells, QROt.Mq0.lo_cells; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_lo_cells : gw_eqs.

Definition finv (m : word -> option byte) : Prop :=
mem_inv rsegs m /\ munch W m0 m /\ wmono rsegs m0 m
/\ rw_cells rsegs m (q + -112) hi_cells
/\ stk rsegs m lo (q + -544)
/\ bytes_at rsegs m A (zb fmt)
/\ va_area m VA slots
/\ rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m ssp_guard [C8 canary].
Lemma gw_eq_finv : @finv = ltac:(GwInst.gw_term (@QROt.Mq0.finv rsegs got_ssp ssp_guard) (@finv)). Proof. unfold finv, QROt.Mq0.finv; rewrite ?gw_eq_W, ?gw_eq_hi_cells; ltac2:(GwEq.gw_rw [[@gw_eq_va_area__3; @gw_eq_va_area__2; @gw_eq_va_area]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_finv : gw_eqs.

#[using="Type"] Lemma u8_lit : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.u8_lit) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.u8_lit)]. Qed.
#[using="HF"] Lemma fmt_rng : forall i, (0 <= i < zlength fmt)%Z -> (0 <= znth fmt i < 256)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.fmt_rng) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.fmt_rng)]. Qed.

#[using="Type"] Lemma states0_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x16718 (zb STATES0).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_STATES0__3; @gw_eq_STATES0__2; @gw_eq_STATES0]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.states0_bytes) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.states0_bytes)]. Qed.

#[using="Type"] Lemma states0_read : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.states0_read) [[@gw_eq_conv_type__3; @gw_eq_conv_type__2; @gw_eq_conv_type]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_Fokd__3; @gw_eq_Fokd__2; @gw_eq_Fokd]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_hi_cells__3; @gw_eq_hi_cells__2; @gw_eq_hi_cells]; [@gw_eq_lo_cells__3; @gw_eq_lo_cells__2; @gw_eq_lo_cells]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]] '([(-65); 91928]%Z : list Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_conv_type__3; @gw_eq_conv_type__2; @gw_eq_conv_type]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.states0_read) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.states0_read)]. Qed.

#[using="Type"] Lemma states01_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 91928 (zb (STATES0 ++ STATES1)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_STATES0__3; @gw_eq_STATES0__2; @gw_eq_STATES0]; [@gw_eq_STATES1__3; @gw_eq_STATES1__2; @gw_eq_STATES1]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.states01_bytes) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.states01_bytes)]. Qed.
#[using="Type"] Lemma states0_read_l : forall m, mem_inv rsegs m -> ov_read_bytes rsegs m (wa (108 + 91928 + -65)) 1 = Some [Z_to_bv 8 1].
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.states0_read_l) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.states0_read_l)]. Qed.
#[using="Type"] Lemma states1_read : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.states1_read) [[@gw_eq_conv_type_l__3; @gw_eq_conv_type_l__2; @gw_eq_conv_type_l]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_Fokd__3; @gw_eq_Fokd__2; @gw_eq_Fokd]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_hi_cells__3; @gw_eq_hi_cells__2; @gw_eq_hi_cells]; [@gw_eq_lo_cells__3; @gw_eq_lo_cells__2; @gw_eq_lo_cells]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]] '([(-65); 91986]%Z : list Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_conv_type_l__3; @gw_eq_conv_type_l__2; @gw_eq_conv_type_l]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.states1_read) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.states1_read)]. Qed.

Definition PFXSTR : list Z := [45; 43; 32; 32; 32; 48; 88; 48; 120]%Z.
Lemma gw_eq_PFXSTR : @PFXSTR = ltac:(GwInst.gw_term (@QROt.Mq0.PFXSTR) (@PFXSTR)). Proof. unfold PFXSTR, QROt.Mq0.PFXSTR; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_PFXSTR : gw_eqs.
#[using="Type"] Lemma pfx_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 66803 (zb PFXSTR).
Proof. rewrite ?gw_eq_PFXSTR; ltac2:(GwEq.gw_rw [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.pfx_bytes) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.pfx_bytes)]. Qed.
#[using="Type"] Lemma pfx_sub : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.pfx_sub) [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]; [@gw_eq_PFXSTR]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_Fokd__3; @gw_eq_Fokd__2; @gw_eq_Fokd]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_hi_cells__3; @gw_eq_hi_cells__2; @gw_eq_hi_cells]; [@gw_eq_lo_cells__3; @gw_eq_lo_cells__2; @gw_eq_lo_cells]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]] '([66803]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_PFXSTR; ltac2:(GwEq.gw_rw [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.pfx_sub) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.pfx_sub)]. Qed.
#[using="Type"] Lemma xdigits_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 79008 (zb XDIGITS).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_XDIGITS__3; @gw_eq_XDIGITS__2; @gw_eq_XDIGITS]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.xdigits_bytes) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.xdigits_bytes)]. Qed.
#[using="Type"] Lemma xdigits_read : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.xdigits_read) [[@gw_eq_XDIGITS__3; @gw_eq_XDIGITS__2; @gw_eq_XDIGITS]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_Fokd__3; @gw_eq_Fokd__2; @gw_eq_Fokd]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_hi_cells__3; @gw_eq_hi_cells__2; @gw_eq_hi_cells]; [@gw_eq_lo_cells__3; @gw_eq_lo_cells__2; @gw_eq_lo_cells]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_PFXSTR__3; @gw_eq_PFXSTR__2; @gw_eq_PFXSTR]] '([79008]%Z : list Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_XDIGITS__3; @gw_eq_XDIGITS__2; @gw_eq_XDIGITS]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.xdigits_read) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.xdigits_read)]. Qed.

Definition JT1 : list Z := [156; 245; 3; 0; 28; 246; 3; 0; 60; 247; 3; 0; 28; 246; 3; 0; 156; 245; 3; 0; 156; 245; 3; 0; 156; 245; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 0; 248; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 156; 247; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 156; 245; 3; 0; 28; 246; 3; 0; 92; 247; 3; 0; 236; 245; 3; 0; 156; 245; 3; 0; 156; 245; 3; 0; 156; 245; 3; 0; 28; 246; 3; 0; 236; 245; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 72; 246; 3; 0; 232; 246; 3; 0; 148; 246; 3; 0; 136; 247; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 52; 246; 3; 0; 28; 246; 3; 0; 36; 247; 3; 0; 28; 246; 3; 0; 28; 246; 3; 0; 156; 247; 3; 0]%Z.
#[using="Type"] Lemma jt1_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 91600 (zb JT1).
Proof.
clear. intros m MI. apply ro_bytes_at. { exact MI. } { lia. } { cbn. lia. }
apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
#[using="Type"] Lemma jt1_read_lit : forall m (t : Z) bs, mem_inv rsegs m -> (65 <= t <= 120)%Z ->
firstn 4 (skipn (Z.to_nat (4 * (t - 65))) (zb JT1)) = bs ->
ov_read_bytes rsegs m (wa (91600 + 4 * (t - 65))) 4 = Some bs.
Proof.
clear. intros m t bs MI Ht <-.
pose proof (bytes_at_ov_read rsegs m 91600 (zb JT1) (Z.to_nat (4 * (t - 65))) 4 (jt1_bytes m MI)) as R.
rewrite Z2Nat.id in R by lia. apply R.
rewrite zb_length. cbn [length JT1]. lia.
Qed.
#[using="Type"] Lemma jt1_read_s : forall m t, mem_inv rsegs m -> t = 115%Z -> ov_read_bytes rsegs m (wa (91600 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 52; Z_to_bv 8 246; Z_to_bv 8 3; Z_to_bv 8 0].
Proof. clear. intros m t MI ->. apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]. Qed.
#[using="Type"] Lemma jt1_read_d : forall m t, mem_inv rsegs m -> (t = 100 \/ t = 105)%Z -> ov_read_bytes rsegs m (wa (91600 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 236; Z_to_bv 8 245; Z_to_bv 8 3; Z_to_bv 8 0].
Proof. clear. intros m t MI [-> | ->]; (apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]). Qed.
#[using="Type"] Lemma jt1_read_u : forall m t, mem_inv rsegs m -> t = 117%Z -> ov_read_bytes rsegs m (wa (91600 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 36; Z_to_bv 8 247; Z_to_bv 8 3; Z_to_bv 8 0].
Proof. clear. intros m t MI ->. apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]. Qed.
#[using="Type"] Lemma jt1_read_x : forall m t, mem_inv rsegs m -> (t = 120 \/ t = 88)%Z -> ov_read_bytes rsegs m (wa (91600 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 156; Z_to_bv 8 247; Z_to_bv 8 3; Z_to_bv 8 0].
Proof. clear. intros m t MI [-> | ->]; (apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]). Qed.

#[using="Type"] Lemma jt1_read_c : forall m t, mem_inv rsegs m -> t = 99%Z -> ov_read_bytes rsegs m (wa (91600 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 92; Z_to_bv 8 247; Z_to_bv 8 3; Z_to_bv 8 0].
Proof. clear. intros m t MI ->. apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]. Qed.

#[using="Type"] Lemma conv_type_cases : forall t ty, conv_type t = Some ty ->
(ty = T_PTR /\ t = 115%Z) \/ (ty = T_INT /\ (t = 100 \/ t = 105)%Z) \/ (ty = T_UINT /\ (t = 117 \/ t = 120 \/ t = 88)%Z) \/ (ty = T_DBL)
\/ (ty = T_INT /\ t = 99%Z).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_T_PTR__3; @gw_eq_T_PTR__2; @gw_eq_T_PTR]; [@gw_eq_conv_type__3; @gw_eq_conv_type__2; @gw_eq_conv_type]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.conv_type_cases) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.conv_type_cases)]. Qed.

#[using="Type"] Lemma fl_shl50 : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.fl_shl50) [[@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_Fokd__3; @gw_eq_Fokd__2; @gw_eq_Fokd]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_hi_cells__3; @gw_eq_hi_cells__2; @gw_eq_hi_cells]; [@gw_eq_lo_cells__3; @gw_eq_lo_cells__2; @gw_eq_lo_cells]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_PFXSTR__3; @gw_eq_PFXSTR__2; @gw_eq_PFXSTR]] '([8192; 131072; 9223372036854775808; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@SIGN64) (Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) (Q6nq.gwt_unf (@LEFT_ADJ) gwt_X))))).
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.fl_shl50) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.fl_shl50)]. Qed.
#[using="Type"] Lemma nzmask_bits' : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.nzmask_bits') [[@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_Fokd__3; @gw_eq_Fokd__2; @gw_eq_Fokd]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_hi_cells__3; @gw_eq_hi_cells__2; @gw_eq_hi_cells]; [@gw_eq_lo_cells__3; @gw_eq_lo_cells__2; @gw_eq_lo_cells]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_PFXSTR__3; @gw_eq_PFXSTR__2; @gw_eq_PFXSTR]] '([65536; 18446744073709486079]%Z : list Z) '(Q6nq.gwt_unf (@ZERO_PAD) gwt_X)).
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.nzmask_bits') | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.nzmask_bits')]. Qed.
#[using="Type"] Lemma nzmask_eq : forall fl, (0 <= fl < 131072)%Z -> Z.land fl 18446744073709486079 = Z.land fl (Z.lnot 65536).
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.nzmask_eq) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.nzmask_eq)]. Qed.
#[using="Type"] Lemma land_bound' : forall a m, (0 <= a)%Z -> (0 <= m)%Z -> (0 <= Z.land a m <= a)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.land_bound') | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.land_bound')]. Qed.

#[using="Type"] Lemma sextw_small : forall p, (-2147483648 <= p < 2147483648)%Z -> bv_swrap 32 (Z.land p 18446744073709551615 + 0) = p.
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.sextw_small) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.sextw_small)]. Qed.

#[using="Type"] Lemma pad_test_xor : forall fl b, Z.land b 73728 = b ->
(Z.land (Z.lxor fl b) 73728 =? 0)%Z = (Z.land fl 73728 =? b)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.pad_test_xor) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.pad_test_xor)]. Qed.

Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].

Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
#[using="Type"] Lemma implM_eq_ms : forall {X} (c : M St X) s Q ms ms', ms = ms' -> implM rsegs c s Q ms' -> implM rsegs c s Q ms.
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.implM_eq_ms) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.implM_eq_ms)]. Qed.
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].

Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

#[using="SFR"] Lemma sink_store : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.sink_store) [[@gw_eq_sink_frame_stmt__3; @gw_eq_sink_frame_stmt__2; @gw_eq_sink_frame_stmt]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_Fokd__3; @gw_eq_Fokd__2; @gw_eq_Fokd]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_hi_cells__3; @gw_eq_hi_cells__2; @gw_eq_hi_cells]; [@gw_eq_lo_cells__3; @gw_eq_lo_cells__2; @gw_eq_lo_cells]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_PFXSTR__3; @gw_eq_PFXSTR__2; @gw_eq_PFXSTR]] '([232]%Z : list Z) 'gwt_X).
Proof. first [ (pose proof SFR as gw_h_; clear SFR; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_sink_frame_stmt__3; @gw_eq_sink_frame_stmt__2; @gw_eq_sink_frame_stmt]]); rename gw_h_ into SFR) | idtac ]; first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.sink_store) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.sink_store)]. Qed.
#[using="SFR"] Lemma sink_call : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.sink_call) [[@gw_eq_sink_frame_stmt__3; @gw_eq_sink_frame_stmt__2; @gw_eq_sink_frame_stmt]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_Fokd__3; @gw_eq_Fokd__2; @gw_eq_Fokd]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_hi_cells__3; @gw_eq_hi_cells__2; @gw_eq_hi_cells]; [@gw_eq_lo_cells__3; @gw_eq_lo_cells__2; @gw_eq_lo_cells]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_PFXSTR__3; @gw_eq_PFXSTR__2; @gw_eq_PFXSTR]] '([232]%Z : list Z) 'gwt_X).
Proof. first [ (pose proof SFR as gw_h_; clear SFR; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_sink_frame_stmt__3; @gw_eq_sink_frame_stmt__2; @gw_eq_sink_frame_stmt]]); rename gw_h_ into SFR) | idtac ]; first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.sink_call) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.sink_call)]. Qed.

#[using="fmt slots"] Lemma arg_ok_W : forall m m' w a, arg_ok Fp B BS m lo q AP w a -> munch W m m' -> arg_ok Fp B BS m' lo q AP w a.
Proof. rewrite ?gw_eq_W; ltac2:(GwEq.gw_rw [[@gw_eq_arg_ok__3; @gw_eq_arg_ok__2; @gw_eq_arg_ok]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.arg_ok_W) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.arg_ok_W)]. Qed.
#[using="fmt slots"] Lemma args_ok_W : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.args_ok_W) [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_W]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_Fokd__3; @gw_eq_Fokd__2; @gw_eq_Fokd]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_hi_cells__3; @gw_eq_hi_cells__2; @gw_eq_hi_cells]; [@gw_eq_lo_cells__3; @gw_eq_lo_cells__2; @gw_eq_lo_cells]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_PFXSTR__3; @gw_eq_PFXSTR__2; @gw_eq_PFXSTR]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_W; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.args_ok_W) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.args_ok_W)]. Qed.

Definition lo_cells14 (pfx s2s za pl plp l10n : word) : list cell :=
[C8 pfx; C8 s2s; C8 za; C8 pl; C8 plp; C8 (Z_to_bv 64 18446744072850558157); C8 (Z_to_bv 64 18446744073709486079);
C8 nla; C8 nlt; C8 (Z_to_bv 64 AP); C8 (Z_to_bv 64 75913); C8 l10n; C8 (Z_to_bv 64 ssp_guard); C8 (Z_to_bv 64 214748364)].
Lemma gw_eq_lo_cells14 : @lo_cells14 = ltac:(GwInst.gw_term (@QROt.Mq0.lo_cells14 ssp_guard) (@lo_cells14)). Proof. unfold lo_cells14, QROt.Mq0.lo_cells14; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_lo_cells14 : gw_eqs.
#[using="Type"] Lemma lo_split : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.lo_split) [[@gw_eq_lo_cells]; [@gw_eq_lo_cells14]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_Fokd__3; @gw_eq_Fokd__2; @gw_eq_Fokd]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_hi_cells__3; @gw_eq_hi_cells__2; @gw_eq_hi_cells]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_PFXSTR__3; @gw_eq_PFXSTR__2; @gw_eq_PFXSTR]] '([(-544); 112; 128]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_lo_cells, ?gw_eq_lo_cells14; first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.lo_split) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.lo_split)]. Qed.
#[using="Type"] Lemma lo_join : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.lo_join) [[@gw_eq_lo_cells]; [@gw_eq_lo_cells14]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_Fokd__3; @gw_eq_Fokd__2; @gw_eq_Fokd]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_hi_cells__3; @gw_eq_hi_cells__2; @gw_eq_hi_cells]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_PFXSTR__3; @gw_eq_PFXSTR__2; @gw_eq_PFXSTR]] '([(-544); 112; 128]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_lo_cells, ?gw_eq_lo_cells14; first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.lo_join) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.lo_join)]. Qed.

Ltac transport_chunks segs m a bs ::=
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ apply (u8arr_frame segs m A2 xs a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ apply (u8ro_frame segs m A2 xs a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Ltac transport_after_call segs m m' MU WM ::=
let W := lazymatch type of MU with munch ?W _ _ => W end in
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; slia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; slia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : stk segs m ?loq ?hiq |- _ =>
first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
| clear H ]
| H : munch ?Wq ?mq m |- _ =>
first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
| fail 100 "callee footprint not inside caller footprint" ]
| H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
end.

#[using="fmt LO GLO QHI HAP HVA"] Lemma pop_arg_callq : forall ra' t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(Ft : bvmap 5 word) fc (m : word -> option byte) (a0v k ty : Z) (slot x y : word),
a0v = (q + -544 + 112)%Z ->
rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] ->
va_area m VA slots -> nth_error slots (Z.to_nat k) = Some slot -> (0 <= k)%Z ->
rw_cells rsegs m (q + -544 + 112) [C8 x; C8 y] ->
stk rsegs m lo (q + -544) ->
mem_inv rsegs m ->
(ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_DBL \/ ty = T_LONG \/ ty = T_ULONG)%Z ->
evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft' m',
ms' = MS (mkR ra' SPv gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
Ft' (ret_pc ra') fc None m' (seg_rom rsegs)
/\ munch [(q + -544 - 16, q + -544); (AP, AP + 8); (q + -544 + 112, q + -544 + 112 + 16)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (q + -544)
/\ rw_cells rsegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (k + 1)))]
/\ rw_cells rsegs m' (q + -544 + 112) [C8 (UzOj.pop_arg_lo ty slot); C8 (UzOj.pop_arg_hi ty slot y)]
/\ Fokd Ft Ft')
(MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a0v) (Z_to_bv 64 ty) (Z_to_bv 64 AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 0x56454) fc None m (seg_rom rsegs)).
Proof. rewrite ?gw_eq_Fokd; ltac2:(GwEq.gw_rw [[@gw_eq_T_LONG__3; @gw_eq_T_LONG__2; @gw_eq_T_LONG]; [@gw_eq_T_PTR__3; @gw_eq_T_PTR__2; @gw_eq_T_PTR]; [@gw_eq_pop_arg_hi__3; @gw_eq_pop_arg_hi__2; @gw_eq_pop_arg_hi]; [@gw_eq_pop_arg_lo__3; @gw_eq_pop_arg_lo__2; @gw_eq_pop_arg_lo]; [@gw_eq_va_area__3; @gw_eq_va_area__2; @gw_eq_va_area]]); first [ (pose proof LO as gw_h_; clear LO; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_PC_DEPTH__3; @gw_eq_PC_DEPTH__2; @gw_eq_PC_DEPTH]]); rename gw_h_ into LO) | idtac ]; first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.pop_arg_callq) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.pop_arg_callq)]. Qed.

#[using="LO GLO QHI"] Lemma strnlen_callq : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.strnlen_callq) [[@gw_eq_PC_DEPTH__3; @gw_eq_PC_DEPTH__2; @gw_eq_PC_DEPTH]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_Fokd__3; @gw_eq_Fokd__2; @gw_eq_Fokd]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_hi_cells__3; @gw_eq_hi_cells__2; @gw_eq_hi_cells]; [@gw_eq_lo_cells__3; @gw_eq_lo_cells__2; @gw_eq_lo_cells]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_PFXSTR__3; @gw_eq_PFXSTR__2; @gw_eq_PFXSTR]; [@gw_eq_lo_cells14__3; @gw_eq_lo_cells14__2; @gw_eq_lo_cells14]] '([(-544); 392740]%Z : list Z) '(Q6nq.gwt_unf (@strnlen_entry) gwt_X)).
Proof. first [ (pose proof LO as gw_h_; clear LO; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_PC_DEPTH__3; @gw_eq_PC_DEPTH__2; @gw_eq_PC_DEPTH]]); rename gw_h_ into LO) | idtac ]; first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.strnlen_callq) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.strnlen_callq)]. Qed.

#[using="Type"] Lemma zb_nonul : forall s, Forall (fun c => 0 < c < 256)%Z s -> ~ In (Z_to_bv 8 0) (zb s).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.zb_nonul) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.zb_nonul)]. Qed.

Definition out_postq (ra' : word) (Ft : bvmap 5 word) (fc : bv 32) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(S : Z) (bs : list Z) (m : word -> option byte) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
ms' = MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra') fc None m' (seg_rom rsegs)
/\ munch [(lo, q + -544); (Fp, Fp + 232); (B, B + BS)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (q + -544)
/\ SINK m' st'
/\ ssp_cells m' canary
/\ bytes_at rsegs m' S (zb bs).
Lemma gw_eq_out_postq : @out_postq = ltac:(GwInst.gw_term (@QROt.Mq0.out_postq rsegs got_ssp ssp_guard) (@out_postq)). Proof. unfold out_postq, QROt.Mq0.out_postq; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_out_postq : gw_eqs.
Lemma out_callq : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.out_callq) [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]; [@gw_eq_out_stmt__3; @gw_eq_out_stmt__2; @gw_eq_out_stmt]; [@gw_eq_PC_DEPTH__3; @gw_eq_PC_DEPTH__2; @gw_eq_PC_DEPTH]; [@gw_eq_topok_stmt__3; @gw_eq_topok_stmt__2; @gw_eq_topok_stmt]; [@gw_eq_out_postq]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_Fokd__3; @gw_eq_Fokd__2; @gw_eq_Fokd]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_hi_cells__3; @gw_eq_hi_cells__2; @gw_eq_hi_cells]; [@gw_eq_lo_cells__3; @gw_eq_lo_cells__2; @gw_eq_lo_cells]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_PFXSTR__3; @gw_eq_PFXSTR__2; @gw_eq_PFXSTR]; [@gw_eq_lo_cells14__3; @gw_eq_lo_cells14__2; @gw_eq_lo_cells14]] '([(-544); 232; 256; 347936]%Z : list Z) '(Q6nq.gwt_unf (@fwritex_entry) gwt_X)).
Proof using BS0 GLO HAP HOUT LO QHI SEP_B SEP_F TOK TQ fmt slots. rewrite ?gw_eq_out_postq; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [ (pose proof HOUT as gw_h_; clear HOUT; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_out_stmt__3; @gw_eq_out_stmt__2; @gw_eq_out_stmt]]); rename gw_h_ into HOUT) | idtac ]; first [ (pose proof LO as gw_h_; clear LO; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_PC_DEPTH__3; @gw_eq_PC_DEPTH__2; @gw_eq_PC_DEPTH]]); rename gw_h_ into LO) | idtac ]; first [ (pose proof TOK as gw_h_; clear TOK; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_topok_stmt__3; @gw_eq_topok_stmt__2; @gw_eq_topok_stmt]]); rename gw_h_ into TOK) | idtac ]; first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.out_callq) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.out_callq)]. Qed.

Definition fp_postq (ra' : word) (Ft : bvmap 5 word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(m : word -> option byte) : Z -> St -> machine_state -> Prop :=
fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
ms' = MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft' (ret_pc ra') fc' None m' (seg_rom rsegs)
/\ munch [(lo, q + -544); (Fp, Fp + 232); (B, B + BS)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ Fokd Ft Ft'
/\ stk rsegs m' lo (q + -544)
/\ SINK m' st'
/\ ssp_cells m' canary.
Lemma gw_eq_fp_postq : @fp_postq = ltac:(GwInst.gw_term (@QROt.Mq0.fp_postq rsegs got_ssp ssp_guard) (@fp_postq)). Proof. unfold fp_postq, QROt.Mq0.fp_postq; rewrite ?gw_eq_Fokd; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_fp_postq : gw_eqs.
#[using="TOK AP VA LO GLO QHI TQ SEP_F SEP_B HAP"] Lemma fp_callq : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq0.fp_callq) [[@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_topok_stmt__3; @gw_eq_topok_stmt__2; @gw_eq_topok_stmt]; [@gw_eq_PC_DEPTH__3; @gw_eq_PC_DEPTH__2; @gw_eq_PC_DEPTH]; [@gw_eq_fp_postq]; [@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_Fokd__3; @gw_eq_Fokd__2; @gw_eq_Fokd]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_hi_cells__3; @gw_eq_hi_cells__2; @gw_eq_hi_cells]; [@gw_eq_lo_cells__3; @gw_eq_lo_cells__2; @gw_eq_lo_cells]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_PFXSTR__3; @gw_eq_PFXSTR__2; @gw_eq_PFXSTR]; [@gw_eq_lo_cells14__3; @gw_eq_lo_cells14__2; @gw_eq_lo_cells14]; [@gw_eq_out_postq__3; @gw_eq_out_postq__2; @gw_eq_out_postq]] '([(-544); 97; 256; 353884]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_fp_postq; ltac2:(GwEq.gw_rw [[@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [ (pose proof TOK as gw_h_; clear TOK; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_topok_stmt__3; @gw_eq_topok_stmt__2; @gw_eq_topok_stmt]]); rename gw_h_ into TOK) | idtac ]; first [ (pose proof LO as gw_h_; clear LO; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_PC_DEPTH__3; @gw_eq_PC_DEPTH__2; @gw_eq_PC_DEPTH]]); rename gw_h_ into LO) | idtac ]; first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.fp_callq) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.fp_callq)]. Qed.

#[using="Type"] Lemma conv_type_dbl : forall t, conv_type t = Some T_DBL -> (69 <= t <= 103)%Z /\ Z.lor t 32 <> 97%Z.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_conv_type__3; @gw_eq_conv_type__2; @gw_eq_conv_type]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq0.conv_type_dbl) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq0.conv_type_dbl)]. Qed.

Definition S_EXIT : Prop :=
forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (r : Z)
(pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte) (apv : word),
let _ := ctx_all in
finv m ->
rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
rw_cells rsegs m (q + -392) [CB 24 digs] ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells rsegs m AP [C8 apv] ->
frm0 fc -> Fok Ft -> (0 <= r <= INT_MAX)%Z ->
evt rsegs (POST r st)
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x56400) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_EXIT : @S_EXIT = ltac:(GwInst.gw_term (@QROt.Mq0.S_EXIT rsegs 0x55624 got_ssp ssp_guard) (@S_EXIT)). Proof. unfold S_EXIT, QROt.Mq0.S_EXIT; rewrite ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_lo_cells, ?gw_eq_finv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_EXIT : gw_eqs.

Definition S_SCAN : Prop :=
forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i n cnt' : Z) (Q : machine_state -> Prop),
let _ := ctx_all in
finv m ->
(0 <= i)%Z -> (0 <= n)%Z -> (i + n < zlength fmt)%Z ->
(forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z ->
(znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z ->
(0 < n \/ znth fmt i = 37)%Z ->
(0 <= cnt' <= INT_MAX)%Z -> (n <= INT_MAX - cnt')%Z ->
(forall a1 a2 : word,
evt rsegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (A + i + n)) a1 a2 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - cnt')) (Z_to_bv 64 cnt') x20 (Z_to_bv 64 (A + i + n)) (Z_to_bv 64 n) (Z_to_bv 64 (A + i)) x24 x25 (Z_to_bv 64 n) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5574c) fc None m (seg_rom rsegs))) ->
evt rsegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (znth fmt i)) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 cnt') x20 x21 x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x556f0) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_SCAN : @S_SCAN = ltac:(GwInst.gw_term (@QROt.Mq0.S_SCAN rsegs 0x55624 got_ssp ssp_guard) (@S_SCAN)). Proof. unfold S_SCAN, QROt.Mq0.S_SCAN; rewrite ?gw_eq_ctx_all, ?gw_eq_finv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_SCAN : gw_eqs.

Definition S_FLAGS : Prop :=
forall (x1 x6 x7 x10 x11 x12 x15 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(p k fl b : Z) (w3 : word) (FL : Z) (s1 : list Z),
let _ := ctx_all in
finv m -> (0 <= p)%Z -> (1 <= k)%Z -> (p + k <= zlength fmt)%Z ->
bv_unsigned w3 = b -> (0 <= fl < 131072)%Z -> (0 <= b < 131072)%Z ->
parse_flags (sfx (p + k)) (Z.lor fl b) = (FL, s1) -> s1 <> [] ->
(forall (k' c' : Z) (a3 a4 a5 : word),
(p + k <= k' < zlength fmt)%Z -> s1 = sfx k' -> c' = znth fmt k' -> flag_bit c' = None -> (0 <= FL < 131072)%Z ->
evt rsegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 c') (Z_to_bv 64 (A + k')) a3 a4 a5 (Z_to_bv 64 1) (Z_to_bv 64 32)
x18 x19 x20 x21 x22 x23 (Z_to_bv 64 FL) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55804) fc None m (seg_rom rsegs))) ->
evt rsegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 w3 (Z_to_bv 64 (A + p + k)) x15 (Z_to_bv 64 1) (Z_to_bv 64 32)
x18 x19 x20 x21 x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x557e0) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_FLAGS : @S_FLAGS = ltac:(GwInst.gw_term (@QROt.Mq0.S_FLAGS rsegs 0x55624 got_ssp ssp_guard) (@S_FLAGS)). Proof. unfold S_FLAGS, QROt.Mq0.S_FLAGS; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_flag_bit__3; @gw_eq_flag_bit__2; @gw_eq_flag_bit]; [@gw_eq_parse_flags__3; @gw_eq_parse_flags__2; @gw_eq_parse_flags]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_FLAGS : gw_eqs.

Definition S_WLOOP : Prop :=
forall (x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(pos acc w : Z) (s2 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= pos < zlength fmt)%Z -> (0 <= acc)%Z ->
is_digit (znth fmt pos) = true -> getint (sfx pos) acc = Some (w, s2) -> s2 <> [] ->
(forall (k2 : Z) (t0 t1 a1 a3 a4 a5 a6 a7 : word),
(pos < k2 < zlength fmt)%Z -> s2 = sfx k2 -> is_digit (znth fmt k2) = false -> (0 <= w <= INT_MAX)%Z ->
evt rsegs Q
(MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k2)) a3 a4 a5 a6 a7
x18 x19 x20 x21 (Z_to_bv 64 w) x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55934) fc None m (seg_rom rsegs))) ->
evt rsegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt pos + -48)) x12 (Z_to_bv 64 (A + pos)) x14 x15 x16 x17
x18 x19 x20 x21 (Z_to_bv 64 acc) x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55898) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_WLOOP : @S_WLOOP = ltac:(GwInst.gw_term (@QROt.Mq0.S_WLOOP rsegs 0x55624 got_ssp ssp_guard) (@S_WLOOP)). Proof. unfold S_WLOOP, QROt.Mq0.S_WLOOP; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_lo_cells, ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_getint__3; @gw_eq_getint__2; @gw_eq_getint]; [@gw_eq_is_digit__3; @gw_eq_is_digit__2; @gw_eq_is_digit]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_WLOOP : gw_eqs.

Definition S_WIDTH : Prop :=
forall (x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(k1 w : Z) (s2 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= k1 < zlength fmt)%Z ->
getint (sfx k1) 0 = Some (w, s2) -> s2 <> [] ->
(forall (k2 : Z) (t0 t1 a1 a3 a4 a5 a6 a7 : word),
(k1 <= k2 < zlength fmt)%Z -> s2 = sfx k2 -> is_digit (znth fmt k2) = false -> (0 <= w <= INT_MAX)%Z ->
evt rsegs Q
(MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k2)) a3 a4 a5 a6 a7
x18 x19 x20 x21 (Z_to_bv 64 w) x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55934) fc None m (seg_rom rsegs))) ->
evt rsegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5584c) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_WIDTH : @S_WIDTH = ltac:(GwInst.gw_term (@QROt.Mq0.S_WIDTH rsegs 0x55624 got_ssp ssp_guard) (@S_WIDTH)). Proof. unfold S_WIDTH, QROt.Mq0.S_WIDTH; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_lo_cells, ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_getint__3; @gw_eq_getint__2; @gw_eq_getint]; [@gw_eq_is_digit__3; @gw_eq_is_digit__2; @gw_eq_is_digit]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_WIDTH : gw_eqs.

Definition S_PLOOP : Prop :=
forall (x1 x6 x7 x10 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(pos acc p : Z) (s3 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= pos < zlength fmt)%Z -> (0 <= acc)%Z ->
is_digit (znth fmt pos) = true -> getint (sfx pos) acc = Some (p, s3) -> s3 <> [] ->
(forall (k3 : Z) (a1 a3 a4 : word),
(pos < k3 < zlength fmt)%Z -> s3 = sfx k3 -> is_digit (znth fmt k3) = false -> (0 <= p <= INT_MAX)%Z ->
evt rsegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 1) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k3)) a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55a6c) fc None m (seg_rom rsegs))) ->
evt rsegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 1) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt pos + -48)) (Z_to_bv 64 (A + pos)) x13 x14 x15 (Z_to_bv 64 10) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 acc) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x559f8) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_PLOOP : @S_PLOOP = ltac:(GwInst.gw_term (@QROt.Mq0.S_PLOOP rsegs 0x55624 got_ssp ssp_guard) (@S_PLOOP)). Proof. unfold S_PLOOP, QROt.Mq0.S_PLOOP; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_lo_cells, ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_getint__3; @gw_eq_getint__2; @gw_eq_getint]; [@gw_eq_is_digit__3; @gw_eq_is_digit__2; @gw_eq_is_digit]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_PLOOP : gw_eqs.

Definition S_PREC : Prop :=
forall (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(k2 k3 p : Z) (xp : bool) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= k2 < zlength fmt)%Z ->
( (znth fmt k2 <> 46 /\ p = -1 /\ xp = false /\ k3 = k2)
\/ (znth fmt k2 = 46 /\ xp = true /\ k2 + 1 < zlength fmt /\ znth fmt (k2 + 1) <> 42
/\ getint (sfx (k2 + 1)) 0 = Some (p, sfx k3) /\ k2 + 1 <= k3 < zlength fmt) )%Z ->
(forall (a1 a3 a4 : word),
(-1 <= p <= INT_MAX)%Z ->
evt rsegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k3)) a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55a6c) fc None m (seg_rom rsegs))) ->
evt rsegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 (Z_to_bv 64 (A + k2)) x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55934) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_PREC : @S_PREC = ltac:(GwInst.gw_term (@QROt.Mq0.S_PREC rsegs 0x55624 got_ssp ssp_guard) (@S_PREC)). Proof. unfold S_PREC, QROt.Mq0.S_PREC; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_lo_cells, ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_getint__3; @gw_eq_getint__2; @gw_eq_getint]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_PREC : gw_eqs.

Definition S_STATE : Prop :=
forall (x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(k3 ty : Z),
let _ := ctx_all in
finv m -> (0 <= k3 < zlength fmt)%Z -> conv_type (znth fmt k3) = Some ty ->
(forall (a2 a3 : word),
evt rsegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 ty) a2 a3 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 (Z_to_bv 64 (A + k3 + 1)) x22 x23 x24 x25 x26 (Z_to_bv 64 0) x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55aec) fc None m (seg_rom rsegs))) ->
evt rsegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) x11 (Z_to_bv 64 (A + k3)) x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55a6c) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_STATE : @S_STATE = ltac:(GwInst.gw_term (@QROt.Mq0.S_STATE rsegs 0x55624 got_ssp ssp_guard) (@S_STATE)). Proof. unfold S_STATE, QROt.Mq0.S_STATE; rewrite ?gw_eq_ctx_all, ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_conv_type__3; @gw_eq_conv_type__2; @gw_eq_conv_type]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_STATE : gw_eqs.

Definition S_STATEL : Prop :=
forall (x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(k3 ty : Z),
let _ := ctx_all in
finv m -> (0 <= k3)%Z -> (k3 + 1 < zlength fmt)%Z -> znth fmt k3 = 108%Z -> conv_type_l (znth fmt (k3 + 1)) = Some ty ->
(forall (a2 a3 : word),
evt rsegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 ty) a2 a3 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 (Z_to_bv 64 (A + k3 + 2)) x22 x23 x24 x25 x26 (Z_to_bv 64 1) x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55aec) fc None m (seg_rom rsegs))) ->
evt rsegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) x11 (Z_to_bv 64 (A + k3)) x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55a6c) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_STATEL : @S_STATEL = ltac:(GwInst.gw_term (@QROt.Mq0.S_STATEL rsegs 0x55624 got_ssp ssp_guard) (@S_STATEL)). Proof. unfold S_STATEL, QROt.Mq0.S_STATEL; rewrite ?gw_eq_ctx_all, ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_conv_type_l__3; @gw_eq_conv_type_l__2; @gw_eq_conv_type_l]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_STATEL : gw_eqs.

Definition S_DIR : Prop :=
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(i : Z) (d : dir) (rest : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= i)%Z -> (i + 1 <= zlength fmt)%Z ->
parse_dir (sfx (i + 1)) = Some (d, rest) ->
(forall (k4 : Z) (a2 a3 a4 t1 : word),
(i + 1 < k4 <= zlength fmt)%Z -> rest = sfx k4 -> znth fmt (k4 - 1) = d_t d ->
(0 <= d_fl d < 131072)%Z -> (0 <= d_w d <= INT_MAX)%Z -> (-1 <= d_p d <= INT_MAX)%Z ->
evt rsegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
(Z_to_bv 64 (-1)) (Z_to_bv 64 (d_ty d)) a2 a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 (Z_to_bv 64 (A + k4)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 (d_fl d)) (Z_to_bv 64 (d_p d)) x26 (Z_to_bv 64 (d_ps d)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55aec) fc None m (seg_rom rsegs))) ->
evt rsegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55770) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_DIR : @S_DIR = ltac:(GwInst.gw_term (@QROt.Mq0.S_DIR rsegs 0x55624 got_ssp ssp_guard) (@S_DIR)). Proof. unfold S_DIR, QROt.Mq0.S_DIR; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_lo_cells, ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_d_ps__3; @gw_eq_d_ps__2; @gw_eq_d_ps]; [@gw_eq_parse_dir__3; @gw_eq_parse_dir__2; @gw_eq_parse_dir]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_DIR : gw_eqs.

Definition S_END : Prop :=
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (r : Z)
(pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte) (apv : word),
let _ := ctx_all in
finv m ->
rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
rw_cells rsegs m (q + -392) [CB 24 digs] ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells rsegs m AP [C8 apv] ->
frm0 fc -> Fok Ft -> (0 <= r <= INT_MAX)%Z ->
evt rsegs (POST r st)
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) FPv x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x562a8) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_END : @S_END = ltac:(GwInst.gw_term (@QROt.Mq0.S_END rsegs 0x55624 got_ssp ssp_guard) (@S_END)). Proof. unfold S_END, QROt.Mq0.S_END; rewrite ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_lo_cells, ?gw_eq_finv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_END : gw_eqs.

Definition S_HEAD (fuel : nat) : Prop :=
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i cnt l k : Z) (args : list parg)
(pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells rsegs m (q + -392) [CB 24 digs] ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i) args) ->
frm0 fc -> Fok Ft ->
(0 <= i)%Z -> (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l <= INT_MAX)%Z ->
implM rsegs (printf_loop OUT OUTFP fuel (sfx i) args (cnt + l)) st POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 cnt) FPv (Z_to_bv 64 (A + i)) x22 x23 x24 x25 (Z_to_bv 64 l) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x556d4) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_HEAD : @S_HEAD = ltac:(GwInst.gw_term (@QROt.Mq0.S_HEAD rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@S_HEAD)). Proof. unfold S_HEAD, QROt.Mq0.S_HEAD; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_lo_cells, ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_HEAD : gw_eqs.

Definition S_CONV : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (d : dir) (a : parg) (args : list parg)
(pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells rsegs m (q + -392) [CB 24 digs] ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) (a :: args) ->
match a with PA_g dd =>
fpcall_stmt Fp B BS SINK TOPOK OUTFP
(f128_of_d dd, d_w d, d_p d, (if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD))%Z, d_t d)
| _ => True end ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(1 <= i4 <= zlength fmt)%Z -> znth fmt (i4 - 1) = d_t d -> dir_ty_ok d ->
(0 <= d_fl d < 131072)%Z -> (0 <= d_w d <= INT_MAX)%Z -> (-1 <= d_p d <= INT_MAX)%Z ->
((d_xp d = false /\ d_p d = -1) \/ (d_xp d = true /\ 0 <= d_p d <= INT_MAX))%Z ->
(0 <= c <= INT_MAX)%Z ->
implM rsegs (cnt' <- conv OUT OUTFP c d a ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
(Z_to_bv 64 (-1)) (Z_to_bv 64 (d_ty d)) x12 x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 (d_fl d)) (Z_to_bv 64 (d_p d)) x26 (Z_to_bv 64 (d_ps d)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55aec) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_CONV : @S_CONV = ltac:(GwInst.gw_term (@QROt.Mq0.S_CONV rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@S_CONV)). Proof. unfold S_CONV, QROt.Mq0.S_CONV; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_lo_cells, ?gw_eq_finv, ?gw_eq_S_HEAD; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv__3; @gw_eq_conv__2; @gw_eq_conv]; [@gw_eq_d_ps__3; @gw_eq_d_ps__2; @gw_eq_d_ps]; [@gw_eq_dir_ty_ok__3; @gw_eq_dir_ty_ok__2; @gw_eq_dir_ty_ok]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_CONV : gw_eqs.

Definition body_loc (BA n : Z) : Prop :=
((q + -392 <= BA /\ BA + n <= q + -368)
\/ ((BA + n <= lo \/ q <= BA) /\ (BA + n <= Fp \/ Fp + 232 <= BA) /\ (BA + n <= B \/ B + BS <= BA)))%Z.
Lemma gw_eq_body_loc : @body_loc = ltac:(GwInst.gw_term (@QROt.Mq0.body_loc) (@body_loc)). Proof. unfold body_loc, QROt.Mq0.body_loc; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_body_loc : gw_eqs.

Definition S_TAIL : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (prefix body : list Z) (BA PFXA : Z)
(s2s za plp alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells rsegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells rsegs m (q + -392) [CB 24 digs] ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
bytes_at rsegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> body_loc BA (zlength body) -> (BA + zlength body < 2^64)%Z -> (zlength body <= INT_MAX)%Z ->
(forall m', mem_inv rsegs m' -> bytes_at rsegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(0 <= PFXA)%Z -> (PFXA + zlength prefix <= 401408)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (-1 <= p <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
implM rsegs (cnt' <- conv_tail OUT c fl w p prefix body ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 (Z_to_bv 64 (BA + zlength body)) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55f70) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_TAIL : @S_TAIL = ltac:(GwInst.gw_term (@QROt.Mq0.S_TAIL rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_TAIL)). Proof. unfold S_TAIL, QROt.Mq0.S_TAIL; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_lo_cells, ?gw_eq_finv, ?gw_eq_S_HEAD, ?gw_eq_body_loc; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_tail__3; @gw_eq_conv_tail__2; @gw_eq_conv_tail]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_TAIL : gw_eqs.

Definition tregs (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 s9 t3 t4 t5 t6 : word) (i4 c w BA wq pq : Z) : bvmap 5 word :=
mkR xra SPv gp tp t0 t1 t2 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) s8 s9 (Z_to_bv 64 wq) (Z_to_bv 64 pq) t3 t4 t5 t6.
Lemma gw_eq_tregs : @tregs = ltac:(GwInst.gw_term (@QROt.Mq0.tregs) (@tregs)). Proof. unfold tregs, QROt.Mq0.tregs; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_tregs : gw_eqs.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
Definition tinv (m : word -> option byte) (st : St) (k i4 : Z) (args : list parg) (fuel : nat)
(PFXA fl n pl pq BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte) : Prop :=
finv m
/\ rw_cells rsegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) (Z_to_bv 64 (Z.land fl 73728)) (Z_to_bv 64 n) (Z_to_bv 64 pl) (Z_to_bv 64 (pl + pq)) (Z_to_bv 64 0) alo ahi j128)
/\ rw_cells rsegs m (q + -392) [CB 24 digs]
/\ rw_cells rsegs m (q + -368) [CB 256 pad]
/\ SINK m st /\ rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] /\ (0 <= k)%Z
/\ args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args
/\ Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args)
/\ bytes_at rsegs m BA (zb body) /\ Forall (fun c => 0 <= c < 256)%Z body /\ body_loc BA n /\ (BA + n < 2^64)%Z /\ n = zlength body
/\ (forall m', mem_inv rsegs m' -> bytes_at rsegs m' PFXA (zb prefix)) /\ Forall (fun c => 0 <= c < 256)%Z prefix
/\ (0 <= PFXA)%Z /\ (PFXA + pl <= 401408)%Z /\ pl = zlength prefix /\ (pl <= 2)%Z
/\ (0 <= i4 <= zlength fmt)%Z /\ (0 <= fl < 131072)%Z /\ (0 <= n <= INT_MAX)%Z /\ (n <= pq)%Z /\ (pl + pq <= INT_MAX)%Z.
Lemma gw_eq_tinv : @tinv = ltac:(GwInst.gw_term (@QROt.Mq0.tinv rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@tinv)). Proof. unfold tinv, QROt.Mq0.tinv; rewrite ?gw_eq_sfx__2, ?gw_eq_lo_cells, ?gw_eq_finv, ?gw_eq_body_loc; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_tinv : gw_eqs.

Definition S_T6 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM rsegs (mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 s9 t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0x5618c) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_T6 : @S_T6 = ltac:(GwInst.gw_term (@QROt.Mq0.S_T6 rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_T6)). Proof. unfold S_T6, QROt.Mq0.S_T6; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_S_HEAD, ?gw_eq_tregs, ?gw_eq_tinv; ltac2:(GwEq.gw_rw [[@gw_eq_mpad__3; @gw_eq_mpad__2; @gw_eq_mpad]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_T6 : gw_eqs.

Definition S_T5 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM rsegs (OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 s9 t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0x56170) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_T5 : @S_T5 = ltac:(GwInst.gw_term (@QROt.Mq0.S_T5 rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_T5)). Proof. unfold S_T5, QROt.Mq0.S_T5; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_S_HEAD, ?gw_eq_tregs, ?gw_eq_tinv; ltac2:(GwEq.gw_rw [[@gw_eq_mpad__3; @gw_eq_mpad__2; @gw_eq_mpad]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_T5 : gw_eqs.

Definition S_T4 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM rsegs (mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0x560ec) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_T4 : @S_T4 = ltac:(GwInst.gw_term (@QROt.Mq0.S_T4 rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_T4)). Proof. unfold S_T4, QROt.Mq0.S_T4; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_S_HEAD, ?gw_eq_tregs, ?gw_eq_tinv; ltac2:(GwEq.gw_rw [[@gw_eq_mpad__3; @gw_eq_mpad__2; @gw_eq_mpad]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_T4 : gw_eqs.

Definition S_T3 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM rsegs (mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0x56064) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_T3 : @S_T3 = ltac:(GwInst.gw_term (@QROt.Mq0.S_T3 rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_T3)). Proof. unfold S_T3, QROt.Mq0.S_T3; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_S_HEAD, ?gw_eq_tregs, ?gw_eq_tinv; ltac2:(GwEq.gw_rw [[@gw_eq_mpad__3; @gw_eq_mpad__2; @gw_eq_mpad]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_T3 : gw_eqs.

Definition S_T2 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM rsegs (OUT prefix ;;; mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0x56048) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_T2 : @S_T2 = ltac:(GwInst.gw_term (@QROt.Mq0.S_T2 rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_T2)). Proof. unfold S_T2, QROt.Mq0.S_T2; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_S_HEAD, ?gw_eq_tregs, ?gw_eq_tinv; ltac2:(GwEq.gw_rw [[@gw_eq_mpad__3; @gw_eq_mpad__2; @gw_eq_mpad]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_T2 : gw_eqs.

Definition S_T1 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
Z.land fl 73728 = 0%Z ->
implM rsegs (mpad OUT 32 wq (pl + pq) fl ;;; OUT prefix ;;; mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 0x55fc8) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_T1 : @S_T1 = ltac:(GwInst.gw_term (@QROt.Mq0.S_T1 rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_T1)). Proof. unfold S_T1, QROt.Mq0.S_T1; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_S_HEAD, ?gw_eq_tregs, ?gw_eq_tinv; ltac2:(GwEq.gw_rw [[@gw_eq_mpad__3; @gw_eq_mpad__2; @gw_eq_mpad]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_T1 : gw_eqs.

Definition S_INTC2 : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p argi : Z) (prefix body : list Z) (BA PFXA : Z)
(s2s za plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells rsegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 argi) ahi j128) ->
rw_cells rsegs m (q + -392) [CB 24 digs] ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
bytes_at rsegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> (BA + zlength body = q + -368)%Z -> (zlength body <= 24)%Z ->
(forall m', mem_inv rsegs m' -> bytes_at rsegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(0 <= PFXA)%Z -> (PFXA + zlength prefix <= 401408)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (-1 <= p <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
(0 <= argi < 2^64)%Z ->
implM rsegs (cnt' <- (if ((argi =? 0) && (p =? 0))%Z then conv_tail OUT c fl w p prefix []
else conv_tail OUT c fl w (Z.max p (zlength body + (if (argi =? 0)%Z then 1 else 0))) prefix body) ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55f38) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_INTC2 : @S_INTC2 = ltac:(GwInst.gw_term (@QROt.Mq0.S_INTC2 rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_INTC2)). Proof. unfold S_INTC2, QROt.Mq0.S_INTC2; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_lo_cells, ?gw_eq_finv, ?gw_eq_S_HEAD; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_tail__3; @gw_eq_conv_tail__2; @gw_eq_conv_tail]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_INTC2 : gw_eqs.

Definition S_INTC : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (argi : Z) (prefix body : list Z) (BA PFXA : Z)
(s2s za plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells rsegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 argi) ahi j128) ->
rw_cells rsegs m (q + -392) [CB 24 digs] ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
bytes_at rsegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> (BA + zlength body = q + -368)%Z -> (zlength body <= 24)%Z ->
(forall m', mem_inv rsegs m' -> bytes_at rsegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(0 <= PFXA)%Z -> (PFXA + zlength prefix <= 401408)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= argi < 2^64)%Z ->
implM rsegs (cnt' <- conv_int OUT c fl w p xp argi prefix body ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55f20) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_INTC : @S_INTC = ltac:(GwInst.gw_term (@QROt.Mq0.S_INTC rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_INTC)). Proof. unfold S_INTC, QROt.Mq0.S_INTC; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_lo_cells, ?gw_eq_finv, ?gw_eq_S_HEAD; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_int__3; @gw_eq_conv_int__2; @gw_eq_conv_int]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_INTC : gw_eqs.

Definition dloop_post (x1 x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (x j : Z) (ds : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (a2 a3 : word) (xq : Z) (W : list Z) (m' : word -> option byte),
ms' = MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xq) (Z_to_bv 64 (q + -392 + (j - zlength W))) a2 a3
(Z_to_bv 64 10) (Z_to_bv 64 18446744072850558157) (Z_to_bv 64 99) x17
x18 x19 x20 x21 x22 (Z_to_bv 64 (q + -392 + (j - zlength W))) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55f08) fc None m' (seg_rom rsegs)
/\ munch [(q + -392, q + -368)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (q + -392) [CB 24 (firstn (Z.to_nat (j - zlength W)) ds ++ zb W ++ skipn (Z.to_nat j) ds)]
/\ (1 <= xq <= 9)%Z /\ dec_digits x = (48 + xq)%Z :: W /\ (zlength W + 1 <= j)%Z.
Lemma gw_eq_dloop_post : @dloop_post = ltac:(GwInst.gw_term (@QROt.Mq0.dloop_post rsegs 0x55624) (@dloop_post)). Proof. unfold dloop_post, QROt.Mq0.dloop_post; rewrite ?gw_eq_W; ltac2:(GwEq.gw_rw [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_dloop_post : gw_eqs.
Definition S_DLOOP : Prop :=
forall (x1 x5 x6 x7 x8 x9 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (x j : Z) (ds : list byte),
let _ := ctx_all in
mem_inv rsegs m -> rw_cells rsegs m (q + -392) [CB 24 ds] ->
(10 <= x < 2^64)%Z -> (zlength (dec_digits x) <= j <= 24)%Z -> x11 = Z_to_bv 64 (q + -392 + j) ->
evt rsegs (dloop_post x1 x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc x j ds m)
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 x) x11 x12 x13
(Z_to_bv 64 10) (Z_to_bv 64 18446744072850558157) (Z_to_bv 64 99) x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55ed0) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_DLOOP : @S_DLOOP = ltac:(GwInst.gw_term (@QROt.Mq0.S_DLOOP rsegs 0x55624) (@S_DLOOP)). Proof. unfold S_DLOOP, QROt.Mq0.S_DLOOP; rewrite ?gw_eq_ctx_all, ?gw_eq_dloop_post; ltac2:(GwEq.gw_rw [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_DLOOP : gw_eqs.

Definition S_FMTU2 : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x11 x12 x13 x14 x15 x16 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (x d jj : Z) (W prefix : list Z) (PFXA : Z)
(pfx s2s za plp ahi : word) (j128 pre pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells rsegs m (q + -544) (lo_cells pfx s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 x) ahi j128) ->
rw_cells rsegs m (q + -392) [CB 24 (pre ++ zb W)] -> zlength pre = jj -> (1 <= jj)%Z ->
((d = 0 /\ W = [] /\ dec_digits x = []) \/ (1 <= d <= 9 /\ dec_digits x = (48 + d) :: W))%Z ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(forall m', mem_inv rsegs m' -> bytes_at rsegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(0 <= PFXA)%Z -> (PFXA + zlength prefix <= 401408)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= x < 2^64)%Z ->
implM rsegs (cnt' <- conv_int OUT c fl w p xp x prefix (dec_digits x) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
(Z_to_bv 64 d) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 PFXA)
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 (q + -392 + jj)) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55f08) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_FMTU2 : @S_FMTU2 = ltac:(GwInst.gw_term (@QROt.Mq0.S_FMTU2 rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_FMTU2)). Proof. unfold S_FMTU2, QROt.Mq0.S_FMTU2; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_W, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_lo_cells, ?gw_eq_finv, ?gw_eq_S_HEAD; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_int__3; @gw_eq_conv_int__2; @gw_eq_conv_int]; [@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_FMTU2 : gw_eqs.

Definition S_FMTU : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x11 x12 x13 x15 x16 x23 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (x : Z) (prefix : list Z) (PFXA : Z)
(pfx s2s za plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells rsegs m (q + -544) (lo_cells pfx s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 x) ahi j128) ->
rw_cells rsegs m (q + -392) [CB 24 digs] ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(forall m', mem_inv rsegs m' -> bytes_at rsegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(0 <= PFXA)%Z -> (PFXA + zlength prefix <= 401408)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= x < 2^64)%Z ->
implM rsegs (cnt' <- conv_int OUT c fl w p xp x prefix (dec_digits x) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
(Z_to_bv 64 x) x11 x12 x13 (Z_to_bv 64 10) x15 x16 (Z_to_bv 64 PFXA)
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55ec0) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_FMTU : @S_FMTU = ltac:(GwInst.gw_term (@QROt.Mq0.S_FMTU rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_FMTU)). Proof. unfold S_FMTU, QROt.Mq0.S_FMTU; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_lo_cells, ?gw_eq_finv, ?gw_eq_S_HEAD; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_int__3; @gw_eq_conv_int__2; @gw_eq_conv_int]; [@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_FMTU : gw_eqs.

Definition S_CV_D : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (i : Z)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (i mod 2^64)) ahi j128) ->
rw_cells rsegs m (q + -392) [CB 24 digs] ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(-2^63 <= i < 2^63)%Z ->
implM rsegs (cnt' <- (let '(argi, prefix) :=
(if INTMAX_MAX <? i mod 2^64 then ((- (i mod 2^64)) mod 2^64, [45])
else if negb (Z.land fl MARK_POS =? 0) then (i mod 2^64, [43])
else if negb (Z.land fl PAD_POS =? 0) then (i mod 2^64, [32])
else (i mod 2^64, []))%Z in
conv_int OUT c fl w p xp argi prefix (dec_digits argi)) ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55bbc) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_CV_D : @S_CV_D = ltac:(GwInst.gw_term (@QROt.Mq0.S_CV_D rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@S_CV_D)). Proof. unfold S_CV_D, QROt.Mq0.S_CV_D; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_lo_cells, ?gw_eq_finv, ?gw_eq_S_HEAD; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_int__3; @gw_eq_conv_int__2; @gw_eq_conv_int]; [@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_CV_D : gw_eqs.

Definition S_CV_U : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (u : Z)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 u) ahi j128) ->
rw_cells rsegs m (q + -392) [CB 24 digs] ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= u < 2^64)%Z ->
implM rsegs (cnt' <- conv_int OUT c fl w p xp u [] (dec_digits u) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55cf4) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_CV_U : @S_CV_U = ltac:(GwInst.gw_term (@QROt.Mq0.S_CV_U rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@S_CV_U)). Proof. unfold S_CV_U, QROt.Mq0.S_CV_U; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_lo_cells, ?gw_eq_finv, ?gw_eq_S_HEAD; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_int__3; @gw_eq_conv_int__2; @gw_eq_conv_int]; [@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_CV_U : gw_eqs.

Definition S_CV_C : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl flc w p : Z) (xp : bool) (i : Z)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (i mod 2^64)) ahi j128) ->
rw_cells rsegs m (q + -392) [CB 24 digs] ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
flc = Z.land fl (Z.lnot ZERO_PAD) ->
implM rsegs (cnt' <- conv_tail OUT c (Z.land fl (Z.lnot ZERO_PAD)) w 1 [] [i mod 256] ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) (Z_to_bv 64 flc) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55d2c) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_CV_C : @S_CV_C = ltac:(GwInst.gw_term (@QROt.Mq0.S_CV_C rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@S_CV_C)). Proof. unfold S_CV_C, QROt.Mq0.S_CV_C; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_lo_cells, ?gw_eq_finv, ?gw_eq_S_HEAD; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_tail__3; @gw_eq_conv_tail__2; @gw_eq_conv_tail]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_CV_C : gw_eqs.

Definition xloop_post (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (l x j : Z) (ds : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (a2 a3 : word) (m' : word -> option byte),
let H := hex_digits l x in
ms' = MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 l) a2 a3 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 (q + -392 + (j - zlength H))) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55dac) fc None m' (seg_rom rsegs)
/\ munch [(q + -392, q + -368)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (q + -392) [CB 24 (firstn (Z.to_nat (j - zlength H)) ds ++ zb H ++ skipn (Z.to_nat j) ds)]
/\ (zlength H <= j)%Z.
Lemma gw_eq_xloop_post : @xloop_post = ltac:(GwInst.gw_term (@QROt.Mq0.xloop_post rsegs 0x55624) (@xloop_post)). Proof. unfold xloop_post, QROt.Mq0.xloop_post; ltac2:(GwEq.gw_rw [[@gw_eq_hex_digits__3; @gw_eq_hex_digits__2; @gw_eq_hex_digits]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_xloop_post : gw_eqs.
Definition S_XLOOP : Prop :=
forall (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (l x j : Z) (ds : list byte),
let _ := ctx_all in
mem_inv rsegs m -> rw_cells rsegs m (q + -392) [CB 24 ds] ->
(0 < x < 2^64)%Z -> (l = 0 \/ l = 32)%Z -> (zlength (hex_digits l x) <= j <= 24)%Z -> x23 = Z_to_bv 64 (q + -392 + j) ->
evt rsegs (xloop_post x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc l x j ds m)
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 x) (Z_to_bv 64 l) x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55d84) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_XLOOP : @S_XLOOP = ltac:(GwInst.gw_term (@QROt.Mq0.S_XLOOP rsegs 0x55624) (@S_XLOOP)). Proof. unfold S_XLOOP, QROt.Mq0.S_XLOOP; rewrite ?gw_eq_ctx_all, ?gw_eq_xloop_post; ltac2:(GwEq.gw_rw [[@gw_eq_hex_digits__3; @gw_eq_hex_digits__2; @gw_eq_hex_digits]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_XLOOP : gw_eqs.

Definition S_CV_X : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (u t : Z)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 u) ahi j128) ->
rw_cells rsegs m (q + -392) [CB 24 digs] ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= u < 2^32)%Z -> (t = 120 \/ t = 88)%Z ->
implM rsegs (cnt' <- conv_int OUT c fl w p xp u
(if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0) then (if t =? 120 then [48; 120] else [48; 88]) else [])%Z
(hex_digits (Z.land t 32) u) ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 (Z_to_bv 64 t) x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55d6c) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_CV_X : @S_CV_X = ltac:(GwInst.gw_term (@QROt.Mq0.S_CV_X rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@S_CV_X)). Proof. unfold S_CV_X, QROt.Mq0.S_CV_X; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_lo_cells, ?gw_eq_finv, ?gw_eq_S_HEAD; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_int__3; @gw_eq_conv_int__2; @gw_eq_conv_int]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_hex_digits__3; @gw_eq_hex_digits__2; @gw_eq_hex_digits]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_CV_X : gw_eqs.

Definition S_CV_S : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p fl10 : Z) (xp : bool) (P : Z) (s : list Z) (slack : list byte)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 P) ahi j128) ->
rw_cells rsegs m (q + -392) [CB 24 digs] ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
bytes_at rsegs m P (zb s ++ Z_to_bv 8 0 :: slack) -> Forall (fun c => 0 < c < 256)%Z s ->
((- (P + zlength s + 1)) mod 8 <= zlength slack)%Z -> (0 < P)%Z ->
(P + zlength s + 1 + zlength slack <= lo \/ q <= P)%Z ->
(P + zlength s + 1 + zlength slack <= Fp \/ Fp + 232 <= P)%Z ->
(P + zlength s + 1 + zlength slack <= B \/ B + BS <= P)%Z ->
(fl10 = Z.land fl (Z.lnot 65536))%Z ->
implM rsegs (cnt' <- (if (p <? 0) && (INT_MAX <=? zlength s) then munr
else conv_tail OUT c (Z.land fl (Z.lnot ZERO_PAD)) w (if p <? 0 then zlength s else Z.min (zlength s) p) []
(firstn (Z.to_nat (if p <? 0 then zlength s else Z.min (zlength s) p)) s))%Z ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) (Z_to_bv 64 fl10) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55c04) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_CV_S : @S_CV_S = ltac:(GwInst.gw_term (@QROt.Mq0.S_CV_S rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@S_CV_S)). Proof. unfold S_CV_S, QROt.Mq0.S_CV_S; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_lo_cells, ?gw_eq_finv, ?gw_eq_S_HEAD; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_tail__3; @gw_eq_conv_tail__2; @gw_eq_conv_tail]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_CV_S : gw_eqs.

Definition S_CV_FP : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (y t : Z)
(pfx s2s za pl plp : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 (hi64 y)) j128) ->
rw_cells rsegs m (q + -392) [CB 24 digs] ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
fpcall_stmt Fp B BS SINK TOPOK OUTFP (y, w, p, fl, t) ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= y < 2^128)%Z -> conv_type t = Some T_DBL ->
implM rsegs (cnt' <- (if xp && (p <? 0) then munr
else if (1 <? w) || (2^20 <=? p) then munr
else r <- OUTFP y w p fl t ;; if (r <? 0) || (INT_MAX - c <? r) then munr else mret (c + r))%Z ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 (Z_to_bv 64 t) x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
Ft (Z_to_bv 64 0x55b6c) fc None m (seg_rom rsegs)).
Lemma gw_eq_S_CV_FP : @S_CV_FP = ltac:(GwInst.gw_term (@QROt.Mq0.S_CV_FP rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@S_CV_FP)). Proof. unfold S_CV_FP, QROt.Mq0.S_CV_FP; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_POST, ?gw_eq_lo_cells, ?gw_eq_finv, ?gw_eq_S_HEAD; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_type__3; @gw_eq_conv_type__2; @gw_eq_conv_type]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_CV_FP : gw_eqs.

Definition POST1 : Z -> machine_state -> Prop :=
fun r ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F (ret_pc ra) fc0 None m' (seg_rom rsegs)
/\ munch [(lo, q)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo q
/\ ssp_cells m' canary.
Lemma gw_eq_POST1 : @POST1 = ltac:(GwInst.gw_term (@QROt.Mq0.POST1 rsegs got_ssp ssp_guard) (@POST1)). Proof. unfold POST1, QROt.Mq0.POST1; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_POST1 : gw_eqs.

Definition S_EXIT1 : Prop :=
forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(m : word -> option byte) (r : Z)
(pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m -> munch [(lo, q)] m0 m ->
rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
rw_cells rsegs m (q + -392) [CB 24 digs] ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
(0 <= r < 2^64)%Z ->
evt rsegs (POST1 r)
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x56400) fc0 None m (seg_rom rsegs)).
Lemma gw_eq_S_EXIT1 : @S_EXIT1 = ltac:(GwInst.gw_term (@QROt.Mq0.S_EXIT1 rsegs 0x55624 got_ssp ssp_guard) (@S_EXIT1)). Proof. unfold S_EXIT1, QROt.Mq0.S_EXIT1; rewrite ?gw_eq_ctx_all, ?gw_eq_lo_cells, ?gw_eq_finv, ?gw_eq_POST1; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_EXIT1 : gw_eqs.

Definition S_P1 : Prop :=
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
(m : word -> option byte) (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m -> munch [(lo, q)] m0 m ->
rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells rsegs m (q + -392) [CB 24 digs] ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
pass1_ok fmt = true ->
evt rsegs (POST1 0)
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 A) x22 x23 x24 x25 (Z_to_bv 64 0) x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x556d4) fc0 None m (seg_rom rsegs)).
Lemma gw_eq_S_P1 : @S_P1 = ltac:(GwInst.gw_term (@QROt.Mq0.S_P1 rsegs 0x55624 got_ssp ssp_guard) (@S_P1)). Proof. unfold S_P1, QROt.Mq0.S_P1; rewrite ?gw_eq_ctx_all, ?gw_eq_lo_cells, ?gw_eq_finv, ?gw_eq_POST1; ltac2:(GwEq.gw_rw [[@gw_eq_pass1_ok__3; @gw_eq_pass1_ok__2; @gw_eq_pass1_ok]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_P1 : gw_eqs.

Definition S_PRO : Prop :=
forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (f : Z) (Q : machine_state -> Prop),
let _ := ctx_all in
stk rsegs m0 lo q -> mem_inv rsegs m0 -> bytes_at rsegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
(0 <= f < 2^64)%Z ->
(forall (m : word -> option byte) (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte) (a0 a1 a2 a3 : word),
finv m -> munch [(q + -544, q)]%Z m0 m ->
rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells rsegs m (q + -392) [CB 24 digs] ->
rw_cells rsegs m (q + -368) [CB 256 pad] ->
evt rsegs Q
(MS (mkR ra SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 a1 a2 a3 nlt x15 x16 x17
s2e (Z_to_bv 64 0) (Z_to_bv 64 f) (Z_to_bv 64 A) s6e s7e s8e s9e (Z_to_bv 64 0) s11e x28 x29 x30 x31)
F (Z_to_bv 64 0x556d4) fc0 None m (seg_rom rsegs))) ->
evt rsegs Q
(MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 f) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
F (Z_to_bv 64 0x55624) fc0 None m0 (seg_rom rsegs)).
Lemma gw_eq_S_PRO : @S_PRO = ltac:(GwInst.gw_term (@QROt.Mq0.S_PRO rsegs 0x55624 got_ssp ssp_guard) (@S_PRO)). Proof. unfold S_PRO, QROt.Mq0.S_PRO; rewrite ?gw_eq_ctx_all, ?gw_eq_lo_cells, ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_va_area__3; @gw_eq_va_area__2; @gw_eq_va_area]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_PRO : gw_eqs.

End PrintfCore.
Lemma gw_eq_ctx_all__2 : @ctx_all = ltac:(GwInst.gw_term (@QROt.Mq0.ctx_all) (@ctx_all)). Proof. unfold ctx_all, QROt.Mq0.ctx_all; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ctx_all__2 : gw_eqs.
Lemma gw_eq_W__2 : @W = ltac:(GwInst.gw_term (@QROt.Mq0.W) (@W)). Proof. unfold W, QROt.Mq0.W; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_W__2 : gw_eqs.
Lemma gw_eq_Fokd__2 : @Fokd = ltac:(GwInst.gw_term (@QROt.Mq0.Fokd) (@Fokd)). Proof. unfold Fokd, QROt.Mq0.Fokd; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_Fokd__2 : gw_eqs.
Lemma gw_eq_Fok__2 : @Fok = ltac:(GwInst.gw_term (@QROt.Mq0.Fok) (@Fok)). Proof. unfold Fok, QROt.Mq0.Fok; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_Fok__2 : gw_eqs.
Lemma gw_eq_POST__2 : @POST = ltac:(GwInst.gw_term (@QROt.Mq0.POST rsegs got_ssp ssp_guard) (@POST)). Proof. unfold POST, QROt.Mq0.POST; rewrite ?gw_eq_W__2, ?gw_eq_Fok__2; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_POST__2 : gw_eqs.
Lemma gw_eq_hi_cells__2 : @hi_cells = ltac:(GwInst.gw_term (@QROt.Mq0.hi_cells) (@hi_cells)). Proof. unfold hi_cells, QROt.Mq0.hi_cells; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_hi_cells__2 : gw_eqs.
Lemma gw_eq_lo_cells__2 : @lo_cells = ltac:(GwInst.gw_term (@QROt.Mq0.lo_cells ssp_guard) (@lo_cells)). Proof. unfold lo_cells, QROt.Mq0.lo_cells; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_lo_cells__2 : gw_eqs.
Lemma gw_eq_finv__2 : @finv = ltac:(GwInst.gw_term (@QROt.Mq0.finv rsegs got_ssp ssp_guard) (@finv)). Proof. unfold finv, QROt.Mq0.finv; rewrite ?gw_eq_W__2, ?gw_eq_hi_cells__2; ltac2:(GwEq.gw_rw [[@gw_eq_va_area__3; @gw_eq_va_area__2; @gw_eq_va_area]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_finv__2 : gw_eqs.
Lemma gw_eq_PFXSTR__2 : @PFXSTR = ltac:(GwInst.gw_term (@QROt.Mq0.PFXSTR) (@PFXSTR)). Proof. unfold PFXSTR, QROt.Mq0.PFXSTR; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_PFXSTR__2 : gw_eqs.
Lemma gw_eq_lo_cells14__2 : @lo_cells14 = ltac:(GwInst.gw_term (@QROt.Mq0.lo_cells14 ssp_guard) (@lo_cells14)). Proof. unfold lo_cells14, QROt.Mq0.lo_cells14; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_lo_cells14__2 : gw_eqs.
Lemma gw_eq_out_postq__2 : @out_postq = ltac:(GwInst.gw_term (@QROt.Mq0.out_postq rsegs got_ssp ssp_guard) (@out_postq)). Proof. unfold out_postq, QROt.Mq0.out_postq; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_out_postq__2 : gw_eqs.
Lemma gw_eq_fp_postq__2 : @fp_postq = ltac:(GwInst.gw_term (@QROt.Mq0.fp_postq rsegs got_ssp ssp_guard) (@fp_postq)). Proof. unfold fp_postq, QROt.Mq0.fp_postq; rewrite ?gw_eq_Fokd__2; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_fp_postq__2 : gw_eqs.
Lemma gw_eq_S_EXIT__2 : @S_EXIT = ltac:(GwInst.gw_term (@QROt.Mq0.S_EXIT rsegs 0x55624 got_ssp ssp_guard) (@S_EXIT)). Proof. unfold S_EXIT, QROt.Mq0.S_EXIT; rewrite ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_EXIT__2 : gw_eqs.
Lemma gw_eq_S_SCAN__2 : @S_SCAN = ltac:(GwInst.gw_term (@QROt.Mq0.S_SCAN rsegs 0x55624 got_ssp ssp_guard) (@S_SCAN)). Proof. unfold S_SCAN, QROt.Mq0.S_SCAN; rewrite ?gw_eq_ctx_all__2, ?gw_eq_finv__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_SCAN__2 : gw_eqs.
Lemma gw_eq_S_FLAGS__2 : @S_FLAGS = ltac:(GwInst.gw_term (@QROt.Mq0.S_FLAGS rsegs 0x55624 got_ssp ssp_guard) (@S_FLAGS)). Proof. unfold S_FLAGS, QROt.Mq0.S_FLAGS; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_finv__2; ltac2:(GwEq.gw_rw [[@gw_eq_flag_bit__3; @gw_eq_flag_bit__2; @gw_eq_flag_bit]; [@gw_eq_parse_flags__3; @gw_eq_parse_flags__2; @gw_eq_parse_flags]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_FLAGS__2 : gw_eqs.
Lemma gw_eq_S_WLOOP__2 : @S_WLOOP = ltac:(GwInst.gw_term (@QROt.Mq0.S_WLOOP rsegs 0x55624 got_ssp ssp_guard) (@S_WLOOP)). Proof. unfold S_WLOOP, QROt.Mq0.S_WLOOP; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2; ltac2:(GwEq.gw_rw [[@gw_eq_getint__3; @gw_eq_getint__2; @gw_eq_getint]; [@gw_eq_is_digit__3; @gw_eq_is_digit__2; @gw_eq_is_digit]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_WLOOP__2 : gw_eqs.
Lemma gw_eq_S_WIDTH__2 : @S_WIDTH = ltac:(GwInst.gw_term (@QROt.Mq0.S_WIDTH rsegs 0x55624 got_ssp ssp_guard) (@S_WIDTH)). Proof. unfold S_WIDTH, QROt.Mq0.S_WIDTH; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2; ltac2:(GwEq.gw_rw [[@gw_eq_getint__3; @gw_eq_getint__2; @gw_eq_getint]; [@gw_eq_is_digit__3; @gw_eq_is_digit__2; @gw_eq_is_digit]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_WIDTH__2 : gw_eqs.
Lemma gw_eq_S_PLOOP__2 : @S_PLOOP = ltac:(GwInst.gw_term (@QROt.Mq0.S_PLOOP rsegs 0x55624 got_ssp ssp_guard) (@S_PLOOP)). Proof. unfold S_PLOOP, QROt.Mq0.S_PLOOP; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2; ltac2:(GwEq.gw_rw [[@gw_eq_getint__3; @gw_eq_getint__2; @gw_eq_getint]; [@gw_eq_is_digit__3; @gw_eq_is_digit__2; @gw_eq_is_digit]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_PLOOP__2 : gw_eqs.
Lemma gw_eq_S_PREC__2 : @S_PREC = ltac:(GwInst.gw_term (@QROt.Mq0.S_PREC rsegs 0x55624 got_ssp ssp_guard) (@S_PREC)). Proof. unfold S_PREC, QROt.Mq0.S_PREC; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2; ltac2:(GwEq.gw_rw [[@gw_eq_getint__3; @gw_eq_getint__2; @gw_eq_getint]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_PREC__2 : gw_eqs.
Lemma gw_eq_S_STATE__2 : @S_STATE = ltac:(GwInst.gw_term (@QROt.Mq0.S_STATE rsegs 0x55624 got_ssp ssp_guard) (@S_STATE)). Proof. unfold S_STATE, QROt.Mq0.S_STATE; rewrite ?gw_eq_ctx_all__2, ?gw_eq_finv__2; ltac2:(GwEq.gw_rw [[@gw_eq_conv_type__3; @gw_eq_conv_type__2; @gw_eq_conv_type]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_STATE__2 : gw_eqs.
Lemma gw_eq_S_STATEL__2 : @S_STATEL = ltac:(GwInst.gw_term (@QROt.Mq0.S_STATEL rsegs 0x55624 got_ssp ssp_guard) (@S_STATEL)). Proof. unfold S_STATEL, QROt.Mq0.S_STATEL; rewrite ?gw_eq_ctx_all__2, ?gw_eq_finv__2; ltac2:(GwEq.gw_rw [[@gw_eq_conv_type_l__3; @gw_eq_conv_type_l__2; @gw_eq_conv_type_l]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_STATEL__2 : gw_eqs.
Lemma gw_eq_S_DIR__2 : @S_DIR = ltac:(GwInst.gw_term (@QROt.Mq0.S_DIR rsegs 0x55624 got_ssp ssp_guard) (@S_DIR)). Proof. unfold S_DIR, QROt.Mq0.S_DIR; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2; ltac2:(GwEq.gw_rw [[@gw_eq_d_ps__3; @gw_eq_d_ps__2; @gw_eq_d_ps]; [@gw_eq_parse_dir__3; @gw_eq_parse_dir__2; @gw_eq_parse_dir]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_DIR__2 : gw_eqs.
Lemma gw_eq_S_END__2 : @S_END = ltac:(GwInst.gw_term (@QROt.Mq0.S_END rsegs 0x55624 got_ssp ssp_guard) (@S_END)). Proof. unfold S_END, QROt.Mq0.S_END; rewrite ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_END__2 : gw_eqs.
Lemma gw_eq_S_HEAD__2 : @S_HEAD = ltac:(GwInst.gw_term (@QROt.Mq0.S_HEAD rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@S_HEAD)). Proof. unfold S_HEAD, QROt.Mq0.S_HEAD; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_HEAD__2 : gw_eqs.
Lemma gw_eq_S_CONV__2 : @S_CONV = ltac:(GwInst.gw_term (@QROt.Mq0.S_CONV rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@S_CONV)). Proof. unfold S_CONV, QROt.Mq0.S_CONV; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2, ?gw_eq_S_HEAD__2; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv__3; @gw_eq_conv__2; @gw_eq_conv]; [@gw_eq_d_ps__3; @gw_eq_d_ps__2; @gw_eq_d_ps]; [@gw_eq_dir_ty_ok__3; @gw_eq_dir_ty_ok__2; @gw_eq_dir_ty_ok]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_CONV__2 : gw_eqs.
Lemma gw_eq_body_loc__2 : @body_loc = ltac:(GwInst.gw_term (@QROt.Mq0.body_loc) (@body_loc)). Proof. unfold body_loc, QROt.Mq0.body_loc; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_body_loc__2 : gw_eqs.
Lemma gw_eq_S_TAIL__2 : @S_TAIL = ltac:(GwInst.gw_term (@QROt.Mq0.S_TAIL rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_TAIL)). Proof. unfold S_TAIL, QROt.Mq0.S_TAIL; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2, ?gw_eq_S_HEAD__2, ?gw_eq_body_loc__2; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_tail__3; @gw_eq_conv_tail__2; @gw_eq_conv_tail]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_TAIL__2 : gw_eqs.
Lemma gw_eq_tregs__2 : @tregs = ltac:(GwInst.gw_term (@QROt.Mq0.tregs) (@tregs)). Proof. unfold tregs, QROt.Mq0.tregs; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_tregs__2 : gw_eqs.
Lemma gw_eq_tinv__2 : @tinv = ltac:(GwInst.gw_term (@QROt.Mq0.tinv rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@tinv)). Proof. unfold tinv, QROt.Mq0.tinv; rewrite ?gw_eq_sfx__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2, ?gw_eq_body_loc__2; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_tinv__2 : gw_eqs.
Lemma gw_eq_S_T6__2 : @S_T6 = ltac:(GwInst.gw_term (@QROt.Mq0.S_T6 rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_T6)). Proof. unfold S_T6, QROt.Mq0.S_T6; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_S_HEAD__2, ?gw_eq_tregs__2, ?gw_eq_tinv__2; ltac2:(GwEq.gw_rw [[@gw_eq_mpad__3; @gw_eq_mpad__2; @gw_eq_mpad]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_T6__2 : gw_eqs.
Lemma gw_eq_S_T5__2 : @S_T5 = ltac:(GwInst.gw_term (@QROt.Mq0.S_T5 rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_T5)). Proof. unfold S_T5, QROt.Mq0.S_T5; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_S_HEAD__2, ?gw_eq_tregs__2, ?gw_eq_tinv__2; ltac2:(GwEq.gw_rw [[@gw_eq_mpad__3; @gw_eq_mpad__2; @gw_eq_mpad]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_T5__2 : gw_eqs.
Lemma gw_eq_S_T4__2 : @S_T4 = ltac:(GwInst.gw_term (@QROt.Mq0.S_T4 rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_T4)). Proof. unfold S_T4, QROt.Mq0.S_T4; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_S_HEAD__2, ?gw_eq_tregs__2, ?gw_eq_tinv__2; ltac2:(GwEq.gw_rw [[@gw_eq_mpad__3; @gw_eq_mpad__2; @gw_eq_mpad]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_T4__2 : gw_eqs.
Lemma gw_eq_S_T3__2 : @S_T3 = ltac:(GwInst.gw_term (@QROt.Mq0.S_T3 rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_T3)). Proof. unfold S_T3, QROt.Mq0.S_T3; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_S_HEAD__2, ?gw_eq_tregs__2, ?gw_eq_tinv__2; ltac2:(GwEq.gw_rw [[@gw_eq_mpad__3; @gw_eq_mpad__2; @gw_eq_mpad]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_T3__2 : gw_eqs.
Lemma gw_eq_S_T2__2 : @S_T2 = ltac:(GwInst.gw_term (@QROt.Mq0.S_T2 rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_T2)). Proof. unfold S_T2, QROt.Mq0.S_T2; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_S_HEAD__2, ?gw_eq_tregs__2, ?gw_eq_tinv__2; ltac2:(GwEq.gw_rw [[@gw_eq_mpad__3; @gw_eq_mpad__2; @gw_eq_mpad]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_T2__2 : gw_eqs.
Lemma gw_eq_S_T1__2 : @S_T1 = ltac:(GwInst.gw_term (@QROt.Mq0.S_T1 rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_T1)). Proof. unfold S_T1, QROt.Mq0.S_T1; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_S_HEAD__2, ?gw_eq_tregs__2, ?gw_eq_tinv__2; ltac2:(GwEq.gw_rw [[@gw_eq_mpad__3; @gw_eq_mpad__2; @gw_eq_mpad]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_T1__2 : gw_eqs.
Lemma gw_eq_S_INTC2__2 : @S_INTC2 = ltac:(GwInst.gw_term (@QROt.Mq0.S_INTC2 rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_INTC2)). Proof. unfold S_INTC2, QROt.Mq0.S_INTC2; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2, ?gw_eq_S_HEAD__2; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_tail__3; @gw_eq_conv_tail__2; @gw_eq_conv_tail]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_INTC2__2 : gw_eqs.
Lemma gw_eq_S_INTC__2 : @S_INTC = ltac:(GwInst.gw_term (@QROt.Mq0.S_INTC rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_INTC)). Proof. unfold S_INTC, QROt.Mq0.S_INTC; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2, ?gw_eq_S_HEAD__2; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_int__3; @gw_eq_conv_int__2; @gw_eq_conv_int]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_INTC__2 : gw_eqs.
Lemma gw_eq_dloop_post__2 : @dloop_post = ltac:(GwInst.gw_term (@QROt.Mq0.dloop_post rsegs 0x55624) (@dloop_post)). Proof. unfold dloop_post, QROt.Mq0.dloop_post; rewrite ?gw_eq_W__2; ltac2:(GwEq.gw_rw [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_dloop_post__2 : gw_eqs.
Lemma gw_eq_S_DLOOP__2 : @S_DLOOP = ltac:(GwInst.gw_term (@QROt.Mq0.S_DLOOP rsegs 0x55624) (@S_DLOOP)). Proof. unfold S_DLOOP, QROt.Mq0.S_DLOOP; rewrite ?gw_eq_ctx_all__2, ?gw_eq_dloop_post__2; ltac2:(GwEq.gw_rw [[@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_DLOOP__2 : gw_eqs.
Lemma gw_eq_S_FMTU2__2 : @S_FMTU2 = ltac:(GwInst.gw_term (@QROt.Mq0.S_FMTU2 rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_FMTU2)). Proof. unfold S_FMTU2, QROt.Mq0.S_FMTU2; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_W__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2, ?gw_eq_S_HEAD__2; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_int__3; @gw_eq_conv_int__2; @gw_eq_conv_int]; [@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_FMTU2__2 : gw_eqs.
Lemma gw_eq_S_FMTU__2 : @S_FMTU = ltac:(GwInst.gw_term (@QROt.Mq0.S_FMTU rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@S_FMTU)). Proof. unfold S_FMTU, QROt.Mq0.S_FMTU; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2, ?gw_eq_S_HEAD__2; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_int__3; @gw_eq_conv_int__2; @gw_eq_conv_int]; [@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_FMTU__2 : gw_eqs.
Lemma gw_eq_S_CV_D__2 : @S_CV_D = ltac:(GwInst.gw_term (@QROt.Mq0.S_CV_D rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@S_CV_D)). Proof. unfold S_CV_D, QROt.Mq0.S_CV_D; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2, ?gw_eq_S_HEAD__2; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_int__3; @gw_eq_conv_int__2; @gw_eq_conv_int]; [@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_CV_D__2 : gw_eqs.
Lemma gw_eq_S_CV_U__2 : @S_CV_U = ltac:(GwInst.gw_term (@QROt.Mq0.S_CV_U rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@S_CV_U)). Proof. unfold S_CV_U, QROt.Mq0.S_CV_U; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2, ?gw_eq_S_HEAD__2; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_int__3; @gw_eq_conv_int__2; @gw_eq_conv_int]; [@gw_eq_dec_digits__3; @gw_eq_dec_digits__2; @gw_eq_dec_digits]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_CV_U__2 : gw_eqs.
Lemma gw_eq_S_CV_C__2 : @S_CV_C = ltac:(GwInst.gw_term (@QROt.Mq0.S_CV_C rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@S_CV_C)). Proof. unfold S_CV_C, QROt.Mq0.S_CV_C; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2, ?gw_eq_S_HEAD__2; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_tail__3; @gw_eq_conv_tail__2; @gw_eq_conv_tail]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_CV_C__2 : gw_eqs.
Lemma gw_eq_xloop_post__2 : @xloop_post = ltac:(GwInst.gw_term (@QROt.Mq0.xloop_post rsegs 0x55624) (@xloop_post)). Proof. unfold xloop_post, QROt.Mq0.xloop_post; ltac2:(GwEq.gw_rw [[@gw_eq_hex_digits__3; @gw_eq_hex_digits__2; @gw_eq_hex_digits]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_xloop_post__2 : gw_eqs.
Lemma gw_eq_S_XLOOP__2 : @S_XLOOP = ltac:(GwInst.gw_term (@QROt.Mq0.S_XLOOP rsegs 0x55624) (@S_XLOOP)). Proof. unfold S_XLOOP, QROt.Mq0.S_XLOOP; rewrite ?gw_eq_ctx_all__2, ?gw_eq_xloop_post__2; ltac2:(GwEq.gw_rw [[@gw_eq_hex_digits__3; @gw_eq_hex_digits__2; @gw_eq_hex_digits]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_XLOOP__2 : gw_eqs.
Lemma gw_eq_S_CV_X__2 : @S_CV_X = ltac:(GwInst.gw_term (@QROt.Mq0.S_CV_X rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@S_CV_X)). Proof. unfold S_CV_X, QROt.Mq0.S_CV_X; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2, ?gw_eq_S_HEAD__2; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_int__3; @gw_eq_conv_int__2; @gw_eq_conv_int]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_hex_digits__3; @gw_eq_hex_digits__2; @gw_eq_hex_digits]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_CV_X__2 : gw_eqs.
Lemma gw_eq_S_CV_S__2 : @S_CV_S = ltac:(GwInst.gw_term (@QROt.Mq0.S_CV_S rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@S_CV_S)). Proof. unfold S_CV_S, QROt.Mq0.S_CV_S; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2, ?gw_eq_S_HEAD__2; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_tail__3; @gw_eq_conv_tail__2; @gw_eq_conv_tail]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_CV_S__2 : gw_eqs.
Lemma gw_eq_S_CV_FP__2 : @S_CV_FP = ltac:(GwInst.gw_term (@QROt.Mq0.S_CV_FP rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@S_CV_FP)). Proof. unfold S_CV_FP, QROt.Mq0.S_CV_FP; rewrite ?gw_eq_sfx__2, ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_POST__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2, ?gw_eq_S_HEAD__2; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_conv_type__3; @gw_eq_conv_type__2; @gw_eq_conv_type]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]; [@gw_eq_printf_loop__3; @gw_eq_printf_loop__2; @gw_eq_printf_loop]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_CV_FP__2 : gw_eqs.
Lemma gw_eq_POST1__2 : @POST1 = ltac:(GwInst.gw_term (@QROt.Mq0.POST1 rsegs got_ssp ssp_guard) (@POST1)). Proof. unfold POST1, QROt.Mq0.POST1; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_POST1__2 : gw_eqs.
Lemma gw_eq_S_EXIT1__2 : @S_EXIT1 = ltac:(GwInst.gw_term (@QROt.Mq0.S_EXIT1 rsegs 0x55624 got_ssp ssp_guard) (@S_EXIT1)). Proof. unfold S_EXIT1, QROt.Mq0.S_EXIT1; rewrite ?gw_eq_ctx_all__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2, ?gw_eq_POST1__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_EXIT1__2 : gw_eqs.
Lemma gw_eq_S_P1__2 : @S_P1 = ltac:(GwInst.gw_term (@QROt.Mq0.S_P1 rsegs 0x55624 got_ssp ssp_guard) (@S_P1)). Proof. unfold S_P1, QROt.Mq0.S_P1; rewrite ?gw_eq_ctx_all__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2, ?gw_eq_POST1__2; ltac2:(GwEq.gw_rw [[@gw_eq_pass1_ok__3; @gw_eq_pass1_ok__2; @gw_eq_pass1_ok]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_P1__2 : gw_eqs.
Lemma gw_eq_S_PRO__2 : @S_PRO = ltac:(GwInst.gw_term (@QROt.Mq0.S_PRO rsegs 0x55624 got_ssp ssp_guard) (@S_PRO)). Proof. unfold S_PRO, QROt.Mq0.S_PRO; rewrite ?gw_eq_ctx_all__2, ?gw_eq_lo_cells__2, ?gw_eq_finv__2; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_va_area__3; @gw_eq_va_area__2; @gw_eq_va_area]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_PRO__2 : gw_eqs.
