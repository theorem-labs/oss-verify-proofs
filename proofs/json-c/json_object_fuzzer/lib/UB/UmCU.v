(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QzQg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfcC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPUx.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7wb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7wb.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzHs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzHs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDgQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDgQ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uwbh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uwbh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UGbx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UGbx. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UB5o.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UB5o. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4WT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4WT. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ujqb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ujqb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UGEX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UGEX. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFHW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFHW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UfbZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UfbZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJ2O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJ2O. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UHhK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UHhK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UL4p.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UL4p. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UP89.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UP89. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UuJ9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UuJ9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxDK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxDK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uoo0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uoo0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UnKY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UnKY. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UqYW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UqYW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U3qs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U3qs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTgq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTgq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UNt7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UNt7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UUNy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UUNy.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCqH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCqH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

From Ltac2 Require Import Ltac2 Constr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac2 rec zt_plain_arith' (t : constr) : bool :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App h args =>
match Constr.Unsafe.kind h with
| Constr.Unsafe.Constant _ _ =>
if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true
else if Constr.equal h '@Z.ge then true else if Constr.equal h '@Z.gt then true
else if Constr.equal h '@lt then true else if Constr.equal h '@ge then true
else if Constr.equal h '@gt then true else if Constr.equal h '@N.le then true
else if Constr.equal h '@N.lt then true else if Constr.equal h '@Z.divide then true
else false
| Constr.Unsafe.Ind _ _ =>
if Constr.equal h '@and then (if zt_plain_arith' (Array.get args 0) then zt_plain_arith' (Array.get args 1) else false)
else if Constr.equal h '@eq then true else if Constr.equal h '@le then true
else false
| _ => false
end
| Constr.Unsafe.Ind _ _ => if Constr.equal t 'True then true else Constr.equal t 'False
| _ => false
end.
Ltac2 rec zt_codomain (t : constr) : constr :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.Prod _ b => zt_codomain b
| Constr.Unsafe.LetIn _ _ b => zt_codomain b
| Constr.Unsafe.Cast c _ _ => zt_codomain c
| _ => t
end.
Ltac2 rec zt_head (t : constr) : constr :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f _ => zt_head f
| Constr.Unsafe.Cast c _ _ => zt_head c
| _ => t
end.
Ltac2 zt_sort_is_prop (ty : constr) : bool :=
lazy_match! zt_codomain ty with Prop => true | _ => false end.
Ltac2 zt_is_prop_fast (ty : constr) : bool :=
let h := zt_head (zt_codomain ty) in
match Constr.Unsafe.kind h with
| Constr.Unsafe.Constant _ _ => zt_sort_is_prop (Constr.type h)
| Constr.Unsafe.Ind _ _ => zt_sort_is_prop (Constr.type h)
| Constr.Unsafe.Var _ => zt_sort_is_prop (Constr.type h)
| _ => false
end.
Ltac2 zt_is_local' (id : ident) : bool :=
match Env.get [id] with None => true | Some _ => false end.
Ltac2 zt_prune_fast () : unit :=
let hs := Control.hyps () in
let ids := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None => if zt_plain_arith' ty then None
else if Bool.and (zt_is_local' id) (zt_is_prop_fast ty) then Some id else None
end) hs in
match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Ltac showt := let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in
idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31.
Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac plia := unfold zlength, got_ssp, ssp_guard in *; lia.

Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.

Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Lemma land_mask_range : forall a m, (0 <= m)%Z -> (0 <= Z.land a m <= m)%Z.
Proof. first [GwInst.gw_exact (@QzQg.Mq0.land_mask_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq0.land_mask_range)]. Qed.

Ltac fix_idx := repeat match goal with
| |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
| |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

Lemma sx32_wval : forall ws i t, wval ws i = t -> (0 <= t < 2^31)%Z -> sx32 (wnth ws i) = Z_to_bv 64 t.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_wnth__3; @gw_eq_wnth__2; @gw_eq_wnth]; [@gw_eq_wval__3; @gw_eq_wval__2; @gw_eq_wval]]); first [GwInst.gw_exact (@QzQg.Mq0.sx32_wval) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq0.sx32_wval)]. Qed.

Lemma zx32_wval : forall ws i, zx32 (wnth ws i) = Z_to_bv 64 (wval ws i).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_wnth__3; @gw_eq_wnth__2; @gw_eq_wnth]; [@gw_eq_wval__3; @gw_eq_wval__2; @gw_eq_wval]]); first [GwInst.gw_exact (@QzQg.Mq0.zx32_wval) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq0.zx32_wval)]. Qed.

Lemma srlw_small : forall t sh, (0 <= t < 2^31)%Z -> (0 <= sh < 32)%Z ->
bv_swrap 32 (Z.shiftr (bv_wrap 32 t) (sh mod 32)) = Z.shiftr t sh.
Proof. first [GwInst.gw_exact (@QzQg.Mq0.srlw_small) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq0.srlw_small)]. Qed.

Ltac eval_swraps := repeat match goal with |- context [bv_swrap 32 ?e] =>
let v := eval vm_compute in (bv_swrap 32 e) in lazymatch isZcst v with true => change (bv_swrap 32 e) with v end end.

Lemma divu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z ->
mul_div M_DIVU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a / b).
Proof. first [GwInst.gw_exact (@QzQg.Mq0.divu_lit) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq0.divu_lit)]. Qed.
Lemma remu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z ->
mul_div M_REMU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a mod b).
Proof. first [GwInst.gw_exact (@QzQg.Mq0.remu_lit) | autorewrite with gw_eqs; GwInst.gw_exact (@QzQg.Mq0.remu_lit)]. Qed.

Section DivW.
Local Open Scope Z_scope.
#[using="Type"] Lemma divw_small : forall v i, (0 <= v < 2^31)%Z -> (0 < i < 2^31)%Z -> v_divw (Z_to_bv 64 v) (Z_to_bv 64 i) = Z_to_bv 64 (v / i)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.divw_small) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.divw_small)]. Qed.
#[using="Type"] Lemma p10s_range : forall j, 0 <= j <= 7 -> 10 <= znth p10s j <= 100000000 /\ (znth p10s j * (1000000000 / znth p10s j) = 1000000000)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.p10s_range) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.p10s_range)]. Qed.
End DivW.

Definition RATP : Z := 0x77c00.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5b860%Z.
Definition w_22 := 0x0000a517%Z.
Definition w_23 := 0x11853a03%Z.
Definition w_170 := 0xea5fc0ef%Z.
Definition w_256 := 0xd4dfc0ef%Z.
Definition w_502 := 0xb29f40ef%Z.
Definition w_509 := 0x959fc0ef%Z.
Definition w_556 := 0x89dfc0ef%Z.
Definition w_560 := 0xad8fd0ef%Z.
Definition w_569 := 0xa1df40ef%Z.
Definition w_573 := 0x859fc0ef%Z.
Definition w_579 := 0x940fc0ef%Z.
Definition w_586 := 0xcedfb0ef%Z.
Definition w_591 := 0x9c5f40ef%Z.
Definition w_595 := 0x801fc0ef%Z.
Definition w_600 := 0x8ecfc0ef%Z.
Definition w_603 := 0x8e0fc0ef%Z.
Definition w_648 := 0xf2cfc0ef%Z.
Definition w_676 := 0x580010ef%Z.
Definition w_683 := 0x855f40ef%Z.
Definition w_690 := 0xe84fc0ef%Z.
Definition w_718 := 0xe14fc0ef%Z.
Definition w_722 := 0x850fd0ef%Z.
Definition w_727 := 0xef1fb0ef%Z.
Definition w_730 := 0xfffba617%Z.
Definition w_733 := 0x13860613%Z.
Definition w_737 := 0xdc8fc0ef%Z.
Definition w_742 := 0x994fd0ef%Z.
Definition w_792 := 0xfffba817%Z.
Definition w_796 := 0x04080813%Z.
Definition w_843 := 0xfffb7697%Z.
Definition w_845 := 0xedc6b683%Z.
Definition w_1077 := 0x878fc0ef%Z.
Definition w_1090 := 0x844fc0ef%Z.
Definition w_1094 := 0xa81fc0ef%Z.
Definition w_1106 := 0x905fb0ef%Z.
Definition w_1109 := 0x9a8fc0ef%Z.
Definition w_1125 := 0xa05fc0ef%Z.
Definition w_1132 := 0x89dfb0ef%Z.
Definition w_1135 := 0x940fc0ef%Z.
Definition w_1148 := 0x9a9fc0ef%Z.
Definition w_1160 := 0x82dfb0ef%Z.
Definition w_1163 := 0x8d0fc0ef%Z.
Definition w_1178 := 0x931fc0ef%Z.
Definition w_1185 := 0xfc8fb0ef%Z.
Definition w_1188 := 0x86cfc0ef%Z.
Definition w_1192 := 0xeadfb0ef%Z.
Definition w_1197 := 0xf98fb0ef%Z.
Definition w_1218 := 0xf4dfb0ef%Z.
Definition w_1219 := 0xb08fb0ef%Z.
Definition w_1222 := 0x655000ef%Z.
Definition w_1228 := 0xf25fb0ef%Z.
Definition w_1229 := 0xae0fb0ef%Z.
Definition w_1234 := 0x64d000ef%Z.
Definition w_1241 := 0xf89fb0ef%Z.
Definition w_1244 := 0xf8dfb0ef%Z.
Definition w_1278 := 0xfffb6517%Z.
Definition w_1279 := 0x7c053707%Z.
Definition w_1281 := 0xfffb6517%Z.
Definition w_1282 := 0x7c453787%Z.
Definition w_1284 := 0xfffb6517%Z.
Definition w_1285 := 0x79853787%Z.
Definition w_1290 := 0xfffb6517%Z.
Definition w_1291 := 0x78053707%Z.
Definition w_1294 := 0x9dcfb0ef%Z.
Definition w_1299 := 0xeb1fb0ef%Z.
Definition w_1306 := 0xce5fb0ef%Z.
Definition w_1311 := 0x519000ef%Z.
Definition w_1314 := 0xc40fb0ef%Z.
Definition w_1321 := 0xe59fb0ef%Z.
Definition w_1329 := 0xe39fb0ef%Z.
Definition w_1332 := 0xe1dfb0ef%Z.
Definition w_1341 := 0x77d000ef%Z.
Definition w_1345 := 0xc49fb0ef%Z.
Definition w_1349 := 0x819fc0ef%Z.
Definition w_1354 := 0xc68fb0ef%Z.
Definition w_1363 := 0xfffb6517%Z.
Definition w_1364 := 0x66c53507%Z.
Definition w_1365 := 0x8c0fb0ef%Z.
Definition w_1370 := 0xce4fb0ef%Z.
Definition w_1382 := 0xd69f30ef%Z.
Definition w_1391 := 0xb0cfb0ef%Z.
Definition w_1419 := 0x6510006f%Z.
Definition w_1421 := 0xb19fb0ef%Z.
Definition w_1425 := 0xd54fc0ef%Z.
Definition w_1430 := 0xbf4fb0ef%Z.
Definition w_1433 := 0xfffb9517%Z.
Definition w_1435 := 0x63c50513%Z.
Definition w_1439 := 0xad1fb0ef%Z.
Definition w_1441 := 0x940f40ef%Z.
Definition w_1463 := 0xa71fb0ef%Z.
Definition w_1467 := 0xa61fb0ef%Z.
Definition w_1589 := 0x879fb0ef%Z.
Definition w_1595 := 0x861fb0ef%Z.
Definition w_1600 := 0xc2cfc0ef%Z.
Definition w_1607 := 0x930fb0ef%Z.
Definition w_1611 := 0x9d1fb0ef%Z.
Definition w_1618 := 0xfffb6517%Z.
Definition w_1619 := 0x27053507%Z.
Definition w_1620 := 0xcc5fa0ef%Z.
Definition w_1623 := 0x8f0fb0ef%Z.
Definition w_1626 := 0x995fb0ef%Z.
Definition w_1697 := 0x87df30ef%Z.
Definition w_1701 := 0xeb8fb0ef%Z.
Definition w_1707 := 0xfa1fa0ef%Z.
Definition w_1712 := 0x841f30ef%Z.
Definition w_1716 := 0xe7cfb0ef%Z.
Definition w_1721 := 0xf69fa0ef%Z.
Definition w_1724 := 0xf5dfa0ef%Z.
Definition w_1735 := 0xaf9fa0ef%Z.
Definition w_1753 := 0xfffb6517%Z.
Definition w_1754 := 0x05453407%Z.
Definition w_1759 := 0xdd0fb0ef%Z.
Definition w_1764 := 0xf5cfb0ef%Z.
Definition w_1769 := 0xf58fb0ef%Z.
Definition w_1775 := 0xa59fa0ef%Z.
Definition w_1780 := 0xdc1fa0ef%Z.
Definition w_1790 := 0xd54fb0ef%Z.
Definition w_1808 := 0xe14fb0ef%Z.
Definition w_1809 := 0x9d1fa0ef%Z.
Definition w_1813 := 0xcf8fb0ef%Z.
Definition w_1818 := 0x504000ef%Z.
Definition w_1827 := 0xc3dfa0ef%Z.
Definition w_1834 := 0xca4fb0ef%Z.
Definition w_1840 := 0xc8cfb0ef%Z.
Definition w_1844 := 0xec9fb0ef%Z.
Definition w_1849 := 0xd69fa0ef%Z.
Definition w_1854 := 0xe04fb0ef%Z.
Definition w_1861 := 0xd39fa0ef%Z.
Definition w_1864 := 0xddcfb0ef%Z.
Definition w_1867 := 0xdc0fb0ef%Z.
Definition w_1872 := 0xb89fa0ef%Z.
Definition w_1874 := 0xdb8f30ef%Z.
Definition w_1895 := 0x6e00006f%Z.
Definition hi_22 := (Z_to_bv 20 10).
Definition hi_730 := (Z_to_bv 20 1048506).
Definition hi_792 := (Z_to_bv 20 1048506).
Definition hi_843 := (Z_to_bv 20 1048503).
Definition hi_1278 := (Z_to_bv 20 1048502).
Definition hi_1281 := (Z_to_bv 20 1048502).
Definition hi_1284 := (Z_to_bv 20 1048502).
Definition hi_1290 := (Z_to_bv 20 1048502).
Definition hi_1363 := (Z_to_bv 20 1048502).
Definition hi_1433 := (Z_to_bv 20 1048505).
Definition hi_1618 := (Z_to_bv 20 1048502).
Definition hi_1753 := (Z_to_bv 20 1048502).
Definition lo_23 := (Z_to_bv 12 280).
Definition lo_733 := (Z_to_bv 12 312).
Definition lo_796 := (Z_to_bv 12 64).
Definition lo_845 := (Z_to_bv 12 3804).
Definition lo_1279 := (Z_to_bv 12 1984).
Definition lo_1282 := (Z_to_bv 12 1988).
Definition lo_1285 := (Z_to_bv 12 1944).
Definition lo_1291 := (Z_to_bv 12 1920).
Definition lo_1364 := (Z_to_bv 12 1644).
Definition lo_1435 := (Z_to_bv 12 1596).
Definition lo_1619 := (Z_to_bv 12 624).
Definition lo_1754 := (Z_to_bv 12 84).
Definition joff_170 := (Z_to_bv 21 2084516).
Definition joff_256 := (Z_to_bv 21 2084172).
Definition joff_502 := (Z_to_bv 21 2050856).
Definition joff_509 := (Z_to_bv 21 2083160).
Definition joff_556 := (Z_to_bv 21 2082972).
Definition joff_560 := (Z_to_bv 21 2085592).
Definition joff_569 := (Z_to_bv 21 2050588).
Definition joff_573 := (Z_to_bv 21 2082904).
Definition joff_579 := (Z_to_bv 21 2081088).
Definition joff_586 := (Z_to_bv 21 2079980).
Definition joff_591 := (Z_to_bv 21 2050500).
Definition joff_595 := (Z_to_bv 21 2082816).
Definition joff_600 := (Z_to_bv 21 2081004).
Definition joff_603 := (Z_to_bv 21 2080992).
Definition joff_648 := (Z_to_bv 21 2082604).
Definition joff_676 := (Z_to_bv 21 5504).
Definition joff_683 := (Z_to_bv 21 2050132).
Definition joff_690 := (Z_to_bv 21 2082436).
Definition joff_718 := (Z_to_bv 21 2082324).
Definition joff_722 := (Z_to_bv 21 2084944).
Definition joff_727 := (Z_to_bv 21 2080496).
Definition joff_737 := (Z_to_bv 21 2082248).
Definition joff_742 := (Z_to_bv 21 2085268).
Definition joff_1077 := (Z_to_bv 21 2080888).
Definition joff_1090 := (Z_to_bv 21 2080836).
Definition joff_1094 := (Z_to_bv 21 2083456).
Definition joff_1106 := (Z_to_bv 21 2078980).
Definition joff_1109 := (Z_to_bv 21 2081192).
Definition joff_1125 := (Z_to_bv 21 2083332).
Definition joff_1132 := (Z_to_bv 21 2078876).
Definition joff_1135 := (Z_to_bv 21 2081088).
Definition joff_1148 := (Z_to_bv 21 2083240).
Definition joff_1160 := (Z_to_bv 21 2078764).
Definition joff_1163 := (Z_to_bv 21 2080976).
Definition joff_1178 := (Z_to_bv 21 2083120).
Definition joff_1185 := (Z_to_bv 21 2078664).
Definition joff_1188 := (Z_to_bv 21 2080876).
Definition joff_1192 := (Z_to_bv 21 2080428).
Definition joff_1197 := (Z_to_bv 21 2078616).
Definition joff_1218 := (Z_to_bv 21 2080588).
Definition joff_1219 := (Z_to_bv 21 2077448).
Definition joff_1222 := (Z_to_bv 21 3668).
Definition joff_1228 := (Z_to_bv 21 2080548).
Definition joff_1229 := (Z_to_bv 21 2077408).
Definition joff_1234 := (Z_to_bv 21 3660).
Definition joff_1241 := (Z_to_bv 21 2080648).
Definition joff_1244 := (Z_to_bv 21 2080652).
Definition joff_1294 := (Z_to_bv 21 2077148).
Definition joff_1299 := (Z_to_bv 21 2080432).
Definition joff_1306 := (Z_to_bv 21 2079972).
Definition joff_1311 := (Z_to_bv 21 3352).
Definition joff_1314 := (Z_to_bv 21 2077760).
Definition joff_1321 := (Z_to_bv 21 2080344).
Definition joff_1329 := (Z_to_bv 21 2080312).
Definition joff_1332 := (Z_to_bv 21 2080284).
Definition joff_1341 := (Z_to_bv 21 3964).
Definition joff_1345 := (Z_to_bv 21 2079816).
Definition joff_1349 := (Z_to_bv 21 2082840).
Definition joff_1354 := (Z_to_bv 21 2077800).
Definition joff_1365 := (Z_to_bv 21 2076864).
Definition joff_1370 := (Z_to_bv 21 2077924).
Definition joff_1382 := (Z_to_bv 21 2047336).
Definition joff_1391 := (Z_to_bv 21 2077452).
Definition joff_1419 := (Z_to_bv 21 3664).
Definition joff_1421 := (Z_to_bv 21 2079512).
Definition joff_1425 := (Z_to_bv 21 2082132).
Definition joff_1430 := (Z_to_bv 21 2077684).
Definition joff_1439 := (Z_to_bv 21 2079440).
Definition joff_1441 := (Z_to_bv 21 2048320).
Definition joff_1463 := (Z_to_bv 21 2079344).
Definition joff_1467 := (Z_to_bv 21 2079328).
Definition joff_1589 := (Z_to_bv 21 2078840).
Definition joff_1595 := (Z_to_bv 21 2078816).
Definition joff_1600 := (Z_to_bv 21 2081836).
Definition joff_1607 := (Z_to_bv 21 2076976).
Definition joff_1611 := (Z_to_bv 21 2079184).
Definition joff_1620 := (Z_to_bv 21 2075844).
Definition joff_1623 := (Z_to_bv 21 2076912).
Definition joff_1626 := (Z_to_bv 21 2079124).
Definition joff_1697 := (Z_to_bv 21 2046076).
Definition joff_1701 := (Z_to_bv 21 2078392).
Definition joff_1707 := (Z_to_bv 21 2076576).
Definition joff_1712 := (Z_to_bv 21 2046016).
Definition joff_1716 := (Z_to_bv 21 2078332).
Definition joff_1721 := (Z_to_bv 21 2076520).
Definition joff_1724 := (Z_to_bv 21 2076508).
Definition joff_1735 := (Z_to_bv 21 2075384).
Definition joff_1759 := (Z_to_bv 21 2078160).
Definition joff_1764 := (Z_to_bv 21 2078556).
Definition joff_1769 := (Z_to_bv 21 2078552).
Definition joff_1775 := (Z_to_bv 21 2075224).
Definition joff_1780 := (Z_to_bv 21 2076096).
Definition joff_1790 := (Z_to_bv 21 2078036).
Definition joff_1808 := (Z_to_bv 21 2078228).
Definition joff_1809 := (Z_to_bv 21 2075088).
Definition joff_1813 := (Z_to_bv 21 2077944).
Definition joff_1818 := (Z_to_bv 21 1284).
Definition joff_1827 := (Z_to_bv 21 2075708).
Definition joff_1834 := (Z_to_bv 21 2077860).
Definition joff_1840 := (Z_to_bv 21 2077836).
Definition joff_1844 := (Z_to_bv 21 2080456).
Definition joff_1849 := (Z_to_bv 21 2076008).
Definition joff_1854 := (Z_to_bv 21 2078212).
Definition joff_1861 := (Z_to_bv 21 2075960).
Definition joff_1864 := (Z_to_bv 21 2078172).
Definition joff_1867 := (Z_to_bv 21 2078144).
Definition joff_1872 := (Z_to_bv 21 2075528).
Definition joff_1874 := (Z_to_bv 21 2045368).
Definition joff_1895 := (Z_to_bv 21 1760).
Definition G_10778 := 0x13408%Z.
Definition G_10788 := 0x13418%Z.
Definition G_10798 := 0x13428%Z.
Definition G_107c0 := 0x13468%Z.
Definition G_116a8 := 0x16500%Z.
Definition got_ssp := got_ssp.
Definition RATP := RATP.
Definition STRING_READ := STRING_READ.
Definition ssp_guard := ssp_guard.
Definition e_errno_loc := 0x50b60%Z.
Definition e_197bc := 0x51024%Z.
Definition e_extenddftf2 := 0x57e74%Z.
Definition e_fpclassifyl := 0x5800c%Z.
Definition e_letf2 := 0x58128%Z.
Definition e_getf2 := 0x581f0%Z.
Definition e_multf3 := 0x582ac%Z.
Definition e_floatsitf := 0x589ac%Z.
Definition e_scalbn := 0x58ab4%Z.
Definition e_subtf3 := 0x58b4c%Z.
Definition e_addtf3 := 0x58b5c%Z.
Definition e_floatunsitf := 0x593f8%Z.
Definition e_divtf3 := 0x5958c%Z.
Definition e_extendsftf2 := 0x5d870%Z.
Lemma CODE : CodeAt.code_at rsegs 0x5b860 (QzQg.Mq0.floatscan_code 0x0000a517%Z 0x11853a03%Z 0xea5fc0ef%Z 0xd4dfc0ef%Z 0xb29f40ef%Z 0x959fc0ef%Z 0x89dfc0ef%Z 0xad8fd0ef%Z 0xa1df40ef%Z 0x859fc0ef%Z 0x940fc0ef%Z 0xcedfb0ef%Z 0x9c5f40ef%Z 0x801fc0ef%Z 0x8ecfc0ef%Z 0x8e0fc0ef%Z 0xf2cfc0ef%Z 0x580010ef%Z 0x855f40ef%Z 0xe84fc0ef%Z 0xe14fc0ef%Z 0x850fd0ef%Z 0xef1fb0ef%Z 0xfffba617%Z 0x13860613%Z 0xdc8fc0ef%Z 0x994fd0ef%Z 0xfffba817%Z 0x04080813%Z 0xfffb7697%Z 0xedc6b683%Z 0x878fc0ef%Z 0x844fc0ef%Z 0xa81fc0ef%Z 0x905fb0ef%Z 0x9a8fc0ef%Z 0xa05fc0ef%Z 0x89dfb0ef%Z 0x940fc0ef%Z 0x9a9fc0ef%Z 0x82dfb0ef%Z 0x8d0fc0ef%Z 0x931fc0ef%Z 0xfc8fb0ef%Z 0x86cfc0ef%Z 0xeadfb0ef%Z 0xf98fb0ef%Z 0xf4dfb0ef%Z 0xb08fb0ef%Z 0x655000ef%Z 0xf25fb0ef%Z 0xae0fb0ef%Z 0x64d000ef%Z 0xf89fb0ef%Z 0xf8dfb0ef%Z 0xfffb6517%Z 0x7c053707%Z 0xfffb6517%Z 0x7c453787%Z 0xfffb6517%Z 0x79853787%Z 0xfffb6517%Z 0x78053707%Z 0x9dcfb0ef%Z 0xeb1fb0ef%Z 0xce5fb0ef%Z 0x519000ef%Z 0xc40fb0ef%Z 0xe59fb0ef%Z 0xe39fb0ef%Z 0xe1dfb0ef%Z 0x77d000ef%Z 0xc49fb0ef%Z 0x819fc0ef%Z 0xc68fb0ef%Z 0xfffb6517%Z 0x66c53507%Z 0x8c0fb0ef%Z 0xce4fb0ef%Z 0xd69f30ef%Z 0xb0cfb0ef%Z 0x6510006f%Z 0xb19fb0ef%Z 0xd54fc0ef%Z 0xbf4fb0ef%Z 0xfffb9517%Z 0x63c50513%Z 0xad1fb0ef%Z 0x940f40ef%Z 0xa71fb0ef%Z 0xa61fb0ef%Z 0x879fb0ef%Z 0x861fb0ef%Z 0xc2cfc0ef%Z 0x930fb0ef%Z 0x9d1fb0ef%Z 0xfffb6517%Z 0x27053507%Z 0xcc5fa0ef%Z 0x8f0fb0ef%Z 0x995fb0ef%Z 0x87df30ef%Z 0xeb8fb0ef%Z 0xfa1fa0ef%Z 0x841f30ef%Z 0xe7cfb0ef%Z 0xf69fa0ef%Z 0xf5dfa0ef%Z 0xaf9fa0ef%Z 0xfffb6517%Z 0x05453407%Z 0xdd0fb0ef%Z 0xf5cfb0ef%Z 0xf58fb0ef%Z 0xa59fa0ef%Z 0xdc1fa0ef%Z 0xd54fb0ef%Z 0xe14fb0ef%Z 0x9d1fa0ef%Z 0xcf8fb0ef%Z 0x504000ef%Z 0xc3dfa0ef%Z 0xca4fb0ef%Z 0xc8cfb0ef%Z 0xec9fb0ef%Z 0xd69fa0ef%Z 0xe04fb0ef%Z 0xd39fa0ef%Z 0xddcfb0ef%Z 0xdc0fb0ef%Z 0xb89fa0ef%Z 0xdb8f30ef%Z 0x6e00006f%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5b860 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5b860 /\ 0x5b860 + 7584 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_e_errno_loc : CodeAt.code_at rsegs e_errno_loc QzQg.Mq0.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Lemma CODE_e_extendsftf2 : CodeAt.code_at rsegs e_extendsftf2 QzQg.Mq0.extendsftf2_code.  Proof. StepGen.code_at_vm. Qed.
Definition divtf3_spec := @divtf3_spec.
Definition getf2_spec := @getf2_spec.
Definition extenddftf2_spec := @extenddftf2_spec.
Definition scalbn_spec := @scalbn_spec.
Definition fabsl_spec := @fabsl_spec.
Definition copysignl_spec := @copysignl_spec.
Definition scalbnl_spec := @scalbnl_spec.
Definition rfmodl_spec := @rfmodl_spec.
Definition letf2_spec := @letf2_spec.
Definition floatsitf_spec := @floatsitf_spec.
Definition addtf3_spec := @addtf3_spec.
Definition subtf3_spec := @subtf3_spec.
Definition multf3_spec := @multf3_spec.
End GwI.

Definition RERRNO : Z := 0x77b5c.
Lemma gw_eq_RERRNO : @RERRNO = ltac:(GwInst.gw_term (@QzQg.Mq0.RERRNO RATP) (@RERRNO)). Proof. unfold RERRNO, QzQg.Mq0.RERRNO; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_RERRNO : gw_eqs.
Definition ERRNO_LOC : Z := 0x50b60.
Lemma gw_eq_ERRNO_LOC : @ERRNO_LOC = ltac:(GwInst.gw_term (@QzQg.Mq0.ERRNO_LOC 0x50b60%Z) (@ERRNO_LOC)). Proof. unfold ERRNO_LOC, QzQg.Mq0.ERRNO_LOC; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ERRNO_LOC : gw_eqs.

Lemma errno_loc_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv rsegs m ->
evt rsegs (fun ms' => exists m', ms' = MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 RERRNO) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
(MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ERRNO_LOC) fc None m (seg_rom rsegs)).
Proof. rewrite ?gw_eq_RERRNO, ?gw_eq_ERRNO_LOC; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.errno_loc_spec) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.errno_loc_spec)]. Qed.

Section CallE.
Local Open Scope Z_scope.
Definition DS : divtf3_stmt := U4WT.divtf3_spec.
#[using="Type"] Lemma mul_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
stk rsegs m (q - 80) q -> mem_inv rsegs m -> (4096 <= q < 2^64)%Z ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt rsegs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 80 (f128_mul X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x582ac) fc None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_call2_post__3; @gw_eq_call2_post__2; @gw_eq_call2_post]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.mul_callE) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.mul_callE)]. Qed.
#[using="Type"] Lemma div_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
stk rsegs m (q - 112) q -> mem_inv rsegs m -> (4096 <= q < 2^64)%Z ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt rsegs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 112 (f128_div X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5958c) fc None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_call2_post__3; @gw_eq_call2_post__2; @gw_eq_call2_post]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.div_callE) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.div_callE)]. Qed.
#[using="Type"] Lemma add_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
stk rsegs m (q - 48) q -> mem_inv rsegs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt rsegs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_add X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x58b5c) fc None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_calla_post__3; @gw_eq_calla_post__2; @gw_eq_calla_post]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.add_callE) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.add_callE)]. Qed.
#[using="Type"] Lemma sub_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
stk rsegs m (q - 48) q -> mem_inv rsegs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt rsegs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_sub X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x58b4c) fc None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_calla_post__3; @gw_eq_calla_post__2; @gw_eq_calla_post]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.sub_callE) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.sub_callE)]. Qed.
#[using="Type"] Lemma letf2_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (al ah bl bh X Y : Z),
mem_inv rsegs m -> al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt rsegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x58128) fc None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_leaf1_post__3; @gw_eq_leaf1_post__2; @gw_eq_leaf1_post]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.letf2_callE) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.letf2_callE)]. Qed.
#[using="Type"] Lemma getf2_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (al ah bl bh X Y : Z),
mem_inv rsegs m -> al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt rsegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_ge X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x581f0) fc None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_leaf1_post__3; @gw_eq_leaf1_post__2; @gw_eq_leaf1_post]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.getf2_callE) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.getf2_callE)]. Qed.

#[using="Type"] Lemma scalbn_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (n : Z),
mem_inv rsegs m -> frm0 fc -> (-2^31 <= n < 2^31)%Z ->
evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (f15 : word) fc' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
(bvmap_set 10 (scalbn_model (reg_get F 10) n) (bvmap_set 15 f15 F)) (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ frm0 fc')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x58ab4) fc None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_scalbn_model__3; @gw_eq_scalbn_model__2; @gw_eq_scalbn_model]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.scalbn_callE) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.scalbn_callE)]. Qed.
#[using="Type"] Lemma fabsl_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (al ah X : Z),
mem_inv rsegs m -> al = lo64 X -> ah = hi64 X ->
evt rsegs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_fabsl X) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FABSL) fc None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_FABSL__3; @gw_eq_FABSL__2; @gw_eq_FABSL]; [@gw_eq_leafq_post__3; @gw_eq_leafq_post__2; @gw_eq_leafq_post]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.fabsl_callE) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.fabsl_callE)]. Qed.
#[using="Type"] Lemma copysignl_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (al ah bl bh X Y : Z),
mem_inv rsegs m -> al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt rsegs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_copysignl X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 COPYSIGNL) fc None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_COPYSIGNL__3; @gw_eq_COPYSIGNL__2; @gw_eq_COPYSIGNL]; [@gw_eq_leafq_post__3; @gw_eq_leafq_post__2; @gw_eq_leafq_post]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.copysignl_callE) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.copysignl_callE)]. Qed.

#[using="Type"] Lemma fmodl_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q lo al ah bl bh X Y r : Z),
stk rsegs m lo q -> mem_inv rsegs m -> (lo <= q - 192) -> (4288 <= q < 2^63) ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
m_fmodl X Y = Some r ->
evt rsegs (fun ms' => exists t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - 192, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo q /\ (forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k))
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FMODL) fc None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_FMODL__3; @gw_eq_FMODL__2; @gw_eq_FMODL]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.fmodl_callE) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.fmodl_callE)]. Qed.
End CallE.

Definition FS_DEPTH : Z := 8656.
Lemma gw_eq_FS_DEPTH : @FS_DEPTH = ltac:(GwInst.gw_term (@QzQg.Mq0.FS_DEPTH) (@FS_DEPTH)). Proof. unfold FS_DEPTH, QzQg.Mq0.FS_DEPTH; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FS_DEPTH : gw_eqs.
Definition FLOATSCAN : Z := 0x5b860.
Lemma gw_eq_FLOATSCAN : @FLOATSCAN = ltac:(GwInst.gw_term (@QzQg.Mq0.FLOATSCAN 0x5b860) (@FLOATSCAN)). Proof. unfold FLOATSCAN, QzQg.Mq0.FLOATSCAN; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FLOATSCAN : gw_eqs.

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
Hypothesis HP30 : (p < 2^31)%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Q1 : (q < 2^63)%Z.
Hypothesis FRM : frm0 fc.

Definition ctx_all : unit :=
let _ := (ra, q, gp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, F, fc, m0,
Fp, T, p, J, txt, pre, post, canary, pok, fuelc, f0, kmin0, c0, fR, yR) in tt.
Lemma gw_eq_ctx_all : @ctx_all = ltac:(GwInst.gw_term (@QzQg.Mq0.ctx_all) (@ctx_all)). Proof. unfold ctx_all, QzQg.Mq0.ctx_all; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_ctx_all : gw_eqs.

Definition Wfs : list (Z * Z) := [(q - FS_DEPTH, q); (Fp, Fp + 232); (RERRNO, RERRNO + 4)]%Z.
Lemma gw_eq_Wfs : @Wfs = ltac:(GwInst.gw_term (@QzQg.Mq0.Wfs RATP) (@Wfs)). Proof. unfold Wfs, QzQg.Mq0.Wfs; rewrite ?gw_eq_RERRNO, ?gw_eq_FS_DEPTH; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_Wfs : gw_eqs.
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).
Notation XA := (q + -8312)%Z.
Notation RFJ' := (RFJ T txt p true J).
Definition zero0 : Z := f128_of_i32 0.
Lemma gw_eq_zero0 : @zero0 = ltac:(GwInst.gw_term (@QzQg.Mq0.zero0) (@zero0)). Proof. unfold zero0, QzQg.Mq0.zero0; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_zero0 : gw_eqs.

Definition FokR (F' : bvmap 5 word) : Prop :=
forall k : bv 5, bv_unsigned k <> 10%Z -> bv_unsigned k <> 14%Z -> bv_unsigned k <> 15%Z -> reg_get F' k = reg_get F k.
Lemma gw_eq_FokR : @FokR = ltac:(GwInst.gw_term (@QzQg.Mq0.FokR) (@FokR)). Proof. unfold FokR, QzQg.Mq0.FokR; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_FokR : gw_eqs.

Definition Fok (F' : bvmap 5 word) : Prop :=
forall k : bv 5, bv_unsigned k <> 8%Z -> bv_unsigned k <> 10%Z -> bv_unsigned k <> 14%Z -> bv_unsigned k <> 15%Z -> reg_get F' k = reg_get F k.
Lemma gw_eq_Fok : @Fok = ltac:(GwInst.gw_term (@QzQg.Mq0.Fok) (@Fok)). Proof. unfold Fok, QzQg.Mq0.Fok; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_Fok : gw_eqs.
#[using="Type"] Lemma Fok_refl : Fok F. Proof. rewrite ?gw_eq_Fok; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.Fok_refl) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.Fok_refl)]. Qed.
#[using="Type"] Lemma Fok_set : forall F' (r : bv 5) v, Fok F' -> (bv_unsigned r = 8 \/ bv_unsigned r = 10 \/ bv_unsigned r = 14 \/ bv_unsigned r = 15)%Z -> Fok (bvmap_set r v F').
Proof. rewrite ?gw_eq_Fok; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.Fok_set) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.Fok_set)]. Qed.
#[using="Type"] Lemma Fok_trans10 : forall F1 F2, Fok F1 -> (forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k) -> Fok F2.
Proof. rewrite ?gw_eq_Fok; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.Fok_trans10) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.Fok_trans10)]. Qed.

Definition fs_post (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' k' c' (ev' : word),
ms' = MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 (lo64 yR)) (Z_to_bv 64 (hi64 yR)) a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch Wfs m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - FS_DEPTH) q
/\ rw_cells rsegs m' Fp (rf_cells T p true fR J)
/\ RFJ' k' c' fR /\ (0 <= k')%Z
/\ bytes_at rsegs m' T (zbytes txt)
/\ ssp_cells m' canary
/\ rw_cells rsegs m' RERRNO [C4 ev']
/\ FokR F' /\ frm0 fc'.
Lemma gw_eq_fs_post : @fs_post = ltac:(GwInst.gw_term (@QzQg.Mq0.fs_post rsegs got_ssp RATP STRING_READ ssp_guard) (@fs_post)). Proof. unfold fs_post, QzQg.Mq0.fs_post; rewrite ?gw_eq_RERRNO, ?gw_eq_FS_DEPTH, ?gw_eq_Wfs, ?gw_eq_FokR; ltac2:(GwEq.gw_rw [[@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_fs_post : gw_eqs.

Definition hi_cells : list cell :=
[C8 canary; C8 (reg_get F 8); C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].
Lemma gw_eq_hi_cells : @hi_cells = ltac:(GwInst.gw_term (@QzQg.Mq0.hi_cells) (@hi_cells)). Proof. unfold hi_cells, QzQg.Mq0.hi_cells; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_hi_cells : gw_eqs.

Definition finv (m : word -> option byte) : Prop :=
mem_inv rsegs m /\ munch Wfs m0 m /\ wmono rsegs m0 m
/\ rw_cells rsegs m (q + -120) hi_cells
/\ stk rsegs m (q - FS_DEPTH) (q + -8416)
/\ bytes_at rsegs m T (zbytes txt)
/\ rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m ssp_guard [C8 canary].
Lemma gw_eq_finv : @finv = ltac:(GwInst.gw_term (@QzQg.Mq0.finv rsegs got_ssp RATP ssp_guard) (@finv)). Proof. unfold finv, QzQg.Mq0.finv; rewrite ?gw_eq_FS_DEPTH, ?gw_eq_Wfs, ?gw_eq_hi_cells; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_finv : gw_eqs.
#[using="Type"] Lemma zbytes_len : length (zbytes txt) = length txt.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.zbytes_len) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.zbytes_len)]. Qed.

Definition framL (j0 : list byte) (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) (ev : word) (m : word -> option byte) : Prop :=
rw_cells rsegs m (q + -8416) [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; CB 8 b96]
/\ rw_cells rsegs m RERRNO [C4 ev].
Lemma gw_eq_framL : @framL = ltac:(GwInst.gw_term (@QzQg.Mq0.framL rsegs RATP) (@framL)). Proof. unfold framL, QzQg.Mq0.framL; rewrite ?gw_eq_RERRNO; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_framL : gw_eqs.

#[using="Type"] Lemma rw_cells_C8_CB8 : forall m A pre (v : word) post,
rw_cells rsegs m A (pre ++ C8 v :: post) <-> rw_cells rsegs m A (pre ++ CB 8 (le8 v) :: post).
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.rw_cells_C8_CB8) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.rw_cells_C8_CB8)]. Qed.
#[using="Type"] Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.le8_of_bytes) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.le8_of_bytes)]. Qed.
#[using="Type"] Lemma cb8_c8_in : forall m A pre post bs, rw_cells rsegs m A (pre ++ CB 8 bs :: post) -> rw_cells rsegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.cb8_c8_in) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.cb8_c8_in)]. Qed.

Definition xrel (ws : list word) (x : list Z) (P : Z -> Prop) : Prop :=
length ws = 2048%nat /\ length x = 2048%nat /\ forall i, (0 <= i < 2048)%Z -> P i -> znth x i = wval ws i.
Lemma gw_eq_xrel : @xrel = ltac:(GwInst.gw_term (@QzQg.Mq0.xrel) (@xrel)). Proof. unfold xrel, QzQg.Mq0.xrel; ltac2:(GwEq.gw_rw [[@gw_eq_wval__3; @gw_eq_wval__2; @gw_eq_wval]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_xrel : gw_eqs.

Notation POST := (fs_post m0).

#[using="BYT"] Lemma txt_char : forall i, (0 <= i < zlength txt)%Z -> (0 <= znth txt i < 256)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.txt_char) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.txt_char)]. Qed.
#[using="Hnum"] Lemma numch_nz : forall i, (0 <= i < p)%Z -> (43 <= znth txt i <= 101)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.numch_nz) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.numch_nz)]. Qed.

#[using="pre"] Lemma frame_release : forall m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws,
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr rsegs m XA ws -> length ws = 2048%nat ->
stk rsegs m (q - FS_DEPTH) q.
Proof. rewrite ?gw_eq_FS_DEPTH, ?gw_eq_finv, ?gw_eq_framL; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.frame_release) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.frame_release)]. Qed.

#[using="pre Hp SE_T SPF SPT SG1 SG3"] Lemma post_tail : forall m m' K F' fc' k c ev,
finv m -> rw_cells rsegs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> rw_cells rsegs m RERRNO [C4 ev] ->
FokR F' -> frm0 fc' -> (0 <= K <= FS_DEPTH)%Z ->
munch [(q - K, q)]%Z m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
stk rsegs m' (q - FS_DEPTH) q ->
forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
POST (MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 (lo64 yR)) (Z_to_bv 64 (hi64 yR)) a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)).
Proof. rewrite ?gw_eq_RERRNO, ?gw_eq_FS_DEPTH, ?gw_eq_FokR, ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.post_tail) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.post_tail)]. Qed.

#[using="Hp SE_T SPF SPT SG1 SG3"] Lemma L_RET34 : forall m (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws k c (r : Z),
let _ := ctx_all in
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr rsegs m XA ws -> length ws = 2048%nat ->
rw_cells rsegs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = r ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) canary x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c330) fct None m (seg_rom rsegs)).
Proof. rewrite ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_finv, ?gw_eq_framL; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.L_RET34) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.L_RET34)]. Qed.

#[using="Hp SE_T SPF SPT SG1 SG3"] Lemma L_RET1 : forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 b96 ev ws k c (r : Z),
let _ := ctx_all in
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 (Z_to_bv 64 ssp_guard) b96 ev m -> u32arr rsegs m XA ws -> length ws = 2048%nat ->
rw_cells rsegs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = r ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c1d0) fct None m (seg_rom rsegs)).
Proof. rewrite ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_finv, ?gw_eq_framL; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.L_RET1) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.L_RET1)]. Qed.

#[using="Hp SE_T SPF SPT SG1 SG3"] Lemma L_RET30 : forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws k c (r : Z),
let _ := ctx_all in
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr rsegs m XA ws -> length ws = 2048%nat ->
rw_cells rsegs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = r ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c32c) fct None m (seg_rom rsegs)).
Proof. rewrite ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_finv, ?gw_eq_framL; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.L_RET30) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.L_RET30)]. Qed.

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_SCL : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws k c (Y e2 : Z),
let _ := ctx_all in
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr rsegs m XA ws -> length ws = 2048%nat ->
rw_cells rsegs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(-2^31 <= e2 < 2^31)%Z ->
yR = m_scalbnl Y e2 ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 (lo64 Y)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 ssp_guard) x19 (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5ce24) fct None m (seg_rom rsegs)).
Proof. rewrite ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_finv, ?gw_eq_framL; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.L_SCL) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.L_SCL)]. Qed.

#[using="Type"] Lemma b2z_land : forall a b, Z.land (Z.b2z a) (Z.b2z b) = Z.b2z (a && b). Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.b2z_land) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.b2z_land)]. Qed.
#[using="Type"] Lemma b2z_lt1 : forall c, (Z.b2z c <? 1) = negb c. Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.b2z_lt1) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.b2z_lt1)]. Qed.

Definition hide (P : Prop) := P.
Lemma gw_eq_hide : @hide = ltac:(GwInst.gw_term (@QzQg.Mq0.hide) (@hide)). Proof. unfold hide, QzQg.Mq0.hide; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_hide : gw_eqs.

#[using="Type"] Lemma swrap32_landW_r : forall a c, bv_swrap 32 (c + Z.land a 18446744073709551615) = bv_swrap 32 (c + a).
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.swrap32_landW_r) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.swrap32_landW_r)]. Qed.

Definition hide2 (P : Prop) := P.
Lemma gw_eq_hide2 : @hide2 = ltac:(GwInst.gw_term (@QzQg.Mq0.hide2) (@hide2)). Proof. unfold hide2, QzQg.Mq0.hide2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_hide2 : gw_eqs.

Definition dfinv (m : word -> option byte) (j0 : list byte) (w16 w24 : word) (b96 : list byte) (ev : word) (ws : list word) (sign : Z) (f : shfile) : Prop :=
finv m
/\ framL j0 (Z_to_bv 64 1021) w16 w24 (Z_to_bv 64 1) (Z_to_bv 64 (-1074)) (Z_to_bv 64 1074) (Z_to_bv 64 53)
(Z_to_bv 64 pok) (Z_to_bv 64 sign) (Z_to_bv 64 18396) (Z_to_bv 64 ssp_guard) b96 ev m
/\ u32arr rsegs m XA ws /\ length ws = 2048%nat /\ rw_cells rsegs m Fp (rf_cells T p true f J).
Lemma gw_eq_dfinv : @dfinv = ltac:(GwInst.gw_term (@QzQg.Mq0.dfinv rsegs got_ssp RATP ssp_guard) (@dfinv)). Proof. unfold dfinv, QzQg.Mq0.dfinv; rewrite ?gw_eq_finv, ?gw_eq_framL; ltac2:(GwEq.gw_rw [[@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_dfinv : gw_eqs.

Definition dfinvG (m : word -> option byte) (j0 : list byte) (w16 w24 w80 : word) (b96 : list byte) (ev : word) (ws : list word) (sign : Z) (f : shfile) : Prop :=
finv m
/\ framL j0 (Z_to_bv 64 1021) w16 w24 (Z_to_bv 64 1) (Z_to_bv 64 (-1074)) (Z_to_bv 64 1074) (Z_to_bv 64 53)
(Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev m
/\ u32arr rsegs m XA ws /\ length ws = 2048%nat /\ rw_cells rsegs m Fp (rf_cells T p true f J).
Lemma gw_eq_dfinvG : @dfinvG = ltac:(GwInst.gw_term (@QzQg.Mq0.dfinvG rsegs got_ssp RATP ssp_guard) (@dfinvG)). Proof. unfold dfinvG, QzQg.Mq0.dfinvG; rewrite ?gw_eq_finv, ?gw_eq_framL; ltac2:(GwEq.gw_rw [[@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_dfinvG : gw_eqs.
#[using="Type"] Lemma dfinvG_dfinv : forall m j0 w16 w24 b96 ev ws sign f,
dfinvG m j0 w16 w24 (Z_to_bv 64 18396) b96 ev ws sign f = dfinv m j0 w16 w24 b96 ev ws sign f.
Proof. rewrite ?gw_eq_dfinv, ?gw_eq_dfinvG; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.dfinvG_dfinv) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.dfinvG_dfinv)]. Qed.

Definition inring (a z i : Z) : Prop := ((i - a) mod 2048 < (z - a) mod 2048)%Z.
Lemma gw_eq_inring : @inring = ltac:(GwInst.gw_term (@QzQg.Mq0.inring) (@inring)). Proof. unfold inring, QzQg.Mq0.inring; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_inring : gw_eqs.
#[using="Type"] Lemma land2047 : forall v, Z.land v 2047 = (v mod 2048)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.land2047) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.land2047)]. Qed.
#[using="Type"] Lemma landW_mod2048 : forall v, ((Z.land v 18446744073709551615) mod 2048 = v mod 2048)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.landW_mod2048) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.landW_mod2048)]. Qed.
#[using="Type"] Lemma inring_plus : forall a z d, (0 <= z < 2048)%Z -> (0 <= d < 2048)%Z -> (d <= (z - a) mod 2048)%Z -> Z.land (a + d) 2047 <> z ->
inring a z (Z.land (a + d) 2047) /\ (d + 1 <= (z - a) mod 2048)%Z.
Proof. rewrite ?gw_eq_inring; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.inring_plus) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.inring_plus)]. Qed.
#[using="Type"] Lemma inring_hit : forall a z d, (0 <= z < 2048)%Z -> (0 <= d < 2048)%Z -> Z.land (a + d) 2047 = z -> ((z - a) mod 2048 = d)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.inring_hit) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.inring_hit)]. Qed.
#[using="Type"] Lemma inring_grow : forall a z i, (0 <= z)%Z -> ((z - a) mod 2048 < 2047)%Z ->
inring a (z + 1) i <-> (inring a z i \/ (i - a) mod 2048 = (z - a) mod 2048)%Z.
Proof. rewrite ?gw_eq_inring; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.inring_grow) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.inring_grow)]. Qed.
#[using="Type"] Lemma mod_eq_idx : forall a z i, (0 <= z < 2048)%Z -> (0 <= i < 2048)%Z -> ((i - a) mod 2048 = (z - a) mod 2048)%Z -> i = z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.mod_eq_idx) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.mod_eq_idx)]. Qed.
#[using="Type"] Lemma inring_mod : forall a z i, inring a (z mod 2048) i <-> inring a z i.
Proof. rewrite ?gw_eq_inring; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.inring_mod) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.inring_mod)]. Qed.
#[using="Type"] Lemma xrel_iff : forall ws x (P Q : Z -> Prop), (forall i, (0 <= i < 2048)%Z -> Q i -> P i) -> xrel ws x P -> xrel ws x Q.
Proof. rewrite ?gw_eq_xrel; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.xrel_iff) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.xrel_iff)]. Qed.

Definition zone (h w : bool) (a z : Z) (i : Z) : Prop := inring a z i \/ (h = true /\ (z <= i)%Z) \/ (w = true /\ (a <= i)%Z).
Lemma gw_eq_zone : @zone = ltac:(GwInst.gw_term (@QzQg.Mq0.zone) (@zone)). Proof. unfold zone, QzQg.Mq0.zone; rewrite ?gw_eq_inring; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_zone : gw_eqs.
#[using="Type"] Lemma zone_in : forall h w a z i, inring a z i -> zone h w a z i.
Proof. rewrite ?gw_eq_inring, ?gw_eq_zone; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.zone_in) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.zone_in)]. Qed.
#[using="Type"] Lemma xrel_window : forall ws x h w a z, xrel ws x (zone h w a z) -> xrel ws x (inring a z).
Proof. rewrite ?gw_eq_xrel, ?gw_eq_inring, ?gw_eq_zone; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.xrel_window) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.xrel_window)]. Qed.

Definition X31 (x : list Z) : Prop := forall i, (0 <= znth x i < 2^31)%Z.
Lemma gw_eq_X31 : @X31 = ltac:(GwInst.gw_term (@QzQg.Mq0.X31) (@X31)). Proof. unfold X31, QzQg.Mq0.X31; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_X31 : gw_eqs.

Definition S_F3 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) Ft fct
j0 w16 w24 b96 ev ws sign k c (Y FR BI e2 bits' : Z),
let _ := ctx_all in
dfinv m j0 w16 w24 b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= bits' <= 53)%Z ->
fin_K3 1024 Y FR BI e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (hi64 FR)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 FR)) (Z_to_bv 64 1021) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5cd10) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_F3 : @S_F3 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_F3 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_F3)). Proof. unfold S_F3, QzQg.Mq0.S_F3; rewrite ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_dfinv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_F3 : gw_eqs.

#[using="Type"] Lemma f128_ge_range : forall a b, (-1 <= f128_ge a b <= 1)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.f128_ge_range) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.f128_ge_range)]. Qed.

Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.

#[using="Type"] Lemma extenddftf2_callF : forall ra' sp' gp' tp' t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F' : bvmap 5 word) fc' (m : word -> option byte) (D : Z),
mem_inv rsegs m -> bv_unsigned (reg_get F' 10) = D ->
evt rsegs (leaf2_post ra' sp' gp' tp' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' (f128_of_d D) m)
(MS (mkR ra' sp' gp' tp' t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x57e74) fc' None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_leaf2_post__3; @gw_eq_leaf2_post__2; @gw_eq_leaf2_post]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.extenddftf2_callF) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.extenddftf2_callF)]. Qed.

Definition S_F2 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (a z Y FR BI e2 bits' : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 FR)) (Z_to_bv 64 (hi64 FR)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= bits' <= 53)%Z ->
xrel ws x (inring a z) -> X31 x -> (0 <= a < 2048)%Z -> (0 <= z < 2048)%Z ->
(Z.land (a + 4) MASK <> z -> inring a z (Z.land (a + 4) MASK)) ->
fin_K2 sign 1024 a z x 4 bits' Y FR BI e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (a + 4)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5cbe8) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_F2 : @S_F2 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_F2 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_F2)). Proof. unfold S_F2, QzQg.Mq0.S_F2; rewrite ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_xrel, ?gw_eq_dfinv, ?gw_eq_inring, ?gw_eq_X31; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_F2 : gw_eqs.

#[using="Type"] Lemma floatsitf_callsg : forall ra' sp' gp' tp' t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F' : bvmap 5 word) fc' (m : word -> option byte) (sg : Z),
mem_inv rsegs m -> (sg = 1 \/ sg = -1)%Z ->
evt rsegs (leaf2_post ra' sp' gp' tp' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' (f128_of_i32 sg) m)
(MS (mkR ra' sp' gp' tp' t0 t1 t2 s0 s1 (Z_to_bv 64 sg) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x589ac) fc' None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_leaf2_post__3; @gw_eq_leaf2_post__2; @gw_eq_leaf2_post]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.floatsitf_callsg) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.floatsitf_callsg)]. Qed.

Definition S_F1 : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (a z Y e2 : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z ->
xrel ws x (inring a z) -> X31 x -> (0 <= a < 2048)%Z -> (0 <= z < 2048)%Z ->
(Z.land (a + 4) MASK <> z -> inring a z (Z.land (a + 4) MASK)) ->
fin_K1 53 (-1074) sign 1024 zero0 a z x 4 Y e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 (a + 4)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x24
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5cafc) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_F1 : @S_F1 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_F1 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_F1)). Proof. unfold S_F1, QzQg.Mq0.S_F1; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_xrel, ?gw_eq_dfinv, ?gw_eq_inring, ?gw_eq_X31; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_F1 : gw_eqs.

#[using="Type"] Lemma lxor_sign_small : forall e, (-2^62 <= e < 2^62)%Z ->
Z.lxor (Z.land e 18446744073709551615) 9223372036854775808 = (e + 2^63)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.lxor_sign_small) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.lxor_sign_small)]. Qed.

#[using="Type"] Lemma clamp0_idiom : forall v, (-2^62 <= v < 2^62)%Z ->
Z.land (Z.land (0 - Z.b2z (9223372036854775808 <? Z.lxor (Z.land v 18446744073709551615) 9223372036854775808)) 18446744073709551615)
(Z.land v 18446744073709551615) = (if v <? 0 then 0 else v)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.clamp0_idiom) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.clamp0_idiom)]. Qed.

#[using="Type"] Lemma cb44_merge : forall m A pre (bs : list byte) (w : word),
rw_cells rsegs m A (pre ++ [CB 4 bs; C4 w]) -> rw_cells rsegs m A (pre ++ [CB 8 (bs ++ le4 w)]).
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.cb44_merge) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.cb44_merge)]. Qed.
Definition C1E9HI : Z := 0x401cdcd650000000.
Lemma gw_eq_C1E9HI : @C1E9HI = ltac:(GwInst.gw_term (@QzQg.Mq0.C1E9HI) (@C1E9HI)). Proof. unfold C1E9HI, QzQg.Mq0.C1E9HI; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_C1E9HI : gw_eqs.

Definition ainv (ws : list word) (x : list Z) (h w : bool) (a z i : Z) : Prop :=
xrel ws x (zone h w a z) /\ X31 x /\ (0 <= z < 2048)%Z /\ (h = false -> z + (4 - i) <= 2052)%Z /\ (i <= (z - a) mod 2048)%Z /\ (w = false -> a <= 60)%Z.
Lemma gw_eq_ainv : @ainv = ltac:(GwInst.gw_term (@QzQg.Mq0.ainv) (@ainv)). Proof. unfold ainv, QzQg.Mq0.ainv; rewrite ?gw_eq_xrel, ?gw_eq_zone, ?gw_eq_X31; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_ainv : gw_eqs.

Definition S_A69C : Prop := forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z Y e2 : Z) (f : nat) sres,
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 3 ->
df_asm_loop f a (mkAS 3 Y z x) = Some sres -> (2 <= f)%nat ->
fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 3)) x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5ca98) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_A69C : @S_A69C = ltac:(GwInst.gw_term (@QzQg.Mq0.S_A69C rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_A69C)). Proof. unfold S_A69C, QzQg.Mq0.S_A69C; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_dfinv, ?gw_eq_C1E9HI, ?gw_eq_ainv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_A69C : gw_eqs.

Definition S_A62C : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z Y e2 : Z) (f : nat) sres,
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 2 ->
df_asm_loop f a (mkAS 2 Y z x) = Some sres -> (3 <= f)%nat ->
fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 2)) (Z_to_bv 64 XA) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5ca28) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_A62C : @S_A62C = ltac:(GwInst.gw_term (@QzQg.Mq0.S_A62C rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_A62C)). Proof. unfold S_A62C, QzQg.Mq0.S_A62C; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_dfinv, ?gw_eq_C1E9HI, ?gw_eq_ainv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_A62C : gw_eqs.

Definition S_A5C4 : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z Y e2 : Z) (f : nat) sres,
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 1 ->
df_asm_loop f a (mkAS 1 Y z x) = Some sres -> (4 <= f)%nat ->
fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c9c0) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_A5C4 : @S_A5C4 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_A5C4 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_A5C4)). Proof. unfold S_A5C4, QzQg.Mq0.S_A5C4; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_dfinv, ?gw_eq_C1E9HI, ?gw_eq_ainv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_A5C4 : gw_eqs.

Definition fin_K0 (sign a z : Z) (x : list Z) (e2 : Z) : option Z := df_final a z x e2 53 (-1074) sign 1024 zero0 zero0.
Lemma gw_eq_fin_K0 : @fin_K0 = ltac:(GwInst.gw_term (@QzQg.Mq0.fin_K0) (@fin_K0)). Proof. unfold fin_K0, QzQg.Mq0.fin_K0; rewrite ?gw_eq_zero0; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_fin_K0 : gw_eqs.

Definition S_A568 : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z e2 xa : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 0 -> a <> z -> xa = znth x a ->
fin_K0 sign a z x e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 xa) x23 x24
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c964) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_A568 : @S_A568 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_A568 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_A568)). Proof. unfold S_A568, QzQg.Mq0.S_A568; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_dfinv, ?gw_eq_ainv, ?gw_eq_fin_K0; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_A568 : gw_eqs.

Definition S_A534 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z e2 S1 : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 0 -> a = z -> S1 = (4 * ((z + 1) mod 2048))%Z ->
fin_K0 sign a z x e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 ((z + 1) mod 2048)) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 x23 x24
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c930) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_A534 : @S_A534 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_A534 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_A534)). Proof. unfold S_A534, QzQg.Mq0.S_A534; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_dfinv, ?gw_eq_ainv, ?gw_eq_fin_K0; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_A534 : gw_eqs.

Definition SN324 (fo : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 i0 Z0 S1 A6 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat fo <= 4100)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (Z.of_nat fo <= 2000)%Z ->
(-2^26 + 18450 * Z.of_nat fo <= rp <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat fo)%Z ->
Z0 = ((z + 1) mod 2048)%Z -> S1 = (4 * Z0)%Z -> A6 = (XA + 4 * ((z - 1) mod 2048))%Z ->
df_dn_loop fo (mkDS rp a z e2 x i0) = Some s' ->
fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c720) fct None m (seg_rom rsegs)).
Lemma gw_eq_SN324 : @SN324 = ltac:(GwInst.gw_term (@QzQg.Mq0.SN324 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@SN324)). Proof. unfold SN324, QzQg.Mq0.SN324; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_xrel, ?gw_eq_dfinv, ?gw_eq_zone, ?gw_eq_X31, ?gw_eq_fin_K0; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_SN324 : gw_eqs.
Definition S_N324 : Prop := forall fo, SN324 fo.
Lemma gw_eq_S_N324 : @S_N324 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_N324 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_N324)). Proof. unfold S_N324, QzQg.Mq0.S_N324; rewrite ?gw_eq_SN324; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_N324 : gw_eqs.

Definition S_N2D4 : Prop := forall (fo : nat) m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 i0 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat fo <= 4100)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (Z.of_nat fo <= 2000)%Z ->
(-2^26 + 18450 * Z.of_nat fo <= rp <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat fo)%Z ->
df_dn_loop fo (mkDS rp a z e2 x i0) = Some s' ->
fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c6d0) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_N2D4 : @S_N2D4 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_N2D4 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_N2D4)). Proof. unfold S_N2D4, QzQg.Mq0.S_N2D4; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_xrel, ?gw_eq_dfinv, ?gw_eq_zone, ?gw_eq_X31, ?gw_eq_fin_K0; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_N2D4 : gw_eqs.

Definition up_K (sign rp a z e2 : Z) (x : list Z) : option Z :=
match df_dn_loop FUEL_SCALE (mkDS rp a z e2 x 0) with
| None => None
| Some s' => fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s')
end.
Lemma gw_eq_up_K : @up_K = ltac:(GwInst.gw_term (@QzQg.Mq0.up_K) (@up_K)). Proof. unfold up_K, QzQg.Mq0.up_K; rewrite ?gw_eq_fin_K0; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_up_K : gw_eqs.
Definition MAGIC : Z := 19342813113834067.
Lemma gw_eq_MAGIC : @MAGIC = ltac:(GwInst.gw_term (@QzQg.Mq0.MAGIC) (@MAGIC)). Proof. unfold MAGIC, QzQg.Mq0.MAGIC; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_MAGIC : gw_eqs.

Definition S_U1A8 : Prop := forall (fo : nat) m (x1 x5 x6 x7 x8 x9 x16 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z <= 2047)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> a <> z ->
(-2^20 <= rp <= 560)%Z -> (-2^20 + 29 * Z.of_nat fo <= e2 <= 0)%Z ->
df_up_loop fo (mkUS rp a z e2 x) = Some s' ->
up_K sign (us_rp s') (us_a s') (us_z s') (us_e2 s') (us_x s') = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c5a4) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_U1A8 : @S_U1A8 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_U1A8 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_U1A8)). Proof. unfold S_U1A8, QzQg.Mq0.S_U1A8; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_xrel, ?gw_eq_dfinv, ?gw_eq_zone, ?gw_eq_X31, ?gw_eq_up_K, ?gw_eq_MAGIC; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_U1A8 : gw_eqs.

#[using="Type"] Lemma df_dn_loop_step : forall n s, df_dn_loop (S n) s = match df_dn_body s with None => None | Some (inl s') => df_dn_loop n s' | Some (inr s') => Some s' end.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.df_dn_loop_step) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.df_dn_loop_step)]. Qed.
#[using="Type"] Lemma df_dni_loop_step : forall n a z x i, df_dni_loop (S n) a z x i =
if (i <? LD_B1B_DIG)%Z then match df_dni_body a z x i with inl i' => df_dni_loop n a z x i' | inr i' => Some i' end else Some i.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.df_dni_loop_step) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.df_dni_loop_step)]. Qed.
#[using="Type"] Lemma df_dnk_loop_step : forall n z sh s, df_dnk_loop (S n) z sh s = if negb (dk_k s =? z)%Z then df_dnk_loop n z sh (df_dnk_body z sh s) else Some s.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.df_dnk_loop_step) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.df_dnk_loop_step)]. Qed.
#[using="Type"] Lemma dn_carry_bound : forall sh tmp, (sh = 1 \/ sh = 9)%Z -> (0 <= tmp <= 2^sh - 1)%Z -> (0 <= Z.shiftr 1000000000 sh * tmp < 2^30)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.dn_carry_bound) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.dn_carry_bound)]. Qed.
#[using="Type"] Lemma shr_half : forall t sh, (0 <= t)%Z -> (1 <= sh)%Z -> (0 <= Z.shiftr t sh <= t / 2)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.shr_half) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.shr_half)]. Qed.
#[using="Type"] Lemma lor_lxor_zero : forall k a v, (0 <= k)%Z -> (0 <= a)%Z -> (0 <= v)%Z ->
Z.lor (Z.lxor k a) v = 0%Z <-> (k = a /\ v = 0%Z).
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.lor_lxor_zero) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.lor_lxor_zero)]. Qed.
#[using="Type"] Lemma lor_lxor_nonneg : forall k a v, (0 <= k)%Z -> (0 <= a)%Z -> (0 <= v)%Z -> (0 <= Z.lor (Z.lxor k a) v)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.lor_lxor_nonneg) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.lor_lxor_nonneg)]. Qed.
#[using="Type"] Lemma rp_upd : forall rp (c : bool),
Z_to_bv 64 (rp + Z.land (Z.land (Z.b2z c + -1) 18446744073709551615) 18446744073709551607) = Z_to_bv 64 (if c then rp else rp - 9)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.rp_upd) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.rp_upd)]. Qed.

#[using="Type"] Lemma dn_az_none : forall fo rp z e2 x i0, (0 <= z < 2048)%Z -> rp <> 36%Z -> df_dn_loop fo (mkDS rp z z e2 x i0) = None.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.dn_az_none) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.dn_az_none)]. Qed.

Definition S_NK : Prop := forall (fi : nat) m (x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x20 x22 x24 x25 x26 x27 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (x : list Z) (h w : bool) (k carry a i rp z sh e2 B : Z) (s1 : st_dnk),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft -> frm0 fct ->
xrel ws x (zone h w a z) -> X31 x ->
(0 <= a < 2048)%Z -> (0 <= z < 2048)%Z -> (0 <= k < 2048)%Z -> ((k - a) mod 2048 <= (z - a) mod 2048)%Z -> k <> z ->
(0 <= carry < 2^30)%Z -> (sh = 1 \/ sh = 9)%Z -> (B + 9 * Z.of_nat fi <= rp <= 560)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (-2^27 <= B)%Z -> (-2^21 <= e2 <= 2^21)%Z ->
df_dnk_loop fi z sh (mkDK k carry a i rp x) = Some s1 ->
(forall m' ws' b96' (x17' x28' x29' x30' x31' : word) (w' : bool),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96' ev ws' sign fR ->
xrel ws' (dk_x s1) (zone h w' (dk_a s1) z) -> X31 (dk_x s1) ->
(0 <= dk_a s1 < 2048)%Z -> (0 <= dk_carry s1 < 2^30)%Z -> (B <= dk_rp s1 <= 560)%Z -> (w' = false -> 9 * dk_a s1 + dk_rp s1 <= 560)%Z -> dk_k s1 = z ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 (dk_carry s1)) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17'
(Z_to_bv 64 z) (Z_to_bv 64 (dk_a s1)) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 (dk_rp s1)) x24 x25 x26 x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0x5c880) fct None m' (seg_rom rsegs))) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 carry) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (2^sh - 1))
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 (Z_to_bv 64 k) x29 x30 x31)
Ft (Z_to_bv 64 0x5c84c) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_NK : @S_NK = ltac:(GwInst.gw_term (@QzQg.Mq0.S_NK rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_NK)). Proof. unfold S_NK, QzQg.Mq0.S_NK; rewrite ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_xrel, ?gw_eq_dfinv, ?gw_eq_zone, ?gw_eq_X31; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_NK : gw_eqs.

Definition S_N484 : Prop := forall (fo : nat), SN324 fo ->
forall (s1 : st_dnk) m (x1 x10 x11 x12 x13 x14 x15 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (h w : bool) (rp z e2 Z0 S1 A6 sh : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws (dk_x s1) (zone h w (dk_a s1) z) -> X31 (dk_x s1) ->
(0 <= dk_a s1 < 2048)%Z -> (0 <= dk_carry s1 < 2^30)%Z -> dk_k s1 = z -> (sh = 1 \/ sh = 9)%Z ->
(0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat (S fo) <= 4100)%Z -> (w = false -> 9 * dk_a s1 + dk_rp s1 <= 560)%Z -> (Z.of_nat (S fo) <= 2000)%Z ->
(-2^26 + 18450 * Z.of_nat (S fo) <= rp <= 560)%Z -> (rp - 18450 <= dk_rp s1 <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat (S fo))%Z ->
Z0 = ((z + 1) mod 2048)%Z -> S1 = (4 * Z0)%Z -> A6 = (XA + 4 * ((z - 1) mod 2048))%Z ->
(let 'mkDK _ carry a1 i rp1 xx := s1 in
let '(z', x') := if nz carry then
if negb ((z + 1) mod 2048 =? a1)%Z then ((z + 1) mod 2048, zupd xx z carry)%Z
else (z, zupd xx ((z - 1) mod 2048) (Z.lor (znth xx ((z - 1) mod 2048)) 1))%Z
else (z, xx) in
df_dn_loop fo (mkDS rp1 a1 z' (e2 + sh) x' i) = Some s') ->
fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 (dk_carry s1)) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17
(Z_to_bv 64 z) (Z_to_bv 64 (dk_a s1)) x20 (Z_to_bv 64 (e2 + sh)) x22 (Z_to_bv 64 (dk_rp s1)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c880) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_N484 : @S_N484 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_N484 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_N484)). Proof. unfold S_N484, QzQg.Mq0.S_N484; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_xrel, ?gw_eq_dfinv, ?gw_eq_zone, ?gw_eq_X31, ?gw_eq_fin_K0, ?gw_eq_SN324; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_N484 : gw_eqs.

Definition S_N3E8 : Prop := forall (fo : nat), SN324 fo ->
forall (iq : Z) m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 Z0 S1 A6 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat (S fo) <= 4100)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (Z.of_nat (S fo) <= 2000)%Z ->
(-2^26 + 18450 * Z.of_nat (S fo) <= rp <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat (S fo))%Z ->
Z0 = ((z + 1) mod 2048)%Z -> S1 = (4 * Z0)%Z -> A6 = (XA + 4 * ((z - 1) mod 2048))%Z -> a <> z ->
match
match df_dnk_loop FUEL_RING z (if 45 <? rp then 9%Z else 1%Z) (mkDK a 0 a iq rp x) with
| Some (mkDK _ carry a1 i rp1 xx) =>
let '(z', x') := (if nz carry then
if negb ((z + 1) mod 2048 =? a1)%Z then ((z + 1) mod 2048, zupd xx z carry)%Z
else (z, zupd xx ((z - 1) mod 2048) (Z.lor (znth xx ((z - 1) mod 2048)) 1))%Z
else (z, xx)) in
Some (inl (mkDS rp1 a1 z' (e2 + (if 45 <? rp then 9%Z else 1%Z)) x' i))
| None => None
end
with
| Some (inl s'') => df_dn_loop fo s''
| Some (inr s'') => Some s''
| None => None
end = Some s' ->
fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c7e4) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_N3E8 : @S_N3E8 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_N3E8 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_N3E8)). Proof. unfold S_N3E8, QzQg.Mq0.S_N3E8; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_xrel, ?gw_eq_dfinv, ?gw_eq_zone, ?gw_eq_X31, ?gw_eq_fin_K0, ?gw_eq_SN324; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_N3E8 : gw_eqs.

#[using="Type"] Lemma df_up_loop_step : forall n s, df_up_loop (S n) s = if df_up_cond s then match df_up_body s with None => None | Some s' => df_up_loop n s' end else Some s.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.df_up_loop_step) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.df_up_loop_step)]. Qed.
#[using="Type"] Lemma df_upk_loop_step : forall n a s, df_upk_loop (S n) a s = match df_upk_body a s with inl s' => df_upk_loop n a s' | inr s' => Some s' end.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.df_upk_loop_step) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.df_upk_loop_step)]. Qed.
#[using="Type"] Lemma mod_add2047 : forall u, ((u + 2047) mod 2048 = (u - 1) mod 2048)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.mod_add2047) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.mod_add2047)]. Qed.

#[using="Type"] Lemma magic_div_1e9 : forall tmp, (0 <= tmp < 2^61)%Z ->
(Z.shiftr ((Z.shiftr tmp 9 * MAGIC) / 2^64) 11 = tmp / 1000000000)%Z.
Proof. rewrite ?gw_eq_MAGIC; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.magic_div_1e9) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.magic_div_1e9)]. Qed.

#[using="Type"] Lemma magic_div_1e9_reg : forall tmp, (0 <= tmp < 2^61)%Z ->
Z.shiftr (Z.land (Z.shiftr (Z.shiftr tmp 9 * Z.land MAGIC 18446744073709551615) 64) 18446744073709551615) 11 = (tmp / 1000000000)%Z.
Proof. rewrite ?gw_eq_MAGIC; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.magic_div_1e9_reg) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.magic_div_1e9_reg)]. Qed.
#[using="Type"] Lemma u32_id : forall v, (0 <= v < 2^32)%Z -> u32 v = v.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.u32_id) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.u32_id)]. Qed.
#[using="Type"] Lemma inring_front : forall a z i, (0 <= a < 2048)%Z -> (0 <= i < 2048)%Z -> (0 <= z < 2048)%Z ->
inring ((a - 1) mod 2048) z i -> i <> ((a - 1) mod 2048)%Z -> z <> ((a - 1) mod 2048)%Z -> inring a z i.
Proof. rewrite ?gw_eq_inring; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.inring_front) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.inring_front)]. Qed.

Definition S_UK : Prop := forall (n : nat) m (x1 x5 x6 x8 x9 x11 x15 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (x : list Z) (h w : bool) (k carry a z : Z) (s1 : st_upk),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft -> frm0 fct ->
xrel ws x (zone h w a z) -> X31 x ->
(0 <= a < 2048)%Z -> (0 <= z < 2048)%Z -> (0 <= k < 2048)%Z -> inring a z k ->
(0 <= carry < 2^31)%Z ->
df_upk_loop n a (mkUK k carry z x) = Some s1 ->
(forall m' ws' (x7' x18' x29' x30' x31' : word) (h' : bool),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
xrel ws' (uk_x s1) (zone h' w a (uk_z s1)) -> X31 (uk_x s1) ->
uk_k s1 = a -> (0 <= uk_carry s1 < 2^31)%Z -> (0 <= uk_z s1 < 2048)%Z -> (h' = false -> h = false /\ uk_z s1 <= z)%Z -> a <> uk_z s1 ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 (Z_to_bv 64 (uk_z s1)) x7' x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 (uk_carry s1)) x17
x18' (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 ((uk_z s1 - 1) mod 2048)) x29' x30' x31')
Ft (Z_to_bv 64 0x5c5b4) fct None m' (seg_rom rsegs))) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 (Z_to_bv 64 k) x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 carry) x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c5e8) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_UK : @S_UK = ltac:(GwInst.gw_term (@QzQg.Mq0.S_UK rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_UK)). Proof. unfold S_UK, QzQg.Mq0.S_UK; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_xrel, ?gw_eq_dfinv, ?gw_eq_inring, ?gw_eq_zone, ?gw_eq_X31, ?gw_eq_MAGIC; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_UK : gw_eqs.

Definition SU1C4 (fo : nat) : Prop := forall m (x1 x6 x7 x8 x9 x16 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z <= 2047)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> a <> z ->
(-2^20 <= rp <= 560)%Z -> (-2^20 + 29 * Z.of_nat fo <= e2 <= 0)%Z ->
df_up_loop fo (mkUS rp a z e2 x) = Some s' ->
up_K sign (us_rp s') (us_a s') (us_z s') (us_e2 s') (us_x s') = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 rp) x6 x7 x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16 (Z_to_bv 64 (XA + 4 * a))
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c5c0) fct None m (seg_rom rsegs)).
Lemma gw_eq_SU1C4 : @SU1C4 = ltac:(GwInst.gw_term (@QzQg.Mq0.SU1C4 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@SU1C4)). Proof. unfold SU1C4, QzQg.Mq0.SU1C4; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_xrel, ?gw_eq_dfinv, ?gw_eq_zone, ?gw_eq_X31, ?gw_eq_up_K, ?gw_eq_MAGIC; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_SU1C4 : gw_eqs.
Definition S_U1C4 : Prop := forall fo, SU1C4 fo.
Lemma gw_eq_S_U1C4 : @S_U1C4 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_U1C4 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_U1C4)). Proof. unfold S_U1C4, QzQg.Mq0.S_U1C4; rewrite ?gw_eq_SU1C4; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_U1C4 : gw_eqs.

Definition S_T : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (rp kz : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (inring 0 kz) -> X31 x -> (1 <= kz <= 2046)%Z -> znth x 0 <> 0%Z -> (-2^15 <= rp <= 537)%Z ->
dfK_tz 53 (-1074) sign fR rp kz x = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c428) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_T : @S_T = ltac:(GwInst.gw_term (@QzQg.Mq0.S_T rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_T)). Proof. unfold S_T, QzQg.Mq0.S_T; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_xrel, ?gw_eq_dfinv, ?gw_eq_inring, ?gw_eq_X31; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_T : gw_eqs.

Definition S_DD0 : Prop := forall m (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (X Y : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = f128_mul X Y ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c1cc) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_DD0 : @S_DD0 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_DD0 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_DD0)). Proof. unfold S_DD0, QzQg.Mq0.S_DD0; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_dfinv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_DD0 : gw_eqs.

Definition S_DD24 : Prop := forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (X u : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(0 <= u < 2^31)%Z -> yR = f128_mul X (f128_of_u32 u) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 u) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c120) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_DD24 : @S_DD24 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_DD24 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_DD24)). Proof. unfold S_DD24, QzQg.Mq0.S_DD24; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_dfinv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_DD24 : gw_eqs.

Definition S_M : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (rp lnz kz : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (inring 0 kz) -> X31 x -> (1 <= kz <= 2046)%Z -> znth x 0 <> 0%Z -> (1 <= lnz < 2^31)%Z -> (-1300 <= rp <= 537)%Z ->
dfK_mid 53 (-1074) sign fR rp lnz kz x = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 lnz) x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c258) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_M : @S_M = ltac:(GwInst.gw_term (@QzQg.Mq0.S_M rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_M)). Proof. unfold S_M, QzQg.Mq0.S_M; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_xrel, ?gw_eq_dfinv, ?gw_eq_inring, ?gw_eq_X31; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_M : gw_eqs.

Definition digz (k j : Z) (i : Z) : Prop := (i < k)%Z \/ i = 0%Z \/ (i = k /\ j <> 0%Z).
Lemma gw_eq_digz : @digz = ltac:(GwInst.gw_term (@QzQg.Mq0.digz) (@digz)). Proof. unfold digz, QzQg.Mq0.digz; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_digz : gw_eqs.

Definition S_P : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 ev ws sign k c (x : list Z) (lrp lnz j kz : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (digz kz j) -> X31 x ->
(0 <= j <= 8)%Z -> (0 <= kz <= 2045)%Z -> znth x 0 <> 0%Z -> (1 <= lnz < 2^31)%Z -> (-1300 <= lrp <= 537)%Z ->
(j <> 0%Z -> znth x kz < 10 ^ j)%Z -> (kz = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) -> (kz = 2045%Z -> j = 0%Z) ->
dfK_pad 53 (-1074) sign fR lrp lnz j kz x = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c1dc) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_P : @S_P = ltac:(GwInst.gw_term (@QzQg.Mq0.S_P rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_P)). Proof. unfold S_P, QzQg.Mq0.S_P; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_xrel, ?gw_eq_dfinv, ?gw_eq_X31, ?gw_eq_digz; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_P : gw_eqs.

Definition S_R : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) ev ws sign k c (x : list Z) (lrp dc lnz j kz : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (digz kz j) -> X31 x ->
(0 <= j <= 8)%Z -> (0 <= kz <= 2045)%Z -> (0 <= dc < 2^31)%Z -> (0 <= lnz < 2^31)%Z -> (znth x 0 <> 0%Z -> 1 <= lnz)%Z ->
(j <> 0%Z -> znth x kz < 10 ^ j)%Z -> (kz = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) -> (kz = 2045%Z -> j = 0%Z) -> (-2^62 <= lrp < 2^62)%Z ->
(znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
dfK_rng 53 (-1074) sign fR lrp dc lnz j kz x = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c0e0) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_R : @S_R = ltac:(GwInst.gw_term (@QzQg.Mq0.S_R rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_R)). Proof. unfold S_R, QzQg.Mq0.S_R; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_xrel, ?gw_eq_dfinvG, ?gw_eq_X31, ?gw_eq_digz; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_R : gw_eqs.

Definition dig_facts (ws : list word) (x : list Z) (j kz dc lnz : Z) : Prop :=
xrel ws x (digz kz j) /\ X31 x /\
(0 <= j <= 8)%Z /\ (0 <= kz <= 2045)%Z /\ (0 <= dc < 2^31)%Z /\ (0 <= lnz < 2^31)%Z /\ (znth x 0 <> 0%Z -> 1 <= lnz)%Z /\
(j <> 0%Z -> znth x kz < 10 ^ j)%Z /\ (kz = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) /\ (kz = 2045%Z -> j = 0%Z).
Lemma gw_eq_dig_facts : @dig_facts = ltac:(GwInst.gw_term (@QzQg.Mq0.dig_facts) (@dig_facts)). Proof. unfold dig_facts, QzQg.Mq0.dig_facts; rewrite ?gw_eq_xrel, ?gw_eq_X31, ?gw_eq_digz; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_dig_facts : gw_eqs.

Definition S_C38 : Prop := forall m (x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) ev ws sign kmin c (x : list Z) (f : shfile) (lrp dc lnz j kz gotdig ng : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (0 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
dig_facts ws x j kz dc lnz -> (znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
(0 <= gotdig <= 1)%Z -> ng = Z.b2z (gotdig =? 0)%Z -> (-2^62 <= lrp < 2^62)%Z ->
(if negb (nz gotdig) then Some (sh_lim0 f, f128_of_i32 0) else dfK_rng 53 (-1074) sign f lrp dc lnz j kz x) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10 (Z_to_bv 64 ng) x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c034) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_C38 : @S_C38 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_C38 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_C38)). Proof. unfold S_C38, QzQg.Mq0.S_C38; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_dfinvG, ?gw_eq_dig_facts; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_C38 : gw_eqs.

Definition S_C2C : Prop := forall m (x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) ev ws sign kmin c (x : list Z) (f : shfile) (lrp dc lnz j kz gotdig ng : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> sh_shlim_neg f = false ->
dig_facts ws x j kz dc lnz -> (znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
(0 <= gotdig <= 1)%Z -> ng = Z.b2z (gotdig =? 0)%Z -> (-2^62 <= lrp < 2^62)%Z ->
(if negb (nz gotdig) then Some (sh_lim0 (sh_unget f), f128_of_i32 0) else dfK_rng 53 (-1074) sign (sh_unget f) lrp dc lnz j kz x) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10 (Z_to_bv 64 ng) x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5c028) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_C2C : @S_C2C = ltac:(GwInst.gw_term (@QzQg.Mq0.S_C2C rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_C2C)). Proof. unfold S_C2C, QzQg.Mq0.S_C2C; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_dfinvG, ?gw_eq_dig_facts; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_C2C : gw_eqs.

Definition S_E : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) ev ws sign kmin c (x : list Z) (f : shfile) (lrp dc lnz j kz gotdig gotrad : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
dig_facts ws x j kz dc lnz -> (znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
(0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z -> (- 2^31 <= lrp < 2^31)%Z ->
dfK_exp fuelc 53 (-1074) sign pok (mkDL f c j kz lrp dc lnz gotdig gotrad x) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 x23 (Z_to_bv 64 kz) (Z_to_bv 64 lrp) (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5beb0) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_E : @S_E = ltac:(GwInst.gw_term (@QzQg.Mq0.S_E rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_E)). Proof. unfold S_E, QzQg.Mq0.S_E; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_dfinvG, ?gw_eq_dig_facts; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_E : gw_eqs.

Definition digI (ws : list word) (x : list Z) (f : shfile) (c j k lrp dc lnz gotdig gotrad : Z) : Prop :=
xrel ws x (digz k j) /\ X31 x /\ (0 <= j <= 8)%Z /\ (0 <= k)%Z /\ (9 * k + j <= dc)%Z /\
(0 <= dc <= sh_rpos f)%Z /\ (c <> (-1)%Z -> dc + 1 <= sh_rpos f)%Z /\
(0 <= lnz <= dc)%Z /\ (znth x 0 <> 0%Z -> 1 <= lnz)%Z /\ (j <> 0%Z -> znth x k < 10 ^ j)%Z /\ (k = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) /\
(- 2^31 <= lrp < 2^31)%Z /\ (0 <= gotdig <= 1)%Z /\ (0 <= gotrad <= 1)%Z /\
(k <= 2045)%Z /\ (k = 2045%Z -> j = 0%Z).
Lemma gw_eq_digI : @digI = ltac:(GwInst.gw_term (@QzQg.Mq0.digI) (@digI)). Proof. unfold digI, QzQg.Mq0.digI; rewrite ?gw_eq_xrel, ?gw_eq_X31, ?gw_eq_digz; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_digI : gw_eqs.

Definition SDn (n : nat) : Prop := forall m (x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
j0 ev ws sign kmin c (x : list Z) (f : shfile) (j k lrp dc lnz gotdig gotrad : Z) (s' : st_dig),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
digI ws x f c j k lrp dc lnz gotdig gotrad ->
(isdigitc c || (c =? 46))%Z = true ->
df_dig_loop n (mkDL f c j k lrp dc lnz gotdig gotrad x) = Some s' ->
dfK_exp fuelc 53 (-1074) sign pok s' = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 dc) (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) (Z_to_bv 64 (Z.b2z (c =? 46)%Z)) x13 x14 x15 x16 x17
(Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5bf68) fct None m (seg_rom rsegs)).
Lemma gw_eq_SDn : @SDn = ltac:(GwInst.gw_term (@QzQg.Mq0.SDn rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@SDn)). Proof. unfold SDn, QzQg.Mq0.SDn; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_dfinv, ?gw_eq_digI; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_SDn : gw_eqs.
Definition S_D : Prop := forall n, SDn n.
Lemma gw_eq_S_D : @S_D = ltac:(GwInst.gw_term (@QzQg.Mq0.S_D rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_D)). Proof. unfold S_D, QzQg.Mq0.S_D; rewrite ?gw_eq_SDn; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_D : gw_eqs.

Definition winv (m : word -> option byte) (j0 : list byte) (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) (ev : word)
(ws : list word) (f : shfile) : Prop :=
finv m /\ framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m
/\ u32arr rsegs m XA ws /\ length ws = 2048%nat /\ rw_cells rsegs m Fp (rf_cells T p true f J).
Lemma gw_eq_winv : @winv = ltac:(GwInst.gw_term (@QzQg.Mq0.winv rsegs got_ssp RATP ssp_guard) (@winv)). Proof. unfold winv, QzQg.Mq0.winv; rewrite ?gw_eq_finv, ?gw_eq_framL; ltac2:(GwEq.gw_rw [[@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_winv : gw_eqs.
#[using="Type"] Lemma winv_dfinvG : forall m j0 w16 w24 w80 b96 ev ws sign f,
winv m j0 (Z_to_bv 64 1021) w16 w24 (Z_to_bv 64 1) (Z_to_bv 64 (-1074)) (Z_to_bv 64 1074) (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws f
= dfinvG m j0 w16 w24 w80 b96 ev ws sign f.
Proof. rewrite ?gw_eq_dfinvG, ?gw_eq_winv; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.winv_dfinvG) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.winv_dfinvG)]. Qed.

Definition X0 : list Z := zupd (zrepeat 0 KMAX) 0 0.
Lemma gw_eq_X0 : @X0 = ltac:(GwInst.gw_term (@QzQg.Mq0.X0) (@X0)). Proof. unfold X0, QzQg.Mq0.X0; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_X0 : gw_eqs.

Definition fch (c : Z) : Prop := is_numch c = true \/ c = 0%Z \/ c = (-1)%Z.
Lemma gw_eq_fch : @fch = ltac:(GwInst.gw_term (@QzQg.Mq0.fch) (@fch)). Proof. unfold fch, QzQg.Mq0.fch; ltac2:(GwEq.gw_rw [[@gw_eq_is_numch__3; @gw_eq_is_numch__2; @gw_eq_is_numch]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_fch : gw_eqs.

Definition S_B0C : Prop := forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x22 x24 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (lrp gotdig gotrad : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 b96 ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> wval ws 0 = 0%Z ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (- sh_rpos f <= lrp <= 0)%Z -> (0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z ->
(isdigitc c || (c =? 46))%Z = true ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 46) x24 (Z_to_bv 64 lrp) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5bf08) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_B0C : @S_B0C = ltac:(GwInst.gw_term (@QzQg.Mq0.S_B0C rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_B0C)). Proof. unfold S_B0C, QzQg.Mq0.S_B0C; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_dfinvG, ?gw_eq_X0; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_wval__3; @gw_eq_wval__2; @gw_eq_wval]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_B0C : gw_eqs.

Definition S_A9C : Prop := forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x22 x24 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (lrp gotdig gotrad : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 b96 ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> wval ws 0 = 0%Z ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (- sh_rpos f <= lrp <= 0)%Z -> (0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z ->
c <> 46%Z ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 46) x24 (Z_to_bv 64 lrp) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5be98) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_A9C : @S_A9C = ltac:(GwInst.gw_term (@QzQg.Mq0.S_A9C rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_A9C)). Proof. unfold S_A9C, QzQg.Mq0.S_A9C; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_dfinvG, ?gw_eq_X0; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_wval__3; @gw_eq_wval__2; @gw_eq_wval]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_A9C : gw_eqs.

Definition S_A44 : Prop := forall m (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w48 w80 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (lrp gotdig : Z),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (- sh_rpos f <= lrp <= 0)%Z -> (0 <= gotdig <= 1)%Z -> c <> 48%Z ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 lrp 0 0 gotdig 1 X0) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) x20 (Z_to_bv 64 Fp) x22 x23 (Z_to_bv 64 1) (Z_to_bv 64 lrp) (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5be40) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_A44 : @S_A44 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_A44 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_A44)). Proof. unfold S_A44, QzQg.Mq0.S_A44; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_winv, ?gw_eq_X0; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_A44 : gw_eqs.

#[using="Type"] Lemma df_dig_loop_step : forall n s, df_dig_loop (S n) s = if df_dig_cond s then match df_dig_body s with inl s' => df_dig_loop n s' | inr s' => Some s' end else Some s.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.df_dig_loop_step) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.df_dig_loop_step)]. Qed.
#[using="Type"] Lemma df_rz_loop_step : forall n g l c f, df_rz_loop (S n) (g, l, c, f) =
(if c =? 48 then df_rz_loop n (1, l - 1, fst (sh_getc f), snd (sh_getc f)) else Some (g, l, c, f))%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.df_rz_loop_step) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.df_rz_loop_step)]. Qed.
#[using="Type"] Lemma df_lz_loop_step : forall n g c f, df_lz_loop (S n) (g, c, f) =
(if c =? 48 then df_lz_loop n (1, fst (sh_getc f), snd (sh_getc f)) else Some (g, c, f))%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq0.df_lz_loop_step) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq0.df_lz_loop_step)]. Qed.

Definition SRZn (n : nat) : Prop := forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w48 w80 : word) (b96 : list byte) ev ws sign kmin (f : shfile) (lrp g : Z) (g' lrp' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws f ->
RFJ' kmin 48 f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(1 - sh_rpos f <= lrp <= 0)%Z ->
df_rz_loop n (g, lrp, 48, f)%Z = Some (g', lrp', c', f') ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f' c' 0 0 lrp' 0 0 g' 1 X0) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 Fp) x22 x23 (Z_to_bv 64 1) (Z_to_bv 64 lrp) (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5be1c) fct None m (seg_rom rsegs)).
Lemma gw_eq_SRZn : @SRZn = ltac:(GwInst.gw_term (@QzQg.Mq0.SRZn rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@SRZn)). Proof. unfold SRZn, QzQg.Mq0.SRZn; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_winv, ?gw_eq_X0; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_SRZn : gw_eqs.
Definition S_RZ : Prop := forall n, SRZn n.
Lemma gw_eq_S_RZ : @S_RZ = ltac:(GwInst.gw_term (@QzQg.Mq0.S_RZ rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_RZ)). Proof. unfold S_RZ, QzQg.Mq0.S_RZ; rewrite ?gw_eq_SRZn; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_RZ : gw_eqs.

Definition S_9EC : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (gotdig : Z) (g' lrp' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (0 <= gotdig <= 1)%Z ->
df_rz_loop fuelc (gotdig, 0, c, f)%Z = Some (g', lrp', c', f') ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f' c' 0 0 lrp' 0 0 g' 1 X0) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 gotdig) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5bde8) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_9EC : @S_9EC = ltac:(GwInst.gw_term (@QzQg.Mq0.S_9EC rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_9EC)). Proof. unfold S_9EC, QzQg.Mq0.S_9EC; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_winv, ?gw_eq_X0; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_9EC : gw_eqs.

Definition S_A64 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 46%Z ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 0 0 0 1 0 X0) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5be60) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_A64 : @S_A64 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_A64 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_A64)). Proof. unfold S_A64, QzQg.Mq0.S_A64; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_winv, ?gw_eq_X0; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_A64 : gw_eqs.

Definition S_7F4 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 46%Z ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 0 0 0 0 0 X0) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5bbf0) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_7F4 : @S_7F4 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_7F4 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_7F4)). Proof. unfold S_7F4, QzQg.Mq0.S_7F4; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_winv, ?gw_eq_X0; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_7F4 : gw_eqs.

Definition S_9C8 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 48%Z ->
dfK_rz fuelc 53 (-1074) sign pok 1 c f = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 1021) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5bdc4) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_9C8 : @S_9C8 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_9C8 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_9C8)). Proof. unfold S_9C8, QzQg.Mq0.S_9C8; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_winv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_9C8 : gw_eqs.

Definition SLZn (n : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin (f : shfile) (g : Z) (g' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin 48 f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
df_lz_loop n (g, 48, f)%Z = Some (g', c', f') ->
dfK_rz fuelc 53 (-1074) sign pok g' c' f' = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 1021) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5bda8) fct None m (seg_rom rsegs)).
Lemma gw_eq_SLZn : @SLZn = ltac:(GwInst.gw_term (@QzQg.Mq0.SLZn rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@SLZn)). Proof. unfold SLZn, QzQg.Mq0.SLZn; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_winv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_SLZn : gw_eqs.
Definition S_LZ : Prop := forall n, SLZn n.
Lemma gw_eq_S_LZ : @S_LZ = ltac:(GwInst.gw_term (@QzQg.Mq0.S_LZ rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_LZ)). Proof. unfold S_LZ, QzQg.Mq0.S_LZ; rewrite ?gw_eq_SLZn; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_LZ : gw_eqs.

Definition S_990 : Prop := forall (n : nat) m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (g' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z ->
df_lz_loop n (1, c, f)%Z = Some (g', c', f') ->
dfK_rz fuelc 53 (-1074) sign pok g' c' f' = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5bd8c) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_990 : @S_990 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_990 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_990)). Proof. unfold S_990, QzQg.Mq0.S_990; rewrite ?gw_eq_ctx_all, ?gw_eq_zero0, ?gw_eq_Fok, ?gw_eq_winv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_990 : gw_eqs.

Definition S_848 : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (2 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
decfloat fuelc (sh_unget f) 48 53 (-1074) sign pok = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5bc44) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_848 : @S_848 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_848 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_848)). Proof. unfold S_848, QzQg.Mq0.S_848; rewrite ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_winv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_848 : gw_eqs.

Definition S_6F8 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 48%Z ->
decfloat fuelc f c 53 (-1074) sign pok = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5baf4) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_6F8 : @S_6F8 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_6F8 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_6F8)). Proof. unfold S_6F8, QzQg.Mq0.S_6F8; rewrite ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_winv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_6F8 : gw_eqs.

Definition FS_tail (sign c : Z) (f : shfile) : option (shfile * Z) :=
if (c =? 48)%Z then
let '(c2, f2) := sh_getc f in
if (Z.lor c2 32 =? 120)%Z then None else decfloat fuelc (sh_unget f2) 48 53 (-1074) sign pok
else decfloat fuelc f c 53 (-1074) sign pok.
Lemma gw_eq_FS_tail : @FS_tail = ltac:(GwInst.gw_term (@QzQg.Mq0.FS_tail) (@FS_tail)). Proof. unfold FS_tail, QzQg.Mq0.FS_tail; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_FS_tail : gw_eqs.

Definition S_618 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z ->
FS_tail sign c f = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x5ba14) fct None m (seg_rom rsegs)).
Lemma gw_eq_S_618 : @S_618 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_618 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_618)). Proof. unfold S_618, QzQg.Mq0.S_618; rewrite ?gw_eq_ctx_all, ?gw_eq_Fok, ?gw_eq_winv, ?gw_eq_FS_tail; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_S_618 : gw_eqs.
End Floatscan.
Lemma gw_eq_ctx_all__2 : @ctx_all = ltac:(GwInst.gw_term (@QzQg.Mq0.ctx_all) (@ctx_all)). Proof. unfold ctx_all, QzQg.Mq0.ctx_all; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ctx_all__2 : gw_eqs.
Lemma gw_eq_Wfs__2 : @Wfs = ltac:(GwInst.gw_term (@QzQg.Mq0.Wfs RATP) (@Wfs)). Proof. unfold Wfs, QzQg.Mq0.Wfs; rewrite ?gw_eq_RERRNO, ?gw_eq_FS_DEPTH; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_Wfs__2 : gw_eqs.
Lemma gw_eq_zero0__2 : @zero0 = ltac:(GwInst.gw_term (@QzQg.Mq0.zero0) (@zero0)). Proof. unfold zero0, QzQg.Mq0.zero0; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_zero0__2 : gw_eqs.
Lemma gw_eq_FokR__2 : @FokR = ltac:(GwInst.gw_term (@QzQg.Mq0.FokR) (@FokR)). Proof. unfold FokR, QzQg.Mq0.FokR; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FokR__2 : gw_eqs.
Lemma gw_eq_Fok__2 : @Fok = ltac:(GwInst.gw_term (@QzQg.Mq0.Fok) (@Fok)). Proof. unfold Fok, QzQg.Mq0.Fok; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_Fok__2 : gw_eqs.
Lemma gw_eq_fs_post__2 : @fs_post = ltac:(GwInst.gw_term (@QzQg.Mq0.fs_post rsegs got_ssp RATP STRING_READ ssp_guard) (@fs_post)). Proof. unfold fs_post, QzQg.Mq0.fs_post; rewrite ?gw_eq_RERRNO, ?gw_eq_FS_DEPTH, ?gw_eq_Wfs__2, ?gw_eq_FokR__2; ltac2:(GwEq.gw_rw [[@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_fs_post__2 : gw_eqs.
Lemma gw_eq_hi_cells__2 : @hi_cells = ltac:(GwInst.gw_term (@QzQg.Mq0.hi_cells) (@hi_cells)). Proof. unfold hi_cells, QzQg.Mq0.hi_cells; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_hi_cells__2 : gw_eqs.
Lemma gw_eq_finv__2 : @finv = ltac:(GwInst.gw_term (@QzQg.Mq0.finv rsegs got_ssp RATP ssp_guard) (@finv)). Proof. unfold finv, QzQg.Mq0.finv; rewrite ?gw_eq_FS_DEPTH, ?gw_eq_Wfs__2, ?gw_eq_hi_cells__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_finv__2 : gw_eqs.
Lemma gw_eq_framL__2 : @framL = ltac:(GwInst.gw_term (@QzQg.Mq0.framL rsegs RATP) (@framL)). Proof. unfold framL, QzQg.Mq0.framL; rewrite ?gw_eq_RERRNO; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_framL__2 : gw_eqs.
Lemma gw_eq_xrel__2 : @xrel = ltac:(GwInst.gw_term (@QzQg.Mq0.xrel) (@xrel)). Proof. unfold xrel, QzQg.Mq0.xrel; ltac2:(GwEq.gw_rw [[@gw_eq_wval__3; @gw_eq_wval__2; @gw_eq_wval]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_xrel__2 : gw_eqs.
Lemma gw_eq_hide__2 : @hide = ltac:(GwInst.gw_term (@QzQg.Mq0.hide) (@hide)). Proof. unfold hide, QzQg.Mq0.hide; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_hide__2 : gw_eqs.
Lemma gw_eq_hide2__2 : @hide2 = ltac:(GwInst.gw_term (@QzQg.Mq0.hide2) (@hide2)). Proof. unfold hide2, QzQg.Mq0.hide2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_hide2__2 : gw_eqs.
Lemma gw_eq_dfinv__2 : @dfinv = ltac:(GwInst.gw_term (@QzQg.Mq0.dfinv rsegs got_ssp RATP ssp_guard) (@dfinv)). Proof. unfold dfinv, QzQg.Mq0.dfinv; rewrite ?gw_eq_finv__2, ?gw_eq_framL__2; ltac2:(GwEq.gw_rw [[@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_dfinv__2 : gw_eqs.
Lemma gw_eq_dfinvG__2 : @dfinvG = ltac:(GwInst.gw_term (@QzQg.Mq0.dfinvG rsegs got_ssp RATP ssp_guard) (@dfinvG)). Proof. unfold dfinvG, QzQg.Mq0.dfinvG; rewrite ?gw_eq_finv__2, ?gw_eq_framL__2; ltac2:(GwEq.gw_rw [[@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_dfinvG__2 : gw_eqs.
Lemma gw_eq_inring__2 : @inring = ltac:(GwInst.gw_term (@QzQg.Mq0.inring) (@inring)). Proof. unfold inring, QzQg.Mq0.inring; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_inring__2 : gw_eqs.
Lemma gw_eq_zone__2 : @zone = ltac:(GwInst.gw_term (@QzQg.Mq0.zone) (@zone)). Proof. unfold zone, QzQg.Mq0.zone; rewrite ?gw_eq_inring__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_zone__2 : gw_eqs.
Lemma gw_eq_X31__2 : @X31 = ltac:(GwInst.gw_term (@QzQg.Mq0.X31) (@X31)). Proof. unfold X31, QzQg.Mq0.X31; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_X31__2 : gw_eqs.
Lemma gw_eq_S_F3__2 : @S_F3 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_F3 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_F3)). Proof. unfold S_F3, QzQg.Mq0.S_F3; rewrite ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_dfinv__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_F3__2 : gw_eqs.
Lemma gw_eq_S_F2__2 : @S_F2 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_F2 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_F2)). Proof. unfold S_F2, QzQg.Mq0.S_F2; rewrite ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_xrel__2, ?gw_eq_dfinv__2, ?gw_eq_inring__2, ?gw_eq_X31__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_F2__2 : gw_eqs.
Lemma gw_eq_S_F1__2 : @S_F1 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_F1 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_F1)). Proof. unfold S_F1, QzQg.Mq0.S_F1; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_xrel__2, ?gw_eq_dfinv__2, ?gw_eq_inring__2, ?gw_eq_X31__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_F1__2 : gw_eqs.
Lemma gw_eq_C1E9HI__2 : @C1E9HI = ltac:(GwInst.gw_term (@QzQg.Mq0.C1E9HI) (@C1E9HI)). Proof. unfold C1E9HI, QzQg.Mq0.C1E9HI; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_C1E9HI__2 : gw_eqs.
Lemma gw_eq_ainv__2 : @ainv = ltac:(GwInst.gw_term (@QzQg.Mq0.ainv) (@ainv)). Proof. unfold ainv, QzQg.Mq0.ainv; rewrite ?gw_eq_xrel__2, ?gw_eq_zone__2, ?gw_eq_X31__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ainv__2 : gw_eqs.
Lemma gw_eq_S_A69C__2 : @S_A69C = ltac:(GwInst.gw_term (@QzQg.Mq0.S_A69C rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_A69C)). Proof. unfold S_A69C, QzQg.Mq0.S_A69C; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_dfinv__2, ?gw_eq_C1E9HI__2, ?gw_eq_ainv__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_A69C__2 : gw_eqs.
Lemma gw_eq_S_A62C__2 : @S_A62C = ltac:(GwInst.gw_term (@QzQg.Mq0.S_A62C rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_A62C)). Proof. unfold S_A62C, QzQg.Mq0.S_A62C; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_dfinv__2, ?gw_eq_C1E9HI__2, ?gw_eq_ainv__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_A62C__2 : gw_eqs.
Lemma gw_eq_S_A5C4__2 : @S_A5C4 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_A5C4 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_A5C4)). Proof. unfold S_A5C4, QzQg.Mq0.S_A5C4; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_dfinv__2, ?gw_eq_C1E9HI__2, ?gw_eq_ainv__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_A5C4__2 : gw_eqs.
Lemma gw_eq_fin_K0__2 : @fin_K0 = ltac:(GwInst.gw_term (@QzQg.Mq0.fin_K0) (@fin_K0)). Proof. unfold fin_K0, QzQg.Mq0.fin_K0; rewrite ?gw_eq_zero0__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_fin_K0__2 : gw_eqs.
Lemma gw_eq_S_A568__2 : @S_A568 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_A568 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_A568)). Proof. unfold S_A568, QzQg.Mq0.S_A568; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_dfinv__2, ?gw_eq_ainv__2, ?gw_eq_fin_K0__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_A568__2 : gw_eqs.
Lemma gw_eq_S_A534__2 : @S_A534 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_A534 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_A534)). Proof. unfold S_A534, QzQg.Mq0.S_A534; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_dfinv__2, ?gw_eq_ainv__2, ?gw_eq_fin_K0__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_A534__2 : gw_eqs.
Lemma gw_eq_SN324__2 : @SN324 = ltac:(GwInst.gw_term (@QzQg.Mq0.SN324 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@SN324)). Proof. unfold SN324, QzQg.Mq0.SN324; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_xrel__2, ?gw_eq_dfinv__2, ?gw_eq_zone__2, ?gw_eq_X31__2, ?gw_eq_fin_K0__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_SN324__2 : gw_eqs.
Lemma gw_eq_S_N324__2 : @S_N324 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_N324 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_N324)). Proof. unfold S_N324, QzQg.Mq0.S_N324; rewrite ?gw_eq_SN324__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_N324__2 : gw_eqs.
Lemma gw_eq_S_N2D4__2 : @S_N2D4 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_N2D4 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_N2D4)). Proof. unfold S_N2D4, QzQg.Mq0.S_N2D4; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_xrel__2, ?gw_eq_dfinv__2, ?gw_eq_zone__2, ?gw_eq_X31__2, ?gw_eq_fin_K0__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_N2D4__2 : gw_eqs.
Lemma gw_eq_up_K__2 : @up_K = ltac:(GwInst.gw_term (@QzQg.Mq0.up_K) (@up_K)). Proof. unfold up_K, QzQg.Mq0.up_K; rewrite ?gw_eq_fin_K0__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_up_K__2 : gw_eqs.
Lemma gw_eq_MAGIC__2 : @MAGIC = ltac:(GwInst.gw_term (@QzQg.Mq0.MAGIC) (@MAGIC)). Proof. unfold MAGIC, QzQg.Mq0.MAGIC; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_MAGIC__2 : gw_eqs.
Lemma gw_eq_S_U1A8__2 : @S_U1A8 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_U1A8 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_U1A8)). Proof. unfold S_U1A8, QzQg.Mq0.S_U1A8; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_xrel__2, ?gw_eq_dfinv__2, ?gw_eq_zone__2, ?gw_eq_X31__2, ?gw_eq_up_K__2, ?gw_eq_MAGIC__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_U1A8__2 : gw_eqs.
Lemma gw_eq_S_NK__2 : @S_NK = ltac:(GwInst.gw_term (@QzQg.Mq0.S_NK rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_NK)). Proof. unfold S_NK, QzQg.Mq0.S_NK; rewrite ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_xrel__2, ?gw_eq_dfinv__2, ?gw_eq_zone__2, ?gw_eq_X31__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_NK__2 : gw_eqs.
Lemma gw_eq_S_N484__2 : @S_N484 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_N484 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_N484)). Proof. unfold S_N484, QzQg.Mq0.S_N484; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_xrel__2, ?gw_eq_dfinv__2, ?gw_eq_zone__2, ?gw_eq_X31__2, ?gw_eq_fin_K0__2, ?gw_eq_SN324__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_N484__2 : gw_eqs.
Lemma gw_eq_S_N3E8__2 : @S_N3E8 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_N3E8 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_N3E8)). Proof. unfold S_N3E8, QzQg.Mq0.S_N3E8; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_xrel__2, ?gw_eq_dfinv__2, ?gw_eq_zone__2, ?gw_eq_X31__2, ?gw_eq_fin_K0__2, ?gw_eq_SN324__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_N3E8__2 : gw_eqs.
Lemma gw_eq_S_UK__2 : @S_UK = ltac:(GwInst.gw_term (@QzQg.Mq0.S_UK rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_UK)). Proof. unfold S_UK, QzQg.Mq0.S_UK; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_xrel__2, ?gw_eq_dfinv__2, ?gw_eq_inring__2, ?gw_eq_zone__2, ?gw_eq_X31__2, ?gw_eq_MAGIC__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_UK__2 : gw_eqs.
Lemma gw_eq_SU1C4__2 : @SU1C4 = ltac:(GwInst.gw_term (@QzQg.Mq0.SU1C4 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@SU1C4)). Proof. unfold SU1C4, QzQg.Mq0.SU1C4; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_xrel__2, ?gw_eq_dfinv__2, ?gw_eq_zone__2, ?gw_eq_X31__2, ?gw_eq_up_K__2, ?gw_eq_MAGIC__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_SU1C4__2 : gw_eqs.
Lemma gw_eq_S_U1C4__2 : @S_U1C4 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_U1C4 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_U1C4)). Proof. unfold S_U1C4, QzQg.Mq0.S_U1C4; rewrite ?gw_eq_SU1C4__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_U1C4__2 : gw_eqs.
Lemma gw_eq_S_T__2 : @S_T = ltac:(GwInst.gw_term (@QzQg.Mq0.S_T rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_T)). Proof. unfold S_T, QzQg.Mq0.S_T; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_xrel__2, ?gw_eq_dfinv__2, ?gw_eq_inring__2, ?gw_eq_X31__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_T__2 : gw_eqs.
Lemma gw_eq_S_DD0__2 : @S_DD0 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_DD0 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_DD0)). Proof. unfold S_DD0, QzQg.Mq0.S_DD0; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_dfinv__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_DD0__2 : gw_eqs.
Lemma gw_eq_S_DD24__2 : @S_DD24 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_DD24 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_DD24)). Proof. unfold S_DD24, QzQg.Mq0.S_DD24; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_dfinv__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_DD24__2 : gw_eqs.
Lemma gw_eq_S_M__2 : @S_M = ltac:(GwInst.gw_term (@QzQg.Mq0.S_M rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_M)). Proof. unfold S_M, QzQg.Mq0.S_M; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_xrel__2, ?gw_eq_dfinv__2, ?gw_eq_inring__2, ?gw_eq_X31__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_M__2 : gw_eqs.
Lemma gw_eq_digz__2 : @digz = ltac:(GwInst.gw_term (@QzQg.Mq0.digz) (@digz)). Proof. unfold digz, QzQg.Mq0.digz; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_digz__2 : gw_eqs.
Lemma gw_eq_S_P__2 : @S_P = ltac:(GwInst.gw_term (@QzQg.Mq0.S_P rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_P)). Proof. unfold S_P, QzQg.Mq0.S_P; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_xrel__2, ?gw_eq_dfinv__2, ?gw_eq_X31__2, ?gw_eq_digz__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_P__2 : gw_eqs.
Lemma gw_eq_S_R__2 : @S_R = ltac:(GwInst.gw_term (@QzQg.Mq0.S_R rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_R)). Proof. unfold S_R, QzQg.Mq0.S_R; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_xrel__2, ?gw_eq_dfinvG__2, ?gw_eq_X31__2, ?gw_eq_digz__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_R__2 : gw_eqs.
Lemma gw_eq_dig_facts__2 : @dig_facts = ltac:(GwInst.gw_term (@QzQg.Mq0.dig_facts) (@dig_facts)). Proof. unfold dig_facts, QzQg.Mq0.dig_facts; rewrite ?gw_eq_xrel__2, ?gw_eq_X31__2, ?gw_eq_digz__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_dig_facts__2 : gw_eqs.
Lemma gw_eq_S_C38__2 : @S_C38 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_C38 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_C38)). Proof. unfold S_C38, QzQg.Mq0.S_C38; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_dfinvG__2, ?gw_eq_dig_facts__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_C38__2 : gw_eqs.
Lemma gw_eq_S_C2C__2 : @S_C2C = ltac:(GwInst.gw_term (@QzQg.Mq0.S_C2C rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_C2C)). Proof. unfold S_C2C, QzQg.Mq0.S_C2C; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_dfinvG__2, ?gw_eq_dig_facts__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_C2C__2 : gw_eqs.
Lemma gw_eq_S_E__2 : @S_E = ltac:(GwInst.gw_term (@QzQg.Mq0.S_E rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_E)). Proof. unfold S_E, QzQg.Mq0.S_E; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_dfinvG__2, ?gw_eq_dig_facts__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_E__2 : gw_eqs.
Lemma gw_eq_digI__2 : @digI = ltac:(GwInst.gw_term (@QzQg.Mq0.digI) (@digI)). Proof. unfold digI, QzQg.Mq0.digI; rewrite ?gw_eq_xrel__2, ?gw_eq_X31__2, ?gw_eq_digz__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_digI__2 : gw_eqs.
Lemma gw_eq_SDn__2 : @SDn = ltac:(GwInst.gw_term (@QzQg.Mq0.SDn rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@SDn)). Proof. unfold SDn, QzQg.Mq0.SDn; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_dfinv__2, ?gw_eq_digI__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_SDn__2 : gw_eqs.
Lemma gw_eq_S_D__2 : @S_D = ltac:(GwInst.gw_term (@QzQg.Mq0.S_D rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_D)). Proof. unfold S_D, QzQg.Mq0.S_D; rewrite ?gw_eq_SDn__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_D__2 : gw_eqs.
Lemma gw_eq_winv__2 : @winv = ltac:(GwInst.gw_term (@QzQg.Mq0.winv rsegs got_ssp RATP ssp_guard) (@winv)). Proof. unfold winv, QzQg.Mq0.winv; rewrite ?gw_eq_finv__2, ?gw_eq_framL__2; ltac2:(GwEq.gw_rw [[@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_winv__2 : gw_eqs.
Lemma gw_eq_X0__2 : @X0 = ltac:(GwInst.gw_term (@QzQg.Mq0.X0) (@X0)). Proof. unfold X0, QzQg.Mq0.X0; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_X0__2 : gw_eqs.
Lemma gw_eq_fch__2 : @fch = ltac:(GwInst.gw_term (@QzQg.Mq0.fch) (@fch)). Proof. unfold fch, QzQg.Mq0.fch; ltac2:(GwEq.gw_rw [[@gw_eq_is_numch__3; @gw_eq_is_numch__2; @gw_eq_is_numch]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_fch__2 : gw_eqs.
Lemma gw_eq_S_B0C__2 : @S_B0C = ltac:(GwInst.gw_term (@QzQg.Mq0.S_B0C rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_B0C)). Proof. unfold S_B0C, QzQg.Mq0.S_B0C; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_dfinvG__2, ?gw_eq_X0__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_wval__3; @gw_eq_wval__2; @gw_eq_wval]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_B0C__2 : gw_eqs.
Lemma gw_eq_S_A9C__2 : @S_A9C = ltac:(GwInst.gw_term (@QzQg.Mq0.S_A9C rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_A9C)). Proof. unfold S_A9C, QzQg.Mq0.S_A9C; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_dfinvG__2, ?gw_eq_X0__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_wval__3; @gw_eq_wval__2; @gw_eq_wval]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_A9C__2 : gw_eqs.
Lemma gw_eq_S_A44__2 : @S_A44 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_A44 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_A44)). Proof. unfold S_A44, QzQg.Mq0.S_A44; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_winv__2, ?gw_eq_X0__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_A44__2 : gw_eqs.
Lemma gw_eq_SRZn__2 : @SRZn = ltac:(GwInst.gw_term (@QzQg.Mq0.SRZn rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@SRZn)). Proof. unfold SRZn, QzQg.Mq0.SRZn; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_winv__2, ?gw_eq_X0__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_SRZn__2 : gw_eqs.
Lemma gw_eq_S_RZ__2 : @S_RZ = ltac:(GwInst.gw_term (@QzQg.Mq0.S_RZ rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_RZ)). Proof. unfold S_RZ, QzQg.Mq0.S_RZ; rewrite ?gw_eq_SRZn__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_RZ__2 : gw_eqs.
Lemma gw_eq_S_9EC__2 : @S_9EC = ltac:(GwInst.gw_term (@QzQg.Mq0.S_9EC rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_9EC)). Proof. unfold S_9EC, QzQg.Mq0.S_9EC; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_winv__2, ?gw_eq_X0__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_9EC__2 : gw_eqs.
Lemma gw_eq_S_A64__2 : @S_A64 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_A64 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_A64)). Proof. unfold S_A64, QzQg.Mq0.S_A64; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_winv__2, ?gw_eq_X0__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_A64__2 : gw_eqs.
Lemma gw_eq_S_7F4__2 : @S_7F4 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_7F4 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_7F4)). Proof. unfold S_7F4, QzQg.Mq0.S_7F4; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_winv__2, ?gw_eq_X0__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_7F4__2 : gw_eqs.
Lemma gw_eq_S_9C8__2 : @S_9C8 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_9C8 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_9C8)). Proof. unfold S_9C8, QzQg.Mq0.S_9C8; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_winv__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_9C8__2 : gw_eqs.
Lemma gw_eq_SLZn__2 : @SLZn = ltac:(GwInst.gw_term (@QzQg.Mq0.SLZn rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@SLZn)). Proof. unfold SLZn, QzQg.Mq0.SLZn; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_winv__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_SLZn__2 : gw_eqs.
Lemma gw_eq_S_LZ__2 : @S_LZ = ltac:(GwInst.gw_term (@QzQg.Mq0.S_LZ rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_LZ)). Proof. unfold S_LZ, QzQg.Mq0.S_LZ; rewrite ?gw_eq_SLZn__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_LZ__2 : gw_eqs.
Lemma gw_eq_S_990__2 : @S_990 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_990 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_990)). Proof. unfold S_990, QzQg.Mq0.S_990; rewrite ?gw_eq_ctx_all__2, ?gw_eq_zero0__2, ?gw_eq_Fok__2, ?gw_eq_winv__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_990__2 : gw_eqs.
Lemma gw_eq_S_848__2 : @S_848 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_848 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_848)). Proof. unfold S_848, QzQg.Mq0.S_848; rewrite ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_winv__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_848__2 : gw_eqs.
Lemma gw_eq_S_6F8__2 : @S_6F8 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_6F8 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_6F8)). Proof. unfold S_6F8, QzQg.Mq0.S_6F8; rewrite ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_winv__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_6F8__2 : gw_eqs.
Lemma gw_eq_FS_tail__2 : @FS_tail = ltac:(GwInst.gw_term (@QzQg.Mq0.FS_tail) (@FS_tail)). Proof. unfold FS_tail, QzQg.Mq0.FS_tail; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FS_tail__2 : gw_eqs.
Lemma gw_eq_S_618__2 : @S_618 = ltac:(GwInst.gw_term (@QzQg.Mq0.S_618 rsegs 0x5b860 got_ssp RATP STRING_READ ssp_guard) (@S_618)). Proof. unfold S_618, QzQg.Mq0.S_618; rewrite ?gw_eq_ctx_all__2, ?gw_eq_Fok__2, ?gw_eq_winv__2, ?gw_eq_FS_tail__2; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_S_618__2 : gw_eqs.
