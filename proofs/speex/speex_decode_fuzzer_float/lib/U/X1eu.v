(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1es.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope bv_scope.
Local Notation psegs := Ubsan.M.loaded_segments.
Local Notation "# x" := (nan_box (low32 x)) (at level 9, format "# x").
#[local] Hint Rewrite length_iir_ys : chunk_sizes.

Section S.
Context {RCEIL : RunCeiling}.
Variables (xs den mem : list word) (px pden py pm : Z).
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variables f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 : word.
Variable mi : word -> option byte.
Variable lo : Z.
Local Notation ord := (Z.of_nat (length den)).
Local Notation N := (Z.of_nat (length xs)).
Hypothesis LMEM : length mem = length den.
Hypothesis ORD : (2 <= ord < 2^31)%Z.
Hypothesis LEN : (1 <= N < 2^31)%Z.
Hypothesis SEPDM : (pden + 4 * ord <= pm \/ pm + 4 * ord <= pden)%Z.
Local Notation R' := (R xs den px pden pm ra sp gp tp).
Local Notation FF' := (FF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31).
Local Notation POST := (iir_post xs den mem px pden py pm ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 mi lo).
Local Notation INNER := (iir_inner xs den mem px pden pm ra sp gp tp
f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 LMEM ORD SEPDM).
Local Notation WD := ([(lo, bv_unsigned sp); (py, py + 4 * N); (pm, pm + 4 * ord)]%Z).
Local Notation FRAME := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0].

Ltac outer_pre i q :=
zstep; replace (Z.shiftl i 2) with (4 * i)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia);
zstep; replace (px + 4 * i)%Z with q by lia;
zstep; zstep; if_false_z; zstep; if_false_z; zstep; if_false_z; zstep; if_false_z;
zstep; zstep; zstep; zstep; zstep; if_false_x; zstep.
Ltac outer_post a q :=
zstep; if_false_z; zstep; if_false_z; zstep; if_false_z;
zstep; zstep; replace a with q by lia;
zstep; zstep; zstep; zstep; if_false_z; zstep; if_false_z; zstep; if_false_z;
zstep; zstep; zstep.
Ltac frame_exit := do 12 zstep; zstep; zstep.

#[using="LMEM ORD LEN SEPDM"] Lemma iir_outer_dj : forall rest orest done x o memv (i q qy : Z) (s7v s8v s9v s10v s11v g12 g13 g14 g15 : word) fc m,
(px + 4 * N <= pm \/ pm + 4 * ord <= px)%Z -> (py + 4 * N <= pm \/ pm + 4 * ord <= py)%Z ->
(py + 4 * N <= pden \/ pden + 4 * ord <= py)%Z -> (px + 4 * N <= py \/ py + 4 * N <= px)%Z ->
(lo + 96 <= bv_unsigned sp)%Z -> (px + 4 * N <= lo \/ bv_unsigned sp <= px)%Z -> (py + 4 * N <= lo \/ bv_unsigned sp <= py)%Z ->
(pden + 4 * ord <= lo \/ bv_unsigned sp <= pden)%Z -> (pm + 4 * ord <= lo \/ bv_unsigned sp <= pm)%Z ->
(0 < px)%Z -> (0 < py)%Z -> (0 < pden)%Z ->
xs = done ++ x :: rest -> length orest = length rest -> i = Z.of_nat (length done) -> memv = iir_st den mem done ->
q = (px + 4 * i)%Z -> qy = (py + 4 * i)%Z ->
frm0 fc -> mem_inv psegs m -> munch WD mi m -> wmono psegs mi m ->
stk psegs m lo (bv_unsigned sp + -96) -> rw_cells psegs m (bv_unsigned sp + -96) FRAME ->
rw_cells psegs m py (f32 (iir_ys den mem done)) -> rw_cells psegs m qy (f32 (o :: orest)) ->
rw_cells psegs m px (f32 done) -> rw_cells psegs m q (f32 (x :: rest)) ->
rw_cells psegs m pm (f32 memv) -> rw_cells psegs m pden (f32 den) ->
evt psegs (POST WD false)
(MS (R' (Z_to_bv 64 py) (Z_to_bv 64 i) s7v s8v s9v s10v s11v) (FF' g12 g13 g14 g15) (Z_to_bv 64 0x2339c) fc None m (seg_rom psegs)).
Proof.
induction rest as [|x' rest IH]; intros orest done x o memv i q qy s7v s8v s9v s10v s11v g12 g13 g14 g15 fc m SEPXM SEPYM SEPYD SEPXY
LOW AXS AYS ADS AMS PX0 PY0 PD0 Hxs Lor Hi Hmv Hq Hqy FRM MI MU WM ST FR DONE Y XD X MEM DEN;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
assert (Lmv : length memv = length den) by (subst memv; apply length_iir_st; [exact LMEM| lia]);
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32 in BY; cbn [length] in BY;
pose proof (rw_cells_bound _ _ _ _ MEM) as BM; rewrite cells_size_f32, Lmv in BM;
pose proof (rw_cells_bound _ _ _ _ DEN) as BD; rewrite cells_size_f32 in BD;
pose proof (rw_cells_bound _ _ _ _ DONE) as BDO; rewrite cells_size_f32, length_iir_ys in BDO;
pose proof (rw_cells_bound _ _ _ _ XD) as BXD; rewrite cells_size_f32 in BXD;
pose proof (rw_cells_bound _ _ _ _ FR) as BFR; cbn [cells_size csize Nat.add] in BFR;
destruct memv as [|mv0 mvt] eqn:Emv; try (cbn in Lmv; lia); rewrite <- Emv in *;
destruct den as [|de0 [|de1 det]] eqn:Eden; try (cbn in ORD; lia); rewrite <- Eden in *;
destruct mvt as [|mv1 mvtt] eqn:Emvt; try (subst; cbn in Lmv; lia); rewrite <- Emvt in *;
rewrite !f32_cons in X; rewrite !f32_cons in Y; rewrite Emv, f32_cons in MEM; unfold R, FF.
- destruct orest; [|cbn in Lor; lia]. rewrite f32_nil in Y, X.
outer_pre i q.
rewrite Emvt in MEM. rewrite Eden in DEN.
assert (Ldm : length det = length mvtt) by (clear - Lmv Emv Emvt Eden; rewrite Emv, Emvt, Eden in Lmv; cbn in Lmv; lia).
assert (Htl : tl memv = [] ++ mv1 :: mvtt) by (rewrite Emv, Emvt; reflexivity).
assert (D0 : rw_cells psegs m pden (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia).
assert (M0 : rw_cells psegs m pm (f32 (iir_upd (fneg_s (fadd_s RNE (# x) (# mv0))) [] []))) by (cbn [iir_upd]; rewrite f32_nil; apply rw_cells_nil; lia).
pose proof (munch_refl [(pm, pm + 4 * ord)]%Z m) as MU0. pose proof (wmono_refl psegs m) as WM0.
call (INNER (Z_to_bv 64 py) (Z_to_bv 64 i) (Z_to_bv 64 (4 * i)) memv _ _ m mvtt [] de0 de1 det [] mv0 mv1 0 pden pm);
[ exact Eden | exact Htl | exact Lmv | reflexivity | exact Ldm | reflexivity | lia | lia | exact PD0
| exact FRM | exact MI | exact MU0 | exact WM0 | exact D0 | exact DEN | exact M0 | exact MEM | ].
clear Ldm Htl; try clear D0; try clear M0; try clear MU0; try clear WM0. unfold R, FF.
match goal with H : rw_cells _ _ (pden + 4 * (ord - 1))%Z _ |- _ => rename H into DL end.
match goal with H : rw_cells _ _ (pm + 4 * (ord - 1))%Z _ |- _ => rename H into ML end.
match goal with H : rw_cells _ _ pden (f32 (firstn _ _)) |- _ => rename H into DP end.
match goal with H : rw_cells _ _ pm (f32 (iir_upd _ _ _)) |- _ => rename H into MP end.
pose proof (rw_cells_bound _ _ _ _ DL) as BDL; pose proof (rw_cells_bound _ _ _ _ ML) as BML; cbn [cells_size csize Nat.add] in BDL, BML.
assert (LUP : length (iir_upd (fneg_s (fadd_s RNE (# x) (# mv0))) den (tl memv)) = (length den - 1)%nat)
by (rewrite length_iir_upd; rewrite Emv; cbn [tl]; subst; cbn in *; lia).
pose proof (firstn_length_le den (n := (length den - 1)%nat) ltac:(lia)) as LFD.
remember (pden + 4 * (ord - 1))%Z as dl eqn:Hdl in *. remember (pm + 4 * (ord - 1))%Z as ml eqn:Hml in *.
outer_post (py + 4 * i)%Z qy.
if_false_x.
frame_exit.
release_frame FR ST (bv_unsigned sp).
chunk_snoc DP DL. replace (f32 (firstn (length den - 1) den) ++ [C4 (last den w0)]) with (f32 den) in DP
by (rewrite <- (firstn_last den) at 1 by (rewrite Eden; discriminate); rewrite f32_app, f32_cons, f32_nil; reflexivity).
chunk_snoc MP ML. rewrite <- f32_nil, <- f32_cons, <- f32_app in MP.
chunk_snoc DONE Y. rewrite <- f32_nil, <- f32_cons, <- f32_app in DONE.
chunk_snoc XD X. rewrite <- f32_nil, <- f32_cons, <- f32_app in XD.
unfold iir_post. finish.
+ rewrite Hxs, iir_ys_app. cbn [iir_ys]. rewrite <- Hmv. unfold iir_yi. rewrite Emv. cbn [hd]. exact DONE.
+ rewrite Hxs, iir_st_app. cbn [iir_st]. rewrite <- Hmv. unfold iir_mem', iir_nyi, iir_yi. rewrite Emv in MP |- *. cbn [hd tl] in MP |- *. exact MP.
+ intros _. rewrite Hxs. exact XD.
- destruct orest as [|o' orest]; [cbn in Lor; lia|]. cbn [length] in HL, BX, BY, Lor. rewrite f32_cons in Y.
outer_pre i q.
rewrite Emvt in MEM. rewrite Eden in DEN.
assert (Ldm : length det = length mvtt) by (clear - Lmv Emv Emvt Eden; rewrite Emv, Emvt, Eden in Lmv; cbn in Lmv; lia).
assert (Htl : tl memv = [] ++ mv1 :: mvtt) by (rewrite Emv, Emvt; reflexivity).
assert (D0 : rw_cells psegs m pden (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia).
assert (M0 : rw_cells psegs m pm (f32 (iir_upd (fneg_s (fadd_s RNE (# x) (# mv0))) [] []))) by (cbn [iir_upd]; rewrite f32_nil; apply rw_cells_nil; lia).
pose proof (munch_refl [(pm, pm + 4 * ord)]%Z m) as MU0. pose proof (wmono_refl psegs m) as WM0.
call (INNER (Z_to_bv 64 py) (Z_to_bv 64 i) (Z_to_bv 64 (4 * i)) memv _ _ m mvtt [] de0 de1 det [] mv0 mv1 0 pden pm);
[ exact Eden | exact Htl | exact Lmv | reflexivity | exact Ldm | reflexivity | lia | lia | exact PD0
| exact FRM | exact MI | exact MU0 | exact WM0 | exact D0 | exact DEN | exact M0 | exact MEM | ].
clear Ldm Htl; try clear D0; try clear M0; try clear MU0; try clear WM0. unfold R, FF.
match goal with H : rw_cells _ _ (pden + 4 * (ord - 1))%Z _ |- _ => rename H into DL end.
match goal with H : rw_cells _ _ (pm + 4 * (ord - 1))%Z _ |- _ => rename H into ML end.
match goal with H : rw_cells _ _ pden (f32 (firstn _ _)) |- _ => rename H into DP end.
match goal with H : rw_cells _ _ pm (f32 (iir_upd _ _ _)) |- _ => rename H into MP end.
pose proof (rw_cells_bound _ _ _ _ DL) as BDL; pose proof (rw_cells_bound _ _ _ _ ML) as BML; cbn [cells_size csize Nat.add] in BDL, BML.
assert (LUP : length (iir_upd (fneg_s (fadd_s RNE (# x) (# mv0))) den (tl memv)) = (length den - 1)%nat)
by (rewrite length_iir_upd; rewrite Emv; cbn [tl]; subst; cbn in *; lia).
pose proof (firstn_length_le den (n := (length den - 1)%nat) ltac:(lia)) as LFD.
remember (pden + 4 * (ord - 1))%Z as dl eqn:Hdl in *. remember (pm + 4 * (ord - 1))%Z as ml eqn:Hml in *.
outer_post (py + 4 * i)%Z qy.
if_true_x.
chunk_snoc DP DL. replace (f32 (firstn (length den - 1) den) ++ [C4 (last den w0)]) with (f32 den) in DP
by (rewrite <- (firstn_last den) at 1 by (rewrite Eden; discriminate); rewrite f32_app, f32_cons, f32_nil; reflexivity).
chunk_snoc MP ML. rewrite <- f32_nil, <- f32_cons, <- f32_app in MP.
chunk_uncons Y as Y1. chunk_snoc DONE Y1. rewrite <- f32_nil, <- f32_cons, <- f32_app in DONE.
chunk_uncons X as X1. chunk_snoc XD X1. rewrite <- f32_nil, <- f32_cons, <- f32_app in XD.
subst dl ml.
eapply (IH orest (done ++ [x]) x' o' (iir_mem' den memv x) (i + 1)%Z (q + 4)%Z (qy + 4)%Z);
[ exact SEPXM | exact SEPYM | exact SEPYD | exact SEPXY
| exact LOW | exact AXS | exact AYS | exact ADS | exact AMS | exact PX0 | exact PY0 | exact PD0
| rewrite Hxs, <- app_assoc; reflexivity
| cbn in Lor; lia
| rewrite length_app; cbn [length]; lia
| rewrite iir_st_app; cbn [iir_st]; rewrite <- Hmv; reflexivity
| lia | lia
| eassumption | eassumption | exact MU | exact WM | exact ST | exact FR
| rewrite iir_ys_app; cbn [iir_ys]; rewrite <- Hmv; unfold iir_yi; rewrite Emv; cbn [hd]; exact DONE
| exact Y
| exact XD
| exact X
| unfold iir_mem', iir_nyi, iir_yi; rewrite Emv in MP |- *; cbn [hd tl] in MP |- *; exact MP
| exact DP ].
Qed.

Ltac iir_prologue :=
zstep; do 12 zstep; zstep; if_false_x; do 42 zstep;
rewrite (swrap32_small (ord + -1)) by lia;
rewrite (Z.mod_small (ord + -1) 18446744073709551616) by lia;
replace (Z.shiftl (ord + -1) 2) with (4 * (ord - 1))%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia);
rewrite (Z.mod_small (pden + 4 * (ord - 1)) 18446744073709551616) by lia;
rewrite (Z.mod_small (pm + 4 * (ord - 1)) 18446744073709551616) by lia;
replace (Z.lxor (ord + -1) 9223372036854775808) with (ord + -1 + 9223372036854775808)%Z
by (change 9223372036854775808%Z with (2^63)%Z; rewrite zb_lxor_sign by lia; rewrite Z.mod_small by lia; reflexivity);
replace (Z.lxor ord 9223372036854775808) with (ord + 9223372036854775808)%Z
by (change 9223372036854775808%Z with (2^63)%Z; rewrite zb_lxor_sign by lia; rewrite Z.mod_small by lia; reflexivity);
rewrite (zb_lxor_ones pm) by lia.

#[using="LMEM ORD LEN SEPDM"] Lemma iir_mem16_spec : forall (olds : list word) t0 t1 t2 a6 a7 t3 t4 t5 t6 fc,
(px + 4 * N <= pm \/ pm + 4 * ord <= px)%Z -> (py + 4 * N <= pm \/ pm + 4 * ord <= py)%Z ->
(py + 4 * N <= pden \/ pden + 4 * ord <= py)%Z -> (px + 4 * N <= py \/ py + 4 * N <= px)%Z ->
length olds = length xs ->
rw_cells psegs mi px (f32 xs) -> rw_cells psegs mi py (f32 olds) ->
rw_cells psegs mi pm (f32 mem) -> rw_cells psegs mi pden (f32 den) ->
mem_inv psegs mi -> frm0 fc ->
stk psegs mi lo (bv_unsigned sp) -> (lo + 96 <= bv_unsigned sp)%Z ->
(px + 4 * N <= lo \/ bv_unsigned sp <= px)%Z -> (py + 4 * N <= lo \/ bv_unsigned sp <= py)%Z ->
(pden + 4 * ord <= lo \/ bv_unsigned sp <= pden)%Z -> (pm + 4 * ord <= lo \/ bv_unsigned sp <= pm)%Z ->
(0 < px)%Z -> (px mod 4 = 0)%Z -> (0 < py)%Z -> (py mod 4 = 0)%Z -> (0 < pden)%Z -> (pden mod 4 = 0)%Z ->
(0 < pm)%Z -> (pm mod 4 = 0)%Z ->
evt psegs (POST WD false)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 px) (Z_to_bv 64 pden) (Z_to_bv 64 py) (Z_to_bv 64 N) (Z_to_bv 64 ord) (Z_to_bv 64 pm) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(mkF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31)
(Z_to_bv 64 0x232bc) fc None mi (seg_rom psegs)).
Proof.
intros olds t0 t1 t2 a6 a7 t3 t4 t5 t6 fc SEPXM SEPYM SEPYD SEPXY LO X Y MEM DEN MI FRM
ST LOW AXS AYS ADS AMS PX0 PX4 PY0 PY4 PD0 PD4 PM0 PM4.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32 in BY.
pose proof (rw_cells_bound _ _ _ _ MEM) as BM; rewrite cells_size_f32, LMEM in BM.
pose proof (rw_cells_bound _ _ _ _ DEN) as BD; rewrite cells_size_f32 in BD.
pose proof (munch_refl WD mi) as MU. pose proof (wmono_refl psegs mi) as WM.
destruct xs as [|x rest] eqn:Exs; [cbn in LEN; lia|]. rewrite <- Exs in *.
destruct olds as [|o orest]; [subst xs; cbn in LO; lia|].
pose proof LO as LO'; cbn [length] in LO', BY.
carve_frame 96%nat ST.
iir_prologue.
replace (Z.land (Z.lor px pm) 3) with 0%Z
by (rewrite Z.land_lor_distr_l; change 3%Z with (Z.ones 2); rewrite !Z.land_ones by lia; change (2^2)%Z with 4%Z; rewrite PX4, PM4; reflexivity).
cond_prep.
replace (Z.shiftl (Z.land 18446744073709551615 (ord + -1)) 2) with (4 * (ord - 1))%Z
by (change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia;
rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
rewrite Exs in X.
eapply (iir_outer_dj rest orest [] x o mem 0%Z px py);
[ exact SEPXM | exact SEPYM | exact SEPYD | exact SEPXY
| exact LOW | exact AXS | exact AYS | exact ADS | exact AMS | exact PX0 | exact PY0 | exact PD0
| exact Exs | subst xs; cbn in LO; lia
| reflexivity | reflexivity | lia | lia
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR
| cbn [iir_ys]; rewrite f32_nil; apply rw_cells_nil; lia
| exact Y
| rewrite f32_nil; apply rw_cells_nil; lia
| exact X | exact MEM | exact DEN ].
Qed.
End S.
