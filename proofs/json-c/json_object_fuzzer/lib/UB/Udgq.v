(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg QWxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7 QJjn QKQo. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI Uu4M Uihm UIsM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhI1 UunB. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qvbw QYIF QRUw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UrIB M2ShallowP2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg QWxq.Mq0.
Import UEQM.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ.
Import UC8c.Mq0.
Import Qsw7 QJjn QKQo.
Import UPZI.Mq0 Uu4M.Mq0 Uihm UIsM.
Import QSL3.
Import UhI1.
Import UunB.
Import Qvbw QYIF.
Import QRUw.Mq2.
Import UrIB.Mq0 M2ShallowP2.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma lxor_ones64 : forall b, 0 <= b < 2^64 -> Z.lxor b (Z.ones 64) = Z.ones 64 - b.
Proof.
intros b Hb.
assert (Hl : Z.log2 b < 64) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
rewrite <- Z.ldiff_ones_l_low by lia. symmetry. apply Z.sub_nocarry_ldiff. apply Z.ldiff_ones_r_low; lia.
Qed.

#[using="Type"] Lemma abs_idiom : forall z, - 2^31 < z < 2^31 ->
bv_swrap 32 (bv_unsigned (wz (Z.lxor (bv_unsigned (wz z)) (bv_unsigned (wz (Z.shiftr (bv_signed (wz z)) 63))))) -
bv_unsigned (wz (Z.shiftr (bv_signed (wz z)) 63))) = Z.abs z.
Proof.
intros z Hz. rewrite (signed_lit z) by lia.
destruct (Z.leb_spec 0 z) as [POS|NEG].
- rewrite (Z.shiftr_div_pow2 z 63) by lia. rewrite (Z.div_small z (2^63)) by lia.
rewrite (unsigned_lit 0) by lia. rewrite (unsigned_lit z) by lia. rewrite Z.lxor_0_r. rewrite (unsigned_lit z) by lia.
rewrite swrap32_id by lia. lia.
- replace (Z.shiftr z 63) with (-1) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; nia).
rewrite !unsigned_lit_wrap.
replace ((-1) mod 2^64) with (Z.ones 64) by reflexivity.
replace (z mod 2^64) with (z + 2^64) by (Z.div_mod_to_equations; nia).
rewrite lxor_ones64 by lia.
change (Z.ones 64) with 18446744073709551615.
rewrite (Z.mod_small) by lia.
replace (18446744073709551615 - (z + 2 ^ 64) - 18446744073709551615) with (- z + (-4294967296) * 4294967296) by lia.
rewrite swrap32_shift. rewrite swrap32_id by lia. lia.
Qed.

Section ShallowP3.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation wz := (Z_to_bv 64).

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB BS : list blk) (lo p D : Z) (r : jroot) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - SH_STK_P.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis SPD : bv_unsigned sp <= D.
Hypothesis DHI : D + 8 <= hi_top S4L HIx.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_rep S4L S4F r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv,
jf_postD S4L D ra sp gp (wz 0x77c00) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) lo rv m' ms' md' ->
jc_glob_P m' -> jroot_rep S4L S4F r m' BS p -> shallow_res S4L HIx S4F r BS LB D m' md' rv ->
realizes rsegs (mkCfg ms' md') T.

Notation sh_inv := (sh_inv ra sp s0 s1 s2 s3 s4 s5 F m0 md0 LB BS lo D).
Notation sh_regs := (sh_regs sp gp s6 s7 s8 s9 s10 s11 p D).

Ltac sh_hyps := try first [ exact Kont | exact JR0 | exact NN | exact DAL | exact DHI | exact SPD | exact RA | exact HT | exact SPA | exact LOS | exact LO ].

#[using="LO LOS SPA HT RA SPD DHI DAL NN JR0 Kont"] Lemma sh_string :
forall (x1 t0 t1 t2 a0 a2 a3 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (np tojs pb udel ud len S bk bn : Z) (str : list byte) (dold errc : word),
sh_inv mc mdc -> HEAPx A (BS ++ LB) mc mdc -> In (p, np) BS -> 48 <= np ->
rw_cells rsegs mc D [C8 dold] -> rw_cells rsegs mc (0x77c00 - 164) [C4 errc] ->
rw_cells rsegs mc p (jhdr_cells JT_STRING 1 tojs pb udel ud ++ [C8 (wz len)]) ->
- 2^31 < len < 2^31 -> Z.of_nat (length str) = Z.abs len ->
((0 <= len /\ S = p + 48) \/ (len < 0 /\ rw_cells rsegs mc (p + 48) [C8 (wz S)])) ->
bytes_at rsegs mc S str -> In (bk, bn) BS -> bk <= S -> S + Z.abs len <= bk + bn ->
(forall m' q (junk' : list byte),
rw_cells rsegs m' q (jhdr_cells JT_STRING 1 tojs 0 0 0 ++
[C8 (wz (Z.abs len)); CB (Z.to_nat (str_objsize (Z.abs len) - 48)) (str ++ [Z_to_bv 8 0] ++ junk')]) ->
scopy S4L S4F r m' [(q, str_objsize (Z.abs len))] q) ->
realizes rsegs (mkCfg (MS (sh_regs x1 t0 t1 t2 a0 a2 a3 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6)
F (wz 0x26b34) fc None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until errc. intros INV HP INp Hnp DC ERR SRC LEN SLEN SADDR SBY INb BK1 BK2 SCB. pose proof INV as (VM & PRES & ST & FR & G).
unfold UrIB.Mq0.sh_frame in FR. unfold UrIB.Mq0.sh_regs. unfold SH_STK_P in LOS. unfold_consts. word_range sp SPR.
change (0x77c00 - 164) with 490332 in ERR.
assert (INp1 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
assert (INb1 : In (bk, bn) (BS ++ LB)) by (apply in_or_app; left; exact INb).
pose proof (heap_blk S4L HIx _ _ _ _ p np HP INp1) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ p np HP INp1) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
pose proof (heap_blk S4L HIx _ _ _ _ bk bn HP INb1) as (_ & Hbal & Hblo & Hbhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hbhi.
unfold jhdr_cells in SRC. cbn [app] in SRC.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] mc) as MU.
stash G. stash SCB.
assert (SBYk : True -> bytes_at rsegs mc S str) by (intros _; exact SBY). clear SBY.
remember (Z.abs len) as n eqn:Hn.
assert (Hn0 : 0 <= n < 2^31) by lia.
apply rz_evt; [exact MOK|].
bstep. bstep. bstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (ABSJ : forall x10 x11 : word, evt rsegs (RZ rsegs mdc T)
(MS (mkR x1 (wz (bv_unsigned sp + -64)) gp (wz 0x77c00) t0 t1 t2 (wz p) (wz D) x10 x11 a2 a3 (wz D) a5 a6 a7
(wz S) (wz n) x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x26b48) fc None mx (seg_rom rsegs))) end.
2:{ destruct SADDR as [(Hl & ES)|(Hl & PD)].
- if_falsex. bstep. bstep. rewrite (unsigned_lit len) by lia. rewrite (Z.shiftl_mul_pow2 len 32) by lia. if_falsex.
subst S. replace (wz len) with (wz n) by (f_equal; lia). apply ABSJ.
- if_truex. step. step. step. step.
rewrite (QRUw.v_slt_0 (wz 0) (wz len)) by (rewrite (signed_lit len), (signed_lit 0) by lia; lia).
replace (wz (0 - bv_unsigned (wz len))) with (wz (- len)) by (apply bv_eq; rewrite !unsigned_lit_wrap; rewrite Zminus_mod_idemp_r; reflexivity).
rewrite (QRUw.v_slti_0 (wz (- len)) 0) by (rewrite QRUw.zsig_lit by lia; lia).
ub_resolve. bstep. bstep. bstep. rewrite (unsigned_lit (- len)) by lia. rewrite (Z.shiftl_mul_pow2 (- len) 32) by lia. if_truex.
replace (wz (- len)) with (wz n) by (f_equal; lia). apply ABSJ. }
intros y10 y11. bstep. rewrite (unsigned_lit n) by lia. rewrite Z.add_0_r. rewrite swrap32_id by lia.
bstep. bstep. bstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (CALL : forall x10 : word, x10 = wz (Z.max n 8) ->
evt rsegs (RZ rsegs mdc T)
(MS (mkR x1 (wz (bv_unsigned sp + -64)) gp (wz 0x77c00) t0 t1 t2 (wz p) (wz D) x10 (wz 8) a2 a3 (wz D) a5 a6 a7
(wz S) (wz n) x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x26b5c) fc None mx (seg_rom rsegs))) end.
2:{ destruct (Z.lt_ge_cases 8 n) as [Hb|Hs].
- if_truex. apply CALL. f_equal. lia.
- if_falsex. bstep. apply CALL. f_equal. lia. }
intros x10 ->. bstep.
replace (Z.max n 8 + 49) with (str_objsize n) by (unfold str_objsize; lia).
bstep.

alloc_call (hi_malloc S4L HIx) S4L HIx HP MU WM MI.
{ unfold str_objsize. lia. }
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR2 by lia.
extend_presD S4L HIx PRES MU WM HP. extend_presD_call PRES HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in SRC; [| eapply client_range_block; [exact INp1 | lia | cbn; lia]]. cbn [hl_segs S4L] in SRC.
assert (SBY2 : bytes_at rsegs m2 S str).
{ eapply (heap_pres_bytes_at S4L); [exact HPR2 | | eapply client_range_block; [exact INb1 | lia | lia]].
eapply (bytes_at_transport rsegs); [exact (SBYk I) | exact MU |]. cbn. lia. }
clear SBYk.
unstash G. pose proof (jc_glob_P_pres _ _ _ _ HPR2 (jc_glob_P_munch _ _ _ G MU WM ltac:(repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia))) as G2. clear G.
clear MU WM MI ST.
apply (proj1 (rw_cells_app rsegs _ p [_; _] _)) in SRC as X. destruct X as [_ SRC8]. cbn [cells_size csize Nat.add app] in SRC8.
apply (proj1 (rw_cells_app rsegs _ (p + 8) [_] _)) in SRC8 as [SRC8 _]. clear SRC.
destruct OUT2 as [(-> & _ & HP2) | (Hq & [junk0 BLK] & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
reenter MOK2.
bstep. if_true.
apply evt_RZ_done.
eapply (sh_join HIx) with (ty := JT_STRING) (tojs := tojs); sh_hyps;
[ split; [eapply model_vm_only_trans; [exact VM | exact VM2] | split; [exact PRES | split; [exact ST2 | split; [exact FR | exact G2]]]]
| apply fsv8_refl | intros Hf; exact Hf | exact DC | exact ERR2 | exact SRC8 | left; split; [reflexivity | exists A2; exact HP2] ].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ q _ HP2 ltac:(left; reflexivity)) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q _ HP2 ltac:(left; reflexivity)) as Hqimg. cbn [hl_img_lo hl_img_hi S4L] in Hqimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
assert (Hqp : q <> p) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ np HP2 INp1)).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q _ p np HP2 ltac:(left; reflexivity) ltac:(right; exact INp1) Hqp) as Hdqp.
assert (Hqb : q <> bk) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ bn HP2 INb1)).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q _ bk bn HP2 ltac:(left; reflexivity) ltac:(right; exact INb1) Hqb) as Hdqb.
stash Hdqb. stash Hpimg. clear Hqb Hqp.

assert (LENJ : length junk0 = Z.to_nat (str_objsize n)) by (destruct BLK as [[[Hwf _] _] _]; exact Hwf).
destruct (rw_cells_CB_cut rsegs _ _ _ _ 48%nat BLK ltac:(unfold str_objsize; lia)) as [HDR REST0].
destruct (rw_cells_CB_cut rsegs _ _ _ _ (Z.to_nat n) REST0 ltac:(unfold str_objsize; lia)) as [DATA REST1].
destruct (rw_cells_CB_cut rsegs _ _ _ _ 1%nat REST1 ltac:(unfold str_objsize; lia)) as [NUL REST2].
clear BLK REST0 REST1.
replace (q + Z.of_nat 48) with (q + 48) in DATA, NUL, REST2 by lia.
replace (q + 48 + Z.of_nat (Z.to_nat n)) with (q + 48 + n) in NUL, REST2 by lia.
replace (q + 48 + n + Z.of_nat 1) with (q + 48 + n + 1) in REST2 by lia.
assert (SBYh : True -> bytes_at rsegs m2 S str) by (intros _; exact SBY2). clear SBY2.
unfold str_objsize in *.
remember (Z.max n 8) as k eqn:Hk. assert (Hk1 : n <= k <= n + 8 /\ 8 <= k) by lia. stash Hk.
pose proof (munch_refl [(q, q + (49 + k))] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
stash G2.
reenter MOK2.
bstep. if_falsex.
bstep. bstep. bstepz. bstepz. bstep. bstep. bstep. bstepz. bstepz. bstepz. bstepz.
bstep. bstep. bstep. bstep. bstep. bstep.

unstash Hdqb.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SBY3 : bytes_at rsegs mx S str) by
(destruct (Z.eq_dec n 0) as [L0|LN];
[ assert (str = []) as -> by (destruct str; [reflexivity| cbn in SLEN; lia]); apply bytes_at_nil; lia
| eapply (bytes_at_transport rsegs); [exact (SBYh I) | exact MU |]; cbn; rewrite SLEN; lia ]) end.
call memcpy_specZ; [lia | lia | lia | lia | lia | exact SBY3 | lia | exact DATA | lia | assumption |].
stash Hdqb. try rename MI0 into MI.
step. step. rewrite (unsigned_lit (q + 48)) by lia.
replace (Z.lxor (q + 48) 18446744073709551615) with (18446744073709551615 - (q + 48)) by (change 18446744073709551615 with (Z.ones 64); symmetry; apply lxor_ones64; lia).
if_falsex. bstep.
set (ez := q + 48 + n) in *.
bstepz.
subst ez.
bstep. bstep.
unstash G2. unstash SCB.
apply evt_RZ_done.
jhdr_split HDR.
apply (proj1 (rw_cells_app rsegs _ q [_; _; _] _)) in HDR as X. destruct X as [QH QM]. cbn [cells_size csize Nat.add app] in QM.

apply (rw_cells_recast rsegs _ _ _ [CB 1 [Z_to_bv 8 0]]) in NUL; [| cbn; auto | reflexivity | reflexivity].
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
pose proof (rw_cells_CB_join rsegs _ _ _ _ _ _ PC ltac:(replace (q + 48 + Z.of_nat (Z.to_nat n)) with (q + 48 + n) by lia; exact NUL)) as J1;
pose proof (rw_cells_CB_join rsegs _ _ _ _ _ _ J1 ltac:(replace (q + 48 + Z.of_nat (Z.to_nat n + 1)) with (q + 48 + n + 1) by lia; exact REST2)) as J2;
match type of J2 with rw_cells _ _ _ [CB ?kk _] => replace kk with (Z.to_nat (49 + k - 48)) in J2 by lia end;
rewrite <- app_assoc in J2; cbn [app] in J2;
replace (q + 48) with (q + Z.of_nat 16 + Z.of_nat (cells_size [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz n)])) in J2 by (cbn; lia);
pose proof (proj2 (rw_cells_app rsegs _ _ _ _) (conj QM J2)) as QT; clear J1 J2 QM PC NUL REST2;
assert (HP3 : HEAPx A2 ((q, 49 + k) :: BS ++ LB) mx md2) by heap_now S4L HIx HP2 MU WM MI;
assert (G3 : jc_glob_P mx) by
(eapply jc_glob_P_outside; [exact G2 | exact MU | exact WM |]; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia)
end.
cbn [app] in QT.
extend_presD S4L HIx PRES MU WM HP2.
eapply (sh_join HIx) with (ty := JT_STRING) (tojs := tojs); sh_hyps;
[ split; [eapply model_vm_only_trans; [exact VM | exact VM2] | split; [exact PRES | split; [exact ST2 | split; [exact FR | exact G3]]]]
| apply fsv8_refl | intros Hf; exact Hf | exact DC | exact ERR2 | exact SRC8 | ].
unstash Hk. subst k.
right. split; [exact Hq|]. exists A2, [(q, 49 + Z.max n 8)], (49 + Z.max n 8), (fn_str_to_json_string S4F).
split; [eapply (heap_perm S4L HIx); [exact HP3 | perm] |].
split; [left; reflexivity|]. split; [lia|]. split; [exact QH|].
intros m' QH' MU' WM'. unfold str_objsize in SCB. eapply (SCB m' q).
unfold jhdr_cells. cbn [app].
apply (proj2 (rw_cells_app rsegs m' q [_; _; _] _)). split; [exact QH'|]. cbn [cells_size csize Nat.add app].
eapply (rw_cells_transport rsegs); [exact QT | exact MU' | exact WM' |]. cbn. lia.
Qed.
End ShallowP3.

Section ShallowMain.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation wz := (Z_to_bv 64).

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB BS : list blk) (lo p D : Z) (r : jroot) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - SH_STK_P.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis SPD : bv_unsigned sp <= D.
Hypothesis DHI : D + 8 <= hi_top S4L HIx.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_rep S4L S4F r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv,
jf_postD S4L D ra sp gp (wz 0x77c00) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) lo rv m' ms' md' ->
jc_glob_P m' -> jroot_rep S4L S4F r m' BS p -> shallow_res S4L HIx S4F r BS LB D m' md' rv ->
realizes rsegs (mkCfg ms' md') T.
Hypothesis NEWO : jo_new_object_P HIx.

Notation sh_inv := (sh_inv ra sp s0 s1 s2 s3 s4 s5 F m0 md0 LB BS lo D).
Notation sh_regs := (sh_regs sp gp s6 s7 s8 s9 s10 s11 p D).
Notation sh_frame := (sh_frame ra sp s0 s1 s2 s3 s4 s5 F).

Ltac sh_hyps := try first [ exact Kont | exact JR0 | exact NN | exact DAL | exact DHI | exact SPD | exact RA | exact HT | exact SPA | exact LOS | exact LO | exact NEWO ].

Definition sh_tgt (ty : Z) : Z :=
match ty with 1 => 0x269cc | 2 => 0x26aec | 3 => 0x26a84 | 4 => 0x26ae0 | 5 => 0x26a14 | _ => 0x26b34 end.
Definition sh_jtab := Eval vm_compute in match image_bytes rsegs 0x13938 24 with Some bs => bs | None => [] end.
#[using="RC__ ra sp D"] Lemma sh_jtab_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x13938 [CB 24 sh_jtab].
Proof.
intros m MI. change 24%nat with (length sh_jtab).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length sh_jtab)) with 24%Z. lia.
Qed.
#[using="LO LOS SPD"] Lemma sh_pro :
forall (t0 t1 t2 a1 a2 a3 a5 a6 a7 t3 t4 t5 t6 : word) (ty np : Z) (A : AS S4L HIx),
HEAPx A (BS ++ LB) m0 md0 -> stk rsegs m0 lo (bv_unsigned sp) ->
rw_cells rsegs m0 p [C4 (wz ty)] -> 1 <= ty <= 6 -> p + 4 <= alloc_ceiling -> In (p, np) BS ->
(forall mc, munch [(bv_unsigned sp - 64, bv_unsigned sp)] m0 mc -> wmono rsegs m0 mc -> mem_inv rsegs mc ->
sh_frame mc -> stk rsegs mc lo (bv_unsigned sp + -64) ->
realizes rsegs (mkCfg (MS (sh_regs ra t0 t1 t2 (wz (sh_tgt ty)) a2 a3 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6)
F (wz (sh_tgt ty)) fc None mc (seg_rom rsegs)) md0) T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp (wz 0x77c00) t0 t1 t2 s0 s1 (wz p) a1 a2 a3 (wz D) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz SH_ENTRY_P) fc None m0 (seg_rom rsegs)) md0) T.
Proof.
intros until A. intros HP ST HDR TY PB INp ARMS.
pose proof (heap_blk S4L HIx _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & _ & _).
unfold UrIB.Mq0.sh_frame, UrIB.Mq0.sh_regs in ARMS. unfold SH_STK_P in LOS. unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m0) as MU.
pose proof (sh_jtab_ro m0 MI) as JT. unfold sh_jtab in JT.
clear HP.
apply rz_evt; [exact MOK|]. unfold SH_ENTRY_P.
carve_frame 64%nat ST.
do 10 bstep.
bstep. norm_sx32. bstep. bstep. bstep. if_falsex. bstep. bstep. bstep. bstep. bstep.
rewrite (unsigned_lit (ty + -1)) by lia. rewrite (Z.shiftl_mul_pow2 (ty + -1) 2) by lia. change (2 ^ 2) with 4.
assert (CASES : exists k : nat, (1 <= k <= 6)%nat /\ ty = Z.of_nat k) by (exists (Z.to_nat ty); split; lia).
destruct CASES as (k & Hk & ->).
do 7 (destruct k as [|k]; [ first [ lia |
match goal with |- context [Z_to_bv 64 ((Z.of_nat ?n + -1) * 4 + 80184)] =>
let v := eval vm_compute in ((Z.of_nat n + -1) * 4 + 80184) in change ((Z.of_nat n + -1) * 4 + 80184) with v end;
bstep;
match goal with |- context [sext 64 (bv_extract 0 32 (le_bytes_to_word ?l))] =>
let v := eval vm_compute in (bv_unsigned (sext 64 (bv_extract 0 32 (le_bytes_to_word l)))) in
replace (sext 64 (bv_extract 0 32 (le_bytes_to_word l))) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity) end;
bstep; bstep;
apply evt_RZ_done; eapply ARMS; [exact MU | exact WM | exact MI | exact FR | exact ST] ] | ]).
exfalso. lia.
Qed.

#[using="LO LOS HT SPD"] Lemma sh_enter : forall A mc errv dold,
HEAPx A (BS ++ LB) m0 md0 -> jc_glob_P m0 ->
rw_cells rsegs m0 D [C8 dold] -> rw_cells rsegs m0 (0x77c00 - 164) [C4 errv] ->
munch [(bv_unsigned sp - 64, bv_unsigned sp)] m0 mc -> wmono rsegs m0 mc -> mem_inv rsegs mc ->
sh_frame mc -> stk rsegs mc lo (bv_unsigned sp + -64) ->
sh_inv mc md0 /\ HEAPx A (BS ++ LB) mc md0 /\ rw_cells rsegs mc D [C8 dold] /\ rw_cells rsegs mc (0x77c00 - 164) [C4 errv] /\
agree_on rsegs (BS ++ LB) m0 mc.
Proof.
intros A mc errv dold HP G DC ERR MU WM MI FR ST. unfold SH_STK_P in LOS. unfold_consts. word_range sp SPR.
assert (HPc : HEAPx A (BS ++ LB) mc md0).
{ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW_with HP. }
split; [| split; [exact HPc | split; [| split]]].
- split; [apply model_vm_only_refl|]. split; [| split; [exact ST | split; [exact FR |]]].
+ eapply presxD_of_munch; [exact MU | exact WM |].
intros a Ha Hc Hd. eapply (client_outside S4L HIx) with (LB0 := BS ++ LB) (SP := bv_unsigned sp); [exact HP | intros b Hb; exact Hb | clia | solve_clientW S4L HIx HP | exact Ha | exact Hc].
+ eapply jc_glob_P_outside; [exact G | exact MU | exact WM |]. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia.
- eapply (rw_cells_transport rsegs); [exact DC | exact MU | exact WM | cbn; lia].
- eapply (rw_cells_transport rsegs); [exact ERR | exact MU | exact WM | cbn; lia].
- eapply (agree_of_munch rsegs); [exact MU | exact WM |]. intros a n Ha. cbn.
pose proof (heap_blk S4L HIx _ _ _ _ a n HP Ha) as (_ & _ & _ & Hhi & _). unfold_consts. lia.
Qed.

#[using="r LO LOS SPA HT RA SPD DHI DAL NN JR0 Kont NEWO"] Lemma sh_main :
forall (t0 t1 t2 a1 a2 a3 a5 a6 a7 t3 t4 t5 t6 : word) (A : AS S4L HIx) (dold errv : word),
HEAPx A (BS ++ LB) m0 md0 -> jc_glob_P m0 ->
rw_cells rsegs m0 D [C8 dold] -> stk rsegs m0 lo (bv_unsigned sp) -> rw_cells rsegs m0 (0x77c00 - 164) [C4 errv] ->
realizes rsegs (mkCfg (MS (mkR ra sp gp (wz 0x77c00) t0 t1 t2 s0 s1 (wz p) a1 a2 a3 (wz D) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz SH_ENTRY_P) fc None m0 (seg_rom rsegs)) md0) T.
Proof.
intros until errv. intros HP G DC ST ERR.
pose proof JR0 as JR. destruct r as [|s|tojs|]; [exfalso; exact (NN eq_refl) | | |]; cbn [jroot_rep] in JR.
-
destruct JR as [Hp J].
destruct s as [|u| |h|kids|kids]; destruct J as (pb & PBS & REST & EBS & OPB & J).
+
destruct J as (b & junk & ER & H). subst REST.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp)) as (_ & _ & _ & Hphi & _).
pose proof H as H1. apply (proj1 (rw_cells_app rsegs m0 p [_] _)) in H1 as [H1 _].
eapply sh_pro with (ty := JT_BOOLEAN); [exact HP | exact ST | exact H1 | unfold JT_BOOLEAN; lia | lia | exact INp |].
intros mc MU WM MI FR STc. change (sh_tgt JT_BOOLEAN) with 0x269cc.
destruct (sh_enter _ _ _ _ HP G DC ERR MU WM MI FR STc) as (INV & HPc & DCc & ERRc & AG).
eapply (sh_bool HIx) with (np := 48); sh_hyps; [exact INV | exact HPc | exact INp | lia | exact DCc | exact ERRc | |].
* eapply (rw_cells_agree rsegs); [exact H | exact AG | exists p, 48; split; [apply in_or_app; left; exact INp | cbn; lia]].
* intros m' q bw' junk' H'. cbn [scopy].
exists 0, [], [(q, 48)]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists (bv_unsigned bw'), junk'. split; [reflexivity|]. rewrite Z_to_bv_bv_unsigned. exact H'.
+
destruct u.
* destruct J as (bits & ud & udn & uds & ER & HU & H & HC). subst REST.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp)) as (_ & _ & _ & Hphi & _).
pose proof H as H1. apply (proj1 (rw_cells_app rsegs m0 p [_] _)) in H1 as [H1 _].
eapply sh_pro with (ty := JT_DOUBLE); [exact HP | exact ST | exact H1 | unfold JT_DOUBLE; lia | lia | exact INp |].
intros mc MU WM MI FR STc. change (sh_tgt JT_DOUBLE) with 0x26aec.
destruct (sh_enter _ _ _ _ HP G DC ERR MU WM MI FR STc) as (INV & HPc & DCc & ERRc & AG).
eapply (sh_double HIx) with (np := 48); sh_hyps; [exact INV | exact HPc | exact INp | lia | exact DCc | exact ERRc | |].
-- eapply (rw_cells_agree rsegs); [exact H | exact AG | exists p, 48; split; [apply in_or_app; left; exact INp | cbn; lia]].
-- intros m' q H'. cbn [scopy]. split; [reflexivity|]. exists bits. exact H'.
* destruct J as (bits & ER & HS & H). subst REST.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp)) as (_ & _ & _ & Hphi & _).
pose proof H as H1. apply (proj1 (rw_cells_app rsegs m0 p [_] _)) in H1 as [H1 _].
eapply sh_pro with (ty := JT_DOUBLE); [exact HP | exact ST | exact H1 | unfold JT_DOUBLE; lia | lia | exact INp |].
intros mc MU WM MI FR STc. change (sh_tgt JT_DOUBLE) with 0x26aec.
destruct (sh_enter _ _ _ _ HP G DC ERR MU WM MI FR STc) as (INV & HPc & DCc & ERRc & AG).
eapply (sh_double HIx) with (np := 48); sh_hyps; [exact INV | exact HPc | exact INp | lia | exact DCc | exact ERRc | |].
-- eapply (rw_cells_agree rsegs); [exact H | exact AG | exists p, 48; split; [apply in_or_app; left; exact INp | cbn; lia]].
-- intros m' q H'. cbn [scopy].
exists 0, [], [(q, 48)]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists bits. split; [reflexivity|]. split; [exact HS | exact H'].
+
destruct J as (cty & v & junk & ER & CTY & H). subst REST.
assert (INp : In (p, 56) BS) by (rewrite EBS; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p 56 HP ltac:(apply in_or_app; left; exact INp)) as (_ & _ & _ & Hphi & _).
pose proof H as H1. apply (proj1 (rw_cells_app rsegs m0 p [_] _)) in H1 as [H1 _].
eapply sh_pro with (ty := JT_INT); [exact HP | exact ST | exact H1 | unfold JT_INT; lia | lia | exact INp |].
intros mc MU WM MI FR STc. change (sh_tgt JT_INT) with 0x26a84.
destruct (sh_enter _ _ _ _ HP G DC ERR MU WM MI FR STc) as (INV & HPc & DCc & ERRc & AG).
eapply (sh_int HIx) with (np := 56); sh_hyps; [exact INV | exact HPc | exact INp | lia | exact DCc | exact ERRc | | exact CTY |].
* eapply (rw_cells_agree rsegs); [exact H | exact AG | exists p, 56; split; [apply in_or_app; left; exact INp | cbn; lia]].
* intros m' q junk' H'. cbn [scopy].
exists 0, [], [(q, 56)]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists cty, v, junk'. split; [reflexivity|]. split; [exact CTY | exact H'].
+
destruct h.
*
destruct J as (len & pd & pdn & str & junk2 & ER & Hlen & Hsl & Hpdn & H & HD). subst REST.
assert (INp : In (p, 56) BS) by (rewrite EBS; left; reflexivity).
assert (INd : In (pd, pdn) BS) by (rewrite EBS; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p 56 HP ltac:(apply in_or_app; left; exact INp)) as (_ & _ & _ & Hphi & _).
pose proof H as H1. apply (proj1 (rw_cells_app rsegs m0 p [_] _)) in H1 as [H1 _].
eapply sh_pro with (ty := JT_STRING); [exact HP | exact ST | exact H1 | unfold JT_STRING; lia | lia | exact INp |].
intros mc MU WM MI FR STc. change (sh_tgt JT_STRING) with 0x26b34.
destruct (sh_enter _ _ _ _ HP G DC ERR MU WM MI FR STc) as (INV & HPc & DCc & ERRc & AG).
apply (rw_cells_agree rsegs (BS ++ LB) m0 mc) in H; [| exact AG | exists p, 56; split; [apply in_or_app; left; exact INp | cbn; lia]].
apply (rw_cells_agree rsegs (BS ++ LB) m0 mc) in HD; [| exact AG | exists pd, pdn; split; [apply in_or_app; left; exact INd | cbn; lia]].
apply (proj1 (rw_cells_app rsegs mc p [_; _; _; _; _; _; _] _)) in H as [H HPD]. cbn [cells_size csize Nat.add app] in HPD.
eapply (sh_string HIx) with (np := 56) (S := pd) (bk := pd) (bn := pdn) (str := str); sh_hyps;
[exact INV | exact HPc | exact INp | lia | exact DCc | exact ERRc | exact H | lia | lia | right; split; [lia | exact HPD] | | exact INd | lia | lia | ].
-- eapply bytes_at_prefix. exact (rw_cells_bytes_at S4L _ _ _ _ HD).
-- intros m' q junk' H'. cbn [scopy].
exists 0, [], [(q, str_objsize (Z.abs len))]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists (Z.abs len), str, junk'. split; [reflexivity|]. split; [lia|]. split; [lia | exact H'].
*
destruct J as (len & str & junk & ER & Hlen & Hsl & H). subst REST.
assert (INp : In (p, str_objsize len) BS) by (rewrite EBS; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p _ HP ltac:(apply in_or_app; left; exact INp)) as (_ & _ & _ & Hphi & _). unfold str_objsize in Hphi.
pose proof H as H1. apply (proj1 (rw_cells_app rsegs m0 p [_] _)) in H1 as [H1 _].
eapply sh_pro with (ty := JT_STRING); [exact HP | exact ST | exact H1 | unfold JT_STRING; lia | lia | exact INp |].
intros mc MU WM MI FR STc. change (sh_tgt JT_STRING) with 0x26b34.
destruct (sh_enter _ _ _ _ HP G DC ERR MU WM MI FR STc) as (INV & HPc & DCc & ERRc & AG).
apply (rw_cells_agree rsegs (BS ++ LB) m0 mc) in H; [| exact AG | exists p, (str_objsize len); split; [apply in_or_app; left; exact INp | cbn; unfold str_objsize; lia]].
apply (proj1 (rw_cells_app rsegs mc p [_; _; _; _; _; _; _] _)) in H as [H HDATA]. cbn [cells_size csize Nat.add app] in HDATA.
eapply (sh_string HIx) with (np := str_objsize len) (S := p + 48) (bk := p) (bn := str_objsize len) (str := str); sh_hyps;
[exact INV | exact HPc | exact INp | unfold str_objsize; lia | exact DCc | exact ERRc | exact H | lia | lia | left; split; [lia | reflexivity] | | exact INp | lia | unfold str_objsize; lia | ].
-- eapply bytes_at_prefix. exact (rw_cells_bytes_at S4L _ _ _ _ HDATA).
-- intros m' q junk' H'. cbn [scopy].
exists 0, [], [(q, str_objsize (Z.abs len))]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists (Z.abs len), str, junk'. split; [reflexivity|]. split; [lia|]. split; [lia | exact H'].
+
destruct J as (t & TBS & kvs & KBS & ER & H & HTB & L1 & L2 & KIDS). subst REST.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp)) as (_ & _ & _ & Hphi & _).
pose proof H as H1. apply (proj1 (rw_cells_app rsegs m0 p [_] _)) in H1 as [H1 _].
eapply sh_pro with (ty := JT_OBJECT); [exact HP | exact ST | exact H1 | unfold JT_OBJECT; lia | lia | exact INp |].
intros mc MU WM MI FR STc. change (sh_tgt JT_OBJECT) with 0x26ae0.
destruct (sh_enter _ _ _ _ HP G DC ERR MU WM MI FR STc) as (INV & HPc & DCc & ERRc & AG).
apply (rw_cells_agree rsegs (BS ++ LB) m0 mc) in H; [| exact AG | exists p, 48; split; [apply in_or_app; left; exact INp | cbn; lia]].
apply (proj1 (rw_cells_app rsegs mc p [_; _; _; _; _; _] _)) in H as [H _].
eapply (sh_object HIx) with (np := 48); sh_hyps; [exact INV | exact HPc | exact INp | lia | exact DCc | exact ERRc | exact H |].
intros m' q pb' PBS' t' TBS' H' OPB' TAB'. cbn [scopy].
exists pb', PBS', ((q, 48) :: TBS'). split; [reflexivity|]. split; [exact OPB'|].
exists t', TBS', [], []. split; [rewrite app_nil_r; reflexivity|]. split; [exact H'|]. split; [exact TAB'|]. repeat split.
+
destruct J as (al & ABS & ps & KBS & ER & H & HA & L1 & L2 & KIDS). subst REST.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp)) as (_ & _ & _ & Hphi & _).
pose proof H as H1. apply (proj1 (rw_cells_app rsegs m0 p [_] _)) in H1 as [H1 _].
eapply sh_pro with (ty := JT_ARRAY); [exact HP | exact ST | exact H1 | unfold JT_ARRAY; lia | lia | exact INp |].
intros mc MU WM MI FR STc. change (sh_tgt JT_ARRAY) with 0x26a14.
destruct (sh_enter _ _ _ _ HP G DC ERR MU WM MI FR STc) as (INV & HPc & DCc & ERRc & AG).
apply (rw_cells_agree rsegs (BS ++ LB) m0 mc) in H; [| exact AG | exists p, 48; split; [apply in_or_app; left; exact INp | cbn; lia]].
apply (proj1 (rw_cells_app rsegs mc p [_; _; _; _; _; _] _)) in H as [H _].
eapply (sh_array HIx) with (np := 48); sh_hyps; [exact INV | exact HPc | exact INp | lia | exact DCc | exact ERRc | exact H |].
intros m' q a' ABS' H' AL'. cbn [scopy].
exists 0, [], ((q, 48) :: ABS'). split; [rewrite app_nil_r; reflexivity|]. split; [left; split; reflexivity|].
exists a', ABS', [], []. split; [rewrite app_nil_r; reflexivity|]. split; [exact H'|]. split; [exact AL'|]. repeat split.
-
destruct JR as (Hp & Htojs & pb & PBS & bits & EBS & OPB & H).
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp)) as (_ & _ & _ & Hphi & _).
pose proof H as H1. apply (proj1 (rw_cells_app rsegs m0 p [_] _)) in H1 as [H1 _].
eapply sh_pro with (ty := JT_DOUBLE); [exact HP | exact ST | exact H1 | unfold JT_DOUBLE; lia | lia | exact INp |].
intros mc MU WM MI FR STc. change (sh_tgt JT_DOUBLE) with 0x26aec.
destruct (sh_enter _ _ _ _ HP G DC ERR MU WM MI FR STc) as (INV & HPc & DCc & ERRc & AG).
eapply (sh_double HIx) with (np := 48); sh_hyps; [exact INV | exact HPc | exact INp | lia | exact DCc | exact ERRc | |].
+ eapply (rw_cells_agree rsegs); [exact H | exact AG | exists p, 48; split; [apply in_or_app; left; exact INp | cbn; lia]].
+ intros m' q H'. cbn [scopy]. split; [reflexivity|]. exists 0, [], bits. split; [reflexivity|]. split; [left; split; reflexivity | exact H'].
-
destruct JR as (Hp & pb & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & ALT).
assert (INp : In (p, 48 + cap) BS) by (rewrite EBS; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p _ HP ltac:(apply in_or_app; left; exact INp)) as (_ & _ & _ & Hphi & _).
destruct ALT as [(Hl & EDBS & Hfit & junk & H) | (Hl & pd & pdn & junk & junk2 & EDBS & Hpdn & H & HD)].
+
pose proof H as H1. apply (proj1 (rw_cells_app rsegs m0 p [_] _)) in H1 as [H1 _].
eapply sh_pro with (ty := JT_STRING); [exact HP | exact ST | exact H1 | unfold JT_STRING; lia | lia | exact INp |].
intros mc MU WM MI FR STc. change (sh_tgt JT_STRING) with 0x26b34.
destruct (sh_enter _ _ _ _ HP G DC ERR MU WM MI FR STc) as (INV & HPc & DCc & ERRc & AG).
apply (rw_cells_agree rsegs (BS ++ LB) m0 mc) in H; [| exact AG | exists p, (48 + cap); split; [apply in_or_app; left; exact INp | cbn; lia]].
apply (proj1 (rw_cells_app rsegs mc p [_; _; _; _; _; _; _] _)) in H as [H HDATA]. cbn [cells_size csize Nat.add app] in HDATA.
eapply (sh_string HIx) with (np := 48 + cap) (S := p + 48) (bk := p) (bn := 48 + cap) (str := str); sh_hyps;
[exact INV | exact HPc | exact INp | lia | exact DCc | exact ERRc | exact H | lia | lia | left; split; [lia | reflexivity] | | exact INp | lia | lia | ].
* eapply bytes_at_prefix. exact (rw_cells_bytes_at S4L _ _ _ _ HDATA).
* intros m' q junk' H'. cbn [scopy].
exists 0, [], [(q, str_objsize (Z.abs len))]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists (Z.abs len), str, junk'. split; [reflexivity|]. split; [lia|]. split; [lia | exact H'].
+
subst DBS.
assert (INd : In (pd, pdn) BS) by (rewrite EBS; right; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app rsegs m0 p [_] _)) in H1 as [H1 _].
eapply sh_pro with (ty := JT_STRING); [exact HP | exact ST | exact H1 | unfold JT_STRING; lia | lia | exact INp |].
intros mc MU WM MI FR STc. change (sh_tgt JT_STRING) with 0x26b34.
destruct (sh_enter _ _ _ _ HP G DC ERR MU WM MI FR STc) as (INV & HPc & DCc & ERRc & AG).
apply (rw_cells_agree rsegs (BS ++ LB) m0 mc) in H; [| exact AG | exists p, (48 + cap); split; [apply in_or_app; left; exact INp | cbn; lia]].
apply (rw_cells_agree rsegs (BS ++ LB) m0 mc) in HD; [| exact AG | exists pd, pdn; split; [apply in_or_app; left; exact INd | cbn; lia]].
apply (proj1 (rw_cells_app rsegs mc p [_; _; _; _; _; _; _] _)) in H as [H HPD]. cbn [cells_size csize Nat.add app] in HPD.
apply (proj1 (rw_cells_app rsegs mc (p + 48) [_] _)) in HPD as [HPD _].
eapply (sh_string HIx) with (np := 48 + cap) (S := pd) (bk := pd) (bn := pdn) (str := str); sh_hyps;
[exact INV | exact HPc | exact INp | lia | exact DCc | exact ERRc | exact H | lia | lia | right; split; [lia | exact HPD] | | exact INd | lia | lia | ].
* eapply bytes_at_prefix. exact (rw_cells_bytes_at S4L _ _ _ _ HD).
* intros m' q junk' H'. cbn [scopy].
exists 0, [], [(q, str_objsize (Z.abs len))]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists (Z.abs len), str, junk'. split; [reflexivity|]. split; [lia|]. split; [lia | exact H'].
Qed.
End ShallowMain.

#[using="Type"] Theorem shallow_P : forall HIx, jo_new_object_P HIx -> shallow_stmt S4L HIx S4F jc_glob_P SH_ENTRY_P SH_STK_P.
Proof.
intros HIx NEWO. unfold shallow_stmt. intros until errv. intros HP JR NN G DC SPD DHI DAL ST LO LOS SPA HT ERR TP RA A0 A4 K.
subst a0 a4 tp. cbn [hl_segs hl_tp S4L] in *.
eapply (sh_main HIx); first [exact K | exact JR | eassumption | exact HP | exact G | exact DC | exact ST | exact ERR].
Qed.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJ3T.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJ3T.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QR2u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QR2u.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uuoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uuoa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UUr4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UUr4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition VISIT_P : Z := 0x29168.
Definition JCVISIT_P : Z := 0x29100.
Definition EMIT_P : Z := 0x21448.
Definition VISIT_FRAME : Z := 96.

Section Generic.
Variable segs : list Segment.
Variable fn : fnaddrs.

#[using="Type"] Lemma jval_hdr_rd0 : forall s m BS p rc, jval segs fn s m BS p rc ->
exists n tojs pb udel ud rest, In (p, n) BS /\ 48 <= n /\
rw_cells segs m p (jhdr_cells (QmZZ.jtype s) rc tojs pb udel ud ++ rest).
Proof.
intros s m BS p rc J.
destruct (proj1 (jval_split segs fn s m BS p rc) J) as (pb0 & PBS & REST & EBS & OPB & JN).
destruct s as [|[|]| |[|]|kids|kids]; cbn in JN.
- destruct JN as (b & junk & -> & H). exists 48, (fn_bool_to_json_string fn), pb0, 0, 0. eexists.
split; [rewrite EBS; apply in_or_app; left; left; reflexivity|]. split; [lia|]. exact H.
- destruct JN as (bits & ud & udn & uds & -> & _ & H & _). exists 48, (fn_ud_to_json_string fn), pb0, (fn_free_userdata fn), ud. eexists.
split; [rewrite EBS; apply in_or_app; left; left; reflexivity|]. split; [lia|]. exact H.
- destruct JN as (bits & -> & _ & H). exists 48, (fn_dbl_to_json_string fn), pb0, 0, 0. eexists.
split; [rewrite EBS; apply in_or_app; left; left; reflexivity|]. split; [lia|]. exact H.
- destruct JN as (cty & v & junk & -> & _ & H). exists 56, (fn_int_to_json_string fn), pb0, 0, 0. eexists.
split; [rewrite EBS; apply in_or_app; left; left; reflexivity|]. split; [lia|]. exact H.
- destruct JN as (len & pd & pdn & str & junk2 & -> & _ & _ & _ & H & _). exists 56, (fn_str_to_json_string fn), pb0, 0, 0. eexists.
split; [rewrite EBS; apply in_or_app; left; left; reflexivity|]. split; [lia|]. exact H.
- destruct JN as (len & str & junk & -> & Hl & _ & H). exists (str_objsize len), (fn_str_to_json_string fn), pb0, 0, 0. eexists.
split; [rewrite EBS; apply in_or_app; left; left; reflexivity|]. split; [unfold str_objsize; lia|]. exact H.
- destruct JN as (t & TBS & kvs & KBS & -> & H & _). exists 48, (fn_obj_to_json_string fn), pb0, 0, 0. eexists.
split; [rewrite EBS; apply in_or_app; left; left; reflexivity|]. split; [lia|]. exact H.
- destruct JN as (a & ABS & ps & KBS & -> & H & _). exists 48, (fn_arr_to_json_string fn), pb0, 0, 0. eexists.
split; [rewrite EBS; apply in_or_app; left; left; reflexivity|]. split; [lia|]. exact H.
Qed.
#[using="Type"] Lemma jval_hdr_rd : forall s m BS p rc, jval segs fn s m BS p rc ->
exists n tojs pb udel ud, In (p, n) BS /\ 48 <= n /\
rw_cells segs m p (jhdr_cells (QmZZ.jtype s) rc tojs pb udel ud).
Proof.
intros s m BS p rc J. destruct (jval_hdr_rd0 s m BS p rc J) as (n & tojs & pb & udel & ud & rest & HIn & Hn & H).
apply rw_cells_app in H as [H _]. exists n, tojs, pb, udel, ud. auto.
Qed.

#[using="Type"] Lemma odepth_kid_arr : forall kids k, In k kids -> odepth k + 1 <= odepth (Some (Sarr kids)).
Proof.
intros kids k Hin. unfold odepth. destruct k as [s|].
- pose proof (kdepth_in kids s Hin). rewrite sdepth_arr. lia.
- rewrite sdepth_arr. pose proof (kdepth_nonneg kids). lia.
Qed.
#[using="Type"] Lemma odepth_kid_obj : forall kids k, In k kids -> odepth k + 1 <= odepth (Some (Sobj kids)).
Proof.
intros kids k Hin. unfold odepth. destruct k as [s|].
- pose proof (kdepth_in kids s Hin). rewrite sdepth_obj. lia.
- rewrite sdepth_obj. pose proof (kdepth_nonneg kids). lia.
Qed.
#[using="Type"] Lemma odepth_nonneg : forall s, 0 <= odepth s.
Proof. intros [s|]; cbn; [apply sdepth_nonneg | lia]. Qed.
End Generic.

Definition vis_post (segs : list Segment) (lo spv : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
ms' = MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(lo, spv)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo spv.
End RC__1.

Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Section VisitP.
Notation wz := (Z_to_bv 64).

Definition blocks_ok (BS : list blk) : Prop :=
forall a n, In (a, n) BS -> 0 < a /\ a mod 16 = 0 /\ 0 <= n /\ a + n <= alloc_ceiling.

Definition VIS (s : option jshape) : Prop :=
forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (BS : list blk) (p lo spv : Z),
mem_inv rsegs m ->
stk rsegs m lo spv -> 0 <= lo -> lo + VISIT_FRAME * (odepth s + 1) <= spv -> spv < 2^64 ->
jopt rsegs S4F s m BS p -> blocks_ok BS -> alloc_ceiling <= lo ->
bv_unsigned ra mod 2 = 0 ->
evt rsegs (vis_post rsegs lo spv ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
(MS (mkR ra (wz spv) gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 (wz EMIT_P) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz VISIT_P) fc None m (seg_rom rsegs)).

Ltac hbs_tac :=
  let b := fresh "b" in let n := fresh "n" in let H := fresh "H" in
  intros b n H;
  match goal with B : blocks_ok ?BS, E : ?BS = _ |- _ =>
    let Hin := fresh "Hin" in
    assert (Hin : In (b, n) BS) by (rewrite E; rewrite ?in_app_iff; cbn [In]; rewrite ?in_app_iff; tauto);
    destruct (B b n Hin) as (?&?&?&?); repeat split; lia
  end.
#[using="Type"] Lemma vis_null : VIS None.
Proof.
intros until spv. intros MI ST LO0 BUD SPH [-> ->] BOK ACL RA.
unfold VISIT_FRAME, odepth in BUD. unfold EMIT_P, VISIT_P.
pose proof (munch_refl [(lo, spv)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
carve_frame 96%nat ST.

do 17 bstep.

do 5 bstep. bstep. bstep.
replace (ret_pc (wz 0x291c0)) with (wz 0x291c0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

bstep. bstep. bstep. if_true. bstep. bstep. if_false. bstep. if_false.

bstep. bstep.
eapply evt_cut; [eapply jo_get_type_null_P | intros ms' ->].
replace (ret_pc (wz 0x29200)) with (wz 0x29200) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep. bstep. try if_lit. bstep. bstep. try if_lit.

do 13 bstep.
lazymatch goal with H : rw_cells rsegs ?mx (spv + -96) _ |- _ => rename H into FR2 end.
lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST2 end.
release_frame FR2 ST2 spv.
finish.
Qed.

#[using="Type"] Lemma vis_scalar : forall s, QmZZ.jtype s <> JT_OBJECT -> QmZZ.jtype s <> JT_ARRAY -> VIS (Some s).
Proof.
intros s NO NA. intros until spv. intros MI ST LO0 BUD SPH [Hp J] BOK ACL RA.
unfold VISIT_FRAME in BUD. pose proof (odepth_nonneg (Some s)) as DN. unfold EMIT_P, VISIT_P.
destruct (jval_hdr_rd rsegs S4F s m BS p 1 J) as (n & tojs & pb & udel & ud & HIn & Hn & HDR).
destruct (BOK p n HIn) as (P0 & P16 & N0 & PN).
pose proof (QmZZ.jtype_range s) as TYR.
unfold jhdr_cells in HDR.
pose proof (munch_refl [(lo, spv)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
carve_frame 96%nat ST.
do 17 bstep.
do 5 bstep. bstep. bstep.
replace (ret_pc (wz 0x291c0)) with (wz 0x291c0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep. bstep. if_true. bstep. bstep. if_false. bstep. if_false.

bstep. bstep.
lazymatch goal with H : rw_cells rsegs ?mx p _ |- _ => rename H into HDR1 end.
eapply evt_cut; [eapply jo_get_type_P with (rest := []);
[rewrite app_nil_r; unfold jhdr_cells; exact HDR1 | lia | lia | first [assumption | lia] | lia | assumption] | intros ms' (w & ->)].
replace (ret_pc (wz 0x29200)) with (wz 0x29200) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep.
assert (TC : QmZZ.jtype s <= 3 \/ QmZZ.jtype s = 6).
{ destruct s; cbn in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; lia. }
destruct TC as [T3 | T6].
-
bstep. if_falsex. bstep. bstep. if_falsex.
do 13 bstep.
lazymatch goal with H : rw_cells rsegs ?mx (spv + -96) _ |- _ => rename H into FR2 end.
lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST2 end.
release_frame FR2 ST2 spv.
finish.
-
rewrite T6 in *. bstep. try if_lit. bstep. bstep. try if_lit.
do 13 bstep.
lazymatch goal with H : rw_cells rsegs ?mx (spv + -96) _ |- _ => rename H into FR2 end.
lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST2 end.
release_frame FR2 ST2 spv.
finish.
Qed.

#[using="Type"] Lemma agree_blocks : forall BS lo hi m m',
munch [(lo, hi)] m m' -> wmono rsegs m m' -> blocks_ok BS -> alloc_ceiling <= lo -> agree_on rsegs BS m m'.
Proof.
intros BS lo hi m m' MU WM BOK ACL. eapply agree_of_munch; [exact MU | exact WM |].
intros a n Hin. destruct (BOK a n Hin) as (A0 & _ & N0 & AN). cbn. lia.
Qed.

#[using="Type"] Lemma vis_tail :
forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m mc : word -> option byte) (lo p spv : Z) (j16 : list byte),
rw_cells rsegs mc (spv + -96) [CB 16 j16; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs mc lo (spv + -96) ->
munch [(lo, spv)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
bv_unsigned ra mod 2 = 0 -> 0 <= lo -> lo <= spv - 96 -> spv < 2^64 ->
evt rsegs (vis_post rsegs lo spv ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
(MS (mkR x1 (wz (spv + -96)) gp tp t0 t1 t2 (wz p) (wz EMIT_P) a0 a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x29360) fc None mc (seg_rom rsegs)).
Proof.
intros until j16. intros FR ST MU WM MI RA LO0 LO SPH. unfold EMIT_P.
do 6 bstep. bstep. bstep. bstep.
replace (ret_pc (wz 0x2937c)) with (wz 0x2937c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep. bstep. try if_lit. bstep. bstep. try if_lit. bstep. try if_lit.

do 13 bstep.
lazymatch goal with H : rw_cells rsegs ?mx (spv + -96) _ |- _ => rename H into FR2 end.
lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST2 end.
release_frame FR2 ST2 spv.
finish.
Qed.

#[using="Type"] Lemma frame16 : forall m A j0 (w : word) rest,
rw_cells rsegs m A (CB 8 j0 :: C8 w :: rest) -> rw_cells rsegs m A (CB 16 (j0 ++ le8 w) :: rest).
Proof.
intros m A j0 w rest H.
assert (L : length j0 = 8%nat) by (destruct H as [[Hwf _] _]; cbn in Hwf; tauto).
change (CB 8 j0 :: C8 w :: rest) with ([CB 8 j0; C8 w] ++ rest) in H.
change (CB 16 (j0 ++ le8 w) :: rest) with ([CB 16 (j0 ++ le8 w)] ++ rest).
eapply rw_cells_recast_prefix; [exact H | | | cbn; reflexivity].
- cbn [cells_wf cell_wf]. split; [| exact I]. rewrite length_app, L. pose proof (length_le8 w). lia.
- cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
Qed.

#[using="Type"] Lemma arr_loop : forall (fuel : nat) (kids : list (option jshape)),
(forall k, In k kids -> VIS k) ->
forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m mc : word -> option byte) (BS : list blk) (p lo spv pb a : Z)
(PBS AL : list blk) (ps : list Z) (KBS : list (list blk)) (j0 : list byte) (ii : Z),
Z.of_nat (length ps) - ii <= Z.of_nat fuel -> 0 <= ii < Z.of_nat (length ps) -> Z.of_nat (length ps) < 2^63 ->
BS = ((p, 48) :: AL ++ concat KBS) ++ PBS -> alist rsegs S4F m AL a ps ->
length ps = length kids -> length KBS = length kids -> akids rsegs S4F m kids ps KBS ->
blocks_ok BS -> alloc_ceiling <= lo -> 0 <= lo -> lo + 96 * (odepth (Some (Sarr kids)) + 1) <= spv -> spv < 2^64 ->
p + 48 <= lo -> 0 < p ->
rw_cells rsegs mc p [C4 (wz 5); C4 (wz 1); C8 (wz (fn_arr_to_json_string S4F)); C8 (wz pb); C8 (wz 0); C8 (wz 0); C8 (wz a)] ->
rw_cells rsegs mc (spv + -96) [CB 8 j0; C8 (wz ii); C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs mc lo (spv + -96) -> munch [(lo, spv)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
bv_unsigned ra mod 2 = 0 ->
evt rsegs (vis_post rsegs lo spv ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
(MS (mkR x1 (wz (spv + -96)) gp tp t0 t1 t2 (wz p) (wz EMIT_P) a0 (wz ii) a2 a3 a4 a5 a6 a7 c2 c3 c4 c5
(wz (Z.of_nat (length ps))) (wz 766) (wz 7547) s9 s10 s11 t3 t4 t5 t6)
F (wz 0x2931c) fc None mc (seg_rom rsegs)).
Proof.
induction fuel as [|fuel IHf]; intros kids IH; intros until ii;
intros Hfuel Hii LEN63 EBS HAL L1 L2 KIDS BOK ACL LO0 BUD SPH P48 P0 HDR FR ST MU WM MI RA.
{ exfalso. lia. }
unfold EMIT_P. pose proof (odepth_nonneg (Some (Sarr kids))) as DN. pose proof (odepth_nonneg k) as DNk || idtac.
assert (P16 : p mod 16 = 0) by (rewrite EBS in BOK; apply (BOK p 48); left; reflexivity).

bstep. bstep. bstep. bstep.
assert (HALc : alist rsegs S4F mc AL a ps).
{ eapply alist_agree; [exact HAL | eapply agree_blocks; [exact MU | exact WM | exact BOK | exact ACL] |].
intros b Hb. rewrite EBS. apply in_or_app; left. right. apply in_or_app; left. exact Hb. }
unfold array_list_get_idx_entry in *.
call (array_list_get_idx_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc AL a ps ii).
all: lazymatch goal with |- evt _ _ _ => idtac | _ => first [assumption | reflexivity | lia | hbs_tac | match goal with |- ?G => idtac "LEFTOVER" G end; shelve] end.
rewrite (proj2 (Z.ltb_lt ii (Z.of_nat (length ps)))) by lia.

destruct (akids_nth rsegs S4F m kids ps KBS (Z.to_nat ii) (al_nth ps ii) KIDS (al_nth_in ps ii ltac:(lia))) as (k & bs & Hk & Hbs & JO).
pose proof (nth_error_In kids (Z.to_nat ii) Hk) as KIN.
pose proof (odepth_kid_arr kids k KIN) as DK.
assert (BSI : incl bs BS).
{ intros b Hb. rewrite EBS. apply in_or_app; left. right. apply in_or_app; right. apply in_concat. exists bs.
split; [eapply nth_error_In; exact Hbs | exact Hb]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc1 end.
lazymatch goal with H : munch _ m mc1 |- _ => rename H into MU1 end.
lazymatch goal with H : wmono rsegs m mc1 |- _ => rename H into WM1 end.
assert (JOc : jopt rsegs S4F k mc1 bs (al_nth ps ii)).
{ destruct k as [s'|]; cbn in JO |- *; [| exact JO]. destruct JO as [NZ J']. split; [exact NZ|].
eapply (jval_agree rsegs S4F); [exact J' | eapply agree_blocks; [exact MU1 | exact WM1 | exact BOK | exact ACL] | exact BSI]. }
assert (BOKk : blocks_ok bs) by (intros b n Hb; apply BOK; apply BSI; exact Hb).

bstep. bstep. bstep. bstep. bstep. bstep.
call (IH k KIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ bs (al_nth ps ii) lo (spv + -96)).
all: lazymatch goal with |- evt _ _ _ => idtac | _ => first [assumption | reflexivity | (unfold VISIT_FRAME in *; lia) | (vm_compute; reflexivity) | match goal with |- ?G => idtac "LEFTOVER" G end; shelve] end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc2 end.
lazymatch goal with H : munch _ m mc2 |- _ => rename H into MU2 end.
lazymatch goal with H : wmono rsegs m mc2 |- _ => rename H into WM2 end.
lazymatch goal with H : mem_inv rsegs mc2 |- _ => rename H into MI2 end.
lazymatch goal with H : stk rsegs mc2 lo _ |- _ => rename H into ST2 end.
lazymatch goal with H : rw_cells rsegs mc2 p _ |- _ => rename H into HDR2 end.
lazymatch goal with H : rw_cells rsegs mc2 (spv + -96) _ |- _ => rename H into FR2 end.
clear HALc JOc.
bstep. bstep. try if_lit. bstep. try if_lit.

bstep. bstep. bstep. bstep.
destruct (Z_lt_dec (ii + 1) (Z.of_nat (length ps))) as [LT | GE].
- if_falsex.
eapply (IHf kids IH); try eassumption; try lia.
- if_truex.
lazymatch goal with H : rw_cells rsegs ?mx (spv + -96) _ |- _ => eapply frame16 in H end.
eapply vis_tail; try eassumption; try lia.
Qed.

#[using="Type"] Lemma vis_arr : forall kids, (forall s, In (Some s) kids -> VIS (Some s)) -> VIS (Some (Sarr kids)).
Proof.
intros kids IHk. intros until spv. intros MI ST LO0 BUD SPH [Hp J] BOK ACL RA.
assert (IH : forall k, In k kids -> VIS k) by (intros [s'|] Hin; [apply IHk; exact Hin | apply vis_null]).
clear IHk.
destruct (sarr_open rsegs S4F kids m BS p 1 J) as (pb & PBS & a & AL & ps & KBS & EBS & OPB & HDR & HAL & L1 & L2 & KIDS).
assert (PIN : In (p, 48) BS) by (rewrite EBS; apply in_or_app; left; left; reflexivity).
destruct (BOK p 48 PIN) as (P0 & P16 & _ & P48).
pose proof (odepth_nonneg (Some (Sarr kids))) as DN.

assert (LEN63 : Z.of_nat (length ps) < 2^63).
{ destruct (alist_open rsegs S4F m AL a ps HAL) as (arr & size & junk & EAL & _ & ARR & _ & Hlen & Hsz).
assert (AIN : In (arr, 8 * size) BS) by (rewrite EBS, EAL; apply in_or_app; left; right; apply in_or_app; left; right; left; reflexivity).
destruct (BOK arr (8 * size) AIN) as (A0 & _ & _ & AS). unfold VISIT_FRAME in BUD. lia. }
unfold VISIT_FRAME in BUD. unfold EMIT_P, VISIT_P.
unfold jhdr_cells, JT_ARRAY in HDR. cbn [app] in HDR.
pose proof (munch_refl [(lo, spv)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
carve_frame 96%nat ST.
do 17 bstep.
do 5 bstep. bstep. bstep.
replace (ret_pc (wz 0x291c0)) with (wz 0x291c0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep. bstep. if_true. bstep. bstep. if_false. bstep. if_false.

bstep. bstep.
lazymatch goal with H : rw_cells rsegs ?mx p _ |- _ => rename H into HDR1 end.
eapply evt_cut; [eapply jo_get_type_P with (rest := [C8 (wz a)]) (ty := 5);
[unfold jhdr_cells; cbn [app]; exact HDR1 | lia | lia | first [assumption | lia] | lia | assumption] | intros ms' (w & ->)].
replace (ret_pc (wz 0x29200)) with (wz 0x29200) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep. bstep. try if_lit.
bstep. bstep. try if_lit. bstep. bstep. try if_lit.

bstep. bstep. bstep. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
lazymatch goal with H : munch _ m m1 |- _ => rename H into MU1 end.
lazymatch goal with H : wmono rsegs m m1 |- _ => rename H into WM1 end.
assert (HAL1 : alist rsegs S4F m1 AL a ps).
{ eapply alist_agree; [exact HAL | eapply agree_blocks; [exact MU1 | exact WM1 | exact BOK | exact ACL] |].
intros b Hb. rewrite EBS. apply in_or_app; left. right. apply in_or_app; left. exact Hb. }
unfold array_list_length_entry in *.
call (array_list_length_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 AL a ps).
all: lazymatch goal with |- evt _ _ _ => idtac | _ => first [assumption | reflexivity | lia | hbs_tac] end.
clear HAL1.

bstepz.
bstep.
destruct (Z.eq_dec (Z.of_nat (length ps)) 0) as [LZ | LNZ].
-
rewrite LZ in *. try if_lit. try if_true.
lazymatch goal with H : rw_cells rsegs ?mx (spv + -96) _ |- _ => eapply frame16 in H end.
eapply vis_tail; try eassumption; try lia.
- if_falsex.
bstep. bstep. bstep. bstep. bstep. bstep.
eapply (arr_loop (S (length ps)) kids IH) with (ii := 0); try eassumption; try lia.
Qed.

#[using="Type"] Lemma obj_loop : forall (fuel : nat) (kids : list (option jshape)),
(forall k, In k kids -> VIS k) ->
forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m mc : word -> option byte) (BS : list blk) (p lo spv pb0 t : Z)
(PBS TBS : list blk) (es : list oent) (KBS : list (list blk)) (j16 : list byte) (j : nat) (e : oent),
Z.of_nat (length es) - Z.of_nat j <= Z.of_nat fuel -> nth_error es j = Some e ->
obj_view rsegs S4F kids m BS p 1 pb0 PBS t TBS es KBS ->
blocks_ok BS -> alloc_ceiling <= lo -> 0 <= lo -> lo + 96 * (odepth (Some (Sobj kids)) + 1) <= spv -> spv < 2^64 ->
rw_cells rsegs mc (spv + -96) [CB 16 j16; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs mc lo (spv + -96) -> munch [(lo, spv)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
bv_unsigned ra mod 2 = 0 ->
evt rsegs (vis_post rsegs lo spv ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
(MS (mkR x1 (wz (spv + -96)) gp tp t0 t1 t2 (wz p) (wz EMIT_P) a0 a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5
(wz (oe_a e)) (wz 766) (wz 7547) s9 s10 s11 t3 t4 t5 t6)
F (wz 0x29294) fc None mc (seg_rom rsegs)).
Proof.
induction fuel as [|fuel IHf]; intros kids IH; intros until e;
intros Hfuel He OV BOK ACL LO0 BUD SPH FR ST MU WM MI RA.
{ exfalso. assert (L : (j < length es)%nat) by (apply nth_error_Some; congruence). lia. }
unfold EMIT_P. pose proof (odepth_nonneg (Some (Sobj kids))) as DN.

assert (OVc : obj_view rsegs S4F kids mc BS p 1 pb0 PBS t TBS es KBS).
{ eapply obj_view_agree; [exact OV | eapply agree_blocks; [exact MU | exact WM | exact BOK | exact ACL]]. }
destruct (obj_view_entry rsegs S4F kids mc BS p 1 pb0 PBS t TBS es KBS j e OVc He) as (EA0 & EA8 & EIB & [pad ENT] & k & bs & Hk & Hbs & KOK).
assert (TBSI : incl TBS BS).
{ destruct OV as (EBS & _). intros b Hb. rewrite EBS. apply in_or_app; left. right. apply in_or_app; left. exact Hb. }
assert (E32 : oe_a e + 32 <= lo).
{ destruct EIB as (ba & bk & Hin & Hlo & Hhi). destruct (BOK ba bk (TBSI _ Hin)) as (_ & _ & _ & B). lia. }
pose proof (nth_error_In kids j Hk) as KIN.
pose proof (odepth_kid_obj kids k KIN) as DK.
assert (BSI : incl bs BS).
{ destruct OV as (EBS & _). intros b Hb. rewrite EBS. apply in_or_app; left. right. apply in_or_app; right. apply in_concat. exists bs.
split; [eapply nth_error_In; exact Hbs | exact Hb]. }
assert (JOc : jopt rsegs S4F k mc bs (oe_v e)) by (destruct k; exact KOK).
assert (BOKk : blocks_ok bs) by (intros b n Hb; apply BOK; apply BSI; exact Hb).
clear OVc KOK.

bstep. bstep. bstep.

bstep. bstep. bstep. bstep. bstep.
call (IH k KIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ bs (oe_v e) lo (spv + -96)).
all: lazymatch goal with |- evt _ _ _ => idtac | _ => first [assumption | reflexivity | (unfold VISIT_FRAME in *; lia) | (vm_compute; reflexivity) | match goal with |- ?G => idtac "LEFTOVER" G end; shelve] end.
clear ENT JOc.
bstep. bstep. try if_lit. bstep. try if_lit.

rewrite (ohd_skipn es (S j)).
destruct (nth_error es (S j)) as [e'|] eqn:He'.
- lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc2 end.
lazymatch goal with H : munch _ m mc2 |- _ => rename H into MU2 end.
lazymatch goal with H : wmono rsegs m mc2 |- _ => rename H into WM2 end.
assert (OV2 : obj_view rsegs S4F kids mc2 BS p 1 pb0 PBS t TBS es KBS).
{ eapply obj_view_agree; [exact OV | eapply agree_blocks; [exact MU2 | exact WM2 | exact BOK | exact ACL]]. }
destruct (obj_view_entry rsegs S4F kids mc2 BS p 1 pb0 PBS t TBS es KBS (S j) e' OV2 He') as (EA0' & _ & EIB' & _).
assert (E32' : oe_a e' + 32 <= lo).
{ destruct EIB' as (ba & bk & Hin & Hlo & Hhi). destruct (BOK ba bk (TBSI _ Hin)) as (_ & _ & _ & B). lia. }
bstep. if_falsex.
eapply (IHf kids IH) with (j := S j); try eassumption; try lia.
- bstep. try if_lit. try if_true.
eapply vis_tail; try eassumption; try lia.
Qed.

#[using="Type"] Lemma vis_obj : forall kids, (forall s, In (Some s) kids -> VIS (Some s)) -> VIS (Some (Sobj kids)).
Proof.
intros kids IHk. intros until spv. intros MI ST LO0 BUD SPH [Hp J] BOK ACL RA.
assert (IH : forall k, In k kids -> VIS k) by (intros [s'|] Hin; [apply IHk; exact Hin | apply vis_null]).
clear IHk.
assert (POS : forall a n, In (a, n) BS -> 0 < a /\ a mod 16 = 0) by (intros b n Hb; destruct (BOK b n Hb) as (A & B & _); auto).
destruct (jval_obj_view rsegs S4F kids m BS p 1 J POS) as (pb0 & PBS & t & TBS & es & KBS & OV).
pose proof OV as (EBS & OPB & HDR & LH & OT & LE & LK & KIDS).
assert (PIN : In (p, 48) BS) by (rewrite EBS; apply in_or_app; left; left; reflexivity).
destruct (BOK p 48 PIN) as (P0 & P16 & _ & P48).
destruct (obj_view_tbl rsegs S4F kids m BS p 1 pb0 PBS t TBS es KBS OV) as [TIN TINB].
destruct (BOK t 56 TINB) as (T0 & T16 & _ & T56).
pose proof (obj_view_head rsegs S4F kids m BS p 1 pb0 PBS t TBS es KBS OV) as HEAD.
pose proof (odepth_nonneg (Some (Sobj kids))) as DN.
unfold VISIT_FRAME in BUD. unfold EMIT_P, VISIT_P.
unfold jhdr_cells, JT_OBJECT in HDR. cbn [app] in HDR.
pose proof (munch_refl [(lo, spv)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
carve_frame 96%nat ST.
do 17 bstep.
do 5 bstep. bstep. bstep.
replace (ret_pc (wz 0x291c0)) with (wz 0x291c0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep. bstep. if_true. bstep. bstep. if_false. bstep. if_false.

bstep. bstep.
lazymatch goal with H : rw_cells rsegs ?mx p _ |- _ => rename H into HDR1 end.
eapply evt_cut; [eapply jo_get_type_P with (rest := [C8 (wz t)]) (ty := 4);
[unfold jhdr_cells; cbn [app]; exact HDR1 | lia | lia | first [assumption | lia] | lia | assumption] | intros ms' (w & ->)].
replace (ret_pc (wz 0x29200)) with (wz 0x29200) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep. bstep. try if_lit.
bstep. bstep. try if_lit. bstep. bstep. try if_lit. bstep. bstep. try if_lit.

bstep. bstep.
lazymatch goal with H : rw_cells rsegs ?mx p _ |- _ => rename H into HDR2 end.
eapply evt_cut; [eapply jo_get_object_P with (rest := []);
[unfold jhdr_cells, JT_OBJECT; cbn [app]; exact HDR2 | lia | lia | first [assumption | lia] | assumption] | intros ms' (w1 & w2 & ->)].
replace (ret_pc (wz 0x29268)) with (wz 0x29268) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

bstep.
assert (OHD : ohd es = match nth_error es 0%nat with Some x => oe_a x | None => 0 end) by (destruct es; reflexivity).
rewrite OHD in *. clear OHD.
bstep.
destruct (nth_error es 0%nat) as [e0|] eqn:He0.
- lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
lazymatch goal with H : munch _ m m1 |- _ => rename H into MU1 end.
lazymatch goal with H : wmono rsegs m m1 |- _ => rename H into WM1 end.
assert (OV1 : obj_view rsegs S4F kids m1 BS p 1 pb0 PBS t TBS es KBS).
{ eapply obj_view_agree; [exact OV | eapply agree_blocks; [exact MU1 | exact WM1 | exact BOK | exact ACL]]. }
destruct (obj_view_entry rsegs S4F kids m1 BS p 1 pb0 PBS t TBS es KBS 0 e0 OV1 He0) as (EA0 & _ & EIB0 & _).
assert (TBSI : incl TBS BS).
{ intros b Hb. rewrite EBS. apply in_or_app; left. right. apply in_or_app; left. exact Hb. }
assert (E32 : oe_a e0 + 32 <= lo).
{ destruct EIB0 as (ba & bk & Hin & Hlo & Hhi). destruct (BOK ba bk (TBSI _ Hin)) as (_ & _ & _ & B). lia. }
if_falsex.
bstep. bstep. bstep. bstep.
eapply (obj_loop (S (length es)) kids IH) with (j := 0%nat); try eassumption; try lia.
- try if_lit. try if_true.
eapply vis_tail; try eassumption; try lia.
Qed.

#[using="Type"] Theorem vis_all : forall s, VIS s.
Proof.
intros [s|]; [| apply vis_null].
induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2.
- apply vis_scalar; cbn; unfold JT_BOOLEAN, JT_OBJECT, JT_ARRAY; lia.
- apply vis_scalar; cbn; unfold JT_DOUBLE, JT_OBJECT, JT_ARRAY; lia.
- apply vis_scalar; cbn; unfold JT_INT, JT_OBJECT, JT_ARRAY; lia.
- apply vis_scalar; cbn; unfold JT_STRING, JT_OBJECT, JT_ARRAY; lia.
- apply vis_obj. exact IHk.
- apply vis_arr. exact IHk.
Qed.
End VisitP.

Section JsonCVisitP.
Variable HIx : heap_iface S4L.

#[using="Type"] Theorem json_c_visit_P : jo_visit_stmt S4L HIx S4F JCVISIT_P EMIT_P 112 96.
Proof.
unfold jo_visit_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) JO A0 A1 A2 A3 K.
cbn [hl_segs hl_tp S4L] in *. unfold JCVISIT_P.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (BOK : blocks_ok BS).
{ intros b n Hb. destruct (heap_blk S4L HIx _ _ _ _ b n HP ltac:(apply in_or_app; left; exact Hb)) as (N0 & AL16 & B0 & BC & _).
split; [exact B0|]. split; [exact AL16|]. split; [exact N0 | exact BC]. }
pose proof (odepth_nonneg s) as DN.
assert (LO0 : 0 <= lo) by (unfold alloc_ceiling, sp_window_lo, stack_max_size in LO; lia).
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
pose proof LO as ACL. unfold alloc_ceiling, sp_window_lo, stack_max_size in LO.
apply rz_evt; [exact MOK|]. subst a0 a1 a2 a3 tp.
carve_frame 16%nat ST.
do 7 bstep. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
lazymatch goal with H : munch _ m m1 |- _ => rename H into MU1 end.
lazymatch goal with H : wmono rsegs m m1 |- _ => rename H into WM1 end.
assert (JO1 : jopt rsegs S4F s m1 BS p).
{ destruct s as [s'|]; cbn in JO |- *; [| exact JO]. destruct JO as [NZ J]. split; [exact NZ|].
eapply (jval_agree rsegs S4F); [exact J | eapply agree_blocks; [exact MU1 | exact WM1 | exact BOK | exact ACL] | apply incl_refl]. }
call (vis_all s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ BS p lo (bv_unsigned sp + -16)).
all: lazymatch goal with
| |- evt _ _ _ => idtac
| |- jopt _ _ _ _ _ _ => exact JO1
| |- bv_unsigned _ mod 2 = 0 => rewrite unsigned_lit by lia; reflexivity
| _ => first [assumption | reflexivity | (unfold VISIT_FRAME in *; lia) | match goal with |- ?G => idtac "LEFTOVER" G end; shelve] end.
bstep. bstep. bstep. bstep. bstep. try if_lit. bstep. try if_lit.
bstep. bstep. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
lazymatch goal with H : munch _ m m2 |- _ => rename H into MU2 end.
lazymatch goal with H : wmono rsegs m m2 |- _ => rename H into WM2 end.
lazymatch goal with H : mem_inv rsegs m2 |- _ => rename H into MI2 end.
lazymatch goal with H : rw_cells rsegs m2 (bv_unsigned sp + -16) _ |- _ => rename H into FR2 end.
lazymatch goal with H : stk rsegs m2 lo _ |- _ => rename H into ST2 end.
release_frame FR2 ST2 (bv_unsigned sp).
apply evt_RZ_done.
assert (HP2 : HEAP S4L HIx A (BS ++ LB) m2 md) by (heap_now S4L HIx HP MU2 WM2 MI2).
eapply (K _ md m2 0).
- split. { apply ret_statew_intro; [apply fsaved_refl | intros Hf; exact Hf]. }
split. { apply model_vm_only_refl. }
split. { exact ST2. }
split. { eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU2 | exact WM2 |].
eapply (client_outside S4L HIx); [exact HP2 | intros b Hb; apply in_or_app; right; exact Hb | clia |].
solve_clientW S4L HIx HP2. }
eexists. eassumption.
- reflexivity.
- destruct s as [s'|]; cbn in JO |- *; [| exact JO]. destruct JO as [NZ J]. split; [exact NZ|].
eapply (jval_agree rsegs S4F); [exact J | eapply agree_blocks; [exact MU2 | exact WM2 | exact BOK | exact ACL] | apply incl_refl].
- exact HP2.
- cbn [hl_tp S4L]. assumption.
Qed.
End JsonCVisitP.

End RC__2.
