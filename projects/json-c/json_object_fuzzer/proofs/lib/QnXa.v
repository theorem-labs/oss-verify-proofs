(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI Qhd4 QZsi Qfub QCKW QsRG Qnhz QBxa QRjH QsV0 Qn1e QMz4 Q9ox QSpR QXup Lib.GwApply QWxq_c1 Qe4Y QHnV QCcH QfLs Qsw7 QJjn Qwm6 QlKV QsKa QJZd Qw5U Qujl Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QbFI.
Import Qhd4.
Import QZsi.
Import Qfub QCKW.Mq5.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QBxa.Mq0 QRjH QsV0 Qn1e QMz4 Q9ox.Mq0 QSpR.Mq2.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.
Import Qe4Y.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QJZd.Mqg Qw5U.
Import Qujl.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition AREAD : Z := 0x52b40.
Definition RSTAGE : Z := 0x614810.
Definition REAL_READ_CELL : Z := 0xea078.
Definition RS_GLO : Z := 0xc2900.
Definition RS_GHI : Z := 0xc4908.

Lemma unpoisoned_of_zero_shadow2 : forall segs m SB s n glo ghi,
(forall g, glo <= g < ghi -> bytes_at segs m (g + SB) [Z_to_bv 8 0]) ->
glo + SB <= (s / 8 + SB) / 8 * 8 -> ((s + n - 1) / 8 + SB) / 8 * 8 + 8 <= ghi + SB -> 0 < n -> 0 <= s -> 0 <= glo + SB ->
unpoisoned segs m SB s n.
Proof.
intros segs m SB s n glo ghi Z0 Hlo Hhi Hn Hs Hpos. split; [exact Hn|]. split; [|split].
- intros g Hg. apply Z0. Z.div_mod_to_equations. lia.
- exists 0. split; [| left; reflexivity]. apply Z0. Z.div_mod_to_equations. lia.
- intros w Hw.
assert (B : forall i, 0 <= i < 8 -> bytes_at segs m (w * 8 + i) [Z_to_bv 8 0]).
{ intros i Hi. replace (w * 8 + i) with ((w * 8 + i - SB) + SB) by lia. apply Z0. Z.div_mod_to_equations. lia. }
exists (repeat (Z_to_bv 8 0) 8). split; [reflexivity|].
destruct (B 0 ltac:(lia)) as (Hw0 & _ & _).
destruct (B 7 ltac:(lia)) as (_ & Hw7 & _). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat] in Hw7.
split; [lia|]. split; [cbn [length repeat Z.of_nat Pos.of_succ_nat Pos.to_nat Nat.iter]; lia|].
intros i Hi. cbn [repeat length] in Hi.
destruct (B (Z.of_nat i) ltac:(lia)) as (_ & _ & Hb). specialize (Hb 0%nat ltac:(cbn; lia)). cbn [nth_error] in Hb.
rewrite Z.add_0_r in Hb.
rewrite Hb. clear -Hi.
do 8 (destruct i as [|i]; [reflexivity|]). cbn in Hi. lia.
Qed.

Definition globals_avoid (regs : list (Z * Z * Z)) (glo ghi : Z) : bool :=
forallb (fun r : Z * Z * Z => let '(b, sz, szr) := r in ((b + szr <=? 8 * glo) || (8 * ghi <=? b))%bool) regs.
Lemma img_shadow_val_outside : forall regs glo ghi g,
globals_avoid regs glo ghi = true -> glo <= g < ghi -> img_shadow_val regs g = 0.
Proof.
induction regs as [|[[b sz] szr] regs IH]; intros glo ghi g Hav Hg; [reflexivity|].
cbn [globals_avoid forallb] in Hav. apply andb_true_iff in Hav as [H1 H2].
cbn [img_shadow_val].
destruct ((b <=? 8 * g) && (8 * g <? b + szr))%bool eqn:E.
- apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
apply orb_true_iff in H1. destruct H1 as [H1|H1]; apply Z.leb_le in H1; lia.
- apply (IH glo ghi g H2 Hg).
Qed.

Section AReadA.
Context {RC__ : Q6q3.RunConsts}.
Variable J : aj_base asegs.
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs J.

Lemma aread_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (K : TSet)
(p : list byte) (off : word) (data junk : list byte) (cnt lo : Z),
CK J cf ->
a0 = Z_to_bv 64 3 -> a1 = Z_to_bv 64 RSTAGE -> a2 = Z_to_bv 64 cnt -> tp = Z_to_bv 64 A_TP ->
fd_lookup (m_fds (cfg_model cf)) (Z_to_bv 64 3) = Some (FdFile p off) ->
fs_lookup (m_fs (cfg_model cf)) p = Some data ->
1 <= cnt <= 65536 ->
rw_cells asegs m RSTAGE [CB (Z.to_nat cnt) junk] ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 2272 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= 2^47 ->
asan_rt_ok m -> ro_cells asegs m REAL_READ_CELL [C8 (Z_to_bv 64 READ_SYM)] ->
(forall g, RS_GLO <= g < RS_GHI -> bytes_at asegs m (g + A_SB) [Z_to_bv 8 0]) ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (cf' : config),
let bs := file_read data off (Z_to_bv 64 cnt) in
munch [(lo, bv_unsigned sp); (RSTAGE, RSTAGE + cnt)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' RSTAGE [CB (length bs) bs; CB (Z.to_nat cnt - length bs) (skipn (length bs) junk)] ->
CNEXT J cf cf' ->
m_fds (cfg_model cf') = fd_insert (m_fds (cfg_model cf)) (Z_to_bv 64 3) (FdFile p (bv_add off (len_word bs))) ->
m_fs (cfg_model cf') = m_fs (cfg_model cf) ->
AJ J K cf'
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (len_word bs) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J K cf (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AREAD) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros HCK -> -> -> -> Hfd Hfs Hcnt DST ST CEIL LO AL SPH RT RR ZSH MI RA HK. cbv zeta in HK.
unfold AREAD, RSTAGE, REAL_READ_CELL, A_TP in *.
word_range sp SPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (0x614810, 0x614810 + cnt)] m) as MU.

pose proof (proj1 (Forall_forall _ _) RT (0xf2e98, [Z_to_bv 8 1])
ltac:(unfold a4_rt_cells, a4_rt_consts; cbn [app]; repeat (try (left; reflexivity); right))) as INITED.
pose proof (proj1 (Forall_forall _ _) RT (A_GOT_SB, le8 (Z_to_bv 64 A_SB_CELL))
ltac:(unfold a4_rt_cells; apply in_or_app; right; left; reflexivity)) as GOT.
pose proof (proj1 (Forall_forall _ _) RT (A_SB_CELL, le8 (Z_to_bv 64 A_SB))
ltac:(unfold a4_rt_cells; apply in_or_app; right; right; left; reflexivity)) as CELL.
cbn [fst snd] in INITED, GOT, CELL. unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL, ZSH.
apply ro_C8_of_bytes_at in GOT. apply ro_C8_of_bytes_at in CELL.
assert (INITEDc : ro_cells asegs m 0xf2e98 [C1 (Z_to_bv 8 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact INITED]). clear INITED.
apply (aj_evt J).
carve_frame 2128%nat ST.
do 12 step.
step.
eapply try_asan_init_spec; [assumption | exact INITEDc | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia
| lia | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros a1x m2 MU2 WM2 MI2 ST2.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x52b74)) with (Z_to_bv 64 0x52b74) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 6 step.
step.
replace (ret_pc (Z_to_bv 64 READ_SYM)) with (Z_to_bv 64 READ_SYM) by (symmetry; apply ret_pc_even; [unfold READ_SYM; lia|reflexivity]).
apply evt_done.

eapply (read_cps_A J SYS) with (lo := lo) (dst := 0x614810) (cnt := cnt);
[ exact HCK | reflexivity | reflexivity | reflexivity | exact Hfd | exact Hfs | lia | lia | rc_lia_prep; lia
| exact DST | rewrite unsigned_lit by lia; exact ST2 | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact MI2 | rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
set (bs := file_read data off (Z_to_bv 64 cnt)) in *.
intros a1y a2y a3y a4y a5y a6y a7y m3 c3. cbv zeta. intros MU3 WM3 MI3 ST3 DST3 HN3 FDS3 FSE3. fold bs in DST3. fold bs.
pose proof (length_file_read_le data off cnt ltac:(lia)) as LENB. fold bs in LENB.
remember (Z.of_nat (length bs)) as n eqn:En.
assert (Hn : 0 <= n <= cnt) by lia.
rc_lia_prep. unfold alloc_ceiling in CEIL.
clear DST.
transport_after_call asegs m2 m3 MU3 WM3; try match goal with H : mem_inv asegs m2 |- _ => clear H end; clear MU3 WM3.
apply (aj_evt J).
replace (ret_pc (Z_to_bv 64 338832)) with (Z_to_bv 64 338832) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
unfold len_word. rewrite <- En. unfold len_word in HK. rewrite <- En in HK. unfold len_word in FDS3. rewrite <- En in FDS3.
step. if_falsex.
step.

assert (TAILG : forall (xra q0 q1 q2 y1 y2 y3 y4 y5 y6 y7 w1 w2 w3 w4 q3 q4 q5 q6 : word) mz,
munch [(lo, bv_unsigned sp); (6375440, 6375440 + cnt)] m mz -> wmono asegs m mz -> mem_inv asegs mz ->
stk asegs mz lo (bv_unsigned sp + -2128) ->
rw_cells asegs mz (bv_unsigned sp + -2128)
[CB 2080 (firstn 2080 (firstn 2088 (firstn 2096 (firstn 2104 (firstn 2112 (firstn 2120 junk0)))))); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mz 6375440 [CB (length bs) bs; CB (Z.to_nat cnt - length bs) (skipn (length bs) junk)] ->
evt asegs (AJ J K c3)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp (Z_to_bv 64 6444320) q0 q1 q2 sp w1 (Z_to_bv 64 n) y1 y2 y3 y4 y5 y6 y7
w2 w3 w4 s5 s6 s7 s8 s9 s10 s11 q3 q4 q5 q6)
F (Z_to_bv 64 0x52bf0) fc None mz (seg_rom asegs))).
{ intros xra q0 q1 q2 y1 y2 y3 y4 y5 y6 y7 w1 w2 w3 w4 q3 q4 q5 q6 mz MUz WMz MIz STz FRz DSTz.
repeat match goal with H : ro_cells asegs ?mc _ _ |- _ => clear H | H : stk asegs ?mc _ _ |- _ => lazymatch mc with mz => fail | _ => clear H end end.
repeat match goal with H : rw_cells asegs ?mc _ _ |- _ => lazymatch mc with mz => fail | _ => clear H end end.
do 9 step.
apply evt_done. unfold bs in DSTz.
eapply HK; [exact MUz | exact WMz | exact MIz | release_frame FRz STz (bv_unsigned sp); exact STz | exact DSTz | exact HN3 | exact FDS3 | exact FSE3]. }
destruct (Z.eq_dec n 0) as [N0|N1].
{
if_truex. eapply TAILG; [exact MU | exact WM | exact MI3 | exact ST3 | exact FR | exact DST3]. }
if_falsex.
step. step. step.
step. if_falsex.
step. step.
step.
assert (RTPL : forall c, In c a4_rt_cells -> fst c + Z.of_nat (length (snd c)) <= 0x614810 \/ 0x624810 <= fst c).
{ intros c Hc. unfold a4_rt_cells, a4_rt_consts in Hc. cbn [app] in Hc.
repeat (destruct Hc as [<- | Hc];
[cbn [fst snd]; unfold A_GOT_SB, A_SB_CELL; rewrite ?length_le8, ?length_le4;
repeat match goal with |- context [Z.of_nat ?k] => let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v end; lia |]).
destruct Hc. }

assert (UP0 : unpoisoned asegs m A_SB 6375440 n).
{ eapply (unpoisoned_of_zero_shadow2 asegs m A_SB 6375440 n RS_GLO RS_GHI);
[ exact ZSH | unfold RS_GLO, A_SB; cbn; lia | unfold RS_GHI, A_SB; Z.div_mod_to_equations; lia | lia | lia | unfold RS_GLO, A_SB; lia ]. }
assert (SHDJ : forall lo' hi' a k, rc_ceil <= lo' -> shadow_span_lo A_SB 6375440 <= a -> a + k <= shadow_span_hi A_SB 6375440 n ->
disjoint_from [(lo', hi'); (6375440, 6375440 + cnt)] a k).
{ intros lo' hi' a k Hlo' Ha Hk. unfold shadow_span_lo, shadow_span_hi, A_SB in Ha, Hk. cbn [disjoint_from].
split; [left | split; [right | exact I]]; Z.div_mod_to_equations; lia. }
destruct (Z.le_gt_cases n 64) as [Hsmall|Hbig].
2: {
replace (bv_ltu (Z_to_bv 64 (n + -65)) (Z_to_bv 64 (-64))) with true
by (symmetry; unfold bv_ltu; rewrite !unsigned_lit_wrap; apply Z.ltb_lt; Z.div_mod_to_equations; lia).
cbv iota.
step. step. step.
step.
eapply region_is_poisoned_sound_U with (s := 6375440) (n := n) (lo := lo);
[ eapply unpoisoned_transport; [exact UP0 | exact MU | intros a k Ha Hk; apply SHDJ; [lia | exact Ha | exact Hk]]
| eapply asan_rt_ok_transport; [exact RT | exact MU | intros cc Hcc; pose proof (a4_rt_cells_in_img cc Hcc); pose proof (RTPL cc Hcc);
cbn [disjoint_from]; split; [left; lia | split; [lia | exact I]]]
| unfold app_mem, A_SB; lia
| lia
| lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST3
| unfold alloc_ceiling; lia
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact MI3
| rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m4 MU4 WM4 MI4 ST4 UP4 RT4.
lazymatch type of MU4 with munch _ ?mc _ =>
transport_after_call asegs mc m4 MU4 WM4; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU4 WM4 end.
replace (ret_pc (Z_to_bv 64 0x52c9c)) with (Z_to_bv 64 0x52c9c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. step.
step. if_truex.
eapply TAILG; [exact MU | exact WM | exact MI4 | exact ST4 | exact FR | exact DST3]. }

replace (bv_ltu (Z_to_bv 64 (n + -65)) (Z_to_bv 64 (-64))) with false
by (symmetry; unfold bv_ltu; rewrite !unsigned_lit_wrap; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
cbv iota.
do 3 step.
step.
do 2 step.
do 2 step.
do 2 step.
step.
sh_norm.
rewrite (unsigned_lit (2147450880 + (6375440 + n + -1) / 8)) by lia.
rewrite !land_m8_64 by lia.
assert (ZW : forall a, RS_GLO + 2147450880 <= a -> a + 8 <= RS_GHI + 2147450880 -> ro_cells asegs m a [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ intros a Ha1 Ha2. unfold RS_GLO, RS_GHI in *. split; [cbn; split; [reflexivity| exact I]|]. cbn [cells_bytes cbytes app].
split; [lia|]. split; [cbn [length repeat Z.of_nat Pos.of_succ_nat Pos.to_nat Nat.iter app]; lia|].
intros i Hi. cbn [repeat length app] in Hi.
destruct (ZSH (a + Z.of_nat i - 2147450880) ltac:(lia)) as (_ & _ & Hb). specialize (Hb 0%nat ltac:(cbn; lia)). cbn [nth_error] in Hb.
rewrite Z.add_0_r in Hb. replace (a + Z.of_nat i - 2147450880 + 2147450880) with (a + Z.of_nat i) in Hb by lia. rewrite Hb.
clear -Hi. do 8 (destruct i as [|i]; [reflexivity|]). cbn in Hi; lia. }
assert (ZW1 : ro_cells asegs m3 2148247808 [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ eapply ro_cells_transport; [apply ZW; unfold RS_GLO, RS_GHI; lia | exact MU | cbn [disjoint_from cells_size csize Nat.add]; split; [left; lia | split; [right; lia | exact I]]]. }
assert (ZW2 : ro_cells asegs m3 2148247816 [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ eapply ro_cells_transport; [apply ZW; unfold RS_GLO, RS_GHI; lia | exact MU | cbn [disjoint_from cells_size csize Nat.add]; split; [left; lia | split; [right; lia | exact I]]]. }
assert (QC : forall w : Z, (w = 2148247808 \/ w = 2148247816) ->
evt asegs (AJ J K c3)
(MS (mkR (Z_to_bv 64 338832) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp (Z_to_bv 64 6444320) t0 t1 t2 sp (Z_to_bv 64 6375440)
(Z_to_bv 64 n) (Z_to_bv 64 2148247810) (Z_to_bv 64 (2147450880 + (6375440 + n + -1) / 8)) (Z_to_bv 64 (6375440 + n + -1))
(Z_to_bv 64 2148247808) (Z_to_bv 64 w) a6y a7y
(Z_to_bv 64 cnt) (Z_to_bv 64 3) (Z_to_bv 64 (bv_unsigned sp + -2120)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 338912) fc None m3 (seg_rom asegs))).
{ intros w Hw.
destruct Hw as [-> | ->].
- step. step.
replace (bv_extract 0 64 (le_bytes_to_word (repeat (Z_to_bv 8 0) 8))) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity).
step. (rewrite ?(unsigned_lit 0) by lia). try change (Z.lor 0 0) with 0.
step. if_falsex.
eapply TAILG; [exact MU | exact WM | exact MI3 | exact ST3 | exact FR | exact DST3].
- step. step.
replace (bv_extract 0 64 (le_bytes_to_word (repeat (Z_to_bv 8 0) 8))) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity).
step. (rewrite ?(unsigned_lit 0) by lia). try change (Z.lor 0 0) with 0.
step. if_falsex.
eapply TAILG; [exact MU | exact WM | exact MI3 | exact ST3 | exact FR | exact DST3]. }
destruct (Z.le_gt_cases n 48) as [H48|H49].
- replace ((2147450880 + (6375440 + n + -1) / 8) / 8 * 8) with 2148247808 by (Z.div_mod_to_equations; lia). apply QC. left; reflexivity.
- replace ((2147450880 + (6375440 + n + -1) / 8) / 8 * 8) with 2148247816 by (Z.div_mod_to_equations; lia). apply QC. right; reflexivity.
Qed.
End AReadA.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZsi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0TL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0TL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMz4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qe4Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qe4Y.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qujl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qujl.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition AREAD : Z := 0x52768.
Definition RSTAGE : Z := 0x612150.
Definition REAL_READ_CELL : Z := 0xe7c58.
Definition RS_GLO : Z := 0xc2428.
Definition RS_GHI : Z := 0xc4430.

Lemma unpoisoned_of_zero_shadow2 : forall segs m SB s n glo ghi,
(forall g, glo <= g < ghi -> bytes_at segs m (g + SB) [Z_to_bv 8 0]) ->
glo + SB <= (s / 8 + SB) / 8 * 8 -> ((s + n - 1) / 8 + SB) / 8 * 8 + 8 <= ghi + SB -> 0 < n -> 0 <= s -> 0 <= glo + SB ->
unpoisoned segs m SB s n.
Proof.
intros segs m SB s n glo ghi Z0 Hlo Hhi Hn Hs Hpos. split; [exact Hn|]. split; [|split].
- intros g Hg. apply Z0. Z.div_mod_to_equations. lia.
- exists 0. split; [| left; reflexivity]. apply Z0. Z.div_mod_to_equations. lia.
- intros w Hw.
assert (B : forall i, 0 <= i < 8 -> bytes_at segs m (w * 8 + i) [Z_to_bv 8 0]).
{ intros i Hi. replace (w * 8 + i) with ((w * 8 + i - SB) + SB) by lia. apply Z0. Z.div_mod_to_equations. lia. }
exists (repeat (Z_to_bv 8 0) 8). split; [reflexivity|].
destruct (B 0 ltac:(lia)) as (Hw0 & _ & _).
destruct (B 7 ltac:(lia)) as (_ & Hw7 & _). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat] in Hw7.
split; [lia|]. split; [cbn [length repeat Z.of_nat Pos.of_succ_nat Pos.to_nat Nat.iter]; lia|].
intros i Hi. cbn [repeat length] in Hi.
destruct (B (Z.of_nat i) ltac:(lia)) as (_ & _ & Hb). specialize (Hb 0%nat ltac:(cbn; lia)). cbn [nth_error] in Hb.
rewrite Z.add_0_r in Hb.
rewrite Hb. clear -Hi.
do 8 (destruct i as [|i]; [reflexivity|]). cbn in Hi. lia.
Qed.

Definition globals_avoid (regs : list (Z * Z * Z)) (glo ghi : Z) : bool :=
forallb (fun r : Z * Z * Z => let '(b, sz, szr) := r in ((b + szr <=? 8 * glo) || (8 * ghi <=? b))%bool) regs.
Lemma img_shadow_val_outside : forall regs glo ghi g,
globals_avoid regs glo ghi = true -> glo <= g < ghi -> img_shadow_val regs g = 0.
Proof.
induction regs as [|[[b sz] szr] regs IH]; intros glo ghi g Hav Hg; [reflexivity|].
cbn [globals_avoid forallb] in Hav. apply andb_true_iff in Hav as [H1 H2].
cbn [img_shadow_val].
destruct ((b <=? 8 * g) && (8 * g <? b + szr))%bool eqn:E.
- apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
apply orb_true_iff in H1. destruct H1 as [H1|H1]; apply Z.leb_le in H1; lia.
- apply (IH glo ghi g H2 Hg).
Qed.

Section AReadA.
Context {RC__ : Q6q3.RunConsts}.
Variable J : aj_base asegs.
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs J.

Lemma aread_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (K : TSet)
(p : list byte) (off : word) (data junk : list byte) (cnt lo : Z),
CK J cf ->
a0 = Z_to_bv 64 3 -> a1 = Z_to_bv 64 RSTAGE -> a2 = Z_to_bv 64 cnt -> tp = Z_to_bv 64 A_TP ->
fd_lookup (m_fds (cfg_model cf)) (Z_to_bv 64 3) = Some (FdFile p off) ->
fs_lookup (m_fs (cfg_model cf)) p = Some data ->
1 <= cnt <= 65536 ->
rw_cells asegs m RSTAGE [CB (Z.to_nat cnt) junk] ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 2272 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= 2^47 ->
asan_rt_ok m -> ro_cells asegs m REAL_READ_CELL [C8 (Z_to_bv 64 READ_SYM)] ->
(forall g, RS_GLO <= g < RS_GHI -> bytes_at asegs m (g + A_SB) [Z_to_bv 8 0]) ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (cf' : config),
let bs := file_read data off (Z_to_bv 64 cnt) in
munch [(lo, bv_unsigned sp); (RSTAGE, RSTAGE + cnt)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' RSTAGE [CB (length bs) bs; CB (Z.to_nat cnt - length bs) (skipn (length bs) junk)] ->
CNEXT J cf cf' ->
m_fds (cfg_model cf') = fd_insert (m_fds (cfg_model cf)) (Z_to_bv 64 3) (FdFile p (bv_add off (len_word bs))) ->
m_fs (cfg_model cf') = m_fs (cfg_model cf) ->
AJ J K cf'
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (len_word bs) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J K cf (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AREAD) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros HCK -> -> -> -> Hfd Hfs Hcnt DST ST CEIL LO AL SPH RT RR ZSH MI RA HK. cbv zeta in HK.
unfold AREAD, RSTAGE, REAL_READ_CELL, A_TP in *.
word_range sp SPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (0x612150, 0x612150 + cnt)] m) as MU.

pose proof (proj1 (Forall_forall _ _) RT (0xf07d8, [Z_to_bv 8 1])
ltac:(unfold a4_rt_cells, a4_rt_consts; cbn [app]; repeat (try (left; reflexivity); right))) as INITED.
pose proof (proj1 (Forall_forall _ _) RT (A_GOT_SB, le8 (Z_to_bv 64 A_SB_CELL))
ltac:(unfold a4_rt_cells; apply in_or_app; right; left; reflexivity)) as GOT.
pose proof (proj1 (Forall_forall _ _) RT (A_SB_CELL, le8 (Z_to_bv 64 A_SB))
ltac:(unfold a4_rt_cells; apply in_or_app; right; right; left; reflexivity)) as CELL.
cbn [fst snd] in INITED, GOT, CELL. unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL, ZSH.
apply ro_C8_of_bytes_at in GOT. apply ro_C8_of_bytes_at in CELL.
assert (INITEDc : ro_cells asegs m 0xf07d8 [C1 (Z_to_bv 8 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact INITED]). clear INITED.
apply (aj_evt J).
carve_frame 2128%nat ST.
do 12 step.
step.
eapply try_asan_init_spec; [assumption | exact INITEDc | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia
| lia | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros a1x m2 MU2 WM2 MI2 ST2.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x5279c)) with (Z_to_bv 64 0x5279c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 6 step.
step.
replace (ret_pc (Z_to_bv 64 READ_SYM)) with (Z_to_bv 64 READ_SYM) by (symmetry; apply ret_pc_even; [unfold READ_SYM; lia|reflexivity]).
apply evt_done.

eapply (read_cps_A J SYS) with (lo := lo) (dst := 0x612150) (cnt := cnt);
[ exact HCK | reflexivity | reflexivity | reflexivity | exact Hfd | exact Hfs | lia | lia | rc_lia_prep; lia
| exact DST | rewrite unsigned_lit by lia; exact ST2 | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact MI2 | rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
set (bs := file_read data off (Z_to_bv 64 cnt)) in *.
intros a1y a2y a3y a4y a5y a6y a7y m3 c3. cbv zeta. intros MU3 WM3 MI3 ST3 DST3 HN3 FDS3 FSE3. fold bs in DST3. fold bs.
pose proof (length_file_read_le data off cnt ltac:(lia)) as LENB. fold bs in LENB.
remember (Z.of_nat (length bs)) as n eqn:En.
assert (Hn : 0 <= n <= cnt) by lia.
rc_lia_prep. unfold alloc_ceiling in CEIL.
clear DST.
transport_after_call asegs m2 m3 MU3 WM3; try match goal with H : mem_inv asegs m2 |- _ => clear H end; clear MU3 WM3.
apply (aj_evt J).
replace (ret_pc (Z_to_bv 64 337848)) with (Z_to_bv 64 337848) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
unfold len_word. rewrite <- En. unfold len_word in HK. rewrite <- En in HK. unfold len_word in FDS3. rewrite <- En in FDS3.
step. if_falsex.
step.

assert (TAILG : forall (xra q0 q1 q2 y1 y2 y3 y4 y5 y6 y7 w1 w2 w3 w4 q3 q4 q5 q6 : word) mz,
munch [(lo, bv_unsigned sp); (6365520, 6365520 + cnt)] m mz -> wmono asegs m mz -> mem_inv asegs mz ->
stk asegs mz lo (bv_unsigned sp + -2128) ->
rw_cells asegs mz (bv_unsigned sp + -2128)
[CB 2080 (firstn 2080 (firstn 2088 (firstn 2096 (firstn 2104 (firstn 2112 (firstn 2120 junk0)))))); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mz 6365520 [CB (length bs) bs; CB (Z.to_nat cnt - length bs) (skipn (length bs) junk)] ->
evt asegs (AJ J K c3)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp (Z_to_bv 64 6434400) q0 q1 q2 sp w1 (Z_to_bv 64 n) y1 y2 y3 y4 y5 y6 y7
w2 w3 w4 s5 s6 s7 s8 s9 s10 s11 q3 q4 q5 q6)
F (Z_to_bv 64 0x52818) fc None mz (seg_rom asegs))).
{ intros xra q0 q1 q2 y1 y2 y3 y4 y5 y6 y7 w1 w2 w3 w4 q3 q4 q5 q6 mz MUz WMz MIz STz FRz DSTz.
repeat match goal with H : ro_cells asegs ?mc _ _ |- _ => clear H | H : stk asegs ?mc _ _ |- _ => lazymatch mc with mz => fail | _ => clear H end end.
repeat match goal with H : rw_cells asegs ?mc _ _ |- _ => lazymatch mc with mz => fail | _ => clear H end end.
do 9 step.
apply evt_done. unfold bs in DSTz.
eapply HK; [exact MUz | exact WMz | exact MIz | release_frame FRz STz (bv_unsigned sp); exact STz | exact DSTz | exact HN3 | exact FDS3 | exact FSE3]. }
destruct (Z.eq_dec n 0) as [N0|N1].
{
if_truex. eapply TAILG; [exact MU | exact WM | exact MI3 | exact ST3 | exact FR | exact DST3]. }
if_falsex.
step. step. step.
step. if_falsex.
step. step.
step.
assert (RTPL : forall c, In c a4_rt_cells -> fst c + Z.of_nat (length (snd c)) <= 0x612150 \/ 0x622150 <= fst c).
{ intros c Hc. unfold a4_rt_cells, a4_rt_consts in Hc. cbn [app] in Hc.
repeat (destruct Hc as [<- | Hc];
[cbn [fst snd]; unfold A_GOT_SB, A_SB_CELL; rewrite ?length_le8, ?length_le4;
repeat match goal with |- context [Z.of_nat ?k] => let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v end; lia |]).
destruct Hc. }

assert (UP0 : unpoisoned asegs m A_SB 6365520 n).
{ eapply (unpoisoned_of_zero_shadow2 asegs m A_SB 6365520 n RS_GLO RS_GHI);
[ exact ZSH | unfold RS_GLO, A_SB; cbn; lia | unfold RS_GHI, A_SB; Z.div_mod_to_equations; lia | lia | lia | unfold RS_GLO, A_SB; lia ]. }
assert (SHDJ : forall lo' hi' a k, rc_ceil <= lo' -> shadow_span_lo A_SB 6365520 <= a -> a + k <= shadow_span_hi A_SB 6365520 n ->
disjoint_from [(lo', hi'); (6365520, 6365520 + cnt)] a k).
{ intros lo' hi' a k Hlo' Ha Hk. unfold shadow_span_lo, shadow_span_hi, A_SB in Ha, Hk. cbn [disjoint_from].
split; [left | split; [right | exact I]]; Z.div_mod_to_equations; lia. }
destruct (Z.le_gt_cases n 64) as [Hsmall|Hbig].
2: {
replace (bv_ltu (Z_to_bv 64 (n + -65)) (Z_to_bv 64 (-64))) with true
by (symmetry; unfold bv_ltu; rewrite !unsigned_lit_wrap; apply Z.ltb_lt; Z.div_mod_to_equations; lia).
cbv iota.
step. step. step.
step.
eapply region_is_poisoned_sound_U with (s := 6365520) (n := n) (lo := lo);
[ eapply unpoisoned_transport; [exact UP0 | exact MU | intros a k Ha Hk; apply SHDJ; [lia | exact Ha | exact Hk]]
| eapply asan_rt_ok_transport; [exact RT | exact MU | intros cc Hcc; pose proof (a4_rt_cells_in_img cc Hcc); pose proof (RTPL cc Hcc);
cbn [disjoint_from]; split; [left; lia | split; [lia | exact I]]]
| unfold app_mem, A_SB; lia
| lia
| lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST3
| unfold alloc_ceiling; lia
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact MI3
| rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m4 MU4 WM4 MI4 ST4 UP4 RT4.
lazymatch type of MU4 with munch _ ?mc _ =>
transport_after_call asegs mc m4 MU4 WM4; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU4 WM4 end.
replace (ret_pc (Z_to_bv 64 0x528c4)) with (Z_to_bv 64 0x528c4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. step.
step. if_truex.
eapply TAILG; [exact MU | exact WM | exact MI4 | exact ST4 | exact FR | exact DST3]. }

replace (bv_ltu (Z_to_bv 64 (n + -65)) (Z_to_bv 64 (-64))) with false
by (symmetry; unfold bv_ltu; rewrite !unsigned_lit_wrap; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
cbv iota.
do 3 step.
step.
do 2 step.
do 2 step.
do 2 step.
step.
sh_norm.
rewrite (unsigned_lit (2147450880 + (6365520 + n + -1) / 8)) by lia.
rewrite !land_m8_64 by lia.
assert (ZW : forall a, RS_GLO + 2147450880 <= a -> a + 8 <= RS_GHI + 2147450880 -> ro_cells asegs m a [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ intros a Ha1 Ha2. unfold RS_GLO, RS_GHI in *. split; [cbn; split; [reflexivity| exact I]|]. cbn [cells_bytes cbytes app].
split; [lia|]. split; [cbn [length repeat Z.of_nat Pos.of_succ_nat Pos.to_nat Nat.iter app]; lia|].
intros i Hi. cbn [repeat length app] in Hi.
destruct (ZSH (a + Z.of_nat i - 2147450880) ltac:(lia)) as (_ & _ & Hb). specialize (Hb 0%nat ltac:(cbn; lia)). cbn [nth_error] in Hb.
rewrite Z.add_0_r in Hb. replace (a + Z.of_nat i - 2147450880 + 2147450880) with (a + Z.of_nat i) in Hb by lia. rewrite Hb.
clear -Hi. do 8 (destruct i as [|i]; [reflexivity|]). cbn in Hi; lia. }
assert (ZW1 : ro_cells asegs m3 2148246568 [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ eapply ro_cells_transport; [apply ZW; unfold RS_GLO, RS_GHI; lia | exact MU | cbn [disjoint_from cells_size csize Nat.add]; split; [left; lia | split; [right; lia | exact I]]]. }
assert (ZW2 : ro_cells asegs m3 2148246576 [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ eapply ro_cells_transport; [apply ZW; unfold RS_GLO, RS_GHI; lia | exact MU | cbn [disjoint_from cells_size csize Nat.add]; split; [left; lia | split; [right; lia | exact I]]]. }
assert (QC : forall w : Z, (w = 2148246568 \/ w = 2148246576) ->
evt asegs (AJ J K c3)
(MS (mkR (Z_to_bv 64 337848) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp (Z_to_bv 64 6434400) t0 t1 t2 sp (Z_to_bv 64 6365520)
(Z_to_bv 64 n) (Z_to_bv 64 2148246570) (Z_to_bv 64 (2147450880 + (6365520 + n + -1) / 8)) (Z_to_bv 64 (6365520 + n + -1))
(Z_to_bv 64 2148246568) (Z_to_bv 64 w) a6y a7y
(Z_to_bv 64 cnt) (Z_to_bv 64 3) (Z_to_bv 64 (bv_unsigned sp + -2120)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 337928) fc None m3 (seg_rom asegs))).
{ intros w Hw.
destruct Hw as [-> | ->].
- step. step.
replace (bv_extract 0 64 (le_bytes_to_word (repeat (Z_to_bv 8 0) 8))) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity).
step. (rewrite ?(unsigned_lit 0) by lia). try change (Z.lor 0 0) with 0.
step. if_falsex.
eapply TAILG; [exact MU | exact WM | exact MI3 | exact ST3 | exact FR | exact DST3].
- step. step.
replace (bv_extract 0 64 (le_bytes_to_word (repeat (Z_to_bv 8 0) 8))) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity).
step. (rewrite ?(unsigned_lit 0) by lia). try change (Z.lor 0 0) with 0.
step. if_falsex.
eapply TAILG; [exact MU | exact WM | exact MI3 | exact ST3 | exact FR | exact DST3]. }
destruct (Z.le_gt_cases n 48) as [H48|H49].
- replace ((2147450880 + (6365520 + n + -1) / 8) / 8 * 8) with 2148246568 by (Z.div_mod_to_equations; lia). apply QC. left; reflexivity.
- replace ((2147450880 + (6365520 + n + -1) / 8) / 8 * 8) with 2148246576 by (Z.div_mod_to_equations; lia). apply QC. right; reflexivity.
Qed.
End AReadA.
