(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uapi.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl QZsi Qhd4 Qwm6 QCKW Qfub QsRG Qnhz QBxa QRjH QsV0 Qn1e QMz4 Q9ox QSpR QXup Lib.GwApply QWxq_c1 Qe4Y QHnV QCcH QfLs Qsw7 QJjn QRUw QlKV QsKa QJZd QpNt Q6q3 QFZX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QbFI. Import QRBl.
Import QZsi Qhd4.Mq1 Qwm6.Mq3.
Import QCKW.Mq5 Qfub.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QBxa.Mq0 QRjH QsV0 Qn1e QMz4 Q9ox.Mq0 QSpR.Mq2.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.
Import Qe4Y.
Import QHnV QCcH QfLs Qsw7 QJjn QRUw.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QJZd.Mqg QpNt.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Import QFZX.Mq7.

Section MIgetrandomT.
Context {RC__ : Q6q3.RunConsts}.
Variable J : aj_base asegs.
Variable wit : TSet -> Prop.
Hypothesis SYSGT : forall (F : FPF) (fc : FPC), @aj_getrandom_tagged_stmt F fc asegs J wit.

Ltac rt_cell RT c H :=
pose proof (proj1 (Forall_forall _ _) RT c
ltac:(unfold a4_rt_cells, a4_rt_consts; cbn [app]; repeat (first [left; reflexivity | right]))) as H;
cbn [fst snd] in H.

Definition igetrandom_tagged_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (K : TSet) (Kb : list byte -> TSet)
(buf len lo : Z) (junk : list byte),
CK J c ->
unpoisoned asegs m A_SB buf len -> asan_rt_ok m ->
1 <= len <= 64 -> 0x647000 <= buf -> app_mem buf len -> buf + len <= 2^47 ->
a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 len -> (a2 = Z_to_bv 64 0 \/ a2 = Z_to_bv 64 GRND_NONBLOCK) ->
rw_cells asegs m buf [CB (Z.to_nat len) junk] ->
(buf + len <= lo \/ bv_unsigned sp <= buf) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= 2^47 -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(wit K -> exists bs, Z.of_nat (length bs) = len /\ wit (Kb bs)) ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (c' : config) (bs : list byte),
Z.of_nat (length bs) = len ->
munch [(buf, buf + len); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' buf [CB (Z.to_nat len) bs] ->
CNEXT J c c' -> model_vm_only (cfg_model c) (cfg_model c') ->
AJ J (Kb bs) c'
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 len) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J K c (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_IGETRANDOM) fc None m (seg_rom asegs)).

Theorem igetrandom_tagged_sound : igetrandom_tagged_stmt.
Proof.
unfold igetrandom_tagged_stmt.
intros until junk. intros HCK UP RT Hlen Hbuf AM Hb47 Ea0 Ea1 Ea2 DST HbLo ST LO LOS SPA SPH MI RA HW HK.
subst a0 a1. unfold_consts. word_range sp SPR.
rt_cell RT (0xf2e98, [Z_to_bv 8 1]) INITED. apply ro_C1_of_bytes_at in INITED.
rt_cell RT (0xea150, le8 (Z_to_bv 64 0xcf4a0)) REALG. apply ro_C8_of_bytes_at in REALG.
rt_cell RT (A_GOT_SB, le8 (Z_to_bv 64 A_SB_CELL)) GOT. apply ro_C8_of_bytes_at in GOT.
rt_cell RT (A_SB_CELL, le8 (Z_to_bv 64 A_SB)) CELL. apply ro_C8_of_bytes_at in CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
pose proof (munch_refl [(buf, buf + len); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
apply (aj_evt J). unfold A_IGETRANDOM. carve_frame 48%nat ST.
bstep.
do 7 bstep.
do 5 bstep.
bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk _ mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2128) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply try_asan_init_spec; [exact MI | assumption | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; lia
| lia | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros a1x m2 MU2 WM2 MI2 ST1'.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x56e3c)) with (Z_to_bv 64 0x56e3c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 7 bstep.

replace (bv_unsigned sp - 2128) with (bv_unsigned sp + -2128) in * by lia.
carve_frame 16%nat ST1'.
bstep. bstepz. do 9 bstep. bstep. bstep.
do 7 bstep.
apply evt_done.
lazymatch goal with |- AJ _ _ _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ c K ecall_fetch ecall_is) end.
assert (WR : QZDE.wr_at asegs m0 buf len).
{ match goal with H : rw_cells _ m0 buf _ |- _ => pose proof (proj2 H) as W end.
cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r, Z2Nat.id in W by lia. exact W. }
assert (RB : forall bs : list byte, length bs = Z.to_nat len ->
ov_read_bytes asegs (write_to_mem m0 (Z_to_bv 64 buf) bs) (Z_to_bv 64 buf) (Z.to_nat len) = Some bs).
{ intros bs LENB. match goal with H : rw_cells _ m0 buf _ |- _ => pose proof (rw_cells_fill0 m0 buf (Z.to_nat len) junk bs H ltac:(lia)) as D3 end.
destruct D3 as [[_ BA] _]. cbn [cells_bytes cbytes app] in BA. rewrite ?app_nil_r in BA.
match type of BA with bytes_at _ _ _ ?l =>
pose proof (bytes_at_read asegs _ buf l 0 (Z.to_nat len) BA ltac:(lia) ltac:(rewrite length_app; cbn; lia)) as RD end.
rewrite Z.add_0_r in RD. change (Z.to_nat 0) with 0%nat in RD. rewrite skipn_O in RD.
rewrite <- LENB in RD. rewrite firstn_app, Nat.sub_diag, firstn_all in RD. cbn [firstn] in RD. rewrite app_nil_r in RD. rewrite <- LENB. exact RD. }
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@aj_getrandom_tagged_w F fc asegs J wit (SYSGT F fc) R pc mm ro c buf len K
(fun ms' => match ov_read_bytes asegs (ms_mem ms') (Z_to_bv 64 buf) (Z.to_nat len) with Some bs0 => Kb bs0 | None => K end) HCK);
[reflexivity | reflexivity | reflexivity | | lia | unfold TASK_SIZE; lia | exact WR | |] end.
{ unfold getr; cbn. destruct Ea2 as [-> | ->]; [left | right]; apply zext32_flag; unfold GRND_NONBLOCK; lia. }
{ intros HX. destruct (HW HX) as (bs & Hbs & HWb). exists bs. split; [exact Hbs|].
cbn [ms_mem QsRG.Mq0.mkst]. rewrite <- write_to_mem_wbytes. rewrite (RB bs ltac:(lia)). exact HWb. }
intros bs c' Hbs HN VMO.
cbn [ms_mem QsRG.Mq0.mkst].
rewrite <- !write_to_mem_wbytes. rewrite (RB bs ltac:(lia)).
assert (LENB : length bs = Z.to_nat len) by lia.
match goal with H : rw_cells _ m0 buf _ |- _ => rename H into DST0 end.
pose proof (wr_at_store_ok asegs m0 buf _ 0 (length bs) (proj2 DST0) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as SOK2.
rewrite Z.add_0_r in SOK2.
pose proof (mem_inv_store asegs m0 (wa buf) bs MI2 SOK2) as MI3.
assert (MU3 : munch [(buf, buf + len); (lo, bv_unsigned sp)] m (write_to_mem m0 (wa buf) bs)).
{ apply munch_write; [exact MU| lia| lia| cbn [inside]; left; lia]. }
assert (MU1 : munch [(buf, buf + len)] m0 (write_to_mem m0 (wa buf) bs)).
{ apply munch_write; [apply munch_refl| lia| lia| cbn [inside]; left; lia]. }
pose proof (wmono_write asegs m m0 (wa buf) bs WM) as WM3.
pose proof (wmono_write asegs m0 m0 (wa buf) bs (wmono_refl asegs m0)) as WM1.
pose proof (rw_cells_fill0 m0 buf (Z.to_nat len) junk bs DST0 ltac:(lia)) as DST3.
change (write_to_mem m0 (Z_to_bv 64 buf) bs) with (write_to_mem m0 (wa buf) bs).
set (m3 := write_to_mem m0 (wa buf) bs) in *.
assert (UP3 : unpoisoned asegs m3 A_SB buf len).
{ eapply unpoisoned_transport; [exact UP | exact MU3 |].
intros a' k' Ha' Hk'. unfold shadow_span_lo, shadow_span_hi, A_SB in Ha', Hk'. rc_pose_range RC__. unfold alloc_ceiling in *.
assert ((buf + len - 1) / 8 <= 2^44) by (Z.div_mod_to_equations; lia).
cbn [disjoint_from]. split; [unfold app_mem, A_SB, A_HMB in AM; destruct AM as (_ & [AM|AM]); [right | left]; Z.div_mod_to_equations; lia|]. split; [left; Z.div_mod_to_equations; lia| exact I]. }
clear UP MU3 WM3.
transport_after_call asegs m0 m3 MU1 WM1. clear MI2 MU1 WM1 SOK2.
clearbody m3.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
replace (QsRG.Mq0.v_addi (Z_to_bv 64 912920) 4) with (Z_to_bv 64 912924 : word) by (apply bv_eq; vm_compute; reflexivity).
unfold QsRG.Mq0.regupd. simp_regs.
bstep.
do 5 bstep.
unfold len_word. rewrite Hbs.
bstep. if_truex.
bstep.
release_frame FR0 ST1' (bv_unsigned sp + -2128).
assert (STm : stk asegs m3 lo (bv_unsigned sp + -48)) by (eapply stk_merge; [exact ST1' | exact ST2 | lia]).
clear ST1' ST2.
set (ln := len - 1). assert (El : len = ln + 1) by (unfold ln; lia). assert (Hln : 0 <= ln < 64) by lia.
rewrite El in *.

assert (TAIL : forall (xra q0 q1 q2 w0 w1 y1 y2 y3 y4 y5 y6 y7 w2 w3 w4 q3 q4 q5 q6 : word),
evt asegs (AJ J (Kb bs) c') (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp q0 q1 q2 w0 w1 (Z_to_bv 64 (ln + 1)) y1 y2 y3 y4 y5 y6 y7
w2 w3 w4 s5 s6 s7 s8 s9 s10 s11 q3 q4 q5 q6)
F (Z_to_bv 64 0x56eb8) fc None m3 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 w1 y1 y2 y3 y4 y5 y6 y7 w2 w3 w4 q3 q4 q5 q6.
bstep.
do 6 bstep.
bstep. bstep.
apply evt_done.
release_frame FR STm (bv_unsigned sp).
eapply (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 c' bs); [lia | assumption | assumption | exact MI3 | exact STm | | exact HN | exact VMO].
clear - DST3 LENB. rewrite LENB in DST3. rewrite Nat.sub_diag in DST3.
destruct DST3 as [[WF BA] WR]. cbn [cells_wf] in WF. destruct WF as (W1 & W2 & _).
apply length_zero_iff_nil in W2. split; [split|].
- cbn [cells_wf cell_wf]. split; [exact LENB | exact I].
- cbn [cells_bytes cbytes app] in BA |- *. rewrite W2 in BA. rewrite !app_nil_r in *. exact BA.
- cbn [cells_size csize Nat.add] in WR |- *. rewrite Nat.add_0_r in *. exact WR. }
bstep. if_false.
bstep. if_falsex.
bstep. bstep. bstep.
bstep. rewrite (unsigned_lit buf) by lia. rewrite (lxor_ones64 buf) by lia. if_falsex.
bstep. bstep.
bstep. replace (ln + -64) with ((ln + 1) + -65) by lia. rewrite size_test_w by lia. cbv iota.
assert (Hh : buf / 8 <= (buf + ln) / 8 <= buf / 8 + 8) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (buf / 8 + A_SB) UP3 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((buf + ln) / 8 + A_SB) UP3 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
assert (GS0 : forall j, 0 <= j -> buf / 8 + j < (buf + ln) / 8 ->
ov_read_bytes asegs m3 (Z_to_bv 64 (buf / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]).
{ intros j Hj Hjl. apply ov_read1_of_ro.
replace (buf / 8 + 2147450880 + j) with ((buf / 8 + j) + A_SB) by (unfold A_SB; lia).
apply (unpoisoned_gran0 asegs _ _ _ _ _ UP3). replace (buf + (ln + 1) - 1) with (buf + ln) by lia. lia. }
assert (HRL : exists v, ov_read_bytes asegs m3 (Z_to_bv 64 ((buf + ln) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (buf + ln) mod 8 < v))).
{ destruct (unpoisoned_last asegs _ _ _ _ UP3) as (v0 & Hro & Hv). replace (buf + (ln + 1) - 1) with (buf + ln) in Hro, Hv by lia.
exists v0. split; [| exact Hv]. apply ov_read1_of_ro. unfold A_SB in Hro. exact Hro. }
do 2 bstep.
bstep.
bstep.
bstep.
bstep. replace (buf + (ln + 1) + -1) with (buf + ln) by lia.
bstep. do 2 bstep. do 2 bstep.
sh_norm.
replace (2147450880 + buf / 8) with (buf / 8 + 2147450880) by lia.
replace (2147450880 + (buf + ln) / 8) with ((buf + ln) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (buf / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((buf + ln) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 bstep. bstep.

assert (LOOPG : forall (Kn : nat) (i : Z) (xra q0 q1 q2 w0 w1 y4' y5' y6 y7 w2 w3 w4 q3 q4 q5 q6 : word),
Z.to_nat ((buf + ln) / 8 - buf / 8 - i) = Kn -> 0 <= i -> buf / 8 + i < (buf + ln) / 8 ->
evt asegs (AJ J (Kb bs) c') (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp q0 q1 q2 w0 w1 (Z_to_bv 64 (ln + 1))
(Z_to_bv 64 (buf / 8 + 2147450880 + i)) (Z_to_bv 64 ((buf + ln) / 8 + 2147450880)) (Z_to_bv 64 0) y4' y5' y6 y7
w2 w3 w4 s5 s6 s7 s8 s9 s10 s11 q3 q4 q5 q6)
F (Z_to_bv 64 0x5701c) fc None m3 (seg_rom asegs))).
{ clear Hh V1c V2c HRL.
induction Kn as [|Kn IH]; intros i xra q0 q1 q2 w0 w1 y4' y5' y6 y7 w2 w3 w4 q3 q4 q5 q6 HKn Hi Hig; [lia|].
pose proof (GS0 i Hi Hig) as HR.
bstep. rewrite ?zxb_zero. clear HR.
bstep. bstep. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
bstep.
destruct (Z.eq_dec (buf / 8 + i + 1) ((buf + ln) / 8)) as [Heq|Hne].
- if_falsex. bstep. bstep. if_true. apply TAIL.
- if_truex. replace (buf / 8 + 2147450880 + i + 1) with (buf / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
bstep.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply TAIL. }
destruct HRL as (vv & HR & Hv).
assert (Hv8 : 0 <= vv < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c.
bstep. rewrite (sxb_small vv) by lia. clear HR.
bstep. rewrite (unsigned_lit (buf + ln)) by lia. rewrite land7_mod8 by lia.
bstep. bstep. bstep. bstep.
destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
bstep.
destruct (Z.eq_dec (buf / 8) ((buf + ln) / 8)) as [Heq1|Hne1].
+ if_truex. bstep. bstep. if_true. apply TAIL.
+ if_falsex. replace (buf / 8 + 2147450880) with (buf / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((buf + ln) / 8 - buf / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 vv)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((buf + ln) mod 8)) (Z_to_bv 64 vv)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
bstep.
destruct (Z.eq_dec (buf / 8) ((buf + ln) / 8)) as [Heq1|Hne1].
+ if_truex. bstep. bstep. if_true. apply TAIL.
+ if_falsex. replace (buf / 8 + 2147450880) with (buf / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((buf + ln) / 8 - buf / 8 - 0)) 0); lia.
Qed.
End MIgetrandomT.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZsi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0TL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0TL.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpNt.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFZX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFZX.Mq2.

Section MIgetrandomT.
Context {RC__ : Q6q3.RunConsts}.
Variable J : aj_base asegs.
Variable wit : TSet -> Prop.
Hypothesis SYSGT : forall (F : FPF) (fc : FPC), @aj_getrandom_tagged_stmt F fc asegs J wit.

Ltac rt_cell RT c H :=
pose proof (proj1 (Forall_forall _ _) RT c
ltac:(unfold a4_rt_cells, a4_rt_consts; cbn [app]; repeat (first [left; reflexivity | right]))) as H;
cbn [fst snd] in H.

Definition igetrandom_tagged_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (K : TSet) (Kb : list byte -> TSet)
(buf len lo : Z) (junk : list byte),
CK J c ->
unpoisoned asegs m A_SB buf len -> asan_rt_ok m ->
1 <= len <= 64 -> 0x645000 <= buf -> app_mem buf len -> buf + len <= 2^47 ->
a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 len -> (a2 = Z_to_bv 64 0 \/ a2 = Z_to_bv 64 GRND_NONBLOCK) ->
rw_cells asegs m buf [CB (Z.to_nat len) junk] ->
(buf + len <= lo \/ bv_unsigned sp <= buf) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= 2^47 -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(wit K -> exists bs, Z.of_nat (length bs) = len /\ wit (Kb bs)) ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (c' : config) (bs : list byte),
Z.of_nat (length bs) = len ->
munch [(buf, buf + len); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' buf [CB (Z.to_nat len) bs] ->
CNEXT J c c' -> model_vm_only (cfg_model c) (cfg_model c') ->
AJ J (Kb bs) c'
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 len) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J K c (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_IGETRANDOM) fc None m (seg_rom asegs)).

Theorem igetrandom_tagged_sound : igetrandom_tagged_stmt.
Proof.
unfold igetrandom_tagged_stmt.
intros until junk. intros HCK UP RT Hlen Hbuf AM Hb47 Ea0 Ea1 Ea2 DST HbLo ST LO LOS SPA SPH MI RA HW HK.
subst a0 a1. unfold_consts. word_range sp SPR.
rt_cell RT (0xf07d8, [Z_to_bv 8 1]) INITED. apply ro_C1_of_bytes_at in INITED.
rt_cell RT (0xe7d30, le8 (Z_to_bv 64 0xccddc)) REALG. apply ro_C8_of_bytes_at in REALG.
rt_cell RT (A_GOT_SB, le8 (Z_to_bv 64 A_SB_CELL)) GOT. apply ro_C8_of_bytes_at in GOT.
rt_cell RT (A_SB_CELL, le8 (Z_to_bv 64 A_SB)) CELL. apply ro_C8_of_bytes_at in CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
pose proof (munch_refl [(buf, buf + len); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
apply (aj_evt J). unfold A_IGETRANDOM. carve_frame 48%nat ST.
step.
do 7 step.
do 5 step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk _ mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2128) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply try_asan_init_spec; [exact MI | assumption | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; lia
| lia | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros a1x m2 MU2 WM2 MI2 ST1'.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x56a64)) with (Z_to_bv 64 0x56a64) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 7 step.

replace (bv_unsigned sp - 2128) with (bv_unsigned sp + -2128) in * by lia.
carve_frame 16%nat ST1'.
step. stepz. do 9 step. step. step.
do 7 step.
apply evt_done.
lazymatch goal with |- AJ _ _ _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ c K ecall_fetch ecall_is) end.
assert (WR : QZDE.wr_at asegs m0 buf len).
{ match goal with H : rw_cells _ m0 buf _ |- _ => pose proof (proj2 H) as W end.
cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r, Z2Nat.id in W by lia. exact W. }
assert (RB : forall bs : list byte, length bs = Z.to_nat len ->
ov_read_bytes asegs (write_to_mem m0 (Z_to_bv 64 buf) bs) (Z_to_bv 64 buf) (Z.to_nat len) = Some bs).
{ intros bs LENB. match goal with H : rw_cells _ m0 buf _ |- _ => pose proof (rw_cells_fill0 m0 buf (Z.to_nat len) junk bs H ltac:(lia)) as D3 end.
destruct D3 as [[_ BA] _]. cbn [cells_bytes cbytes app] in BA. rewrite ?app_nil_r in BA.
match type of BA with bytes_at _ _ _ ?l =>
pose proof (bytes_at_read asegs _ buf l 0 (Z.to_nat len) BA ltac:(lia) ltac:(rewrite length_app; cbn; lia)) as RD end.
rewrite Z.add_0_r in RD. change (Z.to_nat 0) with 0%nat in RD. rewrite skipn_O in RD.
rewrite <- LENB in RD. rewrite firstn_app, Nat.sub_diag, firstn_all in RD. cbn [firstn] in RD. rewrite app_nil_r in RD. rewrite <- LENB. exact RD. }
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@aj_getrandom_tagged_w F fc asegs J wit (SYSGT F fc) R pc mm ro c buf len K
(fun ms' => match ov_read_bytes asegs (ms_mem ms') (Z_to_bv 64 buf) (Z.to_nat len) with Some bs0 => Kb bs0 | None => K end) HCK);
[reflexivity | reflexivity | reflexivity | | lia | unfold TASK_SIZE; lia | exact WR | |] end.
{ unfold getr; cbn. destruct Ea2 as [-> | ->]; [left | right]; apply zext32_flag; unfold GRND_NONBLOCK; lia. }
{ intros HX. destruct (HW HX) as (bs & Hbs & HWb). exists bs. split; [exact Hbs|].
cbn [ms_mem QsRG.Mq0.mkst]. rewrite <- write_to_mem_wbytes. rewrite (RB bs ltac:(lia)). exact HWb. }
intros bs c' Hbs HN VMO.
cbn [ms_mem QsRG.Mq0.mkst].
rewrite <- !write_to_mem_wbytes. rewrite (RB bs ltac:(lia)).
assert (LENB : length bs = Z.to_nat len) by lia.
match goal with H : rw_cells _ m0 buf _ |- _ => rename H into DST0 end.
pose proof (wr_at_store_ok asegs m0 buf _ 0 (length bs) (proj2 DST0) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as SOK2.
rewrite Z.add_0_r in SOK2.
pose proof (mem_inv_store asegs m0 (wa buf) bs MI2 SOK2) as MI3.
assert (MU3 : munch [(buf, buf + len); (lo, bv_unsigned sp)] m (write_to_mem m0 (wa buf) bs)).
{ apply munch_write; [exact MU| lia| lia| cbn [inside]; left; lia]. }
assert (MU1 : munch [(buf, buf + len)] m0 (write_to_mem m0 (wa buf) bs)).
{ apply munch_write; [apply munch_refl| lia| lia| cbn [inside]; left; lia]. }
pose proof (wmono_write asegs m m0 (wa buf) bs WM) as WM3.
pose proof (wmono_write asegs m0 m0 (wa buf) bs (wmono_refl asegs m0)) as WM1.
pose proof (rw_cells_fill0 m0 buf (Z.to_nat len) junk bs DST0 ltac:(lia)) as DST3.
change (write_to_mem m0 (Z_to_bv 64 buf) bs) with (write_to_mem m0 (wa buf) bs).
set (m3 := write_to_mem m0 (wa buf) bs) in *.
assert (UP3 : unpoisoned asegs m3 A_SB buf len).
{ eapply unpoisoned_transport; [exact UP | exact MU3 |].
intros a' k' Ha' Hk'. unfold shadow_span_lo, shadow_span_hi, A_SB in Ha', Hk'. rc_pose_range RC__. unfold alloc_ceiling in *.
assert ((buf + len - 1) / 8 <= 2^44) by (Z.div_mod_to_equations; lia).
cbn [disjoint_from]. split; [unfold app_mem, A_SB, A_HMB in AM; destruct AM as (_ & [AM|AM]); [right | left]; Z.div_mod_to_equations; lia|]. split; [left; Z.div_mod_to_equations; lia| exact I]. }
clear UP MU3 WM3.
transport_after_call asegs m0 m3 MU1 WM1. clear MI2 MU1 WM1 SOK2.
clearbody m3.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
replace (QsRG.Mq0.v_addi (Z_to_bv 64 902996) 4) with (Z_to_bv 64 903000 : word) by (apply bv_eq; vm_compute; reflexivity).
unfold QsRG.Mq0.regupd. simp_regs.
step.
do 5 step.
unfold len_word. rewrite Hbs.
step. if_truex.
step.
release_frame FR0 ST1' (bv_unsigned sp + -2128).
assert (STm : stk asegs m3 lo (bv_unsigned sp + -48)) by (eapply stk_merge; [exact ST1' | exact ST2 | lia]).
clear ST1' ST2.
set (ln := len - 1). assert (El : len = ln + 1) by (unfold ln; lia). assert (Hln : 0 <= ln < 64) by lia.
rewrite El in *.

assert (TAIL : forall (xra q0 q1 q2 w0 w1 y1 y2 y3 y4 y5 y6 y7 w2 w3 w4 q3 q4 q5 q6 : word),
evt asegs (AJ J (Kb bs) c') (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp q0 q1 q2 w0 w1 (Z_to_bv 64 (ln + 1)) y1 y2 y3 y4 y5 y6 y7
w2 w3 w4 s5 s6 s7 s8 s9 s10 s11 q3 q4 q5 q6)
F (Z_to_bv 64 0x56ae0) fc None m3 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 w1 y1 y2 y3 y4 y5 y6 y7 w2 w3 w4 q3 q4 q5 q6.
step.
do 6 step.
step. step.
apply evt_done.
release_frame FR STm (bv_unsigned sp).
eapply (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 c' bs); [lia | assumption | assumption | exact MI3 | exact STm | | exact HN | exact VMO].
clear - DST3 LENB. rewrite LENB in DST3. rewrite Nat.sub_diag in DST3.
destruct DST3 as [[WF BA] WR]. cbn [cells_wf] in WF. destruct WF as (W1 & W2 & _).
apply length_zero_iff_nil in W2. split; [split|].
- cbn [cells_wf cell_wf]. split; [exact LENB | exact I].
- cbn [cells_bytes cbytes app] in BA |- *. rewrite W2 in BA. rewrite !app_nil_r in *. exact BA.
- cbn [cells_size csize Nat.add] in WR |- *. rewrite Nat.add_0_r in *. exact WR. }
step. if_false.
step. if_falsex.
step. step. step.
step. rewrite (unsigned_lit buf) by lia. rewrite (lxor_ones64 buf) by lia. if_falsex.
step. step.
step. replace (ln + -64) with ((ln + 1) + -65) by lia. rewrite size_test_w by lia. cbv iota.
assert (Hh : buf / 8 <= (buf + ln) / 8 <= buf / 8 + 8) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (buf / 8 + A_SB) UP3 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((buf + ln) / 8 + A_SB) UP3 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
assert (GS0 : forall j, 0 <= j -> buf / 8 + j < (buf + ln) / 8 ->
ov_read_bytes asegs m3 (Z_to_bv 64 (buf / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]).
{ intros j Hj Hjl. apply ov_read1_of_ro.
replace (buf / 8 + 2147450880 + j) with ((buf / 8 + j) + A_SB) by (unfold A_SB; lia).
apply (unpoisoned_gran0 asegs _ _ _ _ _ UP3). replace (buf + (ln + 1) - 1) with (buf + ln) by lia. lia. }
assert (HRL : exists v, ov_read_bytes asegs m3 (Z_to_bv 64 ((buf + ln) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (buf + ln) mod 8 < v))).
{ destruct (unpoisoned_last asegs _ _ _ _ UP3) as (v0 & Hro & Hv). replace (buf + (ln + 1) - 1) with (buf + ln) in Hro, Hv by lia.
exists v0. split; [| exact Hv]. apply ov_read1_of_ro. unfold A_SB in Hro. exact Hro. }
do 2 step.
step.
step.
step.
step. replace (buf + (ln + 1) + -1) with (buf + ln) by lia.
step. do 2 step. do 2 step.
sh_norm.
replace (2147450880 + buf / 8) with (buf / 8 + 2147450880) by lia.
replace (2147450880 + (buf + ln) / 8) with ((buf + ln) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (buf / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((buf + ln) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.

assert (LOOPG : forall (Kn : nat) (i : Z) (xra q0 q1 q2 w0 w1 y4' y5' y6 y7 w2 w3 w4 q3 q4 q5 q6 : word),
Z.to_nat ((buf + ln) / 8 - buf / 8 - i) = Kn -> 0 <= i -> buf / 8 + i < (buf + ln) / 8 ->
evt asegs (AJ J (Kb bs) c') (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp q0 q1 q2 w0 w1 (Z_to_bv 64 (ln + 1))
(Z_to_bv 64 (buf / 8 + 2147450880 + i)) (Z_to_bv 64 ((buf + ln) / 8 + 2147450880)) (Z_to_bv 64 0) y4' y5' y6 y7
w2 w3 w4 s5 s6 s7 s8 s9 s10 s11 q3 q4 q5 q6)
F (Z_to_bv 64 0x56c44) fc None m3 (seg_rom asegs))).
{ clear Hh V1c V2c HRL.
induction Kn as [|Kn IH]; intros i xra q0 q1 q2 w0 w1 y4' y5' y6 y7 w2 w3 w4 q3 q4 q5 q6 HKn Hi Hig; [lia|].
pose proof (GS0 i Hi Hig) as HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (buf / 8 + i + 1) ((buf + ln) / 8)) as [Heq|Hne].
- if_falsex. step. step. if_true. apply TAIL.
- if_truex. replace (buf / 8 + 2147450880 + i + 1) with (buf / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply TAIL. }
destruct HRL as (vv & HR & Hv).
assert (Hv8 : 0 <= vv < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c.
step. rewrite (sxb_small vv) by lia. clear HR.
step. rewrite (unsigned_lit (buf + ln)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (buf / 8) ((buf + ln) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL.
+ if_falsex. replace (buf / 8 + 2147450880) with (buf / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((buf + ln) / 8 - buf / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 vv)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((buf + ln) mod 8)) (Z_to_bv 64 vv)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (buf / 8) ((buf + ln) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL.
+ if_falsex. replace (buf / 8 + 2147450880) with (buf / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((buf + ln) / 8 - buf / 8 - 0)) 0); lia.
Qed.
End MIgetrandomT.
