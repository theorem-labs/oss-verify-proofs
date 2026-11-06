(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn Q6WR QrPc QYIF QrIB Q7UD Qhd4 Qwm6 QlKV QsKa Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.

Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoSetScal.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition jo_set_scalar_A_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (r : jroot) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo 16 errv -> jroot_rep A4H A4F r m BS p ->
a0 = Z_to_bv 64 p ->
(forall ms' md' m' rv,
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
rw_cells asegs m' A_ERRNO [C4 errv] ->
jroot_rep A4H A4F r m' BS p -> HEAPAx A (BS ++ LB) LM FRS B m' md' ->
AJ5 A4L HIx A T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Lemma jroot_hdrA : forall r m BS p,
jroot_rep A4H A4F r m BS p -> r <> JRnull -> List.NoDup (map blk_addr BS) ->
exists n ty tojs pb udel ud rest,
In (p, n) BS /\ Z.of_nat (cells_size (jhdr_cells ty 1 tojs pb udel ud ++ rest)) = n /\ 48 <= n /\ 0 <= ty <= 6 /\
rw_cells asegs m p (jhdr_cells ty 1 tojs pb udel ud ++ rest) /\
(ty = JT_BOOLEAN -> r = JRtree Sbool) /\ (ty = JT_INT -> r = JRtree Sint).
Proof.
intros r m BS p RR NN ND. destruct r as [|s|tojs|]; [exfalso; exact (NN eq_refl)| | |].
- destruct RR as [Hp J].
destruct (jval_hdr asegs A4F s m BS p 1 J ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & _).
exists n, (jtype s), tojs, pb, udel, ud, rest. split; [exact INp|]. split; [exact SZ|]. split; [exact N48|].
split; [apply jtype_range|]. split; [exact HDR|].
split; intros E; destruct s as [|u| |h|kids|kids]; cbn [jtype] in E; try discriminate E; reflexivity.
- destruct RR as (Hp & Htojs & pb & PBS & bits & EBS & OPB & HDR).
exists 48, JT_DOUBLE, tojs, pb, 0, 0, [C8 bits]. split; [rewrite EBS; left; reflexivity|]. split; [reflexivity|]. split; [lia|].
split; [unfold JT_DOUBLE; lia|]. split; [exact HDR|]. split; intros E; discriminate E.
- destruct RR as (Hp & pb & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & CASES).
destruct CASES as [(Hl0 & EDBS & Hfit & junk & HDR) | (Hl0 & pd & pdn & junk & junk2 & EDBS & HPD & HDR & HD)].
+ exists (48 + cap), JT_STRING, (fn_str_to_json_string A4F), pb, 0, 0, [C8 (Z_to_bv 64 len); CB (Z.to_nat cap) (str ++ [Z_to_bv 8 0] ++ junk)].
split; [rewrite EBS; left; reflexivity|]. split; [rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; lia|]. split; [lia|].
split; [unfold JT_STRING; lia|]. split; [exact HDR|]. split; intros E; discriminate E.
+ exists (48 + cap), JT_STRING, (fn_str_to_json_string A4F), pb, 0, 0, [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 pd); CB (Z.to_nat (cap - 8)) junk].
split; [rewrite EBS; left; reflexivity|]. split; [rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; lia|]. split; [lia|].
split; [unfold JT_STRING; lia|]. split; [exact HDR|]. split; intros E; discriminate E.
Qed.

Lemma blk_gran0A : forall A LBx LM FRS B m md a n i, HEAPAx A LBx LM FRS B m md -> In (a, n) LBx -> 0 <= i -> 8 * i + 8 <= n ->
ro_cells asegs m (a / 8 + 2147450880 + i) [C1 (Z_to_bv 8 0)].
Proof.
intros A LBx LM FRS B m md a n i HP Hin Hi Hn.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as SH. unfold shad in SH. cbn [hl_sb hl_segs hla_base A4L A4H] in SH. unfold A_SB in SH.
assert (E : 8 * i / 8 = i) by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
pose proof (shadow_at0 asegs m (a / 8 + 2147450880) n (8 * i) ltac:(lia) ltac:(rewrite E; lia) SH) as X. rewrite E in X. exact X.
Qed.

Lemma jroot_null_decA : forall r : jroot, r = JRnull \/ r <> JRnull.
Proof. intros []; [left; reflexivity | right; discriminate ..]. Qed.

Lemma set_int_A : jo_set_scalar_A_stmt 0x9c88c.
Proof.
unfold jo_set_scalar_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR A0 K.
unfold_consts. unfold A_ERRNO, A_TP in *. subst a0 tp. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m) as WM.
destruct (jroot_null_decA r) as [-> | NN].
{
destruct RR as [-> ->]. cbn [app] in HP.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
do 2 step. step. if_truex. do 3 step.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0) end.
- unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia | solve_clientWA A4L HIx HP].
- exact ERR.
- cbn [jroot_rep]. split; reflexivity.
- cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption]. }
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
destruct (jroot_hdrA r m BS p RR NN ND) as (n & ty & tojs & pb & udel & ud & rest & INp & SZ & N48 & TY & HDR & TB & TI).
assert (Hp : p <> 0) by (destruct r; [exfalso; exact (NN eq_refl) | exact (proj1 RR) ..]).
assert (INpA : In (p, n) (BS ++ LB)) by (apply in_or_app; left; exact INp).
blk_factsA A4L HIx HP p n Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
pose proof (blk_gran0A _ _ _ _ _ _ _ p n 0 HP INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.

destruct (proj1 (rw_cells_app asegs m p _ _) HDR) as [HDRH _]. unfold jhdr_cells in HDRH.
destruct (Z.eq_dec ty JT_INT) as [E | NE].
-
specialize (TI E). subst r ty. clear TB. destruct RR as [_ J].
destruct J as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS, OPB.
unfold jhdr_cells, JT_INT in CELLS. cbn [app] in CELLS.
subst REST. cbn [app] in EBS. subst BS. clear HDR HDRH SH0. cbn [app] in HP.
blk_factsA A4L HIx HP p 56 Hpal2 Hplo2 Hphi2 Hpimg2. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg2.
shadow_nowA A4L HIx HP p 56 SHp.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (p, p + 56)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
do 2 step. step. if_falsex.
do 3 step.
asan_chkA.
step. rewrite sx32_small by (unfold JT_INT; lia). step. step. if_lit.
step.
asan_chkA.
stepz.
try clear SHp. heap_nowA_auto A4L HIx HP HPc. shadow_nowA A4L HIx HPc p 56 SHp. a4l. clear HPc.
step. asan_chkA.
stepz.
step. step. do 3 step.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 1) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |]. apply Forall_cons; [| apply Forall_nil].
right; left. exists p, 56. cbn [fst snd]. split; [in_app_prefix|]. split; [| lia].

intro Hi. apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
* exact (nodup_prefix_suffix ((p, 56) :: PBS) LB p 56 56 (nodup_app_l' _ _ ND0) ltac:(left; reflexivity) Hi).
* exact (nodup_prefix_suffix (((p, 56) :: PBS) ++ LB) LM p 56 56 ND0 ltac:(left; reflexivity) Hi).
* refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP _ Hi). in_app_prefix.
+ exact ERR.
+ cbn [jroot_rep]. split; [exact Hp|].
exists pb_, PBS, [(p, 56)]. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh.
assert (NEa : p <> a).
{ intros <-. pose proof ND as ND'. cbn in ND'. inversion ND' as [|x_ l_ Hni Hnd]; subst. apply Hni. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 56 a k HP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin) NEa).
split; [lia | split; [lia | exact I]].
* exists 0, a1, junk_. split; [reflexivity|]. split; [lia|]. unfold jhdr_cells, JT_INT. cbn [app]. assumption.
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
-
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. unfold JT_INT in NE.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
do 2 step. step. if_falsex.
do 3 step.
asan_chkA.
step. rewrite sx32_small by lia. step. step. if_truex.
step. do 3 step.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | solve_clientWA A4L HIx HP].
+ exact ERR.
+ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F r m _ BS BS); [exact RR | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh. split; [lia | exact I].
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
Qed.
End AJoSetScal.
End RC__1.
End Mq0.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg QZDE QRUw QSL3 QT7b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg QZDE.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QSL3. Import QT7b.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Notation SB0 := 2147450880.

Lemma ro_C1_of_repeatH : forall segs m a v n k,
bytes_at segs m a (repeat v n) -> (k < n)%nat -> ro_cells segs m (a + Z.of_nat k) [C1 v].
Proof.
intros segs m a v n k H Hk.
replace n with (k + (1 + (n - k - 1)))%nat in H by lia. rewrite 2!repeat_app in H.
apply bytes_at_app in H as [_ H]. rewrite repeat_length in H. apply bytes_at_app in H as [H _].
split; [cbn; split; exact I | cbn [cells_bytes cbytes app repeat]; exact H].
Qed.

Section HashCoreA.
Variables (kp kn : Z) (ks slack : list byte) (m : word -> option byte).
Let full := ks ++ Z_to_bv 8 0 :: slack.
Let len := Z.of_nat (length ks).
Hypothesis STR : bytes_at asegs m kp full.
Hypothesis MI : mem_inv asegs m.
Hypothesis AL : kp mod 8 = 0.
Hypothesis KP0 : 0 <= kp.
Hypothesis KN : len + 1 <= kn.
Hypothesis KNhi : kp + kn <= 2^47.

Hypothesis SHB : bytes_at asegs m (kp / 8 + SB0) (shadow_bytes kn).

Lemma key_shadowA : forall i, 0 <= i < kn ->
exists v, ro_cells asegs m ((kp + i) / 8 + SB0) [C1 (Z_to_bv 8 v)]
/\ ( (v = 0 /\ kp + i - (kp + i) mod 8 + 8 <= kp + kn)
\/ (v = kn mod 8 /\ 0 < v < 8 /\ kp + i - (kp + i) mod 8 + v = kp + kn) ).
Proof.
intros i Hi. unfold shadow_bytes in SHB.
assert (G : (kp + i) / 8 = kp / 8 + i / 8) by (Z.div_mod_to_equations; lia).
destruct (Z_lt_le_dec (i / 8) (kn / 8)) as [LT | GE].
- exists 0. split.
+ rewrite G. replace (kp / 8 + i / 8 + SB0) with (kp / 8 + SB0 + Z.of_nat (Z.to_nat (i / 8))) by lia.
apply bytes_at_app in SHB as [SHZ _].
eapply (ro_C1_of_repeatH asegs m); [exact SHZ | lia].
+ left. split; [reflexivity|]. Z.div_mod_to_equations. nia.
- assert (Ei : i / 8 = kn / 8) by (Z.div_mod_to_equations; nia).
assert (R8 : kn mod 8 <> 0) by (Z.div_mod_to_equations; nia).
exists (kn mod 8). split.
+ rewrite G, Ei. apply bytes_at_app in SHB as [_ SHL]. rewrite repeat_length in SHL.
destruct (kn mod 8 =? 0) eqn:E8; [apply Z.eqb_eq in E8; lia|].
replace (kp / 8 + SB0 + Z.of_nat (Z.to_nat (kn / 8))) with (kp / 8 + kn / 8 + SB0) in SHL by lia.
split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact SHL].
+ right. split; [reflexivity|]. pose proof (Z.mod_pos_bound kn 8 ltac:(lia)). split; [lia|]. Z.div_mod_to_equations. nia.
Qed.

Definition loop_postA (x1 sp gp tp x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
(ms' : machine_state) : Prop :=
exists (j' : Z) (u0 u1 u2 a2' a3' a4' a5' a7' u3 u4 u5 u6 : word),
0 <= j' /\ 1 <= len - j' <= 12 /\
ms' = MS (mkR x1 sp gp tp u0 u1 u2 (Z_to_bv 64 (kp + j')) (Z_to_bv 64 SB0) (Z_to_bv 64 (len - j')) (Z_to_bv 64 (kp + j')) a2' a3' a4' a5' (Z_to_bv 64 12) a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6)
F (Z_to_bv 64 0xa1224) fc None m (seg_rom asegs).

Lemma hash_loopA :
forall (k : nat) (j : Z) (x1 sp gp tp t0 t1 t2 a2 a3 a4 a5 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32),
(k = Z.to_nat (len - j))%nat -> 0 <= j -> 12 < len - j ->
evt asegs (loop_postA x1 sp gp tp x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc)
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 (kp + j)) (Z_to_bv 64 SB0) (Z_to_bv 64 (len - j)) (Z_to_bv 64 (kp + j)) a2 a3 a4 a5 (Z_to_bv 64 12) a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F (Z_to_bv 64 0xa0e34) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind; intros until fc; intros Hk Hj Hr.
pose proof (bytes_at_bound _ _ _ _ STR) as AB. unfold full in AB. rewrite length_app in AB. cbn [length] in AB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_read asegs m kp full (j + 0) 4 STR ltac:(lia) ltac:(unfold full; rewrite length_app; cbn; lia)) as RD0.
pose proof (bytes_at_read asegs m kp full (j + 4) 4 STR ltac:(lia) ltac:(unfold full; rewrite length_app; cbn; lia)) as RD1.
pose proof (bytes_at_read asegs m kp full (j + 8) 4 STR ltac:(lia) ltac:(unfold full; rewrite length_app; cbn; lia)) as RD2.
replace (kp + (j + 0)) with (kp + j) in RD0 by lia.

destruct (key_shadowA j ltac:(lia)) as (v1 & SH1 & Hv1).
step. step. sh_norm.
lazymatch goal with |- evt ?sg ?Q (MS ?R ?F _ ?fc ?rv ?mm ?ro) =>
eapply evt_cut with (P := fun ms => exists u v : word, ms = MS (bvmap_set 12 u (bvmap_set 17 v R)) F (Z_to_bv 64 0xa0e44) fc rv mm ro) end.
{ step. destruct Hv1 as [[-> Hfull] | (-> & Hv8 & Hend)]; [| exfalso; lia].
rewrite sxb_zero. step. if_false. apply evt_done. do 2 eexists. reflexivity. }
cbv beta. intros ms1 (u1 & w1 & ->). clear SH1.

destruct (key_shadowA (j + 4) ltac:(lia)) as (v2 & SH2 & Hv2). replace (kp + (j + 4)) with (kp + j + 4) in SH2, Hv2, RD1 by lia.
step. step. step. sh_norm. change (4 / 8) with 0 in *. rewrite ?Z.add_0_r in *.
lazymatch goal with |- evt ?sg ?Q (MS ?R ?F _ ?fc ?rv ?mm ?ro) =>
eapply evt_cut with (P := fun ms => exists u v w : word, ms = MS (bvmap_set 5 u (bvmap_set 6 v (bvmap_set 17 w R))) F (Z_to_bv 64 0xa0e5c) fc rv mm ro) end.
{ step. step.
destruct Hv2 as [[-> Hfull] | (-> & Hv8 & Hend)].
- rewrite sxb_zero. step. if_false. apply evt_done. do 3 eexists. reflexivity.
- rewrite (sxb_small (kn mod 8)) by lia. step. if_truex.
step. rewrite (unsigned_lit (kp + j + 4)) by lia. rewrite land7_mod8 by lia.
step. step. if_truex.
apply evt_done. do 3 eexists. reflexivity. }
cbv beta. intros ms2 (u2 & w2 & w2' & ->). clear SH2.

destruct (key_shadowA (j + 8) ltac:(lia)) as (v3 & SH3 & Hv3). replace (kp + (j + 8)) with (kp + j + 8) in SH3, Hv3, RD2 by lia.
step. step. step. sh_norm.
lazymatch goal with |- evt ?sg ?Q (MS ?R ?F _ ?fc ?rv ?mm ?ro) =>
eapply evt_cut with (P := fun ms => exists u v w : word, ms = MS (bvmap_set 6 u (bvmap_set 7 v (bvmap_set 5 w R))) F (Z_to_bv 64 0xa0e74) fc rv mm ro) end.
{ step. step.
destruct Hv3 as [[-> Hfull] | (-> & Hv8 & Hend)].
- rewrite sxb_zero. step. if_false. apply evt_done. do 3 eexists. reflexivity.
- rewrite (sxb_small (kn mod 8)) by lia. step. if_truex.
step. rewrite (unsigned_lit (kp + j + 8)) by lia. rewrite land7_mod8 by lia.
step. step. if_truex.
apply evt_done. do 3 eexists. reflexivity. }
cbv beta. intros ms3 (u3 & w3 & w3' & ->). clear SH3.
do 43 (hstep sp).
replace (kp + j + 12) with (kp + (j + 12)) by lia. replace (len - j + -12) with (len - (j + 12)) by lia.
step.
destruct (Z.lt_ge_cases 12 (len - (j + 12))) as [LT | GE].
- if_truex. eapply (IH (Z.to_nat (len - (j + 12)))); lia.
- if_falsex. step. apply evt_done. unfold loop_postA. exists (j + 12). do 12 eexists.
split; [lia|]. split; [lia|]. reflexivity.
Qed.

Definition fin_postA (x1 sp gp tp : word) (p : Z) (x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
(ms' : machine_state) : Prop :=
exists (u0 u1 u2 a0' a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 : word),
ms' = MS (mkR x1 sp gp tp u0 u1 u2 (Z_to_bv 64 p) (Z_to_bv 64 SB0) a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6)
F (Z_to_bv 64 0xa18d8) fc None m (seg_rom asegs).

Tactic Notation "cut2" constr(PCJ) uconstr(iA) uconstr(iB) := lazymatch goal with |- evt ?sg ?Q (MS ?R ?F _ ?fc ?rv ?mm ?ro) =>
eapply evt_cut with (P := fun ms => exists u v : word, ms = MS (bvmap_set (iA : reg) u (bvmap_set (iB : reg) v R)) F (Z_to_bv 64 PCJ) fc rv mm ro) end.
Tactic Notation "cut3" constr(PCJ) uconstr(iA) uconstr(iB) uconstr(iC) := lazymatch goal with |- evt ?sg ?Q (MS ?R ?F _ ?fc ?rv ?mm ?ro) =>
eapply evt_cut with (P := fun ms => exists u v w : word, ms = MS (bvmap_set (iA : reg) u (bvmap_set (iB : reg) v (bvmap_set (iC : reg) w R))) F (Z_to_bv 64 PCJ) fc rv mm ro) end.
Ltac fin2 := apply evt_done; do 2 eexists; reflexivity.
Ltac fin3 := apply evt_done; do 3 eexists; reflexivity.
Ltac after2 := cbv beta; let u := fresh "u" in let v := fresh "u" in intros ? (u & v & ->).
Ltac after3 := cbv beta; let u := fresh "u" in let v := fresh "u" in let w := fresh "u" in intros ? (u & v & w & ->).

Ltac kshad OFF SH Hv := let v := fresh "v" in destruct (key_shadowA OFF ltac:(lia)) as (v & SH & Hv); rewrite ?Z.add_assoc in SH, Hv.

Ltac krd OFF N RD := pose proof (bytes_at_read asegs m kp full OFF N STR ltac:(lia) ltac:(unfold full; rewrite length_app; cbn; lia)) as RD;
rewrite ?Z.add_assoc in RD.

Ltac arms2 Hv slow := destruct Hv as [[-> ?] | (-> & ? & ?)];
[ rewrite sxb_zero; step; if_false; fin2 | rewrite (sxb_small (kn mod 8)) by lia; step; if_truex; slow; fin2 ].
Ltac arms3 Hv slow := destruct Hv as [[-> ?] | (-> & ? & ?)];
[ rewrite sxb_zero; step; if_false; fin3 | rewrite (sxb_small (kn mod 8)) by lia; step; if_truex; slow; fin3 ].
Ltac slow_b := step; rewrite unsigned_lit by lia; rewrite land7_mod8 by lia; step; if_truex.
Ltac slow_w := step; rewrite unsigned_lit by lia; rewrite land7_mod8 by lia; step; step; if_truex.

Lemma tail12A :
forall (j : Z) (x1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32),
0 <= j -> len - j = 12 ->
evt asegs (fin_postA x1 sp gp tp (kp + j) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc)
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 (kp + j)) (Z_to_bv 64 SB0) a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F (Z_to_bv 64 0xa1520) fc None m (seg_rom asegs)).
Proof.
intros until fc; intros Hj Hr.
pose proof (bytes_at_bound _ _ _ _ STR) as AB. unfold full in AB. rewrite length_app in AB. cbn [length] in AB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
krd (j + 0) 4%nat RD0. krd (j + 4) 4%nat RD1. krd (j + 8) 4%nat RD2. rewrite ?Z.add_0_r in RD0.

step. kshad (j + 8) SH3 Hv3. step. step. sh_norm.
cut2 0xa1534 11%bv 12%bv; [ step; arms2 Hv3 slow_w | after2 ]. clear SH3.

step. kshad (j + 4) SH2 Hv2. step. step. sh_norm.
cut3 0xa154c 12%bv 11%bv 16%bv; [ step; step; arms3 Hv2 slow_w | after3 ]. clear SH2.

kshad (j + 0) SH1 Hv1. rewrite ?Z.add_0_r in SH1, Hv1. step. step. sh_norm.
cut3 0xa1560 12%bv 10%bv 16%bv; [ step; step; arms3 Hv1 slow_w | after3 ]. clear SH1.
step. do 3 (hstep sp). step.
apply evt_done. unfold fin_postA. do 15 eexists. reflexivity.
Qed.

Tactic Notation "bsiteA" constr(OFF) constr(PCJ) :=
let SH := fresh "SH" in let Hv := fresh "Hv" in
kshad OFF SH Hv; step; step; sh_norm; cut2 PCJ 11%bv 12%bv; [ step; arms2 Hv slow_b | after2 ]; clear SH.

Ltac tail_intro := intros until fc; intros Hj Hr;
pose proof (bytes_at_bound _ _ _ _ STR) as AB; unfold full in AB; rewrite length_app in AB; cbn [length] in AB;
pose proof (munch_refl [] m) as MU; pose proof (wmono_refl asegs m) as WM.

Definition tail_stmtA (pc : Z) (rmin : Z) : Prop :=
forall (j : Z) (x1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32),
0 <= j -> rmin <= len - j <= 12 ->
evt asegs (fin_postA x1 sp gp tp (kp + j) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc)
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 (kp + j)) (Z_to_bv 64 SB0) a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

Lemma tail8A : tail_stmtA 0xa14e8 8.
Proof.
unfold tail_stmtA. tail_intro.
krd (j + 0) 4%nat RD0. krd (j + 4) 4%nat RD1. rewrite ?Z.add_0_r in RD0.
step. kshad (j + 4) SH2 Hv2. step. step. sh_norm.
cut2 0xa14fc 11%bv 12%bv; [ step; arms2 Hv2 slow_w | after2 ]. clear SH2.
kshad (j + 0) SH1 Hv1. rewrite ?Z.add_0_r in SH1, Hv1. step. step. sh_norm.
cut3 0xa1510 11%bv 10%bv 12%bv; [ step; step; arms3 Hv1 slow_w | after3 ]. clear SH1.
step. do 2 (hstep sp). step.
apply evt_done. unfold fin_postA. do 15 eexists. reflexivity.
Qed.

Lemma tail9A : tail_stmtA 0xa14cc 9.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 8) 1%nat RD.
step. bsiteA (j + 8) 0xa14e0. step. hstep sp.
apply tail8A; lia.
Qed.

Lemma tail10A : tail_stmtA 0xa14ac 10.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 9) 1%nat RD.
step. bsiteA (j + 9) 0xa14c0. step. do 2 (hstep sp).
apply tail9A; lia.
Qed.

Lemma tail11A : tail_stmtA 0xa148c 11.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 10) 1%nat RD.
step. bsiteA (j + 10) 0xa14a0. step. do 2 (hstep sp).
apply tail10A; lia.
Qed.

Lemma tail4A : tail_stmtA 0xa15d0 4.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 0) 4%nat RD0. rewrite ?Z.add_0_r in RD0.
kshad (j + 0) SH1 Hv1. rewrite ?Z.add_0_r in SH1, Hv1. step. step. sh_norm.
cut2 0xa15e0 10%bv 11%bv; [ step; arms2 Hv1 slow_w | after2 ]. clear SH1.
step. step. hstep sp.
apply evt_done. unfold fin_postA. do 15 eexists. reflexivity.
Qed.
Lemma tail5A : tail_stmtA 0xa15b4 5.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 4) 1%nat RD.
step. bsiteA (j + 4) 0xa15c8. step. hstep sp.
apply tail4A; lia.
Qed.
Lemma tail6A : tail_stmtA 0xa1594 6.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 5) 1%nat RD.
step. bsiteA (j + 5) 0xa15a8. step. do 2 (hstep sp).
apply tail5A; lia.
Qed.
Lemma tail7A : tail_stmtA 0xa1574 7.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 6) 1%nat RD.
step. bsiteA (j + 6) 0xa1588. step. do 2 (hstep sp).
apply tail6A; lia.
Qed.

Lemma tail1A : tail_stmtA 0xa1280 1.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 0) 1%nat RD. rewrite ?Z.add_0_r in RD.
kshad (j + 0) SH1 Hv1. rewrite ?Z.add_0_r in SH1, Hv1. step. step. sh_norm.
cut2 0xa1480 10%bv 11%bv.
{ step. destruct Hv1 as [[-> ?] | (-> & ? & ?)].
- rewrite sxb_zero. step. if_true. fin2.
- rewrite (sxb_small (kn mod 8)) by lia. step. if_falsex. slow_b. fin2. }
after2. clear SH1.
step. hstep sp. step.
apply evt_done. unfold fin_postA. do 15 eexists. reflexivity.
Qed.
Lemma tail2A : tail_stmtA 0xa1260 2.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 1) 1%nat RD.
step. bsiteA (j + 1) 0xa1274. step. do 2 (hstep sp).
apply tail1A; lia.
Qed.
Lemma tail3A : tail_stmtA 0xa1240 3.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 2) 1%nat RD.
step. bsiteA (j + 2) 0xa1254. step. do 2 (hstep sp).
apply tail2A; lia.
Qed.

Definition epi_postA (x1 sp gp tp : word) (p : Z) (x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
(ms' : machine_state) : Prop :=
exists (u0 u1 u2 a0' a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 : word),
ms' = MS (mkR x1 sp gp tp u0 u1 u2 (Z_to_bv 64 p) (Z_to_bv 64 SB0) a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6)
F (Z_to_bv 64 0xa1964) fc None m (seg_rom asegs).

Lemma finmixA :
forall (p : Z) (x1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32),
evt asegs (epi_postA x1 sp gp tp p x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc)
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 p) (Z_to_bv 64 SB0) a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F (Z_to_bv 64 0xa18d8) fc None m (seg_rom asegs)).
Proof.
intros. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
do 35 (hstep sp).
apply evt_done. unfold epi_postA. do 15 eexists. reflexivity.
Qed.

Lemma fin_epiA : forall x1 sp gp tp p x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc ms,
fin_postA x1 sp gp tp p x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc ms ->
evt asegs (epi_postA x1 sp gp tp p x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc) ms.
Proof. intros until ms. intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). apply finmixA. Qed.

Lemma dispatchA :
forall (j : Z) (x1 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32),
0 <= j -> 0 <= len - j <= 12 ->
evt asegs (epi_postA x1 sp gp tp (kp + j) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc)
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 (kp + j)) (Z_to_bv 64 SB0) (Z_to_bv 64 (len - j)) a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F (Z_to_bv 64 0xa1224) fc None m (seg_rom asegs)).
Proof.
intros until fc; intros Hj Hr.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (CASES : exists r, len - j = r /\ (r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/ r = 10 \/ r = 11 \/ r = 12)) by (exists (len - j); lia).
destruct CASES as (r & Er & Hcase). rewrite Er.
destruct Hcase as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]];
(do 6 step);
step.
- apply evt_done. unfold epi_postA. do 15 eexists. reflexivity.
- eapply evt_cut; [apply tail1A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail2A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail3A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail4A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail5A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail6A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail7A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail8A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail9A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail10A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail11A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail12A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
Qed.

Lemma word_pathA :
forall (x1 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32),
evt asegs (fun ms' => exists j, 0 <= j <= len /\ epi_postA x1 sp gp tp (kp + j) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc ms')
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 kp) (Z_to_bv 64 SB0) (Z_to_bv 64 len) a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F (Z_to_bv 64 0xa0e1c) fc None m (seg_rom asegs)).
Proof.
intros. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as AB. unfold full in AB. rewrite length_app in AB. cbn [length] in AB.
step. step.
destruct (Z.lt_ge_cases len 13) as [LT | GE].
- if_truex. step. step.
replace (Z_to_bv 64 kp) with (Z_to_bv 64 (kp + 0)) by (f_equal; lia). replace (Z_to_bv 64 len) with (Z_to_bv 64 (len - 0)) by (f_equal; lia).
eapply evt_cut; [apply dispatchA; lia |]. intros ms Hp. apply evt_done. exists 0. split; [lia | exact Hp].
- if_falsex. step. step. step. step.
replace (Z_to_bv 64 kp) with (Z_to_bv 64 (kp + 0)) by (f_equal; lia). replace (Z_to_bv 64 len) with (Z_to_bv 64 (len - 0)) by (f_equal; lia).
eapply evt_cut; [eapply (hash_loopA (Z.to_nat (len - 0)) 0); lia |].
intros ms (j' & u0 & u1 & u2 & a2' & a3' & a4' & a5' & a7' & u3 & u4 & u5 & u6 & Hj' & Hr' & ->).
eapply evt_cut; [apply dispatchA; lia |]. intros ms Hp. apply evt_done. exists j'. split; [lia | exact Hp].
Qed.
End HashCoreA.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg QZDE.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QSL3. Import QT7b.Mq0.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Notation SB0 := 2147450880.

Lemma ro_C1_of_repeatH : forall segs m a v n k,
bytes_at segs m a (repeat v n) -> (k < n)%nat -> ro_cells segs m (a + Z.of_nat k) [C1 v].
Proof.
intros segs m a v n k H Hk.
replace n with (k + (1 + (n - k - 1)))%nat in H by lia. rewrite 2!repeat_app in H.
apply bytes_at_app in H as [_ H]. rewrite repeat_length in H. apply bytes_at_app in H as [H _].
split; [cbn; split; exact I | cbn [cells_bytes cbytes app repeat]; exact H].
Qed.

Section HashCoreA.
Variables (kp kn : Z) (ks slack : list byte) (m : word -> option byte).
Let full := ks ++ Z_to_bv 8 0 :: slack.
Let len := Z.of_nat (length ks).
Hypothesis STR : bytes_at asegs m kp full.
Hypothesis MI : mem_inv asegs m.
Hypothesis AL : kp mod 8 = 0.
Hypothesis KP0 : 0 < kp.
Hypothesis KN : len + 1 <= kn.
Hypothesis KNhi : kp + kn <= 2^47.

Hypothesis SHB : bytes_at asegs m (kp / 8 + SB0) (shadow_bytes kn).

Lemma key_shadowA : forall i, 0 <= i < kn ->
exists v, ro_cells asegs m ((kp + i) / 8 + SB0) [C1 (Z_to_bv 8 v)]
/\ ( (v = 0 /\ kp + i - (kp + i) mod 8 + 8 <= kp + kn)
\/ (v = kn mod 8 /\ 0 < v < 8 /\ kp + i - (kp + i) mod 8 + v = kp + kn) ).
Proof.
intros i Hi. unfold shadow_bytes in SHB.
assert (G : (kp + i) / 8 = kp / 8 + i / 8) by (Z.div_mod_to_equations; lia).
destruct (Z_lt_le_dec (i / 8) (kn / 8)) as [LT | GE].
- exists 0. split.
+ rewrite G. replace (kp / 8 + i / 8 + SB0) with (kp / 8 + SB0 + Z.of_nat (Z.to_nat (i / 8))) by lia.
apply bytes_at_app in SHB as [SHZ _].
eapply (ro_C1_of_repeatH asegs m); [exact SHZ | lia].
+ left. split; [reflexivity|]. Z.div_mod_to_equations. nia.
- assert (Ei : i / 8 = kn / 8) by (Z.div_mod_to_equations; nia).
assert (R8 : kn mod 8 <> 0) by (Z.div_mod_to_equations; nia).
exists (kn mod 8). split.
+ rewrite G, Ei. apply bytes_at_app in SHB as [_ SHL]. rewrite repeat_length in SHL.
destruct (kn mod 8 =? 0) eqn:E8; [apply Z.eqb_eq in E8; lia|].
replace (kp / 8 + SB0 + Z.of_nat (Z.to_nat (kn / 8))) with (kp / 8 + kn / 8 + SB0) in SHL by lia.
split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact SHL].
+ right. split; [reflexivity|]. pose proof (Z.mod_pos_bound kn 8 ltac:(lia)). split; [lia|]. Z.div_mod_to_equations. nia.
Qed.

Definition loop_postA (x1 sp gp tp x18 x19 x20 x21 x22 x23 x24 x25 x27 : word) (F : bvmap 5 word) (fc : bv 32)
(ms' : machine_state) : Prop :=
exists (j' : Z) (u0 u1 u2 a0' a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 : word),
0 <= j' /\ j' mod 4 = 0 /\ 1 <= len - j' <= 12 /\
ms' = MS (mkR x1 sp gp tp u0 u1 u2 (Z_to_bv 64 (len - j')) (Z_to_bv 64 SB0) a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 (kp + j')) x27 u3 u4 u5 u6)
F (Z_to_bv 64 0xa337c) fc None m (seg_rom asegs).

Lemma hash_loopA :
forall (k : nat) (j : Z) (x1 sp gp tp t2 a0 a2 a3 a4 a5 x18 x19 x20 x21 x22 x23 x24 x25 x27 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32),
(k = Z.to_nat (len - j))%nat -> 0 <= j -> j mod 4 = 0 -> 12 < len - j ->
evt asegs (loop_postA x1 sp gp tp x18 x19 x20 x21 x22 x23 x24 x25 x27 F fc)
(MS (mkR x1 sp gp tp (Z_to_bv 64 (-13)) (Z_to_bv 64 12) t2 (Z_to_bv 64 (len - j)) (Z_to_bv 64 SB0) a0 (Z_to_bv 64 (kp + j)) a2 a3 a4 a5 (Z_to_bv 64 (-4)) (Z_to_bv 64 (-9))
x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 (kp + j)) x27 t3 t4 t5 t6)
F (Z_to_bv 64 0xa2f28) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind; intros until fc; intros Hk Hj Hj4 Hr.
pose proof (bytes_at_bound _ _ _ _ STR) as AB. unfold full in AB. rewrite length_app in AB. cbn [length] in AB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_read asegs m kp full (j + 0) 4 STR ltac:(lia) ltac:(unfold full; rewrite length_app; cbn; lia)) as RD0.
pose proof (bytes_at_read asegs m kp full (j + 4) 4 STR ltac:(lia) ltac:(unfold full; rewrite length_app; cbn; lia)) as RD1.
pose proof (bytes_at_read asegs m kp full (j + 8) 4 STR ltac:(lia) ltac:(unfold full; rewrite length_app; cbn; lia)) as RD2.
replace (kp + (j + 0)) with (kp + j) in RD0 by lia.
step. if_falsex.
step.

destruct (key_shadowA j ltac:(lia)) as (v1 & SH1 & Hv1).
step. step. sh_norm.
lazymatch goal with |- evt ?sg ?Q (MS ?R ?F _ ?fc ?rv ?mm ?ro) =>
eapply evt_cut with (P := fun ms => exists u v : word, ms = MS (bvmap_set 12 u (bvmap_set 28 v R)) F (Z_to_bv 64 0xa2f40) fc rv mm ro) end.
{ step. destruct Hv1 as [[-> Hfull] | (-> & Hv8 & Hend)]; [| exfalso; lia].
rewrite sxb_zero. step. if_false. apply evt_done. do 2 eexists. reflexivity. }
cbv beta. intros ms1 (u1 & w1 & ->). clear SH1.
step. if_falsex. step. if_falsex. step. if_falsex.

destruct (key_shadowA (j + 4) ltac:(lia)) as (v2 & SH2 & Hv2). replace (kp + (j + 4)) with (kp + j + 4) in SH2, Hv2, RD1 by lia.
step. step. step. sh_norm.
lazymatch goal with |- evt ?sg ?Q (MS ?R ?F _ ?fc ?rv ?mm ?ro) =>
eapply evt_cut with (P := fun ms => exists u v w : word, ms = MS (bvmap_set 29 u (bvmap_set 28 v (bvmap_set 30 w R))) F (Z_to_bv 64 0xa2f64) fc rv mm ro) end.
{ step. step.
destruct Hv2 as [[-> Hfull] | (-> & Hv8 & Hend)].
- rewrite sxb_zero. step. if_false. apply evt_done. do 3 eexists. reflexivity.
- rewrite (sxb_small (kn mod 8)) by lia. step. if_truex.
step. rewrite (unsigned_lit (kp + j + 4)) by lia. rewrite land7_mod8 by lia.
step. step. if_truex.
apply evt_done. do 3 eexists. reflexivity. }
cbv beta. intros ms2 (u2 & w2 & w2' & ->). clear SH2.

destruct (key_shadowA (j + 8) ltac:(lia)) as (v3 & SH3 & Hv3). replace (kp + (j + 8)) with (kp + j + 8) in SH3, Hv3, RD2 by lia.
step. step. step. sh_norm.
lazymatch goal with |- evt ?sg ?Q (MS ?R ?F _ ?fc ?rv ?mm ?ro) =>
eapply evt_cut with (P := fun ms => exists u v w : word, ms = MS (bvmap_set 30 u (bvmap_set 29 v (bvmap_set 31 w R))) F (Z_to_bv 64 0xa2f7c) fc rv mm ro) end.
{ step. step.
destruct Hv3 as [[-> Hfull] | (-> & Hv8 & Hend)].
- rewrite sxb_zero. step. if_false. apply evt_done. do 3 eexists. reflexivity.
- rewrite (sxb_small (kn mod 8)) by lia. step. if_truex.
step. rewrite (unsigned_lit (kp + j + 8)) by lia. rewrite land7_mod8 by lia.
step. step. if_truex.
apply evt_done. do 3 eexists. reflexivity. }
cbv beta. intros ms3 (u3 & w3 & w3' & ->). clear SH3.
do 43 (hstep sp).
replace (kp + j + 12) with (kp + (j + 12)) by lia. replace (len - j + -12) with (len - (j + 12)) by lia.
step.
destruct (Z.lt_ge_cases 12 (len - (j + 12))) as [LT | GE].
- if_truex. eapply (IH (Z.to_nat (len - (j + 12)))); lia.
- if_falsex. step. step.
replace (kp + j + 12) with (kp + (j + 12)) by lia.
apply evt_done. unfold loop_postA. exists (j + 12). do 15 eexists.
split; [lia|]. split; [clear -Hj4; Z.div_mod_to_equations; lia|]. split; [lia|]. reflexivity.
Qed.

Definition fin_postA (x1 sp gp tp : word) (p : Z) (x18 x19 x20 x21 x22 x23 x24 x25 x27 : word) (F : bvmap 5 word) (fc : bv 32)
(ms' : machine_state) : Prop :=
exists (u0 u1 u2 u8 a0' a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 : word),
ms' = MS (mkR x1 sp gp tp u0 u1 u2 u8 (Z_to_bv 64 SB0) a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 p) x27 u3 u4 u5 u6)
F (Z_to_bv 64 0xa3c90) fc None m (seg_rom asegs).

Tactic Notation "cut2" constr(PCJ) uconstr(iA) uconstr(iB) := lazymatch goal with |- evt ?sg ?Q (MS ?R ?F _ ?fc ?rv ?mm ?ro) =>
eapply evt_cut with (P := fun ms => exists u v : word, ms = MS (bvmap_set (iA : reg) u (bvmap_set (iB : reg) v R)) F (Z_to_bv 64 PCJ) fc rv mm ro) end.
Tactic Notation "cut3" constr(PCJ) uconstr(iA) uconstr(iB) uconstr(iC) := lazymatch goal with |- evt ?sg ?Q (MS ?R ?F _ ?fc ?rv ?mm ?ro) =>
eapply evt_cut with (P := fun ms => exists u v w : word, ms = MS (bvmap_set (iA : reg) u (bvmap_set (iB : reg) v (bvmap_set (iC : reg) w R))) F (Z_to_bv 64 PCJ) fc rv mm ro) end.
Ltac fin2 := apply evt_done; do 2 eexists; reflexivity.
Ltac fin3 := apply evt_done; do 3 eexists; reflexivity.
Ltac after2 := cbv beta; let u := fresh "u" in let v := fresh "u" in intros ? (u & v & ->).
Ltac after3 := cbv beta; let u := fresh "u" in let v := fresh "u" in let w := fresh "u" in intros ? (u & v & w & ->).
Ltac kshad OFF SH Hv := let v := fresh "v" in destruct (key_shadowA OFF ltac:(lia)) as (v & SH & Hv); rewrite ?Z.add_assoc in SH, Hv.
Ltac krd OFF N RD := pose proof (bytes_at_read asegs m kp full OFF N STR ltac:(lia) ltac:(unfold full; rewrite length_app; cbn; lia)) as RD;
rewrite ?Z.add_assoc in RD.
Ltac arms2 Hv slow := destruct Hv as [[-> ?] | (-> & ? & ?)];
[ rewrite sxb_zero; step; if_false; fin2 | rewrite (sxb_small (kn mod 8)) by lia; step; if_truex; slow; fin2 ].
Ltac arms3 Hv slow := destruct Hv as [[-> ?] | (-> & ? & ?)];
[ rewrite sxb_zero; step; if_false; fin3 | rewrite (sxb_small (kn mod 8)) by lia; step; if_truex; slow; fin3 ].

Ltac slow_b := step; rewrite unsigned_lit by lia; rewrite land7_mod8 by lia; step; if_truex.
Ltac slow_w := step; rewrite unsigned_lit by lia; rewrite land7_mod8 by lia; step; step; if_truex.

Ltac trapf := step; if_falsex.

Ltac al4 E := step; rewrite (unsigned_lit E) by lia; rewrite (ub_land3 E) by (Z.div_mod_to_equations; lia); step; if_false.

Tactic Notation "bsiteA" constr(OFF) constr(PCJ) :=
let SH := fresh "SH" in let Hv := fresh "Hv" in
kshad OFF SH Hv; step; step; sh_norm; cut2 PCJ 11%bv 12%bv; [ step; arms2 Hv slow_b | after2 ]; clear SH.
Ltac tail_intro := intros until fc; intros Hj Hj4 Hr;
pose proof (bytes_at_bound _ _ _ _ STR) as AB; unfold full in AB; rewrite length_app in AB; cbn [length] in AB;
pose proof (munch_refl [] m) as MU; pose proof (wmono_refl asegs m) as WM.
Ltac to_fin := apply evt_done; unfold fin_postA; do 16 eexists; reflexivity.

Definition tail_stmtA (pc : Z) (rmin : Z) : Prop :=
forall (j : Z) (x1 sp gp tp t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x27 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32),
0 <= j -> (kp + j) mod 4 = 0 -> rmin <= len - j <= 12 ->
evt asegs (fin_postA x1 sp gp tp (kp + j) x18 x19 x20 x21 x22 x23 x24 x25 x27 F fc)
(MS (mkR x1 sp gp tp t0 t1 t2 x8 (Z_to_bv 64 SB0) a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 (kp + j)) x27 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

Lemma tail1A : tail_stmtA 0xa33ec 1.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 0) 1%nat RD. rewrite ?Z.add_0_r in RD.
trapf.
kshad (j + 0) SH1 Hv1. rewrite ?Z.add_0_r in SH1, Hv1. step. step. sh_norm.
cut2 0xa3400 10%bv 11%bv; [ step; arms2 Hv1 slow_b | after2 ]. clear SH1.
step. hstep sp. step.
to_fin.
Qed.
Lemma tail2A : tail_stmtA 0xa33c0 2.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 1) 1%nat RD.
step. step. trapf. step.
bsiteA (j + 1) 0xa33e0. step. do 2 (hstep sp).
apply tail1A; lia.
Qed.
Lemma tail3A : tail_stmtA 0xa3398 3.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 2) 1%nat RD.
step. step. trapf.
bsiteA (j + 2) 0xa33b4. step. do 2 (hstep sp).
apply tail2A; lia.
Qed.

Lemma tail4A : tail_stmtA 0xa3848 4.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 0) 4%nat RD0. rewrite ?Z.add_0_r in RD0.
trapf. al4 (kp + j).
kshad (j + 0) SH1 Hv1. rewrite ?Z.add_0_r in SH1, Hv1. step. step. sh_norm.
cut2 0xa3864 10%bv 11%bv; [ step; arms2 Hv1 slow_w | after2 ]. clear SH1.
step. hstep sp. step.
to_fin.
Qed.
Lemma tail5A : tail_stmtA 0xa3820 5.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 4) 1%nat RD.
step. step. trapf. step.
bsiteA (j + 4) 0xa3840. step. hstep sp.
apply tail4A; lia.
Qed.
Lemma tail6A : tail_stmtA 0xa37f4 6.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 5) 1%nat RD.
step. step. trapf. step.
bsiteA (j + 5) 0xa3814. step. do 2 (hstep sp).
apply tail5A; lia.
Qed.
Lemma tail7A : tail_stmtA 0xa37cc 7.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 6) 1%nat RD.
step. step. trapf.
bsiteA (j + 6) 0xa37e8. step. do 2 (hstep sp).
apply tail6A; lia.
Qed.

Lemma tail8A : tail_stmtA 0xa36fc 8.
Proof.
unfold tail_stmtA. tail_intro.
krd (j + 0) 4%nat RD0. krd (j + 4) 4%nat RD1. rewrite ?Z.add_0_r in RD0.
step. step. trapf. step.
al4 (kp + j + 4). trapf. al4 (kp + j).
kshad (j + 4) SH2 Hv2. step. step. sh_norm.
cut2 0xa3730 11%bv 12%bv; [ step; arms2 Hv2 slow_w | after2 ]. clear SH2.
kshad (j + 0) SH1 Hv1. rewrite ?Z.add_0_r in SH1, Hv1. step. step. sh_norm.
cut3 0xa3744 11%bv 10%bv 12%bv; [ step; step; arms3 Hv1 slow_w | after3 ]. clear SH1.
step. do 2 (hstep sp). step.
to_fin.
Qed.
Lemma tail9A : tail_stmtA 0xa36d8 9.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 8) 1%nat RD.
step. step. trapf.
bsiteA (j + 8) 0xa36f4. step. hstep sp.
apply tail8A; lia.
Qed.
Lemma tail10A : tail_stmtA 0xa36ac 10.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 9) 1%nat RD.
trapf. step. trapf. step.
bsiteA (j + 9) 0xa36cc. step. do 2 (hstep sp).
apply tail9A; lia.
Qed.
Lemma tail11A : tail_stmtA 0xa3680 11.
Proof.
unfold tail_stmtA. tail_intro. krd (j + 10) 1%nat RD.
trapf. step. trapf. step.
bsiteA (j + 10) 0xa36a0. step. do 2 (hstep sp).
apply tail10A; lia.
Qed.

Lemma tail12A : tail_stmtA 0xa3754 12.
Proof.
unfold tail_stmtA. tail_intro.
krd (j + 0) 4%nat RD0. krd (j + 4) 4%nat RD1. krd (j + 8) 4%nat RD2. rewrite ?Z.add_0_r in RD0.
step. step. trapf. al4 (kp + j + 8).
kshad (j + 8) SH3 Hv3. step. step. sh_norm.
cut2 0xa3778 11%bv 12%bv; [ step; arms2 Hv3 slow_w | after2 ]. clear SH3.
step. al4 (kp + j + 4). trapf. al4 (kp + j).
kshad (j + 4) SH2 Hv2. step. step. sh_norm.
cut3 0xa37a4 12%bv 11%bv 16%bv; [ step; step; arms3 Hv2 slow_w | after3 ]. clear SH2.
kshad (j + 0) SH1 Hv1. rewrite ?Z.add_0_r in SH1, Hv1. step. step. sh_norm.
cut3 0xa37b8 12%bv 10%bv 16%bv; [ step; step; arms3 Hv1 slow_w | after3 ]. clear SH1.
step. do 3 (hstep sp). step.
to_fin.
Qed.

Definition epi_postA (x1 sp gp tp : word) (p : Z) (x18 x19 x20 x21 x22 x23 x24 x25 x27 : word) (F : bvmap 5 word) (fc : bv 32)
(ms' : machine_state) : Prop :=
exists (u0 u1 u2 u8 a0' a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 : word),
ms' = MS (mkR x1 sp gp tp u0 u1 u2 u8 (Z_to_bv 64 SB0) a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 p) x27 u3 u4 u5 u6)
F (Z_to_bv 64 0xa3d1c) fc None m (seg_rom asegs).

Lemma finmixA :
forall (p : Z) (x1 sp gp tp t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x27 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32),
evt asegs (epi_postA x1 sp gp tp p x18 x19 x20 x21 x22 x23 x24 x25 x27 F fc)
(MS (mkR x1 sp gp tp t0 t1 t2 x8 (Z_to_bv 64 SB0) a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 p) x27 t3 t4 t5 t6)
F (Z_to_bv 64 0xa3c90) fc None m (seg_rom asegs)).
Proof.
intros. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
do 35 (hstep sp).
apply evt_done. unfold epi_postA. do 16 eexists. reflexivity.
Qed.

Lemma fin_epiA : forall x1 sp gp tp p x18 x19 x20 x21 x22 x23 x24 x25 x27 F fc ms,
fin_postA x1 sp gp tp p x18 x19 x20 x21 x22 x23 x24 x25 x27 F fc ms ->
evt asegs (epi_postA x1 sp gp tp p x18 x19 x20 x21 x22 x23 x24 x25 x27 F fc) ms.
Proof. intros until ms. intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). apply finmixA. Qed.

Lemma dispatchA :
forall (j : Z) (x1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x27 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32),
0 <= j -> (kp + j) mod 4 = 0 -> 0 <= len - j <= 12 ->
evt asegs (epi_postA x1 sp gp tp (kp + j) x18 x19 x20 x21 x22 x23 x24 x25 x27 F fc)
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 (len - j)) (Z_to_bv 64 SB0) a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 (kp + j)) x27 t3 t4 t5 t6)
F (Z_to_bv 64 0xa337c) fc None m (seg_rom asegs)).
Proof.
intros until fc; intros Hj Hj4 Hr.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (CASES : exists r, len - j = r /\ (r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/ r = 10 \/ r = 11 \/ r = 12)) by (exists (len - j); lia).
destruct CASES as (r & Er & Hcase). rewrite Er.
destruct Hcase as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]];
(do 6 step);
step.
- apply evt_done. unfold epi_postA. do 16 eexists. reflexivity.
- eapply evt_cut; [apply tail1A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail2A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail3A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail4A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail5A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail6A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail7A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail8A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail9A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail10A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail11A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
- eapply evt_cut; [apply tail12A; lia | intros ms Hp; exact (fin_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp)].
Qed.

Lemma word_pathA :
forall (x1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x27 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32),
evt asegs (fun ms' => exists j, 0 <= j <= len /\ epi_postA x1 sp gp tp (kp + j) x18 x19 x20 x21 x22 x23 x24 x25 x27 F fc ms')
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 SB0) a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 kp) x27 t3 t4 t5 t6)
F (Z_to_bv 64 0xa2f04) fc None m (seg_rom asegs)).
Proof.
intros. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as AB. unfold full in AB. rewrite length_app in AB. cbn [length] in AB.
assert (AL4 : (kp + 0) mod 4 = 0) by (clear -AL; Z.div_mod_to_equations; lia).
step. step.
destruct (Z.lt_ge_cases len 13) as [LT | GE].
- if_truex. step. step. step.
replace (Z_to_bv 64 kp) with (Z_to_bv 64 (kp + 0)) by (f_equal; lia). replace (Z_to_bv 64 len) with (Z_to_bv 64 (len - 0)) by (f_equal; lia).
eapply evt_cut; [apply dispatchA; lia |]. intros ms Hp. apply evt_done. exists 0. split; [lia | exact Hp].
- if_falsex. do 7 step.
replace (Z_to_bv 64 kp) with (Z_to_bv 64 (kp + 0)) by (f_equal; lia). replace (Z_to_bv 64 len) with (Z_to_bv 64 (len - 0)) by (f_equal; lia).
eapply evt_cut; [eapply (hash_loopA (Z.to_nat (len - 0)) 0); lia |].
intros ms (j' & u0 & u1 & u2 & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & u3 & u4 & u5 & u6 & Hj' & Hj4' & Hr' & ->).
eapply evt_cut; [apply dispatchA; [lia | clear -AL Hj4'; Z.div_mod_to_equations; lia | lia] |]. intros ms Hp. apply evt_done. exists j'. split; [lia | exact Hp].
Qed.
End HashCoreA.
End RC__1.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrPc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrPc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrIB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoSetScal.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition jo_set_scalar_A_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (r : jroot) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo 16 errv -> jroot_rep A4H A4F r m BS p ->
a0 = Z_to_bv 64 p ->
(forall ms' md' m' rv,
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
rw_cells asegs m' A_ERRNO [C4 errv] ->
jroot_rep A4H A4F r m' BS p -> HEAPAx A (BS ++ LB) LM FRS B m' md' ->
AJ5 A4L HIx A T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Lemma jroot_hdrA : forall r m BS p,
jroot_rep A4H A4F r m BS p -> r <> JRnull -> List.NoDup (map blk_addr BS) ->
exists n ty tojs pb udel ud rest,
In (p, n) BS /\ Z.of_nat (cells_size (jhdr_cells ty 1 tojs pb udel ud ++ rest)) = n /\ 48 <= n /\ 0 <= ty <= 6 /\
rw_cells asegs m p (jhdr_cells ty 1 tojs pb udel ud ++ rest) /\
(ty = JT_BOOLEAN -> r = JRtree Sbool) /\ (ty = JT_INT -> r = JRtree Sint).
Proof.
intros r m BS p RR NN ND. destruct r as [|s|tojs|]; [exfalso; exact (NN eq_refl)| | |].
- destruct RR as [Hp J].
destruct (jval_hdr asegs A4F s m BS p 1 J ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & _).
exists n, (jtype s), tojs, pb, udel, ud, rest. split; [exact INp|]. split; [exact SZ|]. split; [exact N48|].
split; [apply jtype_range|]. split; [exact HDR|].
split; intros E; destruct s as [|u| |h|kids|kids]; cbn [jtype] in E; try discriminate E; reflexivity.
- destruct RR as (Hp & Htojs & pb & PBS & bits & EBS & OPB & HDR).
exists 48, JT_DOUBLE, tojs, pb, 0, 0, [C8 bits]. split; [rewrite EBS; left; reflexivity|]. split; [reflexivity|]. split; [lia|].
split; [unfold JT_DOUBLE; lia|]. split; [exact HDR|]. split; intros E; discriminate E.
- destruct RR as (Hp & pb & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & CASES).
destruct CASES as [(Hl0 & EDBS & Hfit & junk & HDR) | (Hl0 & pd & pdn & junk & junk2 & EDBS & HPD & HDR & HD)].
+ exists (48 + cap), JT_STRING, (fn_str_to_json_string A4F), pb, 0, 0, [C8 (Z_to_bv 64 len); CB (Z.to_nat cap) (str ++ [Z_to_bv 8 0] ++ junk)].
split; [rewrite EBS; left; reflexivity|]. split; [rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; lia|]. split; [lia|].
split; [unfold JT_STRING; lia|]. split; [exact HDR|]. split; intros E; discriminate E.
+ exists (48 + cap), JT_STRING, (fn_str_to_json_string A4F), pb, 0, 0, [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 pd); CB (Z.to_nat (cap - 8)) junk].
split; [rewrite EBS; left; reflexivity|]. split; [rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; lia|]. split; [lia|].
split; [unfold JT_STRING; lia|]. split; [exact HDR|]. split; intros E; discriminate E.
Qed.

Lemma blk_gran0A : forall A LBx LM FRS B m md a n i, HEAPAx A LBx LM FRS B m md -> In (a, n) LBx -> 0 <= i -> 8 * i + 8 <= n ->
ro_cells asegs m (a / 8 + 2147450880 + i) [C1 (Z_to_bv 8 0)].
Proof.
intros A LBx LM FRS B m md a n i HP Hin Hi Hn.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as SH. unfold shad in SH. cbn [hl_sb hl_segs hla_base A4L A4H] in SH. unfold A_SB in SH.
assert (E : 8 * i / 8 = i) by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
pose proof (shadow_at0 asegs m (a / 8 + 2147450880) n (8 * i) ltac:(lia) ltac:(rewrite E; lia) SH) as X. rewrite E in X. exact X.
Qed.

Lemma jroot_null_decA : forall r : jroot, r = JRnull \/ r <> JRnull.
Proof. intros []; [left; reflexivity | right; discriminate ..]. Qed.

Lemma set_int_A : jo_set_scalar_A_stmt 0x9e1d0.
Proof.
unfold jo_set_scalar_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR A0 K.
unfold_consts. unfold A_ERRNO, A_TP in *. subst a0 tp. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m) as WM.
destruct (jroot_null_decA r) as [-> | NN].
{
destruct RR as [-> ->]. cbn [app] in HP.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
do 2 bstep. bstep. if_truex. do 3 bstep.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0) end.
- unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia | solve_clientWA A4L HIx HP].
- exact ERR.
- cbn [jroot_rep]. split; reflexivity.
- cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption]. }
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
destruct (jroot_hdrA r m BS p RR NN ND) as (n & ty & tojs & pb & udel & ud & rest & INp & SZ & N48 & TY & HDR & TB & TI).
assert (Hp : p <> 0) by (destruct r; [exfalso; exact (NN eq_refl) | exact (proj1 RR) ..]).
assert (INpA : In (p, n) (BS ++ LB)) by (apply in_or_app; left; exact INp).
blk_factsA A4L HIx HP p n Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
pose proof (blk_gran0A _ _ _ _ _ _ _ p n 0 HP INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.

destruct (proj1 (rw_cells_app asegs m p _ _) HDR) as [HDRH _]. unfold jhdr_cells in HDRH.
destruct (Z.eq_dec ty JT_INT) as [E | NE].
-
specialize (TI E). subst r ty. clear TB. destruct RR as [_ J].
destruct J as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS, OPB.
unfold jhdr_cells, JT_INT in CELLS. cbn [app] in CELLS.
subst REST. cbn [app] in EBS. subst BS. clear HDR HDRH SH0. cbn [app] in HP.
blk_factsA A4L HIx HP p 56 Hpal2 Hplo2 Hphi2 Hpimg2. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg2.
shadow_nowA A4L HIx HP p 56 SHp.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (p, p + 56)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
do 2 bstep. bstep. if_falsex.
do 3 bstep.
asan_chkA.
bstep. rewrite sx32_small by (unfold JT_INT; lia). bstep. bstep. if_lit.
bstep.
asan_chkA.
bstepz.
try clear SHp. heap_nowA_auto A4L HIx HP HPc. shadow_nowA A4L HIx HPc p 56 SHp. a4l. clear HPc.
bstep. asan_chkA.
bstepz.
bstep. bstep. do 3 bstep.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 1) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |]. apply Forall_cons; [| apply Forall_nil].
right; left. exists p, 56. cbn [fst snd]. split; [in_app_prefix|]. split; [| lia].

intro Hi. apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
* exact (nodup_prefix_suffix ((p, 56) :: PBS) LB p 56 56 (nodup_app_l' _ _ ND0) ltac:(left; reflexivity) Hi).
* exact (nodup_prefix_suffix (((p, 56) :: PBS) ++ LB) LM p 56 56 ND0 ltac:(left; reflexivity) Hi).
* refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP _ Hi). in_app_prefix.
+ exact ERR.
+ cbn [jroot_rep]. split; [exact Hp|].
exists pb_, PBS, [(p, 56)]. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh.
assert (NEa : p <> a).
{ intros <-. pose proof ND as ND'. cbn in ND'. inversion ND' as [|x_ l_ Hni Hnd]; subst. apply Hni. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 56 a k HP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin) NEa).
split; [lia | split; [lia | exact I]].
* exists 0, a1, junk_. split; [reflexivity|]. split; [lia|]. unfold jhdr_cells, JT_INT. cbn [app]. assumption.
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
-
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. unfold JT_INT in NE.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
do 2 bstep. bstep. if_falsex.
do 3 bstep.
asan_chkA.
bstep. rewrite sx32_small by lia. bstep. bstep. if_truex.
bstep. do 3 bstep.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | solve_clientWA A4L HIx HP].
+ exact ERR.
+ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F r m _ BS BS); [exact RR | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh. split; [lia | exact I].
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
Qed.
End AJoSetScal.
End RC__1.
