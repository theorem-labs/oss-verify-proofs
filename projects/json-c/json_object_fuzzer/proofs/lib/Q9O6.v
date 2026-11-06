(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Qc3B QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn Q6WR QrPc QYIF Q7UD Qhd4 Qwm6 QlKV QsKa Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 QsKa.Mq8.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoGetPure.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition jo_post_frameW (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (lo : Z)
(r : word) (m' : word -> option byte) (ms' : machine_state) (md' : config) : Prop :=
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM) (bv_unsigned sp) m m' /\
(exists errv', rw_cells asegs m' A_ERRNO [C4 errv']).

Definition jo_get_pure_A_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (s : option jshape) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo 16 errv -> jopt asegs A4F s m BS p ->
frm0 fc -> a0 = Z_to_bv 64 p ->
(forall ms' md' m' (rv : word),
jo_post_frameW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
rw_cells asegs m' A_ERRNO [C4 errv] ->
jopt asegs A4F s m' BS p -> HEAPAx A (BS ++ LB) LM FRS B m' md' ->
AJ5 A4L HIx A T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Ltac gpA_open PRE JO sp m s BS p :=
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA);
pose proof (jopt_frame_onlyA HIx _ _ _ _ _ _ _ _ _ (bv_unsigned sp) _ _ HP LO JO 16) as JOK;
unfold_consts; unfold A_ERRNO, A_TP in *;
lazymatch type of TP with ?t = _ => subst t end;
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI; cbn [hl_segs hla_base A4L A4H] in MI;
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL];
pose proof (wmono_refl asegs m) as WM;
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU;
destruct s as [sh|];
[ destruct JO as [Hp J];
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0;
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0));
destruct (jval_hdr asegs A4F sh m BS p 1 J ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & CLOSE);
let LBx := lazymatch type of HP with HEAPA _ _ _ (_ ++ ?LBx) _ _ _ _ _ => LBx end in (
assert (INpA : In (p, n) (BS ++ LBx)) by (apply in_or_app; left; exact INp);
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; exact INpA)) as (_ & Hpal & Hplo & Hphi & _);
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi;
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; exact INpA)) as Hpimg; cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg;
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 0 HP INpA ltac:(lia) ltac:(lia)) as SH0; rewrite Z.add_0_r in SH0;
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 1 HP INpA ltac:(lia) ltac:(lia)) as SH1; replace (p / 8 + 2147450880 + 1) with (p / 8 + 2147450881) in SH1 by lia;
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 2 HP INpA ltac:(lia) ltac:(lia)) as SH2; replace (p / 8 + 2147450880 + 2) with (p / 8 + 2147450882) in SH2 by lia;
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 3 HP INpA ltac:(lia) ltac:(lia)) as SH3; replace (p / 8 + 2147450880 + 3) with (p / 8 + 2147450883) in SH3 by lia;
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 4 HP INpA ltac:(lia) ltac:(lia)) as SH4; replace (p / 8 + 2147450880 + 4) with (p / 8 + 2147450884) in SH4 by lia;
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 5 HP INpA ltac:(lia) ltac:(lia)) as SH5; replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia;
destruct (proj1 (rw_cells_app asegs m p _ _) HDR) as [HDRH _]; unfold jhdr_cells in HDRH;
pose proof (jtype_range sh) as JR;
a4l; (let L4 := constr:(A4L) in let SG := constr:(asegs) in let WX := constr:(asegs_wx) in reenterA SG L4 HIx WX HP) )
| destruct JO as [Hp HBS]; rewrite Hp in *;
a4l; (let L4 := constr:(A4L) in let SG := constr:(asegs) in let WX := constr:(asegs_wx) in reenterA SG L4 HIx WX HP) ].

Ltac gpA_ret K HP FR ST MU WM JOK sp :=
evt_done5;
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ _ mf _) end;
[ unfold jo_post_frameW; split;
[ apply ret_statew_intro;
[ first [ apply fsaved_refl
| let k := fresh "k" in let Hk := fresh "Hk" in
intros k Hk; cbn [FSAVED In] in Hk; repeat (destruct Hk as [<- | Hk]); [..| destruct Hk];
rewrite !freg_get_other by (vm_compute; reflexivity); reflexivity ]
| first [ intros Hf; exact Hf | intros _; assumption ] ] |];
split; [apply model_vm_only_refl|];
split; [release_frame FR ST (bv_unsigned sp); exact ST|]; split; [| eexists; eassumption];
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP | let Hb := fresh in intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | (let L4 := constr:(A4L) in solve_clientWA L4 HIx HP)]
| eassumption
| apply JOK; [lia | exact MU | exact WM]
| eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption] ].

Lemma get_type_A : jo_get_pure_A_stmt 0x9ae00.
Proof.
unfold jo_get_pure_A_stmt.
intros until errv.
intros PRE JO FRM A0 K.
cbn [hl_segs hla_base A4L A4H] in *.
subst a0.
gpA_open PRE JO sp m s BS p.
-
carve_frame 16%nat ST.
step. step. step. if_falsex.
step. step. step.
asan_chkA.
step.
step. step. step.
gpA_ret K HP FR ST MU WM JOK sp.
-
carve_frame 16%nat ST.
step. step. step. if_truex.
step. step. step.
gpA_ret K HP FR ST MU WM JOK sp.
Qed.

Lemma get_object_A : jo_get_pure_A_stmt 0x9bdf0.
Proof.
unfold jo_get_pure_A_stmt.
intros until errv.
intros PRE JO FRM A0 K.
cbn [hl_segs hla_base A4L A4H] in *.
subst a0.
gpA_open PRE JO sp m s BS p.
-
carve_frame 16%nat ST.
step. step. step. if_falsex.
step. step. step.
asan_chkA.
step.
rewrite sx32_small by lia.
step.
step.
destruct sh as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit; try (do 4 step; gpA_ret K HP FR ST MU WM JOK sp).
destruct (jval_obj_open asegs A4F kids m BS p 1 J) as (pb1 & PBS & t & TBS & kvs & KBS & EBS & OPB & HDR1 & LT & OK).
unfold jhdr_cells in HDR1.
cbn [app hl_segs hla_base A4L A4H] in HDR1.
arm_blkA HIx; catch_upA.
step.
asan_chkA.
step.
do 4 step.
gpA_ret K HP FR ST MU WM JOK sp.
-
carve_frame 16%nat ST.
step. step. step. if_truex.
step. step. step.
gpA_ret K HP FR ST MU WM JOK sp.
Qed.

Lemma get_array_A : jo_get_pure_A_stmt 0x9ec44.
Proof.
unfold jo_get_pure_A_stmt.
intros until errv.
intros PRE JO FRM A0 K.
cbn [hl_segs hla_base A4L A4H] in *.
subst a0.
gpA_open PRE JO sp m s BS p.
-
carve_frame 16%nat ST.
step. step. step. if_falsex.
step. step. step.
asan_chkA.
step.
rewrite sx32_small by lia.
step.
step.
destruct sh as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit; try (do 4 step; gpA_ret K HP FR ST MU WM JOK sp).
destruct (jval_arr_open asegs A4F kids m BS p 1 J) as (pb1 & PBS & a & ABS & ps & KBS & EBS & OPB & HDR1 & AL & OK).
unfold jhdr_cells in HDR1.
cbn [app hl_segs hla_base A4L A4H] in HDR1.
arm_blkA HIx; catch_upA.
step.
asan_chkA.
step.
do 4 step.
gpA_ret K HP FR ST MU WM JOK sp.
-
carve_frame 16%nat ST.
step. step. step. if_truex.
step. step. step.
gpA_ret K HP FR ST MU WM JOK sp.
Qed.

Lemma get_string_len_A : jo_get_pure_A_stmt 0x9e810.
Proof.
unfold jo_get_pure_A_stmt.
intros until errv.
intros PRE JO FRM A0 K.
cbn [hl_segs hla_base A4L A4H] in *.
subst a0.
gpA_open PRE JO sp m s BS p.
-
carve_frame 16%nat ST.
step. step. step. if_falsex.
step. step. step.
asan_chkA.
step.
rewrite sx32_small by lia.
step.
step.
destruct sh as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit; try (do 4 step; gpA_ret K HP FR ST MU WM JOK sp).
destruct J as (pb_ & PBS & REST & EBS & OPB & J).
cbn [hl_segs hla_base A4L A4H] in J.
assert (CELLS : exists len tl, - 2^31 < len < 2^31 /\ rw_cells asegs m p (jhdr_cells 6 1 (fn_str_to_json_string A4F) pb_ 0 0 ++ C8 (Z_to_bv 64 len) :: tl)).
{
destruct h; [destruct J as (len & pd & pdn & str & junk2 & _ & HL & _ & _ & C & _) | destruct J as (len & str & junk_p & _ & HL & _ & C)];
exists len; eexists; (split; [lia | exact C]).
}
clear J.
destruct CELLS as (len & tl & Hlen & CELLS).
unfold jhdr_cells in CELLS.
cbn [app] in CELLS.
arm_blkA HIx; catch_upA.
step.
asan_chkA.
step.
step.
step.
step.
do 4 step.
gpA_ret K HP FR ST MU WM JOK sp.
-
carve_frame 16%nat ST.
step. step. step. if_truex.
step. step. step.
gpA_ret K HP FR ST MU WM JOK sp.
Qed.

Lemma get_boolean_A : jo_get_pure_A_stmt 0x9c0e4.
Proof.
unfold jo_get_pure_A_stmt.
intros until errv.
intros PRE JO FRM A0 K.
cbn [hl_segs hla_base A4L A4H] in *.
subst a0.
gpA_open PRE JO sp m s BS p.
-
carve_frame 16%nat ST.
step. step. step. if_falsex.
step. step. step.
asan_chkA.
step.
rewrite sx32_small by lia.
step.
step.
step.
destruct sh as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit.
+
step.
step.
if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & (b & junk_ & ER & CELLS)).
cbn [hl_segs hla_base A4L A4H] in CELLS.
unfold jhdr_cells in CELLS.
cbn [app] in CELLS.
arm_blkA HIx; catch_upA.
step.
asan_chkA.
step.
do 5 step.
gpA_ret K HP FR ST MU WM JOK sp.
+
step.
step.
if_lit.
step.
step.
if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & J).
cbn [hl_segs hla_base A4L A4H] in J.
assert (CELLS : exists tojs' udel' ud' bits, rw_cells asegs m p (jhdr_cells 2 1 tojs' pb_ udel' ud' ++ [C8 bits])).
{
destruct u; [destruct J as (bits & ud_ & udn & uds & _ & _ & C & _) | destruct J as (bits & _ & _ & C)]; do 4 eexists; exact C.
}
clear J.
destruct CELLS as (tojs' & udel' & ud' & bits & CELLS).
unfold jhdr_cells in CELLS.
cbn [app] in CELLS.
arm_blkA HIx; catch_upA.
step.
asan_chkA.
step.
step.
step.
step.
do 5 step.
gpA_ret K HP FR ST MU WM JOK sp.
+
step.
step.
if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)).
cbn [hl_segs hla_base A4L A4H] in CELLS.
unfold jhdr_cells in CELLS.
cbn [app] in CELLS.
arm_blkA HIx; catch_upA.
step.
asan_chkA.
step.
rewrite sx32_small by lia.
step.
step.
destruct Hcty as [-> | ->]; if_lit.
*
step.
if_lit.
step.
site_granA HIx p 6.
asan_chkA.
step.
step.
do 4 step.
gpA_ret K HP FR ST MU WM JOK sp.
*
step.
site_granA HIx p 6.
asan_chkA.
step.
step.
do 4 step.
gpA_ret K HP FR ST MU WM JOK sp.
+
step.
step.
if_lit.
step.
step.
if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & J).
cbn [hl_segs hla_base A4L A4H] in J.
assert (CELLS : exists len tl, rw_cells asegs m p (jhdr_cells 6 1 (fn_str_to_json_string A4F) pb_ 0 0 ++ C8 (Z_to_bv 64 len) :: tl)).
{
destruct h; [destruct J as (len & pd & pdn & str & junk2 & _ & HL & _ & _ & C & _) | destruct J as (len & str & junk_p & _ & HL & _ & C)];
exists len; eexists; exact C.
}
clear J.
destruct CELLS as (len & tl & CELLS).
unfold jhdr_cells in CELLS.
cbn [app] in CELLS.
arm_blkA HIx; catch_upA.
step.
asan_chkA.
step.
step.
do 4 step.
gpA_ret K HP FR ST MU WM JOK sp.
+
step.
step.
if_lit.
step.
step.
if_lit.
step.
step. step. step.
gpA_ret K HP FR ST MU WM JOK sp.

+
step.
step.
if_lit.
step.
step.
if_lit.
step.
step. step. step.
gpA_ret K HP FR ST MU WM JOK sp.

-
carve_frame 16%nat ST.
step. step. step. if_truex.
step.
do 5 step.
gpA_ret K HP FR ST MU WM JOK sp.
Qed.
End AJoGetPure.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QCcH Q0Ek QjDH.Mq0.
Import Qvbw.
Import QlKV.Mq2 QsKa.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.

Lemma akids_okp : forall m ks vs bss, akids segs fn m ks vs bss -> kids_okp segs fn m ks vs bss.
Proof.
intros m ks. induction ks as [|k ks IH]; intros vs bss H; destruct vs as [|v vs]; destruct bss as [|bs bss]; cbn in H |- *; try exact H; try (destruct H; fail).
destruct H as [H1 H2]. split; [exact H1 | apply IH; exact H2].
Qed.
Lemma okids_okv : forall m ks kvs bss, okids segs fn m ks kvs bss -> kids_okv segs fn m ks kvs bss.
Proof.
intros m ks. induction ks as [|k ks IH]; intros kvs bss H; destruct kvs as [|[kk v] kvs]; destruct bss as [|bs bss]; cbn in H |- *; try exact H; try (destruct H; fail).
destruct H as [H1 H2]. split; [exact H1 | apply IH; exact H2].
Qed.

Lemma arr_add_jtx : forall m kids ps KBS PBS (b0 b1 b2 b2' : blk) vs VBS w wv,
akids segs fn m kids ps KBS ->
jtx (Sarr kids) ((b0 :: [b1; b2] ++ concat KBS) ++ PBS) = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
jtx (Sarr (kids ++ [vs])) ((b0 :: [b1; b2'] ++ concat (KBS ++ [VBS])) ++ PBS) = Some (w + (2 + wv), []).
Proof.
intros m kids ps KBS PBS b0 b1 b2 b2' vs VBS w wv KIDS Hw Hwv.
cbn [app] in Hw. rewrite <- ?app_assoc in Hw. rewrite jtx_arr_eq in Hw.
destruct ((snd b0 =? 48) && (snd b1 =? 32)) eqn:E; [| discriminate].
destruct (jtxk_arr_tail segs fn m kids (fun s _ bs p rc JV X w0 R H => jtx_val_tail segs fn s m bs p rc JV X w0 R H) ps KBS (akids_okp _ _ _ _ KIDS) [] PBS _ w [] pbtail_nil Hw) as (P & EP & _).
symmetry in EP. apply app_eq_nil in EP as [_ ->].
rewrite app_nil_r in Hw. rewrite app_nil_r. cbn [app]. rewrite concat_app. cbn [concat]. rewrite app_nil_r.
apply (jtx_arr_add_opt kids b0 b1 b2' (concat KBS) w vs VBS wv); [| exact Hwv].
unfold jfresh. rewrite jtx_arr_eq, E. exact Hw.
Qed.

Lemma obj_add_jtx : forall m kids kvs KBS PBS (b0 b1 b2 b2' kb : blk) (keys : list blk) vs VBS w wv,
okids segs fn m kids kvs KBS -> length keys = length kids ->
jtx (Sobj kids) ((b0 :: (b1 :: b2 :: keys) ++ concat KBS) ++ PBS) = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
jtx (Sobj (kids ++ [vs])) ((b0 :: (b1 :: b2' :: keys ++ [kb]) ++ concat (KBS ++ [VBS])) ++ PBS) = Some (w + (key_w (snd kb) + wv), []).
Proof.
intros m kids kvs KBS PBS b0 b1 b2 b2' kb keys vs VBS w wv KIDS LK Hw Hwv.
cbn [app] in Hw. rewrite <- ?app_assoc in Hw. rewrite jtx_obj_eq in Hw.
destruct ((snd b0 =? 48) && (snd b1 =? 56) && (length kids <=? length (keys ++ concat KBS ++ PBS))%nat) eqn:E; [| discriminate].
rewrite <- LK in Hw. rewrite firstn_app_exact, skipn_app_exact in Hw by reflexivity.
destruct (jtxk_obj_tail segs fn m kids (fun s _ bs p rc JV X w0 R H => jtx_val_tail segs fn s m bs p rc JV X w0 R H) kvs KBS (okids_okv _ _ _ _ KIDS) keys [] PBS _ w [] pbtail_nil Hw) as (P & EP & _).
symmetry in EP. apply app_eq_nil in EP as [_ ->].
rewrite app_nil_r in Hw. rewrite app_nil_r. cbn [app]. rewrite concat_app. cbn [concat]. rewrite app_nil_r.
apply (jtx_obj_add_opt kids b0 b1 b2' keys (concat KBS) w kb vs VBS wv LK); [| exact Hwv].
unfold jfresh. rewrite jtx_obj_eq.
apply andb_prop in E as [E1 _]. rewrite E1. cbn [andb].
replace (length kids <=? length (keys ++ concat KBS))%nat with true by (symmetry; apply Nat.leb_le; rewrite length_app, LK; lia).
rewrite <- LK. rewrite firstn_app_exact, skipn_app_exact by reflexivity. exact Hw.
Qed.
End WithSegs.
End Mq1.
From Stdlib Require Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qsw7 QJjn.
Import Q7UD Qhd4.
Import Qwm6.Mq0 QlKV.Mq2 QsKa.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition ASER_BOOL : Z := 0x9ae48.
Definition ASER_DBL : Z := 0x9af30.
Definition ASER_DBLF : Z := 0x9d3bc.
Definition ASER_INT : Z := 0x9af3c.
Definition ASER_STR : Z := 0x9ba30.
Definition ASER_OBJ : Z := 0x9b1a4.
Definition ASER_ARR : Z := 0x9b600.
Definition ASER_UD : Z := 0x9dcec.
Definition AGET_STRING : Z := 0x9e680.
Definition AMEMAPPEND : Z := 0x9a0ac.
Definition AESCAPE : Z := 0x9fe90.

Definition A_JHEX_SLOT : Z := 0xea520.
Definition A_JHEX : Z := 0x23320.
Definition JHEX_A (m : word -> option byte) : Prop := bytes_at asegs m A_JHEX_SLOT (le8 (wz A_JHEX)).
Lemma JHEX_A_pres : forall LBx SP m m', heap_pres A4H LBx SP m m' -> JHEX_A m -> JHEX_A m'.
Proof.
intros LBx SP m m' HPR H. unfold JHEX_A in *. eapply (heap_pres_bytes_at A4H); [exact HPR | exact H |].
right; left. intros a Ha. cbn [hl_client_static A4H hla_base A4L]. unfold a4_client_static, A_JHEX_SLOT in *. cbn [length le8] in Ha. left.
change (Z.of_nat (length (le8 (wz A_JHEX)))) with 8 in Ha. lia.
Qed.

Definition fn_ofF (fn : fnaddrs) (s : jshape) : Z :=
match s with
| Sbool => fn_bool_to_json_string fn | Sdouble false => fn_dbl_to_json_string fn
| Sdouble true => fn_ud_to_json_string fn | Sint => fn_int_to_json_string fn
| Sstr _ => fn_str_to_json_string fn | Sobj _ => fn_obj_to_json_string fn | Sarr _ => fn_arr_to_json_string fn
end.
Definition afn_of (s : jshape) : Z := fn_ofF A4F s.

Definition aflags_ok (fl : Z) : Prop := 0 <= fl < 2^31 /\ Z.land fl 58 = 0.

Definition ser_capb (cap bpos w : Z) : Z := Z.max cap (2 * (bpos + w) + 9).
Definition ser_need (cap bpos w : Z) : Z := 64 * (ser_capb cap bpos w - cap).

Definition ASER_LEVEL : Z := 256.
Definition ASER_LEAF : Z := 16384.
Definition ser_budgetA (s : jshape) : Z := ASER_LEVEL * sdepth s + ASER_LEAF.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.
Notation rw_cells := (rw_cells segs).

Definition jnode (s : jshape) (m : word -> option byte) (REST : list blk) (p rc pb0 : Z) : Prop :=
match s with
| Sbool =>
exists (b : Z) junk, REST = [(p, 48)] /\
rw_cells m p (jhdr_cells JT_BOOLEAN rc (fn_bool_to_json_string fn) pb0 0 0 ++ [C4 (wz b); CB 4 junk])
| Sdouble false =>
exists (bits : word), REST = [(p, 48)] /\ dbl_special bits /\
rw_cells m p (jhdr_cells JT_DOUBLE rc (fn_dbl_to_json_string fn) pb0 0 0 ++ [C8 bits])
| Sdouble true =>
exists (bits : word) (ud udn : Z) (uds : list byte), REST = [(p, 48); (ud, udn)] /\ udn <= 2^31 /\
rw_cells m p (jhdr_cells JT_DOUBLE rc (fn_ud_to_json_string fn) pb0 (fn_free_userdata fn) ud ++ [C8 bits]) /\
cstr segs m ud udn uds
| Sint =>
exists (cty : Z) (v : word) junk, REST = [(p, 56)] /\ (cty = 0 \/ cty = 1) /\
rw_cells m p (jhdr_cells JT_INT rc (fn_int_to_json_string fn) pb0 0 0 ++ [C4 (wz cty); CB 4 junk; C8 v])
| Sstr false =>
exists (len : Z) (str : list byte) junk, REST = [(p, str_objsize len)] /\ 0 <= len < 2^31 /\ Z.of_nat (length str) = len /\
rw_cells m p (jhdr_cells JT_STRING rc (fn_str_to_json_string fn) pb0 0 0 ++
[C8 (wz len); CB (Z.to_nat (str_objsize len - 48)) (str ++ [Z_to_bv 8 0] ++ junk)])
| Sstr true =>
exists (len : Z) (pd pdn : Z) (str : list byte) junk2, REST = [(p, 56); (pd, pdn)] /\
- 2^31 < len < 0 /\ Z.of_nat (length str) = - len /\ - len + 1 <= pdn /\
rw_cells m p (jhdr_cells JT_STRING rc (fn_str_to_json_string fn) pb0 0 0 ++ [C8 (wz len); C8 (wz pd)]) /\
rw_cells m pd [CB (Z.to_nat pdn) (str ++ [Z_to_bv 8 0] ++ junk2)]
| Sobj kids =>
exists (t : Z) (TBS : list blk) (kvs : list (Z * Z)) (KBS : list (list blk)),
REST = (p, 48) :: TBS ++ concat KBS /\
rw_cells m p (jhdr_cells JT_OBJECT rc (fn_obj_to_json_string fn) pb0 0 0 ++ [C8 (wz t)]) /\
lhtab2 segs fn m TBS t kvs /\ length kvs = length kids /\ length KBS = length kids /\ kids_okv segs fn m kids kvs KBS
| Sarr kids =>
exists (a : Z) (ABS : list blk) (ps : list Z) (KBS : list (list blk)),
REST = (p, 48) :: ABS ++ concat KBS /\
rw_cells m p (jhdr_cells JT_ARRAY rc (fn_arr_to_json_string fn) pb0 0 0 ++ [C8 (wz a)]) /\
alist segs fn m ABS a ps /\ length ps = length kids /\ length KBS = length kids /\ kids_okp segs fn m kids ps KBS
end.

#[using="Type"] Lemma jval_split : forall s m BS p rc,
jval segs fn s m BS p rc <-> exists pb0 PBS REST, BS = REST ++ PBS /\ opt_pbuf segs m PBS pb0 /\ jnode s m REST p rc pb0.
Proof.
intros s m BS p rc. destruct s as [|[|]| |[|]|kids|kids]; cbn; try reflexivity.
all: split; intros (pb0 & PBS & REST & E & O & H); exists pb0, PBS, REST; (split; [exact E|]); (split; [exact O|]); exact H.
Qed.

#[using="Type"] Lemma jval_jtx_node : forall s m BS p rc Y w R, jval segs fn s m BS p rc -> jtx s (BS ++ Y) = Some (w, R) ->
exists pb0 PBS REST, BS = REST ++ PBS /\ opt_pbuf segs m PBS pb0 /\ jnode s m REST p rc pb0 /\ jtx s (REST ++ (PBS ++ Y)) = Some (w, R).
Proof.
intros s m BS p rc Y w R JV H. destruct (proj1 (jval_split s m BS p rc) JV) as (pb0 & PBS & REST & -> & OP & JN).
exists pb0, PBS, REST. split; [reflexivity|]. split; [exact OP|]. split; [exact JN|]. rewrite <- app_assoc in H. exact H.
Qed.
End WithSegs.

Section ASer.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition ser_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (pb cap bpos w lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : word) (errv' : word) (buf' cap' bpos' : Z) (content' : list byte) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
HEAPAx A' ((pb, PB_SZ) :: (buf', cap') :: LB) LM FRS B' m' md' /\
pbuf_core asegs m' pb buf' bpos' cap' content' /\

bpos <= bpos' <= bpos + w /\ cap <= cap' <= ser_capb cap bpos w /\
bB B - 64 * (cap' - cap) <= bB B' /\ bD B <= bD B'.

Definition ser_specA (entry : Z) (s : jshape) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB REST LM : list blk) (FRS : list frame) (B : bud)
(p rc pb0 pb buf bpos cap lv fl lo w : Z) (Y R : list blk) (content : list byte) (errv : word),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbuf_core asegs m pb buf bpos cap content ->
jnode asegs A4F s m REST p rc pb0 -> incl REST LB ->
jtx s (REST ++ Y) = Some (w, R) ->
32 <= cap < 2^30 -> bpos + w < 2^28 -> ser_need cap bpos w <= bB B ->
aflags_ok fl -> 0 <= lv -> lv + sdepth s <= 1000 ->
Z.of_nat (length FRS) + 1 < 4096 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ser_budgetA s ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> JHEX_A m ->
tp = wz A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = wz p -> a1 = wz pb -> a2 = wz lv -> a3 = wz fl ->
(forall ms' md' A', ser_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb cap bpos w lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz entry) fc None m (seg_rom asegs)).

Definition ser_specA_al (d : Z) (entry : Z) (s : jshape) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB REST LM : list blk) (FRS : list frame) (B : bud)
(p rc pb0 pb buf bpos cap lv fl lo w : Z) (Y R : list blk) (content : list byte) (errv : word),
bv_unsigned sp mod 32 = d ->
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbuf_core asegs m pb buf bpos cap content ->
jnode asegs A4F s m REST p rc pb0 -> incl REST LB ->
jtx s (REST ++ Y) = Some (w, R) ->
32 <= cap < 2^30 -> bpos + w < 2^28 -> ser_need cap bpos w <= bB B ->
aflags_ok fl -> 0 <= lv -> lv + sdepth s <= 1000 ->
Z.of_nat (length FRS) + 1 < 4096 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ser_budgetA s ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> JHEX_A m ->
tp = wz A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = wz p -> a1 = wz pb -> a2 = wz lv -> a3 = wz fl ->
(forall ms' md' A', ser_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb cap bpos w lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz entry) fc None m (seg_rom asegs)).

Lemma ser_specA_of_al : forall entry s, ser_specA_al 0 entry s -> ser_specA_al 16 entry s -> ser_specA entry s.
Proof.
intros entry s H0 H16. unfold ser_specA. intros until errv. intros HP PB JN INCL JTX CAP TXT NEED FL Hlv Hlvd FRSN ST LO LOS SPA.
assert (D32 : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16) by (clear - SPA; Z.div_mod_to_equations; lia).
destruct D32 as [D32 | D32]; [eapply H0 | eapply H16]; eassumption.
Qed.

Definition SERVALA : Prop := forall s, ser_specA (afn_of s) s.
End ASer.

Lemma ser_capb_mono : forall cap cap' bpos bpos' w w', cap <= cap' <= ser_capb cap bpos w -> bpos' + w' <= bpos + w -> ser_capb cap' bpos' w' <= ser_capb cap bpos w.
Proof. intros cap cap' bpos bpos' w w' H1 H2. unfold ser_capb in *. lia. Qed.
Lemma ser_need_step : forall cap cap' bpos bpos' w w' (bB0 bB1 : Z),
cap <= cap' <= ser_capb cap bpos w -> bpos' + w' <= bpos + w -> ser_need cap bpos w <= bB0 -> bB0 - 64 * (cap' - cap) <= bB1 -> ser_need cap' bpos' w' <= bB1.
Proof. intros cap cap' bpos bpos' w w' bB0 bB1 H1 H2 H3 H4. pose proof (ser_capb_mono _ _ _ _ _ _ H1 H2). unfold ser_need in *. lia. Qed.

End RC__1.
End Mq2.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi QUZl Q7S0 QytA Qy5Y Q4J3 Q8zf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import QZAi.Mq1 QZAi.Mq2 QUZl Q7S0.Mq0 Q7S0.Mq1.
Import QytA Qy5Y.Mq4 Q4J3.Mq3.
Import Q6q3.
Import QlKV.Mq9 Q8zf.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Open Scope Z_scope.

Definition sel0 : unit -> ev -> option Z := fun _ _ => None.
Definition upd0 : unit -> ev -> Z -> unit := fun o _ _ => o.
Lemma follow_eruns0 {RC__ : RunConsts} {R} (t : M R) : forall ans, follow (eruns sel0 upd0 tt t) ans = option_map (pair tt) (follow t ans).
Proof.
induction t as [r|e k IH]; intros ans; [reflexivity|].
cbn [eruns sel0]. destruct e; destruct ans as [|a ans']; cbn [follow option_map]; try reflexivity; apply IH.
Qed.
Lemma follow_of_eruns0 {RC__ : RunConsts} {R} (t : M R) ans x : follow (eruns sel0 upd0 tt t) ans = Some (tt, x) -> follow t ans = Some x.
Proof. rewrite follow_eruns0. destruct (follow t ans) as [y|]; cbn; [intros E; injection E as ->; reflexivity | discriminate]. Qed.

Section A. Context {RC__ : RunConsts}.
Variables (sec : Z) (resv : list (Z * Z)) (a1 a2 a3 a4 : Z).
Hypothesis H1 : brk0_answer_ok a1 = true.
Hypothesis Hb : round_up_pg a1 = a1.
Hypothesis H2 : brk_answer_ok a1 (a1 + 2 * PGSZ) a2 = true.
Hypothesis H3 : (a2 =? a1 + 2 * PGSZ) = true.
Hypothesis H4 : brk_pages_ok (minit sec resv) a1 (2 * PGSZ) = true.
Hypothesis H5 : mmap_fixed_answer_ok a1 a3 = true.
Hypothesis H6 : mmap_answer_ok (resv ++ [(a1 + 4096, 4096)]) 4096 a4 = true.
Hypothesis H7 : is_err a4 = false.

Lemma crun_A_gen : follow (cmalloc (strip (minit sec resv)) 40) [a1; a2; a3; a4] = Some (strip (ST0_A sec resv a1 a4), Some (1%N, 64)).
Proof using H1 Hb H2 H3 H4 H5 H6 H7.
apply follow_of_eruns0.
mgo. mchk H1. rewrite Hb.
mgo. mchk H2.
mgo. mchk H3.
mgo. mchk H4.
mgo. mchk H5.
mgo. mchk H6.
mgo. mchk H7.
mgo.
lazymatch goal with |- follow (eruns ?s ?u ?o (SRet ?x)) [] = ?r => let x' := flat x in change_no_check (Some (o, x') = r) end.
reflexivity.
Qed.
End A.

Theorem startup_cmalloc40_brk {RC__ : RunConsts} (sec : Z) (resv : list (Z * Z)) (brk0 g3 grp : Z) :
brk0_answer_ok brk0 = true ->
brk_pages_ok (minit sec resv) brk0 (2 * PGSZ) = true ->
mmap_fixed_answer_ok brk0 g3 = true ->
mmap_answer_ok (resv ++ [(brk0 + 4096, 4096)]) 4096 grp = true ->
is_err grp = false ->
follow (cmalloc (strip (minit sec resv)) 40) [brk0; brk0 + 2 * PGSZ; g3; grp] = Some (strip (ST0_A sec resv brk0 grp), Some (1%N, 64)).
Proof.
intros H1 H4 H5 H6 H7.
apply crun_A_gen with (a3 := g3); try assumption.
- unfold brk0_answer_ok in H1. apply andb_prop in H1 as [H1 _]. apply andb_prop in H1 as [H1a H1b].
apply round_up_pg_aligned; [apply Z.ltb_lt in H1a; lia | apply Z.eqb_eq in H1b; exact H1b].
- unfold brk_answer_ok. rewrite Z.eqb_refl. reflexivity.
- apply Z.eqb_refl.
Qed.

Definition BLK0_A (sec : Z) (resv : list (Z * Z)) (brk0 grp : Z) : block :=
(((1%N, 64), fresh_off (strip (ST0_A sec resv brk0 grp)) (1%N, 64) 40), grp + 64, 40).

Theorem areach_main_A {RC__ : RunConsts} (sec : Z) (resv : list (Z * Z)) (brk0 g3 grp : Z) :
0 <= sec < 2^64 ->
brk0_answer_ok brk0 = true ->
brk_pages_ok (minit sec resv) brk0 (2 * PGSZ) = true ->
mmap_fixed_answer_ok brk0 g3 = true ->
mmap_answer_ok (resv ++ [(brk0 + 4096, 4096)]) 4096 grp = true ->
is_err grp = false ->
AREACH_from resv sec (ST0_A sec resv brk0 grp) [BLK0_A sec resv brk0 grp].
Proof.
intros Hs H1 H4 H5 H6 H7.
pose proof (startup_malloc40_brk sec resv brk0 g3 grp H1 H4 H5 H6 H7) as RUN.
pose proof (startup_cmalloc40_brk sec resv brk0 g3 grp H1 H4 H5 H6 H7) as CRUN.
pose proof (areach_malloc_some (minit sec resv) [] 40 o0 o0 _ _ (1%N, 64) _ (1%N, 64) (areach_init Hs) ltac:(lia) RUN CRUN) as AR.
exact AR.
Qed.

Lemma brk_link_main_A {RC__ : RunConsts} (sec : Z) (resv : list (Z * Z)) (brk0 grp : Z) :
brk_link (ST0_A sec resv brk0 grp) (brk0 + 8192).
Proof. reflexivity. Qed.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw QbFI QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QRUw.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqd QsKa.Mqh.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoGetPure.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition jo_post_frameW (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (lo : Z)
(r : word) (m' : word -> option byte) (ms' : machine_state) (md' : config) : Prop :=
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM) (bv_unsigned sp) m m' /\
(exists errv', rw_cells asegs m' A_ERRNO [C4 errv']).

Definition jo_get_pure_A_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (s : option jshape) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo 16 errv -> jopt asegs A4F s m BS p ->
frm0 fc -> a0 = Z_to_bv 64 p ->
(forall ms' md' m' (rv : word),
jo_post_frameW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
rw_cells asegs m' A_ERRNO [C4 errv] ->
jopt asegs A4F s m' BS p -> HEAPAx A (BS ++ LB) LM FRS B m' md' ->
AJ5 A4L HIx A T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Ltac gpA_open PRE JO sp m s BS p :=
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA);
pose proof (jopt_frame_onlyA HIx _ _ _ _ _ _ _ _ _ (bv_unsigned sp) _ _ HP LO JO 16) as JOK;
unfold_consts; unfold A_ERRNO, A_TP in *;
lazymatch type of TP with ?t = _ => subst t end;
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI; cbn [hl_segs hla_base A4L A4H] in MI;
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL];
pose proof (wmono_refl asegs m) as WM;
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU;
destruct s as [sh|];
[ destruct JO as [Hp J];
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0;
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0));
destruct (jval_hdr asegs A4F sh m BS p 1 J ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & CLOSE);
let LBx := lazymatch type of HP with HEAPA _ _ _ (_ ++ ?LBx) _ _ _ _ _ => LBx end in (
assert (INpA : In (p, n) (BS ++ LBx)) by (apply in_or_app; left; exact INp);
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; exact INpA)) as (_ & Hpal & Hplo & Hphi & _);
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi;
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; exact INpA)) as Hpimg; cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg;
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 0 HP INpA ltac:(lia) ltac:(lia)) as SH0; rewrite Z.add_0_r in SH0;
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 1 HP INpA ltac:(lia) ltac:(lia)) as SH1; replace (p / 8 + 2147450880 + 1) with (p / 8 + 2147450881) in SH1 by lia;
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 2 HP INpA ltac:(lia) ltac:(lia)) as SH2; replace (p / 8 + 2147450880 + 2) with (p / 8 + 2147450882) in SH2 by lia;
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 3 HP INpA ltac:(lia) ltac:(lia)) as SH3; replace (p / 8 + 2147450880 + 3) with (p / 8 + 2147450883) in SH3 by lia;
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 4 HP INpA ltac:(lia) ltac:(lia)) as SH4; replace (p / 8 + 2147450880 + 4) with (p / 8 + 2147450884) in SH4 by lia;
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 5 HP INpA ltac:(lia) ltac:(lia)) as SH5; replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia;
destruct (proj1 (rw_cells_app asegs m p _ _) HDR) as [HDRH _]; unfold jhdr_cells in HDRH;
pose proof (jtype_range sh) as JR;
a4l; (let L4 := constr:(A4L) in let SG := constr:(asegs) in let WX := constr:(asegs_wx) in reenterA SG L4 HIx WX HP) )
| destruct JO as [Hp HBS]; rewrite Hp in *;
a4l; (let L4 := constr:(A4L) in let SG := constr:(asegs) in let WX := constr:(asegs_wx) in reenterA SG L4 HIx WX HP) ].

Ltac gpA_ret K HP FR ST MU WM JOK sp :=
evt_done5;
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ _ mf _) end;
[ unfold jo_post_frameW; split;
[ apply ret_statew_intro;
[ first [ apply fsaved_refl
| let k := fresh "k" in let Hk := fresh "Hk" in
intros k Hk; cbn [FSAVED In] in Hk; repeat (destruct Hk as [<- | Hk]); [..| destruct Hk];
rewrite !freg_get_other by (vm_compute; reflexivity); reflexivity ]
| first [ intros Hf; exact Hf | intros _; assumption ] ] |];
split; [apply model_vm_only_refl|];
split; [release_frame FR ST (bv_unsigned sp); exact ST|]; split; [| eexists; eassumption];
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP | let Hb := fresh in intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | (let L4 := constr:(A4L) in solve_clientWA L4 HIx HP)]
| eassumption
| apply JOK; [lia | exact MU | exact WM]
| eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption] ].

Lemma get_type_A : jo_get_pure_A_stmt 0x9c4b8.
Proof.
unfold jo_get_pure_A_stmt.
intros until errv.
intros PRE JO FRM A0 K.
cbn [hl_segs hla_base A4L A4H] in *.
subst a0.
gpA_open PRE JO sp m s BS p.
-
carve_frame 16%nat ST.
bstep. bstep. bstep. if_falsex.
bstep. bstep. bstep.
asan_chkA.
bstep.
bstep. bstep. bstep.
gpA_ret K HP FR ST MU WM JOK sp.
-
carve_frame 16%nat ST.
bstep. bstep. bstep. if_truex.
bstep. bstep. bstep.
gpA_ret K HP FR ST MU WM JOK sp.
Qed.

Lemma get_object_A : jo_get_pure_A_stmt 0x9d5e8.
Proof.
unfold jo_get_pure_A_stmt.
intros until errv.
intros PRE JO FRM A0 K.
cbn [hl_segs hla_base A4L A4H] in *.
subst a0.
gpA_open PRE JO sp m s BS p.
-
carve_frame 16%nat ST.
bstep. bstep. bstep. if_falsex.
bstep. bstep. bstep.
asan_chkA.
bstep.
rewrite sx32_small by lia.
bstep.
bstep.
destruct sh as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit; try (do 4 bstep; gpA_ret K HP FR ST MU WM JOK sp).
destruct (jval_obj_open asegs A4F kids m BS p 1 J) as (pb1 & PBS & t & TBS & kvs & KBS & EBS & OPB & HDR1 & LT & OK).
unfold jhdr_cells in HDR1.
cbn [app hl_segs hla_base A4L A4H] in HDR1.
arm_blkA HIx; catch_upA.
bstep.
asan_chkA.
bstep.
do 4 bstep.
gpA_ret K HP FR ST MU WM JOK sp.
-
carve_frame 16%nat ST.
bstep. bstep. bstep. if_truex.
bstep. bstep. bstep.
gpA_ret K HP FR ST MU WM JOK sp.
Qed.

Lemma get_array_A : jo_get_pure_A_stmt 0xa08b4.
Proof.
unfold jo_get_pure_A_stmt.
intros until errv.
intros PRE JO FRM A0 K.
cbn [hl_segs hla_base A4L A4H] in *.
subst a0.
gpA_open PRE JO sp m s BS p.
-
carve_frame 16%nat ST.
bstep. bstep. bstep. if_falsex.
bstep. bstep. bstep.
asan_chkA.
bstep.
rewrite sx32_small by lia.
bstep.
bstep.
destruct sh as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit; try (do 4 bstep; gpA_ret K HP FR ST MU WM JOK sp).
destruct (jval_arr_open asegs A4F kids m BS p 1 J) as (pb1 & PBS & a & ABS & ps & KBS & EBS & OPB & HDR1 & AL & OK).
unfold jhdr_cells in HDR1.
cbn [app hl_segs hla_base A4L A4H] in HDR1.
arm_blkA HIx; catch_upA.
bstep.
asan_chkA.
bstep.
do 4 bstep.
gpA_ret K HP FR ST MU WM JOK sp.
-
carve_frame 16%nat ST.
bstep. bstep. bstep. if_truex.
bstep. bstep. bstep.
gpA_ret K HP FR ST MU WM JOK sp.
Qed.

Lemma get_string_len_A : jo_get_pure_A_stmt 0xa03f4.
Proof.
unfold jo_get_pure_A_stmt.
intros until errv.
intros PRE JO FRM A0 K.
cbn [hl_segs hla_base A4L A4H] in *.
subst a0.
gpA_open PRE JO sp m s BS p.
-
carve_frame 16%nat ST.
bstep. bstep. bstep. if_falsex.
bstep. bstep. bstep.
asan_chkA.
bstep.
rewrite sx32_small by lia.
bstep.
bstep.
destruct sh as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit; try (do 5 bstep; gpA_ret K HP FR ST MU WM JOK sp).
destruct J as (pb_ & PBS & REST & EBS & OPB & J).
cbn [hl_segs hla_base A4L A4H] in J.
assert (CELLS : exists len tl, - 2^31 < len < 2^31 /\ rw_cells asegs m p (jhdr_cells 6 1 (fn_str_to_json_string A4F) pb_ 0 0 ++ C8 (Z_to_bv 64 len) :: tl)).
{
destruct h; [destruct J as (len & pd & pdn & str & junk2 & _ & HL & _ & _ & C & _) | destruct J as (len & str & junk_p & _ & HL & _ & C)];
exists len; eexists; (split; [lia | exact C]).
}
clear J.
destruct CELLS as (len & tl & Hlen & CELLS).
unfold jhdr_cells in CELLS.
cbn [app] in CELLS.
arm_blkA HIx; catch_upA.
bstep.
asan_chkA.
bstep.

bstep.
destruct (Z.lt_ge_cases len 0) as [Hneg | Hnn].
+ if_falsex. bstep. bstep. bstep. bstep.
rewrite wz_neg_unsigned. rewrite (v_slt_0 (Z_to_bv 64 0) (Z_to_bv 64 len)) by (rewrite !signed_lit by lia; lia).
rewrite (v_slti_0 (Z_to_bv 64 (- len)) 0) by (rewrite zsig_lit by lia; lia).
if_lit. do 4 bstep.
gpA_ret K HP FR ST MU WM JOK sp.
+ if_truex. do 4 bstep.
gpA_ret K HP FR ST MU WM JOK sp.
-
carve_frame 16%nat ST.
bstep. bstep. bstep. if_truex.
bstep. bstep. bstep. bstep.
gpA_ret K HP FR ST MU WM JOK sp.
Qed.

Lemma get_boolean_A : jo_get_pure_A_stmt 0x9d978.
Proof.
unfold jo_get_pure_A_stmt.
intros until errv.
intros PRE JO FRM A0 K.
cbn [hl_segs hla_base A4L A4H] in *.
subst a0.
gpA_open PRE JO sp m s BS p.
-
carve_frame 16%nat ST.
bstep. bstep. bstep. if_falsex.
bstep. bstep. bstep.
asan_chkA.
bstep.
rewrite sx32_small by lia.
bstep.
bstep.
bstep.
destruct sh as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit.
+
bstep.
bstep.
if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & (b & junk_ & ER & CELLS)).
cbn [hl_segs hla_base A4L A4H] in CELLS.
unfold jhdr_cells in CELLS.
cbn [app] in CELLS.
arm_blkA HIx; catch_upA.
bstep.
asan_chkA.
bstep.
do 5 bstep.
gpA_ret K HP FR ST MU WM JOK sp.
+
bstep.
bstep.
if_lit.
bstep.
bstep.
if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & J).
cbn [hl_segs hla_base A4L A4H] in J.
assert (CELLS : exists tojs' udel' ud' bits, rw_cells asegs m p (jhdr_cells 2 1 tojs' pb_ udel' ud' ++ [C8 bits])).
{
destruct u; [destruct J as (bits & ud_ & udn & uds & _ & _ & C & _) | destruct J as (bits & _ & _ & C)]; do 4 eexists; exact C.
}
clear J.
destruct CELLS as (tojs' & udel' & ud' & bits & CELLS).
unfold jhdr_cells in CELLS.
cbn [app] in CELLS.
arm_blkA HIx; catch_upA.
bstep.
asan_chkA.
bstep.
bstep.
bstep.
bstep.
do 5 bstep.
gpA_ret K HP FR ST MU WM JOK sp.
+
bstep.
bstep.
if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)).
cbn [hl_segs hla_base A4L A4H] in CELLS.
unfold jhdr_cells in CELLS.
cbn [app] in CELLS.
arm_blkA HIx; catch_upA.
bstep.
asan_chkA.
bstep.
rewrite sx32_small by lia.
bstep.
bstep.
destruct Hcty as [-> | ->]; if_lit.
*
bstep.
if_lit.
bstep.
site_granA HIx p 6.
asan_chkA.
bstep.
bstep.
do 4 bstep.
gpA_ret K HP FR ST MU WM JOK sp.
*
bstep.
site_granA HIx p 6.
asan_chkA.
bstep.
bstep.
do 4 bstep.
gpA_ret K HP FR ST MU WM JOK sp.
+
bstep.
bstep.
if_lit.
bstep.
bstep.
if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & J).
cbn [hl_segs hla_base A4L A4H] in J.
assert (CELLS : exists len tl, rw_cells asegs m p (jhdr_cells 6 1 (fn_str_to_json_string A4F) pb_ 0 0 ++ C8 (Z_to_bv 64 len) :: tl)).
{
destruct h; [destruct J as (len & pd & pdn & str & junk2 & _ & HL & _ & _ & C & _) | destruct J as (len & str & junk_p & _ & HL & _ & C)];
exists len; eexists; exact C.
}
clear J.
destruct CELLS as (len & tl & CELLS).
unfold jhdr_cells in CELLS.
cbn [app] in CELLS.
arm_blkA HIx; catch_upA.
bstep.
asan_chkA.
bstep.
bstep.
do 4 bstep.
gpA_ret K HP FR ST MU WM JOK sp.
+
bstep.
bstep.
if_lit.
bstep.
bstep.
if_lit.
bstep.
bstep. bstep. bstep.
gpA_ret K HP FR ST MU WM JOK sp.

+
bstep.
bstep.
if_lit.
bstep.
bstep.
if_lit.
bstep.
bstep. bstep. bstep.
gpA_ret K HP FR ST MU WM JOK sp.

-
carve_frame 16%nat ST.
bstep. bstep. bstep. if_truex.
bstep.
do 5 bstep.
gpA_ret K HP FR ST MU WM JOK sp.
Qed.
End AJoGetPure.
End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qsw7 QJjn.
Import QbFI. Import Qhd4.
Import Qwm6.Mq4. Import QlKV.Mq2 QsKa.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition ASER_BOOL : Z := 0x9c508.
Definition ASER_DBL : Z := 0x9c600.
Definition ASER_DBLF : Z := 0x9ee14.
Definition ASER_INT : Z := 0x9c60c.
Definition ASER_STR : Z := 0x9d200.
Definition ASER_OBJ : Z := 0x9c878.
Definition ASER_ARR : Z := 0x9cd50.
Definition ASER_UD : Z := 0x9f7cc.
Definition AGET_STRING : Z := 0xa0250.
Definition AMEMAPPEND : Z := 0x9b4fc.
Definition AESCAPE : Z := 0xa1c40.

Definition A_JHEX_SLOT : Z := 0xec940.
Definition A_JHEX : Z := 0x23380.
Definition JHEX_A (m : word -> option byte) : Prop := bytes_at asegs m A_JHEX_SLOT (le8 (wz A_JHEX)).
Lemma JHEX_A_pres : forall LBx SP m m', heap_pres A4H LBx SP m m' -> JHEX_A m -> JHEX_A m'.
Proof.
intros LBx SP m m' HPR H. unfold JHEX_A in *. eapply (heap_pres_bytes_at A4H); [exact HPR | exact H |].
right; left. intros a Ha. cbn [hl_client_static A4H hla_base A4L]. unfold a4_client_static, A_JHEX_SLOT in *. cbn [length le8] in Ha. left.
change (Z.of_nat (length (le8 (wz A_JHEX)))) with 8 in Ha. lia.
Qed.

Definition fn_ofF (fn : fnaddrs) (s : jshape) : Z :=
match s with
| Sbool => fn_bool_to_json_string fn | Sdouble false => fn_dbl_to_json_string fn
| Sdouble true => fn_ud_to_json_string fn | Sint => fn_int_to_json_string fn
| Sstr _ => fn_str_to_json_string fn | Sobj _ => fn_obj_to_json_string fn | Sarr _ => fn_arr_to_json_string fn
end.
Definition afn_of (s : jshape) : Z := fn_ofF A4F s.

Definition aflags_ok (fl : Z) : Prop := 0 <= fl < 2^31 /\ Z.land fl 58 = 0.

Definition ser_capb (cap bpos w : Z) : Z := Z.max cap (2 * (bpos + w) + 9).
Definition ser_need (cap bpos w : Z) : Z := 64 * (ser_capb cap bpos w - cap).

Definition ASER_LEVEL : Z := 256.
Definition ASER_LEAF : Z := 16384.
Definition ser_budgetA (s : jshape) : Z := ASER_LEVEL * sdepth s + ASER_LEAF.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.
Notation rw_cells := (rw_cells segs).

Definition jnode (s : jshape) (m : word -> option byte) (REST : list blk) (p rc pb0 : Z) : Prop :=
match s with
| Sbool =>
exists (b : Z) junk, REST = [(p, 48)] /\
rw_cells m p (jhdr_cells JT_BOOLEAN rc (fn_bool_to_json_string fn) pb0 0 0 ++ [C4 (wz b); CB 4 junk])
| Sdouble false =>
exists (bits : word), REST = [(p, 48)] /\ dbl_special bits /\
rw_cells m p (jhdr_cells JT_DOUBLE rc (fn_dbl_to_json_string fn) pb0 0 0 ++ [C8 bits])
| Sdouble true =>
exists (bits : word) (ud udn : Z) (uds : list byte), REST = [(p, 48); (ud, udn)] /\ udn <= 2^31 /\
rw_cells m p (jhdr_cells JT_DOUBLE rc (fn_ud_to_json_string fn) pb0 (fn_free_userdata fn) ud ++ [C8 bits]) /\
cstr segs m ud udn uds
| Sint =>
exists (cty : Z) (v : word) junk, REST = [(p, 56)] /\ (cty = 0 \/ cty = 1) /\
rw_cells m p (jhdr_cells JT_INT rc (fn_int_to_json_string fn) pb0 0 0 ++ [C4 (wz cty); CB 4 junk; C8 v])
| Sstr false =>
exists (len : Z) (str : list byte) junk, REST = [(p, str_objsize len)] /\ 0 <= len < 2^31 /\ Z.of_nat (length str) = len /\
rw_cells m p (jhdr_cells JT_STRING rc (fn_str_to_json_string fn) pb0 0 0 ++
[C8 (wz len); CB (Z.to_nat (str_objsize len - 48)) (str ++ [Z_to_bv 8 0] ++ junk)])
| Sstr true =>
exists (len : Z) (pd pdn : Z) (str : list byte) junk2, REST = [(p, 56); (pd, pdn)] /\
- 2^31 < len < 0 /\ Z.of_nat (length str) = - len /\ - len + 1 <= pdn /\
rw_cells m p (jhdr_cells JT_STRING rc (fn_str_to_json_string fn) pb0 0 0 ++ [C8 (wz len); C8 (wz pd)]) /\
rw_cells m pd [CB (Z.to_nat pdn) (str ++ [Z_to_bv 8 0] ++ junk2)]
| Sobj kids =>
exists (t : Z) (TBS : list blk) (kvs : list (Z * Z)) (KBS : list (list blk)),
REST = (p, 48) :: TBS ++ concat KBS /\
rw_cells m p (jhdr_cells JT_OBJECT rc (fn_obj_to_json_string fn) pb0 0 0 ++ [C8 (wz t)]) /\
lhtab2 segs fn m TBS t kvs /\ length kvs = length kids /\ length KBS = length kids /\ kids_okv segs fn m kids kvs KBS
| Sarr kids =>
exists (a : Z) (ABS : list blk) (ps : list Z) (KBS : list (list blk)),
REST = (p, 48) :: ABS ++ concat KBS /\
rw_cells m p (jhdr_cells JT_ARRAY rc (fn_arr_to_json_string fn) pb0 0 0 ++ [C8 (wz a)]) /\
alist segs fn m ABS a ps /\ length ps = length kids /\ length KBS = length kids /\ kids_okp segs fn m kids ps KBS
end.

#[using="Type"] Lemma jval_split : forall s m BS p rc,
jval segs fn s m BS p rc <-> exists pb0 PBS REST, BS = REST ++ PBS /\ opt_pbuf segs m PBS pb0 /\ jnode s m REST p rc pb0.
Proof.
intros s m BS p rc. destruct s as [|[|]| |[|]|kids|kids]; cbn; try reflexivity.
all: split; intros (pb0 & PBS & REST & E & O & H); exists pb0, PBS, REST; (split; [exact E|]); (split; [exact O|]); exact H.
Qed.

#[using="Type"] Lemma jval_jtx_node : forall s m BS p rc Y w R, jval segs fn s m BS p rc -> jtx s (BS ++ Y) = Some (w, R) ->
exists pb0 PBS REST, BS = REST ++ PBS /\ opt_pbuf segs m PBS pb0 /\ jnode s m REST p rc pb0 /\ jtx s (REST ++ (PBS ++ Y)) = Some (w, R).
Proof.
intros s m BS p rc Y w R JV H. destruct (proj1 (jval_split s m BS p rc) JV) as (pb0 & PBS & REST & -> & OP & JN).
exists pb0, PBS, REST. split; [reflexivity|]. split; [exact OP|]. split; [exact JN|]. rewrite <- app_assoc in H. exact H.
Qed.
End WithSegs.

Section ASer.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition ser_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (pb cap bpos w lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : word) (errv' : word) (buf' cap' bpos' : Z) (content' : list byte) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
HEAPAx A' ((pb, PB_SZ) :: (buf', cap') :: LB) LM FRS B' m' md' /\
pbuf_core asegs m' pb buf' bpos' cap' content' /\

bpos <= bpos' <= bpos + w /\ cap <= cap' <= ser_capb cap bpos w /\
bB B - 64 * (cap' - cap) <= bB B' /\ bD B <= bD B'.

Definition ser_specA (entry : Z) (s : jshape) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB REST LM : list blk) (FRS : list frame) (B : bud)
(p rc pb0 pb buf bpos cap lv fl lo w : Z) (Y R : list blk) (content : list byte) (errv : word),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbuf_core asegs m pb buf bpos cap content ->
jnode asegs A4F s m REST p rc pb0 -> incl REST LB ->
jtx s (REST ++ Y) = Some (w, R) ->
32 <= cap < 2^30 -> bpos + w < 2^28 -> ser_need cap bpos w <= bB B ->
aflags_ok fl -> 0 <= lv -> lv + sdepth s <= 1000 ->
Z.of_nat (length FRS) + 1 < 4096 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ser_budgetA s ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> JHEX_A m ->
tp = wz A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = wz p -> a1 = wz pb -> a2 = wz lv -> a3 = wz fl ->
(forall ms' md' A', ser_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb cap bpos w lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz entry) fc None m (seg_rom asegs)).

Definition ser_specA_al (d : Z) (entry : Z) (s : jshape) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB REST LM : list blk) (FRS : list frame) (B : bud)
(p rc pb0 pb buf bpos cap lv fl lo w : Z) (Y R : list blk) (content : list byte) (errv : word),
bv_unsigned sp mod 32 = d ->
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbuf_core asegs m pb buf bpos cap content ->
jnode asegs A4F s m REST p rc pb0 -> incl REST LB ->
jtx s (REST ++ Y) = Some (w, R) ->
32 <= cap < 2^30 -> bpos + w < 2^28 -> ser_need cap bpos w <= bB B ->
aflags_ok fl -> 0 <= lv -> lv + sdepth s <= 1000 ->
Z.of_nat (length FRS) + 1 < 4096 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ser_budgetA s ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> JHEX_A m ->
tp = wz A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = wz p -> a1 = wz pb -> a2 = wz lv -> a3 = wz fl ->
(forall ms' md' A', ser_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb cap bpos w lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz entry) fc None m (seg_rom asegs)).

Lemma ser_specA_of_al : forall entry s, ser_specA_al 0 entry s -> ser_specA_al 16 entry s -> ser_specA entry s.
Proof.
intros entry s H0 H16. unfold ser_specA. intros until errv. intros HP PB JN INCL JTX CAP TXT NEED FL Hlv Hlvd FRSN ST LO LOS SPA.
assert (D32 : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16) by (clear - SPA; Z.div_mod_to_equations; lia).
destruct D32 as [D32 | D32]; [eapply H0 | eapply H16]; eassumption.
Qed.

Definition SERVALA : Prop := forall s, ser_specA (afn_of s) s.
End ASer.

Lemma ser_capb_mono : forall cap cap' bpos bpos' w w', cap <= cap' <= ser_capb cap bpos w -> bpos' + w' <= bpos + w -> ser_capb cap' bpos' w' <= ser_capb cap bpos w.
Proof. intros cap cap' bpos bpos' w w' H1 H2. unfold ser_capb in *. lia. Qed.
Lemma ser_need_step : forall cap cap' bpos bpos' w w' (bB0 bB1 : Z),
cap <= cap' <= ser_capb cap bpos w -> bpos' + w' <= bpos + w -> ser_need cap bpos w <= bB0 -> bB0 - 64 * (cap' - cap) <= bB1 -> ser_need cap' bpos' w' <= bB1.
Proof. intros cap cap' bpos bpos' w w' bB0 bB1 H1 H2 H3 H4. pose proof (ser_capb_mono _ _ _ _ _ _ H1 H2). unfold ser_need in *. lia. Qed.

End RC__1.
End Mq5.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Fixpoint nblk0 (s : jshape) : Z :=
match s with
| Sbool | Sint | Sdouble false | Sstr false => 1
| Sdouble true | Sstr true => 2
| Sarr kids => 3 + (fix go (ks : list (option jshape)) : Z := match ks with [] => 0 | None :: ks' => go ks' | Some s' :: ks' => nblk0 s' + go ks' end) kids
| Sobj kids => 3 + (fix go (ks : list (option jshape)) : Z := match ks with [] => 0 | None :: ks' => 1 + go ks' | Some s' :: ks' => 1 + nblk0 s' + go ks' end) kids
end.
Fixpoint nblk0k (ks : list (option jshape)) : Z := match ks with [] => 0 | None :: ks' => nblk0k ks' | Some s' :: ks' => nblk0 s' + nblk0k ks' end.
Lemma nblk0_arr : forall kids, nblk0 (Sarr kids) = 3 + nblk0k kids.
Proof. intros kids. cbn [nblk0]. f_equal. all: induction kids as [|[s'|] kids IH]; cbn [nblk0k]; [reflexivity | rewrite IH; reflexivity | exact IH]. Qed.
Lemma nblk0_obj : forall kids, nblk0 (Sobj kids) = 3 + Z.of_nat (length kids) + nblk0k kids.
Proof.
intros kids. cbn [nblk0]. rewrite <- Z.add_assoc. f_equal.
all: induction kids as [|[s'|] kids IH]; cbn [nblk0k length]; [reflexivity | rewrite IH; lia | rewrite IH; lia].
Qed.

Fixpoint nnodes (s : jshape) : Z :=
match s with
| Sarr kids | Sobj kids => 1 + (fix go (ks : list (option jshape)) : Z := match ks with [] => 0 | None :: ks' => go ks' | Some s' :: ks' => nnodes s' + go ks' end) kids
| _ => 1
end.
Fixpoint nnodesk (ks : list (option jshape)) : Z := match ks with [] => 0 | None :: ks' => nnodesk ks' | Some s' :: ks' => nnodes s' + nnodesk ks' end.
Lemma nnodes_arr : forall kids, nnodes (Sarr kids) = 1 + nnodesk kids.
Proof. intros kids. cbn [nnodes]. f_equal. all: induction kids as [|[s'|] kids IH]; cbn [nnodesk]; [reflexivity | rewrite IH; reflexivity | exact IH]. Qed.
Lemma nnodes_obj : forall kids, nnodes (Sobj kids) = 1 + nnodesk kids.
Proof. intros kids. cbn [nnodes]. f_equal. all: induction kids as [|[s'|] kids IH]; cbn [nnodesk]; [reflexivity | rewrite IH; reflexivity | exact IH]. Qed.

Lemma nnodes_le_nblk0 : forall s, 1 <= nnodes s <= nblk0 s.
Proof.
induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2; try (cbn; lia); try (destruct u; cbn; lia); try (destruct h; cbn; lia).
- rewrite nblk0_obj, nnodes_obj. assert (0 <= nnodesk kids <= nblk0k kids); [| lia]. induction kids as [|[s'|] kids IH]; cbn [nblk0k nnodesk]; [lia | | apply IH; intros s Hs; apply IHk; right; exact Hs].
pose proof (IHk s' (or_introl eq_refl)). specialize (IH (fun s Hs => IHk s (or_intror Hs))). lia.
- rewrite nblk0_arr, nnodes_arr. assert (0 <= nnodesk kids <= nblk0k kids); [| lia]. induction kids as [|[s'|] kids IH]; cbn [nblk0k nnodesk]; [lia | | apply IH; intros s Hs; apply IHk; right; exact Hs].
pose proof (IHk s' (or_introl eq_refl)). specialize (IH (fun s Hs => IHk s (or_intror Hs))). lia.
Qed.

Lemma jtxk_arr_length : forall ks, (forall s, In (Some s) ks -> forall bs w r, jtx s bs = Some (w, r) -> Z.of_nat (length bs) = nblk0 s + Z.of_nat (length r)) ->
forall bs acc w r, jtxk_arr ks bs acc = Some (w, r) -> Z.of_nat (length bs) = nblk0k ks + Z.of_nat (length r).
Proof.
induction ks as [|[s'|] ks IH]; intros HK bs acc w r H; cbn [jtxk_arr nblk0k] in *.
- injection H as _ <-. lia.
- destruct (jtx s' bs) as [[w' bs']|] eqn:E; [|discriminate].
pose proof (HK s' (or_introl eq_refl) _ _ _ E). specialize (IH (fun s Hs => HK s (or_intror Hs)) _ _ _ _ H). lia.
- exact (IH (fun s Hs => HK s (or_intror Hs)) _ _ _ _ H).
Qed.
Lemma jtxk_obj_length : forall ks, (forall s, In (Some s) ks -> forall bs w r, jtx s bs = Some (w, r) -> Z.of_nat (length bs) = nblk0 s + Z.of_nat (length r)) ->
forall keys bs acc w r, jtxk_obj ks keys bs acc = Some (w, r) -> Z.of_nat (length bs) = nblk0k ks + Z.of_nat (length r).
Proof.
induction ks as [|[s'|] ks IH]; intros HK keys bs acc w r H; cbn [jtxk_obj nblk0k] in *.
- injection H as _ <-. lia.
- destruct keys as [|[k kn] keys]; [discriminate|]. destruct (jtx s' bs) as [[w' bs']|] eqn:E; [|discriminate].
pose proof (HK s' (or_introl eq_refl) _ _ _ E). specialize (IH (fun s Hs => HK s (or_intror Hs)) _ _ _ _ _ H). lia.
- destruct keys as [|[k kn] keys]; [discriminate|]. exact (IH (fun s Hs => HK s (or_intror Hs)) _ _ _ _ _ H).
Qed.
Theorem jtx_length : forall s BS w R, jtx s BS = Some (w, R) -> Z.of_nat (length BS) = nblk0 s + Z.of_nat (length R).
Proof.
induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2; intros bs w r H.
- cbn in H. destruct bs as [|[a z] bs]; [discriminate|]. destruct (z =? 48); [injection H as _ <-; cbn [length nblk0]; lia | discriminate].
- destruct u; cbn in H.
+ destruct bs as [|[a z] [|[a1 z1] bs]]; try discriminate. destruct (z =? 48); [injection H as _ <-; cbn [length nblk0]; lia | discriminate].
+ destruct bs as [|[a z] bs]; [discriminate|]. destruct (z =? 48); [injection H as _ <-; cbn [length nblk0]; lia | discriminate].
- cbn in H. destruct bs as [|[a z] bs]; [discriminate|]. destruct (z =? 56); [injection H as _ <-; cbn [length nblk0]; lia | discriminate].
- destruct h; cbn in H.
+ destruct bs as [|[a z] [|[a1 z1] bs]]; try discriminate. destruct (z =? 56); [injection H as _ <-; cbn [length nblk0]; lia | discriminate].
+ destruct bs as [|[a z] bs]; [discriminate|]. destruct (Z.leb_spec 57 z); [injection H as _ <-; cbn [length nblk0]; lia | discriminate].
- destruct bs as [|[a0 z0] [|[a1 z1] [|b2 r0]]]; try discriminate. rewrite jtx_obj_eq in H.
destruct ((snd (a0, z0) =? 48) && (snd (a1, z1) =? 56)); [|discriminate]. cbn [andb] in H.
destruct (Nat.leb_spec (length kids) (length r0)) as [LE|GT]; [|discriminate].
pose proof (jtxk_obj_length kids IHk _ _ _ _ _ H) as L. rewrite length_skipn in L. rewrite nblk0_obj. cbn [length]. lia.
- destruct bs as [|[a0 z0] [|[a1 z1] [|b2 r0]]]; try discriminate. rewrite jtx_arr_eq in H.
destruct ((snd (a0, z0) =? 48) && (snd (a1, z1) =? 32)); [|discriminate].
pose proof (jtxk_arr_length kids IHk _ _ _ _ H) as L. rewrite nblk0_arr. cbn [length]. lia.
Qed.

Lemma jtxk_arr_blkw : forall ks, (forall s, In (Some s) ks -> forall bs w r, jtx s bs = Some (w, r) -> 8 * nblk0 s <= w) ->
forall bs acc w r, jtxk_arr ks bs acc = Some (w, r) -> acc + 8 * nblk0k ks <= w.
Proof.
induction ks as [|[s'|] ks IH]; intros HK bs acc w r H; cbn [jtxk_arr nblk0k] in *.
- injection H as <- _. lia.
- destruct (jtx s' bs) as [[w' bs']|] eqn:E; [|discriminate].
pose proof (HK s' (or_introl eq_refl) _ _ _ E). specialize (IH (fun s Hs => HK s (or_intror Hs)) _ _ _ _ H). lia.
- specialize (IH (fun s Hs => HK s (or_intror Hs)) _ _ _ _ H). unfold NULL_W in *. lia.
Qed.
Lemma jtxk_obj_blkw : forall ks, (forall s, In (Some s) ks -> forall bs w r, jtx s bs = Some (w, r) -> 8 * nblk0 s <= w) ->
forall keys bs acc w r, jtxk_obj ks keys bs acc = Some (w, r) -> acc + 8 * (Z.of_nat (length ks) + nblk0k ks) <= w.
Proof.
induction ks as [|[s'|] ks IH]; intros HK keys bs acc w r H; cbn [jtxk_obj nblk0k length] in *.
- injection H as <- _. lia.
- destruct keys as [|[k kn] keys]; [discriminate|]. destruct (jtx s' bs) as [[w' bs']|] eqn:E; [|discriminate].
pose proof (HK s' (or_introl eq_refl) _ _ _ E). specialize (IH (fun s Hs => HK s (or_intror Hs)) _ _ _ _ _ H). unfold key_w in *. lia.
- destruct keys as [|[k kn] keys]; [discriminate|]. specialize (IH (fun s Hs => HK s (or_intror Hs)) _ _ _ _ _ H). unfold key_w, NULL_W in *. lia.
Qed.
Theorem jtx_blk_weight : forall s BS w R, jtx s BS = Some (w, R) -> 8 * nblk0 s <= w.
Proof.
induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2; intros bs w r H.
- cbn in H. destruct bs as [|[a z] bs]; [discriminate|]. destruct (z =? 48); [injection H as <- _; cbn [nblk0]; lia | discriminate].
- destruct u; cbn in H.
+ destruct bs as [|[a z] [|[a1 z1] bs]]; try discriminate. destruct (z =? 48); [injection H as <- _; cbn [nblk0]; lia | discriminate].
+ destruct bs as [|[a z] bs]; [discriminate|]. destruct (z =? 48); [injection H as <- _; cbn [nblk0]; lia | discriminate].
- cbn in H. destruct bs as [|[a z] bs]; [discriminate|]. destruct (z =? 56); [injection H as <- _; cbn [nblk0]; lia | discriminate].
- destruct h; cbn in H.
+ destruct bs as [|[a z] [|[a1 z1] bs]]; try discriminate. destruct (z =? 56); [injection H as <- _; cbn [nblk0]; lia | discriminate].
+ destruct bs as [|[a z] bs]; [discriminate|]. destruct (Z.leb_spec 57 z); [injection H as <- _; cbn [nblk0]; unfold str_w; lia | discriminate].
- destruct bs as [|[a0 z0] [|[a1 z1] [|b2 r0]]]; try discriminate. rewrite jtx_obj_eq in H.
destruct ((snd (a0, z0) =? 48) && (snd (a1, z1) =? 56) && (length kids <=? length r0)%nat); [|discriminate].
pose proof (jtxk_obj_blkw kids IHk _ _ _ _ _ H). rewrite nblk0_obj. lia.
- destruct bs as [|[a0 z0] [|[a1 z1] [|b2 r0]]]; try discriminate. rewrite jtx_arr_eq in H.
destruct ((snd (a0, z0) =? 48) && (snd (a1, z1) =? 32)); [|discriminate].
pose proof (jtxk_arr_blkw kids IHk _ _ _ _ H). rewrite nblk0_arr. lia.
Qed.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.
Notation jvalx := (jval segs fn).

Lemma opt_pbuf_length : forall m PBS pb, opt_pbuf segs m PBS pb -> Z.of_nat (length PBS) <= 2.
Proof. intros m PBS pb [[_ ->]|[_ (buf & bpos & size & content & -> & _)]]; cbn [length]; lia. Qed.

Lemma kids_okp_length : forall m kids, (forall s, In (Some s) kids -> forall bs p rc, jvalx s m bs p rc -> Z.of_nat (length bs) <= nblk0 s + 2 * nnodes s) ->
forall ps KBS, kids_okp segs fn m kids ps KBS -> Z.of_nat (length (concat KBS)) <= nblk0k kids + 2 * nnodesk kids.
Proof.
induction kids as [|[s'|] kids IH]; intros HK ps KBS OK.
- destruct ps; [|destruct OK]. destruct KBS; [|destruct OK]. cbn. lia.
- destruct ps as [|v ps]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv JV] OK].
cbn [concat nblk0k nnodesk]. rewrite length_app. pose proof (HK s' (or_introl eq_refl) _ _ _ JV). specialize (IH (fun s Hs => HK s (or_intror Hs)) _ _ OK). lia.
- destruct ps as [|v ps]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv ->] OK].
cbn [concat nblk0k nnodesk app]. exact (IH (fun s Hs => HK s (or_intror Hs)) _ _ OK).
Qed.
Lemma kids_okv_length : forall m kids, (forall s, In (Some s) kids -> forall bs p rc, jvalx s m bs p rc -> Z.of_nat (length bs) <= nblk0 s + 2 * nnodes s) ->
forall kvs KBS, kids_okv segs fn m kids kvs KBS -> Z.of_nat (length (concat KBS)) <= nblk0k kids + 2 * nnodesk kids.
Proof.
induction kids as [|[s'|] kids IH]; intros HK kvs KBS OK.
- destruct kvs; [|destruct OK]. destruct KBS; [|destruct OK]. cbn. lia.
- destruct kvs as [|[kk v] kvs]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv JV] OK].
cbn [concat nblk0k nnodesk]. rewrite length_app. pose proof (HK s' (or_introl eq_refl) _ _ _ JV). specialize (IH (fun s Hs => HK s (or_intror Hs)) _ _ OK). lia.
- destruct kvs as [|[kk v] kvs]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv ->] OK].
cbn [concat nblk0k nnodesk app]. exact (IH (fun s Hs => HK s (or_intror Hs)) _ _ OK).
Qed.

Theorem jval_length_le : forall s m BS p rc, jvalx s m BS p rc -> Z.of_nat (length BS) <= nblk0 s + 2 * nnodes s.
Proof.
induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2; intros m bs p rc JV.
- destruct JV as (pb & PBS & REST & -> & OP & b & junk & -> & _). pose proof (opt_pbuf_length _ _ _ OP). rewrite length_app. cbn [length nblk0 nnodes]. lia.
- destruct u.
+ destruct JV as (pb & PBS & REST & -> & OP & bits & ud & udn & uds & -> & _). pose proof (opt_pbuf_length _ _ _ OP). rewrite length_app. cbn [length nblk0 nnodes]. lia.
+ destruct JV as (pb & PBS & REST & -> & OP & bits & -> & _). pose proof (opt_pbuf_length _ _ _ OP). rewrite length_app. cbn [length nblk0 nnodes]. lia.
- destruct JV as (pb & PBS & REST & -> & OP & cty & v & junk & -> & _). pose proof (opt_pbuf_length _ _ _ OP). rewrite length_app. cbn [length nblk0 nnodes]. lia.
- destruct h.
+ destruct JV as (pb & PBS & REST & -> & OP & len & pd & pdn & str & junk2 & -> & _). pose proof (opt_pbuf_length _ _ _ OP). rewrite length_app. cbn [length nblk0 nnodes]. lia.
+ destruct JV as (pb & PBS & REST & -> & OP & len & str & junk & -> & _). pose proof (opt_pbuf_length _ _ _ OP). rewrite length_app. cbn [length nblk0 nnodes]. lia.
- destruct JV as (pb & PBS & REST & -> & OP & t & TBS & kvs & KBS & -> & _ & (tbl & size & es & svs & Ekvs & -> & _) & L1 & L2 & OK).
pose proof (opt_pbuf_length _ _ _ OP). pose proof (kids_okv_length m kids (fun s Hs => IHk s Hs m) kvs KBS OK) as LK.
assert (LKe : length es = length kids) by (rewrite Ekvs, length_map in L1; exact L1).
unfold lh_blocks. rewrite nblk0_obj, nnodes_obj. rewrite length_app. cbn [length app]. rewrite length_app, length_map. lia.
- destruct JV as (pb & PBS & REST & -> & OP & a & ABS & ps & KBS & -> & _ & (arr & size & junk & -> & _) & L1 & L2 & OK).
pose proof (opt_pbuf_length _ _ _ OP). pose proof (kids_okp_length m kids (fun s Hs => IHk s Hs m) ps KBS OK) as LK.
rewrite nblk0_arr, nnodes_arr. rewrite length_app. cbn [length app]. lia.
Qed.

Lemma kids_okp_length_ge : forall m kids, (forall s, In (Some s) kids -> forall bs p rc, jvalx s m bs p rc -> nblk0 s <= Z.of_nat (length bs)) ->
forall ps KBS, kids_okp segs fn m kids ps KBS -> nblk0k kids <= Z.of_nat (length (concat KBS)).
Proof.
induction kids as [|[s'|] kids IH]; intros HK ps KBS OK.
- cbn. lia.
- destruct ps as [|v ps]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv JV] OK].
cbn [concat nblk0k]. rewrite length_app. pose proof (HK s' (or_introl eq_refl) _ _ _ JV). specialize (IH (fun s Hs => HK s (or_intror Hs)) _ _ OK). lia.
- destruct ps as [|v ps]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv ->] OK].
cbn [concat nblk0k app]. exact (IH (fun s Hs => HK s (or_intror Hs)) _ _ OK).
Qed.
Lemma kids_okv_length_ge : forall m kids, (forall s, In (Some s) kids -> forall bs p rc, jvalx s m bs p rc -> nblk0 s <= Z.of_nat (length bs)) ->
forall kvs KBS, kids_okv segs fn m kids kvs KBS -> nblk0k kids <= Z.of_nat (length (concat KBS)).
Proof.
induction kids as [|[s'|] kids IH]; intros HK kvs KBS OK.
- cbn. lia.
- destruct kvs as [|[kk v] kvs]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv JV] OK].
cbn [concat nblk0k]. rewrite length_app. pose proof (HK s' (or_introl eq_refl) _ _ _ JV). specialize (IH (fun s Hs => HK s (or_intror Hs)) _ _ OK). lia.
- destruct kvs as [|[kk v] kvs]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv ->] OK].
cbn [concat nblk0k app]. exact (IH (fun s Hs => HK s (or_intror Hs)) _ _ OK).
Qed.
Theorem jval_length_ge : forall s m BS p rc, jvalx s m BS p rc ->
exists pb0 PBS REST, BS = REST ++ PBS /\ opt_pbuf segs m PBS pb0 /\ nblk0 s <= Z.of_nat (length REST).
Proof.
induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2; intros m bs p rc JV.
- destruct JV as (pb & PBS & REST & -> & OP & b & junk & -> & _). exists pb, PBS, [(p, 48)]. split; [reflexivity|]. split; [exact OP|]. cbn [length nblk0]. lia.
- destruct u.
+ destruct JV as (pb & PBS & REST & -> & OP & bits & ud & udn & uds & -> & _). exists pb, PBS, [(p, 48); (ud, udn)]. split; [reflexivity|]. split; [exact OP|]. cbn [length nblk0]. lia.
+ destruct JV as (pb & PBS & REST & -> & OP & bits & -> & _). exists pb, PBS, [(p, 48)]. split; [reflexivity|]. split; [exact OP|]. cbn [length nblk0]. lia.
- destruct JV as (pb & PBS & REST & -> & OP & cty & v & junk & -> & _). exists pb, PBS, [(p, 56)]. split; [reflexivity|]. split; [exact OP|]. cbn [length nblk0]. lia.
- destruct h.
+ destruct JV as (pb & PBS & REST & -> & OP & len & pd & pdn & str & junk2 & -> & _). exists pb, PBS, [(p, 56); (pd, pdn)]. split; [reflexivity|]. split; [exact OP|]. cbn [length nblk0]. lia.
+ destruct JV as (pb & PBS & REST & -> & OP & len & str & junk & -> & _). exists pb, PBS, [(p, str_objsize len)]. split; [reflexivity|]. split; [exact OP|]. cbn [length nblk0]. lia.
- destruct JV as (pb & PBS & REST & -> & OP & t & TBS & kvs & KBS & -> & _ & (tbl & size & es & svs & Ekvs & -> & _) & L1 & L2 & OK).
exists pb, PBS. eexists. split; [reflexivity|]. split; [exact OP|].
assert (LK : nblk0k kids <= Z.of_nat (length (concat KBS))).
{ eapply (kids_okv_length_ge m kids); [| exact OK]. intros s Hs bs0 p0 rc0 JV0. destruct (IHk s Hs m bs0 p0 rc0 JV0) as (pb1 & PBS1 & REST1 & -> & _ & H). rewrite length_app. lia. }
assert (LKe : length es = length kids) by (rewrite Ekvs, length_map in L1; exact L1).
unfold lh_blocks. rewrite nblk0_obj. cbn [length app]. rewrite length_app, length_map. lia.
- destruct JV as (pb & PBS & REST & -> & OP & a & ABS & ps & KBS & -> & _ & (arr & size & junk & -> & _) & L1 & L2 & OK).
exists pb, PBS. eexists. split; [reflexivity|]. split; [exact OP|].
assert (LK : nblk0k kids <= Z.of_nat (length (concat KBS))).
{ eapply (kids_okp_length_ge m kids); [| exact OK]. intros s Hs bs0 p0 rc0 JV0. destruct (IHk s Hs m bs0 p0 rc0 JV0) as (pb1 & PBS1 & REST1 & -> & _ & H). rewrite length_app. lia. }
rewrite nblk0_arr. cbn [length app]. lia.
Qed.

End WithSegs.
