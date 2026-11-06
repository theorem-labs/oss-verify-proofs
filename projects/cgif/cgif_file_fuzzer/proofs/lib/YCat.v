(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI10 YC4a YC8i YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbk YC8g.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8h YC8j YCbc YCbf YCbd.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbe YCbg.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC85 YC88 YCb9 YCb6 YCba YCb7 YCbb YCb4.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCau YCav YCaw YCax YCay YCaz YCb0 YCb1 YCb2 YCb3.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_both3_1_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_1_listing PI) (@pa_relro_lo _ lib_both3_1_listing PI) (@pa_relro_hi _ lib_both3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma U_addw_small : forall E a b, U E a + U E b < 2 ^ 31 -> U E (SAluw ALU_ADD a b) = U E a + U E b.
Proof.
intros E a b Hab. pose proof (U_range E a) as Ha. pose proof (U_range E b) as Hb. unfold M64 in Ha, Hb.
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite !(Z.mod_small _ (2 ^ 32)) by lia.
unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
rewrite (Z.mod_small (U E a + U E b + 2 ^ 31)) by lia. replace (U E a + U E b + 2 ^ 31 - 2 ^ 31) with (U E a + U E b) by lia.
apply Z.mod_small. lia.
Qed.
Lemma mod64_negcoef : forall a s c, 0 <= s -> 0 <= c - (2 ^ 64 - a) * s -> c - (2 ^ 64 - a) * s < 2 ^ 64 ->
(a * s + c) mod 2 ^ 64 = c - (2 ^ 64 - a) * s.
Proof.
intros a s c Hs Hlo Hhi. replace (a * s + c) with ((c - (2 ^ 64 - a) * s) + s * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Ltac kill_ovf Hc E38 :=
exfalso;
lazymatch type of Hc with branch_taken BC_NE (sv_denot ?Ev (SAluw ALU_ADD ?X ?Y)) (sv_denot _ ?A3) = true =>
let HX := fresh "HX" in let HY := fresh "HY" in let HA := fresh "HA" in let HU := fresh "HU" in
let lx := eval vm_compute in (lin_of X) in lazymatch lx with Some (?l, ?c) =>
pose proof (lin_of_sound Ev X l c ltac:(vm_compute; reflexivity)) as HX end;
let ly := eval vm_compute in (lin_of Y) in lazymatch ly with Some (?l, ?c) =>
pose proof (lin_of_sound Ev Y l c ltac:(vm_compute; reflexivity)) as HY end;
let la := eval vm_compute in (lin_of A3) in lazymatch la with Some (?l, ?c) =>
pose proof (lin_of_sound Ev A3 l c ltac:(vm_compute; reflexivity)) as HA end;
cbn [lin_denot] in HX, HY, HA; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in HX, HY, HA; rewrite ?ew_ewset_other in HX, HY, HA by lia;
rewrite E38 in HX, HY, HA; rewrite ?unsigned_lit_small in HX, HY, HA by lia;
rewrite ?Z.add_0_r in HX; rewrite ?Z.add_0_r in HY; rewrite ?Z.add_0_r in HA;
unfold M64 in HX, HY, HA;
first [rewrite Z.mod_small in HX by lia | rewrite mod64_negcoef in HX by lia];
first [rewrite Z.mod_small in HY by lia | rewrite mod64_negcoef in HY by lia];
first [rewrite Z.mod_small in HA by lia | rewrite mod64_negcoef in HA by lia];
assert (HU : U Ev (SAluw ALU_ADD X Y) = U Ev A3) by (rewrite U_addw_small by (rewrite HX, HY; lia); rewrite HX, HY, HA; lia);
apply U_inj in HU; rewrite HU in Hc; unfold branch_taken in Hc; rewrite bv_eqb_unsigned, Z.eqb_refl in Hc; discriminate Hc
end.
Ltac eval_n Nx E38 HN :=
lazymatch Nx with U ?Ev (SAlu ALU_SRL ?inner (SLit 48)) =>
let HI := fresh "HI" in
let li := eval vm_compute in (lin_of inner) in lazymatch li with Some (?l, ?c) =>
pose proof (lin_of_sound Ev inner l c ltac:(vm_compute; reflexivity)) as HI end;
cbn [lin_denot] in HI; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in HI; rewrite ?ew_ewset_other in HI by lia;
rewrite E38 in HI; rewrite ?unsigned_lit_small in HI by lia; rewrite ?Z.add_0_r in HI; unfold M64 in HI;
first [rewrite Z.mod_small in HI by lia | rewrite mod64_negcoef in HI by lia];
lazymatch type of HI with _ = ?v =>
assert (HN : Nx = v / 2 ^ 48)
by (rewrite U_SAlu; cbn [zalu_raw]; rewrite HI, U_SLit; change (Z.land (zcanon 48) 63) with 48;
rewrite Z.shiftr_div_pow2 by lia; apply zcanon_id; unfold M64; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]) end;
lazymatch type of HN with _ = (?c - (2 ^ 64 - ?a) * ?sg) / _ =>
let q := eval vm_compute in (c / 2 ^ 48) in let m := eval vm_compute in ((2 ^ 64 - a) / 2 ^ 48) in
replace (c - (2 ^ 64 - a) * sg) with ((q - m * sg) * 2 ^ 48) in HN by lia; rewrite Z.div_mul in HN by lia end;
clear HI
end.
Ltac xdummy_facts HS :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let RF := lazymatch goal with H : ew _ 516 = Z_to_bv 64 _ |- _ => H end in
lazymatch type of RF with _ = Z_to_bv 64 ?Fv =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hw ?msx) =>
let rsm := eval vm_compute in (ss_mem ssx) in
let i0 := xidx_reg rsm 516%nat 0 in let i0 := eval vm_compute in i0 in let r0 := eval vm_compute in (nth i0 rsm got_regionP) in
let i2 := xidx_reg rsm 529%nat 0 in let i2 := eval vm_compute in i2 in let r2 := eval vm_compute in (nth i2 rsm got_regionP) in
let HR0 := fresh "HR0" in let HR2 := fresh "HR2" in let V4 := fresh "V4" in let Hsh4 := fresh "Hsh4" in let Hsa := fresh "Hsa" in
let Vpd := fresh "Vpd" in let HRApd := fresh "HRApd" in
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict] in HR0;
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i2 r2 HS ltac:(vm_compute; reflexivity)) as HR2; cbn [ms_mem restrict] in HR2;
xbyte HR0 32 Vpd;
lazymatch type of HR2 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ev _ 529 (SB + Fv / 8) cs lo hi wlo whi 4 1%N (SLit 1) 1 HR2 ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V4 end;
pose proof (aview_of_val_mem1 pa_segs _ _ _ _ V4 ltac:(lia)) as Hsh4;
let HFq := lazymatch goal with H : Fv = 32 * (Fv / 32) |- _ => H end in
let HF8 := lazymatch goal with H : Fv / 8 = 4 * (Fv / 32) |- _ => H end in
assert (Hsa : shadow_of_addr SHADOW_OFF (Fv + 32) = SB + Fv / 8 + 4)
by (unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; rewrite HFq at 1; rewrite HF8;
replace (32 * (Fv / 32) + 32) with ((4 * (Fv / 32) + 4) * 8) by lia; rewrite Z.div_mul by lia; lia);
assert (HRApd : range_addressable (aview pa_segs Hw (ms_mem msx)) SHADOW_OFF (Fv + 32) 1)
by (apply (block_shadow_range _ _ (Fv + 32) 1); [| lia | lia];
apply block_shadow_cells1; [rewrite HFq; replace (32 * (Fv / 32) + 32) with ((4 * (Fv / 32) + 4) * 8) by lia; apply Z_mod_mult | lia | rewrite Hsa; exact Hsh4]);
clear HR0 HR2 V4 Hsh4 Hsa end end.
Ltac xpre_D_sinkB :=
lazymatch goal with H : asink_at ?sg ?Kv ?m ?md ?f ?L |- _ =>
lazymatch L with context [?Sg ++ PRE_G ?Wd ?Hd ?sgct ?GCT ?rattr ?loops] =>
let HKs1 := lazymatch goal with Hk : sgct <= 2 ^ _ |- _ => Hk end in
lazymatch type of HKs1 with _ <= 2 ^ ?Kl =>
let HKlo := lazymatch goal with Hk : 0 <= Kl <= 8 |- _ => Hk end in
let HKs2 := lazymatch goal with Hk : 2 ^ Kl < 2 * sgct |- _ => Hk end in
let Hc := lazymatch goal with Hk : sgct <> 0 |- _ => Hk end in
let Hn0 := lazymatch goal with Hk : _ - _ * sgct = 0 |- _ => Hk | Hk : _ - _ * sgct <> 0 |- _ => Hk end in
let v := eval vm_compute in (2 ^ Z.max Kl 1) in
assert (HSINKD : asink_at sg Kv m md f (Sg ++ PRE_D Wd Hd sgct GCT rattr loops));
[ replace (Sg ++ PRE_D Wd Hd sgct GCT rattr loops) with L; [exact H|];
unfold PRE_D, PRE_G, PRE_C; rewrite (proj2 (Z.eqb_neq sgct 0) Hc); rewrite (gct_pad_K Kl sgct GCT HKlo ltac:(lia) HKs1 HKs2);
change (2 ^ Z.max Kl 1) with v;
lazymatch type of Hn0 with
| ?n = 0 => replace (3 * (v - sgct)) with 0 by (clear - Hn0; lia); cbn [Z.to_nat repeat]
| ?n <> 0 => replace (3 * (v - sgct)) with n by (clear; lia) end;
rewrite ?app_nil_r, <- ?app_assoc; reflexivity | ] end end end.
Section g.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_1) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_both3_1 PI.
Hypothesis TLF : PALibF B.
Variables wfn hw : Z.
Hypothesis Rwfn : 0 <= wfn < 2 ^ 64 /\ wfn mod 2 = 0.
Hypothesis Rhw : 0 <= hw < 2 ^ 64 /\ hw mod 2 = 0.
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B K.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Hypothesis WFNX : twcbF_spec SEGS K B wfn.
Hypothesis HGOT7 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 7)) 8 (BASE + AF_both3_cgif_raw_newgif).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Ltac rn_drop_ly ly3 EFA3 EFL3 :=
repeat match goal with H : context [ly3] |- _ => first [clear H | rewrite EFA3 in H | rewrite EFL3 in H | fail 2 "ly3 still used in" H] end.
Lemma rn_GX : rn_fromX K MT B wfn hw ss_DX PRE_D -> rn_fromX K MT B wfn hw ss_GX PRE_G.
Proof.
intros RD.
eapply rn_G0X; try eassumption;
first [eapply rn_G1X_0 | eapply rn_G1X_1 | eapply rn_G1X_2 | eapply rn_G1X_3 | eapply rn_G1X_4 | eapply rn_G1X_5 | eapply rn_G1X_6 | eapply rn_G1X_7 | eapply rn_G1X_8]; eassumption.
Qed.
End g.
End e.
End d.
