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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbe.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC85 YC88 YCb9 YCb6 YCba YCb7.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg lib_both3_1_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_1_listing PI) (@pa_relro_lo _ lib_both3_1_listing PI) (@pa_relro_hi _ lib_both3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Ltac idx_of_baselo rs n lo :=
lazymatch rs with
| YP09.mkRegion (Some n) lo _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_baselo tl n lo in constr:(S i)
end.
Definition dropAt {A} (i : nat) (m : list A) : list A := firstn i m ++ skipn (S i) m.
Lemma range_addressable_zero8 : forall (rd : Z -> option Z) Bs p,
rd (shadow_of_addr Bs p) = Some 0 -> p mod 8 = 0 -> range_addressable rd Bs p 8.
Proof.
intros rd Bs p Hz Hp. apply zero_shadow_range; [exact Hp | reflexivity |].
intros i Hi. change (8 / 8) with 1 in Hi. replace i with 0 by lia. rewrite Z.add_0_r. exact Hz.
Qed.
Ltac xhas_net Hc :=
let E34 := lazymatch goal with H : ew _ 34 = Z_to_bv 64 ?r |- _ => H end in
lazymatch type of E34 with _ = Z_to_bv 64 ?rattr =>
let R24 := lazymatch goal with H : 0 <= rattr < _ |- _ => H end in
let Hnet := fresh "Hnet" in let Hl := fresh "Hl" in
unfold branch_taken in Hc; rewrite ?bv_eqb_unsigned in Hc; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hc;
rewrite ?ew_ewset_other in Hc by lia; rewrite E34 in Hc; rewrite alu64_unsigned in Hc; cbn [zalu_raw] in Hc;
rewrite (unsigned_lit_small rattr) in Hc by (clear - R24; lia); rewrite Z.add_0_r in Hc;
rewrite (unsigned_lit_small rattr), (unsigned_lit_small 3), (unsigned_lit_small 1) in Hc by (clear - R24; lia);
assert (Hl : 0 <= Z.land rattr 3 <= 3) by (rewrite (YI0j.land_bits01 rattr 3) by lia; destruct (Z.testbit _ _ && _), (Z.testbit _ _ && _); cbn; lia);
unfold bv_wrap, bv_modulus in Hc; rewrite (Z.mod_small (Z.land rattr 3)) in Hc by (clear - Hl; cbn; lia);
pose proof (YI0j.has_net_land rattr) as Hnet; destruct (Z.land rattr 3 =? 1); cbn [negb] in Hc; try discriminate Hc; clear Hc Hl end.
Ltac xpre_X_sink :=
lazymatch goal with H : asink_at ?sg ?Kv ?m ?md ?f ?L |- _ =>
lazymatch L with context [?Sg ++ PRE_D ?Wd ?Hd ?sgct ?GCT ?rattr ?loops] =>
let Hnet := lazymatch goal with Hn : YI0j.has_net rattr = _ |- _ => Hn end in
assert (HSINKX : asink_at sg Kv m md f (Sg ++ PRE_X Wd Hd sgct GCT rattr loops));
[ replace (Sg ++ PRE_X Wd Hd sgct GCT rattr loops) with L; [exact H|];
unfold PRE_X, PRE_D; rewrite YI0j.raw_header_eq; unfold rn_pk; rewrite Hnet; rewrite ?app_nil_r, <- ?app_assoc; reflexivity | ] end end.
Section d.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
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
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Lemma rn_DX : rn_fromX K MT B wfn hw ss_XX PRE_X -> rn_fromX K MT B wfn hw ss_DX PRE_D.
Proof.
rn_preludeX.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E32' : ew E 32 = Z_to_bv 64 g) by (rewrite (AG 32%nat) by lia; exact E32).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
pose proof Hcfg as Hc'. cbn [obj_at LAY_RawConfig] in Hc'.
destruct Hc' as (_ & [_ R8] & [_ R16] & [_ R24] & [_ R28] & [_ R30] & [_ R32] & [_ R34] & _).
cbn [fst snd N.to_nat Z.of_N] in R8, R16, R24, R28, R30, R32, R34.
change (2 ^ (8 * 8)) with (2 ^ 64) in R8, R16. change (2 ^ (8 * 4)) with (2 ^ 32) in R24. change (2 ^ (8 * 2)) with 65536 in R28, R30, R32, R34.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_baselo rs 516%nat 0 in
let rs2 := eval vm_compute in (dropAt i rs) in
pose proof (st_ok_pi_submem Ev ssx msx rs2 HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_baselo rs 516%nat 0 in
let rs2 := eval vm_compute in (dropAt i rs) in
pose proof (st_ok_submem SEGS Ev ssx msx rs2 HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 0 49 0 49 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres3 (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold CGIF_SIZE; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 0 49 0 49 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres3 (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold CGIF_SIZE; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 67 113 67 113 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres3 (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold CGIF_SIZE; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 67 113 67 113 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres3 (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold CGIF_SIZE; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 49 67 49 67 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres3 (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold CGIF_SIZE; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 49 67 49 67 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres3 (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold CGIF_SIZE; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS. reshok_bx HS 35%nat.
paj_run_tok RUN HS HJ3 SHOK RBspan.
all: try (oblFX HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
1: awrR AG fpos F EFA3.
xsink_stretch HFr HSINK. clear_frames.
psrr_branch_tok RUN BR HS SHOK RBspan.
-
xhas_net Hc.
paj_run_to_tok RUNTO HS HJ3 SHOK RBspan 0x5bc.
all: try (oblFX HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (oblG HJ3 E32' E35 Hing3).
all: try (oblR HJ3 Rres E35 Hres_in).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrR AG fpos F EFA3.
xsink_stretch HFr HSINK. clear_frames.
rebaseE HS AG HEv. clear HEv.
xpre_X_sink.
rn_join HS ss_XX 871%nat rn_deads_X.
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx ?Wx _ _ _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg rest cid pos E0 Ev Wx lyx Sx msv _ k fpos res Sg GCT);
[ exact HPRE | exact Hchne | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_EX_havoc; [clear; lia | repeat (apply rn_EX_ewset; [clear; lia|]); split; [repeat (split; [eassumption|]); eassumption | split; [exact E44 | exact E45]]]
| split; [exact HJ3 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | split; [exact Ares | split; [exact HSINKX | exact MLE]]]]]]]]
| exact Hsg | exact HSmax | exact HGCT | exact HS ] end end.
-
xhas_net Hc.
paj_run_tok RUN HS HJ3 SHOK RBspan.
all: try (oblFX HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrR AG fpos F EFA3.
xsink_stretch HFr HSINK. clear_frames.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRfs; cbn [ms_mem restrict] in HRfs;
lazymatch type of HRfs with region_ok _ _ _ (YP09.mkRegion (Some 529%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi 6 1%N (SLit 0) 0 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V6;
pose proof (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi 7 1%N (SLit 0) 0 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V7;
pose proof (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi 8 1%N (SLit 3) 3 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V8 end;
clear HRfs;
pose proof (aview_of_val_mem1 SEGS _ _ _ _ V6 ltac:(lia)) as Hsh6;
pose proof (aview_of_val_mem1 SEGS _ _ _ _ V7 ltac:(lia)) as Hsh7;
pose proof (aview_of_val_mem1 SEGS _ _ _ _ V8 ltac:(lia)) as Hsh8;
assert (HRA3 : range_addressable (aview SEGS (w_H W3) (ms_mem msX)) SHADOW_OFF (F + 49) 18);
[ eapply (range_addressable_sub (aview SEGS (w_H W3) (ms_mem msX)) SHADOW_OFF (F + 48) 19); [|lia|lia];
replace 19 with (8 + (8 + 3)) by reflexivity; apply range_addressable_app; [lia| |];
[ apply range_addressable_zero8; [|rewrite HFq; replace (32 * (F / 32) + 48) with ((4 * (F / 32) + 6) * 8) by lia; apply Z_mod_mult];
rewrite <- Hsh6; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 48) with ((4 * (F / 32) + 6) * 8) by lia; rewrite Z.div_mul by lia; lia
| replace (F + 48 + 8) with (F + 56) by lia; apply range_addressable_app; [lia| |];
[ apply range_addressable_zero8; [|rewrite HFq; replace (32 * (F / 32) + 56) with ((4 * (F / 32) + 7) * 8) by lia; apply Z_mod_mult];
rewrite <- Hsh7; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 56) with ((4 * (F / 32) + 7) * 8) by lia; rewrite Z.div_mul by lia; lia
| replace (F + 56 + 8) with (F + 64) by lia;
eapply (range_addressable_partial _ SHADOW_OFF (F + 64) 3); [|rewrite HFq; replace (32 * (F / 32) + 64) with ((4 * (F / 32) + 8) * 8) by lia; apply Z_mod_mult|lia];
rewrite <- Hsh8; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 64) with ((4 * (F / 32) + 8) * 8) by lia; rewrite Z.div_mul by lia; lia ] ]
| ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRfs; cbn [ms_mem restrict] in HRfs;
lazymatch type of HRfs with region_ok _ _ _ (YP09.mkRegion (Some 529%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi 6 1%N (SLit 0) 0 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V6;
pose proof (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi 7 1%N (SLit 0) 0 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V7;
pose proof (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi 8 1%N (SLit 3) 3 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V8 end;
clear HRfs;
pose proof (aview_of_val_mem1 SEGS _ _ _ _ V6 ltac:(lia)) as Hsh6;
pose proof (aview_of_val_mem1 SEGS _ _ _ _ V7 ltac:(lia)) as Hsh7;
pose proof (aview_of_val_mem1 SEGS _ _ _ _ V8 ltac:(lia)) as Hsh8;
assert (HRA3 : range_addressable (aview SEGS (w_H W3) (ms_mem msX)) SHADOW_OFF (F + 49) 18);
[ eapply (range_addressable_sub (aview SEGS (w_H W3) (ms_mem msX)) SHADOW_OFF (F + 48) 19); [|lia|lia];
replace 19 with (8 + (8 + 3)) by reflexivity; apply range_addressable_app; [lia| |];
[ apply range_addressable_zero8; [|rewrite HFq; replace (32 * (F / 32) + 48) with ((4 * (F / 32) + 6) * 8) by lia; apply Z_mod_mult];
rewrite <- Hsh6; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 48) with ((4 * (F / 32) + 6) * 8) by lia; rewrite Z.div_mul by lia; lia
| replace (F + 48 + 8) with (F + 56) by lia; apply range_addressable_app; [lia| |];
[ apply range_addressable_zero8; [|rewrite HFq; replace (32 * (F / 32) + 56) with ((4 * (F / 32) + 7) * 8) by lia; apply Z_mod_mult];
rewrite <- Hsh7; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 56) with ((4 * (F / 32) + 7) * 8) by lia; rewrite Z.div_mul by lia; lia
| replace (F + 56 + 8) with (F + 64) by lia;
eapply (range_addressable_partial _ SHADOW_OFF (F + 64) 3); [|rewrite HFq; replace (32 * (F / 32) + 64) with ((4 * (F / 32) + 8) * 8) by lia; apply Z_mod_mult|lia];
rewrite <- Hsh8; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 64) with ((4 * (F / 32) + 8) * 8) by lia; rewrite Z.div_mul by lia; lia ] ]
| ]  end.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
idtac.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_atS SEGS B LAWS Hsegs OSet (SIGMA AS_asan_memset) AMEMSET _ (ms_regs msX) (ms_mem msX) TRAWNEW_STK (spZ regs) (asink_fp pf) ly S W mem md [(2, fpos)]
ly3 S3 _ _ (F + 49) 0 18 (-192) (Z_to_bv 64 (BASE + 0x474)) HJ3) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite RF. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- exact Ra1.
- exact Ra2.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split; [| unfold ESTACK; lia]. right. right. right. exists 2, fpos. split; [left; reflexivity|]. left.
unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 2) with 256. rewrite EFA3. fold F. lia.
- apply amem_range_high; zone_lia.
- exact HRA3.
- intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 _ _ _ 2 fpos (F + 49) 18 (proj1 HJ3) Hfin3);
[rewrite EFA3; fold F; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; lia | lia].
- exact I. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4 & HSM4).
xsink_intrin Hfr4 HSM4 HSINK. clear HSM4.
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp V6 V7 V8 Hsh6 Hsh7 Hsh8 HRA3.
aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ4) Hfin3) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4.
change (256 / 8) with 32 in HFSpres4. rewrite !EFA3 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
reseat HS HJ4 HP4 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG
ltac:(idtac; first [ keptI Hfr4 Hpres4 AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
assert (HRO : region_ok SEGS Ev (ms_mem (restrict (w_H W3) msx))
(YP09.mkRegion (Some 516%nat) 49 67 49 67 [YP09.mkChunk 66 (CVal 1 (SLit 0))]));
[ unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres4 (F + o) ltac:(lia)))
| repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with |- YP09.chunk_ok _ ?Ey ?mx _ (YP09.mkChunk ?off _) =>
apply (chunk_ok_val SEGS Ey mx F off 1 (SLit 0) 0);
[ reflexivity | cbn; lia | cbn; lia
| let VV := fresh "VV" in pose proof (proj1 (val_mem1_of_aview SEGS _ _ _ _ (Heff (off - 49) ltac:(lia)))) as VV;
replace (F + 49 + (off - 49)) with (F + off) in VV by lia; exact VV ] end ]
| pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 49 67 49 67 [YP09.mkChunk 66 (CVal 1 (SLit 0))]) HS eq_refl HRO
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS HRO; rename HS3 into HS ] end.
norm_ss HS. reshok_bx HS 35%nat. clear_frames. relow HS AG E10 E32 E10' E32'.
paj_run_to_tok RUNTO HS HJ4 SHOK RBspan 0x5bc.
all: try (oblFX HJ4 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (oblG HJ4 E32' E35 Hing3).
all: try (oblR HJ4 Rres E35 Hres_in).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrR AG fpos F EFA3.
xsink_stretch HFr HSINK. clear_frames.
xnet19_facts HS.
wcb_siteX (13%bv : bv 5) HS HWX HGA HRAX HHVX HJ4 HAR3 Hfin3 HfinS3 Hing3 Hres_in Eab3 Hfrs3 EFA3 EFL3 HFpres4 HFSpres4 Hrpres3 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
reshok_bx HS 35%nat. relow HS AG E10 E32 E10' E32'.
paj_run_to_tok RUNTO HS HJ4 SHOK RBspan 0x5bc.
all: try (oblFX HJ4 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (oblG HJ4 E32' E35 Hing3).
all: try (oblR HJ4 Rres E35 Hres_in).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrR AG fpos F EFA3.
xsink_stretch HFr HSINK. clear_frames.
rebaseE HS AG HEv. clear HEv.
xpre_X_sink.
rn_join HS ss_XX 871%nat rn_deads_X.
lazymatch type of HJ4 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx ?Wx _ _ _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg rest cid pos E0 Ev Wx lyx Sx msv _ k fpos res Sg GCT);
[ exact HPRE | exact Hchne | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_EX_havoc; [clear; lia | repeat (apply rn_EX_ewset; [clear; lia|]); split; [repeat (split; [eassumption|]); eassumption | split; [exact E44 | exact E45]]]
| split; [exact HJ4 | split; [clear - Hk3; lia | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | split; [exact Ares | split; [exact HSINKX | exact MLE]]]]]]]]
| exact Hsg | exact HSmax | exact HGCT | exact HS ] end end.
Qed.
End d.
End c.
End b.
