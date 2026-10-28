(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8j ACbc ACbf ACbd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbe.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbg.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC85 YC88 YC7k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6 ACba ACb7 ACbb.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
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
let Hn0 := lazymatch goal with Hk : 3 * (2 ^ Z.max Kl 1 - sgct) = 0 |- _ => Hk | Hk : 3 * (2 ^ Z.max Kl 1 - sgct) <> 0 |- _ => Hk end in
assert (HSINKD : asink_at sg Kv m md f (Sg ++ PRE_D Wd Hd sgct GCT rattr loops));
[ replace (Sg ++ PRE_D Wd Hd sgct GCT rattr loops) with L; [exact H|];
unfold PRE_D, PRE_G, PRE_C; rewrite (proj2 (Z.eqb_neq sgct 0) Hc); rewrite (gct_pad_K Kl sgct GCT HKlo ltac:(lia) HKs1 HKs2);
lazymatch type of Hn0 with
| _ = 0 => rewrite Hn0; cbn [Z.to_nat repeat]
| _ <> 0 => idtac end;
rewrite ?app_nil_r, <- ?app_assoc; reflexivity | ] end end end.
Section g.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
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
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 7)) 8 (BASE + AF_asan3_cgif_raw_newgif).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Lemma rn_GX : rn_fromX K MT B wfn hw ss_DX PRE_D -> rn_fromX K MT B wfn hw ss_GX PRE_G.
Proof.
rn_preludeX.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E32' : ew E 32 = Z_to_bv 64 g) by (rewrite (AG 32%nat) by lia; exact E32).
pose proof Hcfg as Hc'. cbn [obj_at LAY_RawConfig] in Hc'. destruct Hc' as (_ & _ & _ & _ & _ & _ & [_ R32] & _). cbn [fst snd N.to_nat Z.of_N] in R32.
change (2 ^ (8 * 2)) with 65536 in R32.
assert (Hc : sgct <> 0).
{ pose proof (st_ok_cond_In SEGS E _ _ (mkAC BC_NE (SOff 38 0) (SLit 0)) HS ltac:(cbn; left; reflexivity)) as Q.
unfold acond_ok, branch_taken in Q. cbn [ac_c ac_a ac_b sv_denot negb] in Q. rewrite bv_eqb_unsigned in Q.
rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Q by lia.
destruct (Z.eqb_spec sgct 0); [discriminate Q | lia]. }
reshok_bx HS 35%nat.
prreg HS (12%bv : bv 5) Ra2. prreg HS (13%bv : bv 5) Ra3. prreg HS (15%bv : bv 5) Ra5.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (rn_pow2bX B LAWS 9 0 sgct W3 (ms_regs msX) (ms_mem msX) _ TRAWNEW_STK (spZ regs) (asink_fp pf) ly S W mem md [(2, fpos)] ly3 S3 k eq_refl HJ3);
[ exact Ra2 | exact Ra3 | rewrite Ra5; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E38
| clear; lia | clear - Hc Hsg R32; lia | change (2 ^ 0) with 1; clear - Hc R32; lia ] end. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & Kp & -> & HJ5 & HK11 & HK12 & HK14 & HKlo & HKs1 & HKs2 & Hav5 & Hpr5 & [HFS5 HFD5] & Hrg5).
clear Ra2 Ra3 Ra5.
lazymatch type of HSINK with asink_at _ _ (mrestrict _ ?mo) ?mdo _ ?SG =>
assert (HSINK5 : asink_at SEGS K (mrestrict (w_H W3) mem5) md5 pf SG);
[ apply (asink_at_model SEGS K _ mdo); [exact HFS5 | exact HFD5 |]; apply (asink_at_frame SEGS K (mrestrict (w_H W3) mo)); [|exact HSINK];
intros a _; apply (mbyte_of_aview SEGS); apply Hav5
| clear HSINK; rename HSINK5 into HSINK ] end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_stretch_hi HS kk regs5 (mrestrict (w_H W3) mem5) POW_CLOB_B 0x31c HS2;
specialize (HS2 Hrg5 (regions_kept_all Ev (w_H W3) (ms_mem msX) mem5 _ Hav5 Hpr5)) end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => lazymatch type of HEv with _ = havoc _ ?kk _ =>
assert (EK : ew Ev (kk + 0)%nat = Z_to_bv 64 Kp)
by (rewrite HEv; unfold POW_CLOB_B; cbn [map]; rewrite (ew_havoc_new _ kk [getr regs5 11%bv; getr regs5 12%bv; getr regs5 14%bv] 0 (Z_to_bv 64 0) ltac:(cbn; lia)); cbn [nth]; exact HK11) end end.
cbn [Nat.add] in EK. clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => lazymatch type of EK with ew _ ?ka = _ =>
pose proof (st_ok_pi_add_fact Ev _ _ ka (mkAF 0 8 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS end end.
assert (HKK1 : 2 ^ Kp <= 2 ^ Z.max Kp 1) by (apply Z.pow_le_mono_r; lia).
assert (Hp2 : 2 <= 2 ^ Z.max Kp 1 <= 256).
{ destruct (rn_pow_cases Kp HKlo) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
[ change (2 ^ Z.max 0 1) with 2 | change (2 ^ Z.max 1 1) with 2 | change (2 ^ Z.max 2 1) with 4 | change (2 ^ Z.max 3 1) with 8
| change (2 ^ Z.max 4 1) with 16 | change (2 ^ Z.max 5 1) with 32 | change (2 ^ Z.max 6 1) with 64 | change (2 ^ Z.max 7 1) with 128
| change (2 ^ Z.max 8 1) with 256 ]; clear; lia. }
norm_ss HS. reshok_bx HS 35%nat. relow HS AG E10 E32 E10' E32'.
paj_run_to_tok RUNTO HS HJ5 SHOK RBspan 0x368.
all: try (oblFX HJ5 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (oblG HJ5 E32' E35 Hing3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
all: try (awrR AG fpos F EFA3).
xsink_stretch HFr HSINK. clear_frames.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ5) Hfin3) as (_ & _ & HFpres5 & HFSpres5). change (fs_frame_bytes 2) with 256 in HFpres5, HFSpres5.
change (256 / 8) with 32 in HFSpres5. rewrite !EFA3 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
fs_rw HS E529 HFSpres5.
paj_run_to_sh RUNTOP HS HJ5 0x374; [awrR AG fpos F EFA3|]. xsink_stretch HFr HSINK. clear_frames.
fs_ro HS. reshok_bx HS 35%nat.
psrr_branch_tok RUN BR HS SHOK RBspan.
all: lazymatch type of Hc0 with context [sv_denot ?Ex (SAlu ALU_AND ?a ?b)] => lazymatch type of EK with ew _ ?ka = _ =>
replace (sv_denot Ex (SAlu ALU_AND a b)) with (Z_to_bv 64 (2 ^ Z.max Kp 1)) in Hc0
by (symmetry; exact (denot_rn_pow_mask Ex ka Kp ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact EK) HKlo)) end end.
all: unfold branch_taken in Hc0; rewrite bv_eqb_unsigned in Hc0; cbn [sv_denot] in Hc0;
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hc0; rewrite ?ew_ewset_other in Hc0 by lia;
rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc0 by lia.
-
apply Z.eqb_eq in Hc0.
assert (Hn0 : 3 * (2 ^ Z.max Kp 1 - sgct) = 0) by lia.
paj_run_to_tok RUNTO HS HJ5 SHOK RBspan 0x3b8; [awrR AG fpos F EFA3|]. xsink_stretch HFr HSINK. clear_frames.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ5) Hfin3) as (_ & _ & HFpres6 & HFSpres6). change (fs_frame_bytes 2) with 256 in HFpres6, HFSpres6.
change (256 / 8) with 32 in HFSpres6. rewrite !EFA3 in HFpres6, HFSpres6. fold F in HFpres6, HFSpres6.
fs_rw HS E529 HFSpres6.
paj_run_to_sh RUNTOP HS HJ5 0x3c0; [awrR AG fpos F EFA3|]. xsink_stretch HFr HSINK. clear_frames.
fs_ro HS. rebaseE HS AG HEv. clear HEv.
xpre_D_sinkB.
rn_join HS ss_DX 771%nat rn_deads_D_X_unused.
lazymatch type of HJ5 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx ?Wx _ _ _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg rest cid pos E0 Ev Wx lyx Sx msv _ k fpos res Sg GCT);
[ exact HPRE | exact Hchne | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_EX_havoc; [clear; lia | repeat (apply rn_EX_ewset; [clear; lia|]); split; [repeat (split; [eassumption|]); eassumption | split; [exact E44 | exact E45]]]
| split; [exact HJ5 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | split; [exact Ares | split; [exact HSINKD | exact MLE]]]]]]]]
| exact Hsg | exact HSmax | exact HGCT | exact HS ] end end.
-
apply Z.eqb_neq in Hc0.
assert (Hn : 3 <= 3 * (2 ^ Z.max Kp 1 - sgct) <= 765) by (clear - Hc0 HKs1 HKK1 Hp2 Hc R32; lia).
assert (Hn0 : 3 * (2 ^ Z.max Kp 1 - sgct) <> 0) by lia.
paj_run_to_tok RUNTO HS HJ5 SHOK RBspan 0x38c; [awrR AG fpos F EFA3|]. xsink_stretch HFr HSINK. clear_frames.
rebaseE HS AG HEv. clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 32%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 56 8%N (SOff 42 0) hw HRg ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E42, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as M56;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 80 8%N (SOff 44 0) pf HRg ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E44, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as M80;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 64 8%N (SOff 40 0) (bv_unsigned (ew Ex 40)) HRg ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity)
ltac:(pose proof (bv_unsigned_in_range 64 (ew Ex 40)) as Q; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Q; exact Q) ltac:(cbn; lia)) as M64 end;
clear HRg end.
prreg HS (2%bv : bv 5) Q2. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25. prreg HS (23%bv : bv 5) Q23.
xdummy_facts HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) => lazymatch type of EK with ew _ ?ka = _ =>
let e := eval vm_compute in (sr_get (ss_regs ssx) 19%bv) in
assert (Qn : getr (ms_regs msX) 19%bv = Z_to_bv 64 (3 * (2 ^ Z.max Kp 1 - sgct)));
[ rewrite (st_ok_restrict_reg SEGS _ _ _ _ 19%bv HS); change (sv_denot Ev e = Z_to_bv 64 (3 * (2 ^ Z.max Kp 1 - sgct)));
apply bv_eq; rewrite unsigned_lit_small by lia; change (bv_unsigned (sv_denot Ev e)) with (U Ev e);
apply (denot_rn_ndummy Ev ka 38 Kp sgct EK HKlo E38); clear - Hc0 HKs1 HKK1 Hc R32; lia | ] end end.
assert (Qal : (spZ regs - 192) mod 16 = 0) by
(pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D;
replace (32 * (spZ regs / 32) - 192) with ((2 * (spZ regs / 32) - 12) * 16) by lia; apply Z_mod_mult).
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
assert (Qtop : spZ regs < ly_top ly - 16) by (destruct Hch as [[_ Hnil] | (Qa & Qb & _)]; [exfalso; exact (Hchne Hnil) | lia]).
assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia.
assert (Qceil : alloc_ceiling <= spZ regs) by lia.
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rsm := eval vm_compute in (ss_mem ssx) in let i := idx_of_base rsm 2%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rsm got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRr ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRr ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0;
clear HRr;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) (spZ regs - 192) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
pose proof HJ5 as (_ & (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _) & _);
apply (achain_ly_top ly ly3); [exact Etop|];
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 192) Hch Qtop64 (aview_above_of_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5)
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop ltac:(lia))
| ] end end.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
aconsts HROD HJ5 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl); cbn [ss_pc].
eapply SRr_bind;
[ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
lazymatch type of HSINK with asink_at _ _ _ _ _ ?SG =>
eapply (rn_wdbX B LAWS wfn hw Rwfn Rhw K AIL WFNX (Z.to_nat (3 * (2 ^ Z.max Kp 1 - sgct))) (3 * (2 ^ Z.max Kp 1 - sgct)) W3 (ms_regs msX) (ms_mem msX) mdX
(spZ regs - 192) ly3 S3 g (bv_unsigned (ew Ev 40)) ((spZ regs, raZ regs, s0Z regs) :: ch) pf (F + 32) fpos SG ltac:(clear - Hn; lia)) end;
[ eapply (ajournal_sub_init SEGS B TRAWNEW_STK (spZ regs) (asink_fp pf) ly S W mem md [(2, fpos)] ly3 S3 W3 _ _ k WDBX_STK (spZ regs - 192) (asink_fp pf) (-192));
[exact HJ5 | clear; lia | reflexivity | clear; lia | unfold WDBX_STK, WCBF_STK, YC20.WCB_STK, AFWRITE_STK; clear; lia | rewrite FFS; unfold WDBX_STK, WCBF_STK, YC20.WCB_STK, AFWRITE_STK; clear; lia]
| rewrite Q2; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp; f_equal; clear; lia
| exact Qal
| rewrite Q3; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Q4; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| unfold s0Z at 1; rewrite Q8; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp; exact Hch1
| exact Qn | clear - Hn; lia | exact Q21
| rewrite Q22; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E41
| rewrite Q25; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; exact E32
| exact Hing3 | exact M56 | exact M80 | exact M64
| pose proof (bv_unsigned_in_range 64 (ew Ev 40)) as Q; change (bv_modulus 64) with (2 ^ 64) in Q; exact Q
| rewrite Q23; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; evalE AG
| exact Vpd | exact Hfin3 | exact Hinf3 | exact Hp_ia
| rewrite !EFA3; fold F; apply xfacts_i; clear - XF HFal; unfold xfacts in XF; unfold WDBX_STK, WCBF_STK, YC20.WCB_STK, AFWRITE_STK, TRAWNEW_STK in *; lia
| exact HRApd | exact HSINK
| let HGlen := fresh "HGlen" in destruct (HGCT Hc) as (_ & _ & _ & _ & HGlen); clear - HSmax Hn HGlen Hc R32 Hp2; unfold PRE_G, YI0j.hdr13 in *;
set (P := 2 ^ Z.max Kp 1) in *; clearbody P;
rewrite !length_app, length_firstn in *; cbn [length] in *; rewrite Nat.min_l by (apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia); unfold HDR_OUT in HSmax; lia ] end end
| ].
cbv beta; intros W6 c6 Hwle6 (ly6 & S6 & regs6 & mem6 & md6 & -> & HJw & (Ely6 & ES6) & HK19 & HK21 & HSINKw & Hrg6); subst ly6 S6.
pose proof (Permutation_refl (ablocks B ly3 S3)) as HPb6; clear HSINK Vpd HRApd; rename HSINKw into HSINK.
clear Q2 Q21 Q22 Q25 Q23 Qn M56 M80 M64 Q3 Q4 Q8 Vra Vs0 Hch1.
pose proof (ajournal_sub_tok SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5 HJw ltac:(rewrite FFS; unfold WDBX_STK, WCBF_STK, YC20.WCB_STK, AFWRITE_STK; clear; lia) ltac:(clear; lia)
ltac:(intros aa Haa; left; exact Haa)) as HJ6.
cbn [app] in HJ6; replace (k + 0) with k in HJ6 by lia.
pose proof (proj1 HJ6) as HAR6.
pose proof Hfrs3 as Hfrs6; pose proof Hfin3 as Hfin6; pose proof HfinS3 as HfinS6; pose proof Eab3 as Eab6; pose proof Hres_in as Hres_in6; pose proof Hing3 as Hing6.
pose proof EFA3 as EFA6; pose proof EFL3 as EFL6.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR6 Hfin6) as (_ & _ & HFpres6 & HFSpres6); change (fs_frame_bytes 2) with 256 in HFpres6, HFSpres6;
change (256 / 8) with 32 in HFSpres6; rewrite !EFA6 in HFpres6, HFSpres6; fold F in HFpres6, HFSpres6.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res 48 HAR6 Hres_in6) as (_ & _ & _ & _ & Hrpres6 & _); change (req_size 48) with 48 in Hrpres6.
aconsts HROD HJ6 Kgot6 Kcell6 Kguar6 Kuar6 Vgr6.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
let n := eval vm_compute in (length (ss_mem ssx)) in let idxs := eval vm_compute in (seq 0 n) in
jafter_stretch_keep_hi HS kk regs6 (mrestrict (w_H W6) mem6) WDB_CLOB 0x3a8 idxs HS2;
specialize (HS2 Hrg6);
match type of HS2 with ?tq -> _ => assert (HRK : tq) end;
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 516%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_frame_sub (segs:=SEGS) B Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 516%nat F lo hi wlo whi _ 2 fpos HJw);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; lia
| xFP | intros aa Haa; apply (fun H => proj1 (HFpres6 aa H)); lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 529%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_fshadow_sub (segs:=SEGS) B Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 529%nat (SB + F / 8) lo hi wlo whi _ 2 fpos HJw);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia
| rewrite EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32; lia
| xFP | intros aa Haa; lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 534%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_block_subw (segs:=SEGS) B Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 534%nat lo hi wlo whi _ res 48 HJw);
[ evalE AG | exact Hres_in | exact Hres_in6 | lia | change (req_size 48) with 48; lia
| xFP | intros aa Haa; apply (fun H => proj1 (Hrpres6 aa H)); lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub SEGS B); [exact HJw | exact HJ6 | evalE AG | lia | rewrite FFS; lia | lia | cbn; lia | cbn; lia]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 10%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_frame_sub (segs:=SEGS) B Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 10%nat cfgp lo hi wlo whi _ cid pos HJw);
[ evalE AG | exact HfinS3 | rewrite EFA3; lia | rewrite EFA3; lia | xFP | intros aa Haa; lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_block_sub SEGS B); [exact HJw | evalE AG | exact Hing3 | exact Hing6 | lia | change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia
| xFP ]
| |- _ => keptI I I AG Kgot3 Kgot6 Kcell3 Kcell6 Kguar3 Kguar6 Kuar3 Kuar6 Vgr3 Vgr6
end
| specialize (HS2 HRK); clear HRK ] end.
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS; rebaseE HS AG HEv; clear HEv.
pose proof (st_ok_pi_pin_reg' _ _ _ 19%bv 0 HS ltac:(cbn [ms_regs restrict mkst]; exact HK19) eq_refl) as HS3; clear HS; rename HS3 into HS.
pose proof (st_ok_pi_pin_reg' _ _ _ 21%bv 0 HS ltac:(cbn [ms_regs restrict mkst]; exact HK21) eq_refl) as HS3; clear HS; rename HS3 into HS.
norm_ss HS.
clear HJ3 HAR3 Hfin3 HfinS3 Hing3 Hres_in Eab3 Hfrs3 HFpres3 HFSpres3 Hrpres3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3 HJ5 HJw HPb6 Hwle6 Hrg6 HK19 HK21.
clear EFA3 EFL3.
rename HAR6 into HAR3; rename Hfin6 into Hfin3; rename HfinS6 into HfinS3; rename Hing6 into Hing3; rename Hres_in6 into Hres_in.
rename Eab6 into Eab3; rename Hfrs6 into Hfrs3; rename EFA6 into EFA3; rename EFL6 into EFL3; rename HFpres6 into HFpres3; rename HFSpres6 into HFSpres3.
rename Hrpres6 into Hrpres3; rename Kgot6 into Kgot3; rename Kcell6 into Kcell3; rename Kguar6 into Kguar3; rename Kuar6 into Kuar3; rename Vgr6 into Vgr3.
reshok_bx HS 35%nat; relow HS AG E10 E32 E10' E32'.
paj_run_to_tok RUNTO HS HJ6 SHOK RBspan 0x3b8; [awrR AG fpos F EFA3|].
xsink_stretch HFr HSINK.
clear_frames.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ6) Hfin3) as (_ & _ & HFpres7 & HFSpres7); change (fs_frame_bytes 2) with 256 in HFpres7, HFSpres7;
change (256 / 8) with 32 in HFSpres7; rewrite !EFA3 in HFpres7, HFSpres7; fold F in HFpres7, HFSpres7.
fs_rw HS E529 HFSpres7.
paj_run_to_sh RUNTOP HS HJ6 0x3c0; [awrR AG fpos F EFA3|].
xsink_stretch HFr HSINK.
clear_frames.
fs_ro HS; rebaseE HS AG HEv; clear HEv.
xpre_D_sinkB.
rn_join HS ss_DX 771%nat rn_deads_D_X_unused.
lazymatch type of HJ6 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx ?Wx _ _ _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg rest cid pos E0 Ev Wx lyx Sx msv _ k fpos res Sg GCT);
[ exact HPRE | exact Hchne | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_EX_havoc; [clear; lia | repeat (apply rn_EX_ewset; [clear; lia|]); split; [repeat (split; [eassumption|]); eassumption | split; [exact E44 | exact E45]]]
| split; [exact HJ6 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | split; [exact Ares | split; [exact HSINKD | exact MLE]]]]]]]]
| exact Hsg | exact HSmax | exact HGCT | exact HS ] end end.
Qed.
End g.
End e.
End d.
