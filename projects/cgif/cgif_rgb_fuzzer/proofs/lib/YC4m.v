(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC4o YC4q YC4p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rn_G : rn_from B ss_D -> rn_from B ss_G.
Proof.
rn_prelude.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E32' : ew E 32 = Z_to_bv 64 g) by (rewrite (AG 32%nat) by lia; exact E32).
pose proof Hcfg as Hc'. cbn [obj_at LAY_RawConfig] in Hc'. destruct Hc' as (_ & _ & _ & _ & _ & _ & [_ R32] & _). cbn [fst snd N.to_nat Z.of_N] in R32.
change (2 ^ (8 * 2)) with 65536 in R32.
assert (Hc : sgct <> 0).
{ pose proof (st_ok_cond_In trasegs E _ _ (mkAC BC_NE (SOff 38 0) (SLit 0)) HS ltac:(cbn; left; reflexivity)) as Q.
unfold acond_ok, branch_taken in Q. cbn [ac_c ac_a ac_b sv_denot negb] in Q. rewrite bv_eqb_unsigned in Q.
rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Q by lia.
destruct (Z.eqb_spec sgct 0); [discriminate Q | lia]. }
reshok_bx HS 35%nat.
rreg HS (12%bv : bv 5) Ra2. rreg HS (13%bv : bv 5) Ra3. rreg HS (15%bv : bv 5) Ra5.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (rn_pow2b B LAWS 9 0 sgct W3 (ms_regs msX) (ms_mem msX) _ TRAWNEW_STK (spZ regs) [] ly S W mem md [(2, fpos)] ly3 S3 k eq_refl HJ3);
[ exact Ra2 | exact Ra3 | rewrite Ra5; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E38
| clear; lia | clear - Hc Hsg R32; lia | change (2 ^ 0) with 1; clear - Hc R32; lia ] end. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & K & -> & HJ5 & HK11 & HK12 & HK14 & HKlo & HKs1 & HKs2 & Hav5 & Hpr5 & Hrg5).
clear Ra2 Ra3 Ra5.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
jafter_stretch HS kk regs5 (mrestrict (w_H W3) mem5) POW_CLOB_B 0x88690 HS2;
specialize (HS2 Hrg5 (regions_kept_all Ev (w_H W3) (ms_mem msX) mem5 _ Hav5 Hpr5)) end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of HEv with Ev = havoc _ ?kk _ =>
assert (EK : ew Ev (kk + 0)%nat = Z_to_bv 64 K) by (rewrite HEv; rewrite (ew_havoc_new _ kk _ 0 (Z_to_bv 64 0)) by (cbn; lia); exact HK11);
cbn [Nat.add] in EK;
lazymatch type of EK with ew _ ?ka = _ =>
pose proof (st_ok_add_fact trasegs Ev _ _ ka (mkAF 0 8 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS end end end.
clear HEv. norm_ss HS. reshok_bx HS 35%nat. relow HS AG E10 E32 E10' E32'.
aj_run_to_tok tratbl_lib_ok HS HJ5 SHOK RBspan 0x886dc.
all: try (oblF HJ5 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (oblG HJ5 E32' E35 Hing3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrR AG fpos F EFA3.
clear_frames.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ5) Hfin3) as (_ & _ & HFpres5 & HFSpres5). change (fs_frame_bytes 2) with 256 in HFpres5, HFSpres5.
change (256 / 8) with 32 in HFSpres5. rewrite !EFA3 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
fs_rw HS E58 HFSpres5.
aj_run_to_sh tratbl_lib_ok HS HJ5 0x886e8; [awrR AG fpos F EFA3|]. clear_frames.
fs_ro HS. reshok_bx HS 35%nat.
srr_branch_tok tratbl_lib_ok HS SHOK RBspan.
+
aj_run_to_tok tratbl_lib_ok HS HJ5 SHOK RBspan 0x8872c; [awrR AG fpos F EFA3|]. clear_frames.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ5) Hfin3) as (_ & _ & HFpres6 & HFSpres6). change (fs_frame_bytes 2) with 256 in HFpres6, HFSpres6.
change (256 / 8) with 32 in HFSpres6. rewrite !EFA3 in HFpres6, HFSpres6. fold F in HFpres6, HFSpres6.
fs_rw HS E58 HFSpres6.
aj_run_to_sh tratbl_lib_ok HS HJ5 0x88734; [awrR AG fpos F EFA3|]. clear_frames.
fs_ro HS. rebaseE HS AG HEv. clear HEv.
rn_join HS ss_D 300%nat rn_deads_D.
lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos res);
[ exact HPRE | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_E_havoc; [clear; lia | repeat (apply rn_E_ewset; [clear; lia|]); repeat (split; [eassumption|]); eassumption]
| split; [exact HJ5 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | exact Ares]]]]]]
| exact Hsg | exact HS ] end.
+
rebaseE HS AG HEv. rewrite <- HEv in Hc0. rewrite <- HEv in SHOK. clear HEv.
unfold branch_taken in Hc0.
lazymatch type of Hc0 with context [sv_denot ?Ex (SAlu ALU_AND ?a ?b)] => lazymatch type of EK with ew _ ?ka = _ =>
replace (sv_denot Ex (SAlu ALU_AND a b)) with (Z_to_bv 64 (2 ^ Z.max K 1)) in Hc0 by (symmetry; exact (denot_rn_pow_mask Ex ka K EK HKlo)) end end.
rewrite bv_eqb_unsigned in Hc0. cbn [sv_denot] in Hc0. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned in Hc0.
assert (Hp2 : 2 <= 2 ^ Z.max K 1 <= 256).
{ destruct (rn_pow_cases K HKlo) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
[ change (2 ^ Z.max 0 1) with 2 | change (2 ^ Z.max 1 1) with 2 | change (2 ^ Z.max 2 1) with 4 | change (2 ^ Z.max 3 1) with 8
| change (2 ^ Z.max 4 1) with 16 | change (2 ^ Z.max 5 1) with 32 | change (2 ^ Z.max 6 1) with 64 | change (2 ^ Z.max 7 1) with 128
| change (2 ^ Z.max 8 1) with 256 ]; clear; lia. }
rewrite !unsigned_lit_small in Hc0 by lia. apply Z.eqb_neq in Hc0.
assert (HKK1 : 2 ^ K <= 2 ^ Z.max K 1) by (apply Z.pow_le_mono_r; lia).
assert (Hn : 3 <= 3 * (2 ^ Z.max K 1 - sgct) <= 765) by (clear - Hp2 HKK1 Hc0 HKs1 Hc R32; lia).
aj_run_to_tok tratbl_lib_ok HS HJ5 SHOK RBspan 0x88700; [awrR AG fpos F EFA3|]. clear_frames.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 32%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 56 8%N (SLit A_writecb) A_writecb HRg ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(unfold A_writecb; cbn; lia) ltac:(cbn; lia)) as M56;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 80 8%N (SLit 0) 0 HRg ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as M80;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 64 8%N (SOff 40 0) (bv_unsigned (ew Ex 40)) HRg ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity)
ltac:(pose proof (bv_unsigned_in_range 64 (ew Ex 40)) as Q; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Q; exact Q) ltac:(cbn; lia)) as M64 end;
clear HRg end.
rreg HS (2%bv : bv 5) Q2. rreg HS (21%bv : bv 5) Q19. rreg HS (22%bv : bv 5) Q21. rreg HS (24%bv : bv 5) Q24. rreg HS (25%bv : bv 5) Q25.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) 19%bv) in
assert (Q18 : getr (ms_regs msX) 19%bv = Z_to_bv 64 (3 * (2 ^ Z.max K 1 - sgct)));
[ rewrite (st_ok_restrict_reg trasegs _ _ _ _ 19%bv HS); change (sv_denot Ev e = Z_to_bv 64 (3 * (2 ^ Z.max K 1 - sgct)));
apply bv_eq; rewrite unsigned_lit_small by lia; change (bv_unsigned (sv_denot Ev e)) with (U Ev e);
lazymatch type of EK with ew _ ?ka = _ => apply (denot_rn_ndummy Ev ka 38 K sgct EK HKlo E38) end; clear - Hc0 HKs1 HKK1 Hc R32; lia | ] end.
assert (Qal : (spZ regs - 192) mod 16 = 0).
{ pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D.
replace (32 * (spZ regs / 32) - 192) with ((2 * (spZ regs / 32) - 12) * 16) by lia. apply Z_mod_mult. }
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
eapply (rn_wdb B TL LAWS (Z.to_nat (3 * (2 ^ Z.max K 1 - sgct))) (3 * (2 ^ Z.max K 1 - sgct)) W3 (ms_regs msX) (ms_mem msX) _
TRAWNEW_STK (spZ regs) [] ly S W mem md [(2, fpos)] ly3 S3 k (spZ regs - 192) g (bv_unsigned (ew Ev 40)) ltac:(clear - Hn; lia) HJ5);
[ rewrite Q2; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp; f_equal; clear; lia
| exact Qal | rewrite FFS; clear; lia | clear; lia | clear - C1 Hceil Hslo FFS; lia | clear - H47 Hshi; lia
| exact Q18 | clear - Hn; lia | exact Q19 | exact Q21
| rewrite Q24; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E35
| rewrite Q25; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; exact E32
| exact Hing3 | exact M56 | exact M80 | exact M64
| pose proof (bv_unsigned_in_range 64 (ew Ev 40)) as Q; change (bv_modulus 64) with (2 ^ 64) in Q; exact Q ] end end. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HK18 & HK19 & Hav6 & Hpr6 & Hrg6).
clear Q2 Q19 Q21 Q24 Q25 Q18 M56 M80 M64.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
jafter_stretch_keep HS kk regs6 (mrestrict (w_H W3) mem6) WDB_CLOB 0x8871c [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13]%nat HS2;
lazymatch type of HS2 with _ -> Forall _ ?rs -> _ =>
assert (HRK : Forall (fun r => 0 <= base_val Ev (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val Ev (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val Ev (YQ0b.r_base r) + YQ0b.r_hi r <= spZ regs - 192 - 16 \/ spZ regs - 192 <= base_val Ev (YQ0b.r_base r) + YQ0b.r_lo r)) rs);
[ repeat apply Forall_cons; try apply Forall_nil; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite ?RF, ?E58, ?Rres; rewrite ?(AG 2%nat), ?(AG 10%nat), ?(AG 32%nat) by lia; rewrite ?Usp, ?E10, ?E32;
rewrite ?unsigned_lit_small by (unfold SB; lia);
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawnew, CGIF_SIZE, SB;
clear - HFceil HFhigh HF8lo HF8hi Hceil Hslo Hshi H47 Hrh Hrceil Hgh Hgceil Hfceil Hfhigh Hflo Hfhi C1 C2 C3 C4 C5 FFS;
zone_lia
| specialize (HS2 Hrg6 (regions_kept_out Ev (w_H W3) (ms_mem msX) mem6 (spZ regs - 192 - 16) (spZ regs - 192) _ Hav6 Hpr6 HRK)) ] end end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv. clear HEv.
pose proof (st_ok_pin_reg' trasegs _ _ _ 19%bv 0 HS ltac:(cbn [ms_regs restrict mkst]; exact HK18) eq_refl) as HS3. clear HS. rename HS3 into HS.
pose proof (st_ok_pin_reg' trasegs _ _ _ 21%bv 0 HS ltac:(cbn [ms_regs restrict mkst]; exact HK19) eq_refl) as HS3. clear HS. rename HS3 into HS.
norm_ss HS. reshok_bx HS 35%nat. relow HS AG E10 E32 E10' E32'.
aj_run_to_tok tratbl_lib_ok HS HJ6 SHOK RBspan 0x8872c; [awrR AG fpos F EFA3|]. clear_frames.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ6) Hfin3) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 2) with 256 in HFpres7, HFSpres7.
change (256 / 8) with 32 in HFSpres7. rewrite !EFA3 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
fs_rw HS E58 HFSpres7.
aj_run_to_sh tratbl_lib_ok HS HJ6 0x88734; [awrR AG fpos F EFA3|]. clear_frames.
fs_ro HS. rebaseE HS AG HEv. clear HEv.
rn_join HS ss_D 300%nat rn_deads_D.
lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos res);
[ exact HPRE | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_E_havoc; [clear; lia | repeat (apply rn_E_ewset; [clear; lia|]); repeat (split; [eassumption|]); eassumption]
| split; [exact HJ6 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | exact Ares]]]]]]
| exact Hsg | exact HS ] end.
Qed.
End d.
End c.
