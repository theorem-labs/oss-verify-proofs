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
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCfu YCe9 YChv YChx YChw.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
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
Section f.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rn_G : rn_from B ss_D -> rn_from B ss_G.
Proof.
rn_prelude.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E32' : ew E 32 = Z_to_bv 64 g) by (rewrite (AG 32%nat) by lia; exact E32).
pose proof Hcfg as Hc'. cbn [obj_at LAY_RawConfig] in Hc'. destruct Hc' as (_ & _ & _ & _ & _ & _ & [_ R32] & _). cbn [fst snd N.to_nat Z.of_N] in R32.
change (2 ^ (8 * 2)) with 65536 in R32.
assert (Hc : sgct <> 0).
{ pose proof (st_ok_cond_In trbsegs E _ _ (mkAC BC_NE (SOff 38 0) (SLit 0)) HS ltac:(cbn; left; reflexivity)) as Q.
unfold acond_ok, branch_taken in Q. cbn [ac_c ac_a ac_b sv_denot negb] in Q. rewrite bv_eqb_unsigned in Q.
rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Q by lia.
destruct (Z.eqb_spec sgct 0); [discriminate Q | lia]. }
reshok_bx HS 35%nat.
rreg HS (12%bv : bv 5) Ra2. rreg HS (13%bv : bv 5) Ra3. rreg HS (14%bv : bv 5) Ra4. rreg HS (11%bv : bv 5) Ra1. rreg HS (16%bv : bv 5) Ra6.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (rn_pow2b B LAWS 9 0 sgct W3 (ms_regs msX) (ms_mem msX) _ TRAWNEW_STK (spZ regs) [] ly S W mem md [(2, fpos)] ly3 S3 k eq_refl HJ3);
[ exact Ra2 | exact Ra3 | exact Ra4 | rewrite Ra1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E38
| exact Ra6 | clear; lia | clear - Hc Hsg R32; lia | change (2 ^ 0) with 1; clear - Hc R32; lia ] end. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & K & -> & HJ5 & HK12 & HK16 & HK15 & HKlo & HKs1 & HKs2 & Hav5 & Hpr5 & Hrg5).
clear Ra2 Ra3 Ra4 Ra1 Ra6.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
jafter_stretch HS kk regs5 (mrestrict (w_H W3) mem5) POW_CLOB_B 0x89114 HS2;
specialize (HS2 Hrg5 (regions_kept_all Ev (w_H W3) (ms_mem msX) mem5 _ Hav5 Hpr5)) end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv. clear HEv.
assert (HKK1 : 2 ^ K <= 2 ^ Z.max K 1) by (apply Z.pow_le_mono_r; lia).
destruct (rn_pow_cases K HKlo) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]].
all: cbn in HKs1, HKs2, HKK1.
all: pose proof (st_ok_pin_reg' trbsegs _ _ _ 12%bv _ HS ltac:(cbn [ms_regs restrict mkst]; exact HK12) eq_refl) as HS3; clear HS; rename HS3 into HS.
all: pose proof (st_ok_pin_reg' trbsegs _ _ _ 16%bv _ HS ltac:(cbn [ms_regs restrict mkst]; exact HK16) eq_refl) as HS3; clear HS; rename HS3 into HS.
all: pose proof (st_ok_pin_reg' trbsegs _ _ _ 15%bv _ HS ltac:(cbn [ms_regs restrict mkst]; exact HK15) eq_refl) as HS3; clear HS; rename HS3 into HS.
all: lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of HKs1 with _ <= 2 ^ ?KK =>
let hi := eval vm_compute in (2 ^ Z.max KK 1) in
pose proof (st_ok_add_fact trbsegs Ev _ _ 38 (mkAF 1 hi 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E38, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - Hc HKs1 R32; cbn in HKs1; lia)) as HS3;
clear HS; rename HS3 into HS end end.
all: norm_ss HS; reshok_bx HS 35%nat; relow HS AG E10 E32 E10' E32'.
all: aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK RBspan 0x89178.
all: try (oblF HJ5 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (oblG HJ5 E32' E35 Hing3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
all: try (awrR AG fpos F EFA3).
all: try clear_frames.
all: srr_branch_tok trbtbl_lib_ok HS SHOK RBspan; [kill_ovf Hc0 E38 |].
all: aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK RBspan 0x89178.
all: try (oblF HJ5 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (oblG HJ5 E32' E35 Hing3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
all: try (awrR AG fpos F EFA3).
all: try clear_frames.
all: destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ5) Hfin3) as (_ & _ & HFpres5 & HFSpres5); change (fs_frame_bytes 2) with 256 in HFpres5, HFSpres5;
change (256 / 8) with 32 in HFSpres5; rewrite !EFA3 in HFpres5, HFSpres5; fold F in HFpres5, HFSpres5.
all: fs_rw HS E58 HFSpres5.
all: (aj_run_to_sh trbtbl_lib_ok HS HJ5 0x89184; [awrR AG fpos F EFA3|]).
all: clear_frames.
all: fs_ro HS; reshok_bx HS 35%nat.
all: srr_branch_tok trbtbl_lib_ok HS SHOK RBspan.
all: lazymatch goal with Hb : branch_taken BC_EQ (sv_denot ?Ev ?Nx) (sv_denot _ (SLit 0)) = _ |- _ =>
eval_n (U Ev Nx) E38 HN;
rewrite branch_eq_U, U_SLit, HN in Hb; change (zcanon 0) with 0 in Hb end.
all: match goal with Hb : (_ =? 0) = true |- _ => apply Z.eqb_eq in Hb; rename Hb into Hn0 | Hb : (_ =? 0) = false |- _ => apply Z.eqb_neq in Hb; rename Hb into Hn0 end.
all: lazymatch type of Hn0 with _ = 0 =>
aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK RBspan 0x891b4; [awrR AG fpos F EFA3|]; clear_frames;
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ5) Hfin3) as (_ & _ & HFpres6 & HFSpres6); change (fs_frame_bytes 2) with 256 in HFpres6, HFSpres6;
change (256 / 8) with 32 in HFSpres6; rewrite !EFA3 in HFpres6, HFSpres6; fold F in HFpres6, HFSpres6;
fs_rw HS E58 HFSpres6;
aj_run_to_sh trbtbl_lib_ok HS HJ5 0x891c4; [awrR AG fpos F EFA3|]; clear_frames;
fs_ro HS; rebaseE HS AG HEv; clear HEv;
rn_join HS ss_D 300%nat rn_deads_D;
lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos res);
[ exact HPRE | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_E_havoc; [clear; lia | repeat (apply rn_E_ewset; [clear; lia|]); repeat (split; [eassumption|]); eassumption]
| split; [exact HJ5 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | exact Ares]]]]]]
| exact Hsg | exact HS ] end
| _ <> 0 => idtac end.
all: lazymatch type of Hn0 with ?n <> 0 => assert (Hn : 3 <= n <= 765) by (clear - Hn0 HKs1 Hc R32; lia) end.
all: aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK RBspan 0x89188; [awrR AG fpos F EFA3|].
all: clear_frames.
all: lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
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
all: rreg HS (2%bv : bv 5) Q2; rreg HS (21%bv : bv 5) Q19; rreg HS (22%bv : bv 5) Q21; rreg HS (19%bv : bv 5) Q18; rreg HS (24%bv : bv 5) Q24; rreg HS (25%bv : bv 5) Q25.
all: lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
lazymatch type of Hn0 with ?n <> 0 =>
let e := eval vm_compute in (sr_get (ss_regs ssx) 21%bv) in
assert (Qn : getr (ms_regs msX) 21%bv = Z_to_bv 64 n);
[ rewrite (st_ok_restrict_reg trbsegs _ _ _ _ 21%bv HS); change (sv_denot Ev e = Z_to_bv 64 n);
apply bv_eq; rewrite unsigned_lit_small by lia; change (bv_unsigned (sv_denot Ev e)) with (U Ev e); exact HN | ] end end.
all: assert (Qal : (spZ regs - 192) mod 16 = 0) by
(pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D;
replace (32 * (spZ regs / 32) - 192) with ((2 * (spZ regs / 32) - 12) * 16) by lia; apply Z_mod_mult).
all: rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl); cbn [ss_pc].
all: eapply SRr_bind;
[ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of Hn0 with ?n <> 0 =>
eapply (rn_wdb B TL LAWS (Z.to_nat n) n W3 (ms_regs msX) (ms_mem msX) _
TRAWNEW_STK (spZ regs) [] ly S W mem md [(2, fpos)] ly3 S3 k (spZ regs - 192) g (bv_unsigned (ew Ev 40)) ltac:(clear - Hn; lia) HJ5);
[ rewrite Q2; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp; f_equal; clear; lia
| exact Qal | rewrite FFS; clear; lia | clear; lia | clear - C1 Hceil Hslo FFS; lia | clear - H47 Hshi; lia
| exact Qn | clear - Hn; lia | exact Q21 | exact Q18
| rewrite Q24; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E35
| rewrite Q25; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; exact E32
| exact Hing3 | exact M56 | exact M80 | exact M64
| pose proof (bv_unsigned_in_range 64 (ew Ev 40)) as Q; change (bv_modulus 64) with (2 ^ 64) in Q; exact Q ] end end end
| ].
all: cbv beta; intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HK19 & HK21 & Hav6 & Hpr6 & Hrg6).
all: clear Q2 Q19 Q21 Q18 Q24 Q25 Qn M56 M80 M64.
all: lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
jafter_stretch_keep HS kk regs6 (mrestrict (w_H W3) mem6) WDB_CLOB 0x891a4 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13]%nat HS2;
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
all: clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS; rebaseE HS AG HEv; clear HEv.
all: pose proof (st_ok_pin_reg' trbsegs _ _ _ 21%bv 0 HS ltac:(cbn [ms_regs restrict mkst]; exact HK19) eq_refl) as HS3; clear HS; rename HS3 into HS.
all: pose proof (st_ok_pin_reg' trbsegs _ _ _ 22%bv 0 HS ltac:(cbn [ms_regs restrict mkst]; exact HK21) eq_refl) as HS3; clear HS; rename HS3 into HS.
all: norm_ss HS; reshok_bx HS 35%nat; relow HS AG E10 E32 E10' E32'.
all: (aj_run_to_tok trbtbl_lib_ok HS HJ6 SHOK RBspan 0x891b4; [awrR AG fpos F EFA3|]).
all: clear_frames.
all: destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ6) Hfin3) as (_ & _ & HFpres7 & HFSpres7); change (fs_frame_bytes 2) with 256 in HFpres7, HFSpres7;
change (256 / 8) with 32 in HFSpres7; rewrite !EFA3 in HFpres7, HFSpres7; fold F in HFpres7, HFSpres7.
all: fs_rw HS E58 HFSpres7.
all: (aj_run_to_sh trbtbl_lib_ok HS HJ6 0x891c4; [awrR AG fpos F EFA3|]).
all: clear_frames.
all: fs_ro HS; rebaseE HS AG HEv; clear HEv.
all: rn_join HS ss_D 300%nat rn_deads_D.
all: lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos res);
[ exact HPRE | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_E_havoc; [clear; lia | repeat (apply rn_E_ewset; [clear; lia|]); repeat (split; [eassumption|]); eassumption]
| split; [exact HJ6 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | exact Ares]]]]]]
| exact Hsg | exact HS ] end.
Qed.
End f.
End d.
