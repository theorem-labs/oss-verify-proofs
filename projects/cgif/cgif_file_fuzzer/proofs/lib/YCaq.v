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
Section d.
Context {PI : PAImg lib_both3_1_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_1_listing PI) (@pa_relro_lo _ lib_both3_1_listing PI) (@pa_relro_hi _ lib_both3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma range_addressable_zero8 : forall (rd : Z -> option Z) Bs p,
rd (shadow_of_addr Bs p) = Some 0 -> p mod 8 = 0 -> range_addressable rd Bs p 8.
Proof.
intros rd Bs p Hz Hp. apply zero_shadow_range; [exact Hp | reflexivity |].
intros i Hi. change (8 / 8) with 1 in Hi. replace i with 0 by lia. rewrite Z.add_0_r. exact Hz.
Qed.
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
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
Hypothesis WFNX : twcbF_spec SEGS K B wfn.
Hypothesis HGOT7 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 7)) 8 (BASE + AF_both3_cgif_raw_newgif).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Lemma rn_BX : rn_fromX K MT B wfn hw ss_CX PRE_C -> rn_fromX K MT B wfn hw ss_BX PRE_C.
Proof.
rn_preludeX. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
pose proof (st_ok_pi_submem E ssx msx
(nth 0 (ss_mem ssx) got_regionP :: nth 1 (ss_mem ssx) got_regionP :: trim_lo (nth 2 (ss_mem ssx) got_regionP) 125 :: skipn 3 (ss_mem ssx)) HS
ltac:(cbn [ss_mem ss_BX nth skipn]; apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|];
apply submem_keep; [apply subregion_trim_lo|]; apply submem_refl) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ _ ?ssx ?msx =>
pose proof (st_ok_submem SEGS E ssx msx
(nth 0 (ss_mem ssx) got_regionP :: nth 1 (ss_mem ssx) got_regionP :: trim_lo (nth 2 (ss_mem ssx) got_regionP) 125 :: skipn 3 (ss_mem ssx)) HS
ltac:(cbn [ss_mem ss_BX nth skipn]; apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|];
apply submem_keep; [apply subregion_trim_lo|]; apply submem_refl) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ _ _ _ =>
pose proof (st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 516%nat) 0 113 0 113 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres3 (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold CGIF_SIZE; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS | st_ok _ _ _ _ =>
pose proof (st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 516%nat) 0 113 0 113 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres3 (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold CGIF_SIZE; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ _ _ _ =>
pose proof (st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 516%nat) 113 125 113 125 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres3 (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold CGIF_SIZE; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS | st_ok _ _ _ _ =>
pose proof (st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 516%nat) 113 125 113 125 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres3 (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold CGIF_SIZE; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS. reshok_bx HS 35%nat.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by exact EFA3.
paj_run_tok RUN HS HJ3 SHOK RBspan;
[ oblFX HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal | oblFX HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal | awrR AG fpos F EFA3 |].
xsink_stretch HFr HSINK. clear HF HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) 3 _ HS eq_refl) as HRfs; cbn [ms_mem restrict] in HRfs;
lazymatch type of HRfs with region_ok _ _ _ (YP09.mkRegion (Some 529%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi 14 1%N (SLit 0) 0 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V14;
pose proof (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi 15 1%N (SLit 5) 5 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V15 end;
clear HRfs;
pose proof (aview_of_val_mem1 SEGS _ _ _ _ V14 ltac:(lia)) as Hsh14;
pose proof (aview_of_val_mem1 SEGS _ _ _ _ V15 ltac:(lia)) as Hsh15;
assert (HRA3 : range_addressable (aview SEGS (w_H W3) (ms_mem msX)) SHADOW_OFF (F + 113) 12);
[ eapply (range_addressable_sub (aview SEGS (w_H W3) (ms_mem msX)) SHADOW_OFF (F + 112) 13); [|lia|lia];
replace 13 with (8 + 5) by reflexivity; apply range_addressable_app; [lia| |];
[ apply range_addressable_zero8; [|rewrite HFq; replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by lia; apply Z_mod_mult];
rewrite <- Hsh14; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by lia; rewrite Z.div_mul by lia; lia
| replace (F + 112 + 8) with (F + 120) by lia;
eapply (range_addressable_partial _ SHADOW_OFF (F + 120) 5); [|rewrite HFq; replace (32 * (F / 32) + 120) with ((4 * (F / 32) + 15) * 8) by lia; apply Z_mod_mult|lia];
rewrite <- Hsh15; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 120) with ((4 * (F / 32) + 15) * 8) by lia; rewrite Z.div_mul by lia; lia ]
| ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) 3 _ HS eq_refl) as HRfs; cbn [ms_mem restrict] in HRfs;
lazymatch type of HRfs with region_ok _ _ _ (YP09.mkRegion (Some 529%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi 14 1%N (SLit 0) 0 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V14;
pose proof (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi 15 1%N (SLit 5) 5 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V15 end;
clear HRfs;
pose proof (aview_of_val_mem1 SEGS _ _ _ _ V14 ltac:(lia)) as Hsh14;
pose proof (aview_of_val_mem1 SEGS _ _ _ _ V15 ltac:(lia)) as Hsh15;
assert (HRA3 : range_addressable (aview SEGS (w_H W3) (ms_mem msX)) SHADOW_OFF (F + 113) 12);
[ eapply (range_addressable_sub (aview SEGS (w_H W3) (ms_mem msX)) SHADOW_OFF (F + 112) 13); [|lia|lia];
replace 13 with (8 + 5) by reflexivity; apply range_addressable_app; [lia| |];
[ apply range_addressable_zero8; [|rewrite HFq; replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by lia; apply Z_mod_mult];
rewrite <- Hsh14; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by lia; rewrite Z.div_mul by lia; lia
| replace (F + 112 + 8) with (F + 120) by lia;
eapply (range_addressable_partial _ SHADOW_OFF (F + 120) 5); [|rewrite HFq; replace (32 * (F / 32) + 120) with ((4 * (F / 32) + 15) * 8) by lia; apply Z_mod_mult|lia];
rewrite <- Hsh15; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 120) with ((4 * (F / 32) + 15) * 8) by lia; rewrite Z.div_mul by lia; lia ]
| ]  end.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
idtac.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_atS SEGS B LAWS Hsegs OSet (SIGMA AS_asan_memset) AMEMSET _ (ms_regs msX) (ms_mem msX) TRAWNEW_STK (spZ regs) (asink_fp pf) ly S W mem md [(2, fpos)]
ly3 S3 _ _ (F + 113) 0 12 (-192) (Z_to_bv 64 (BASE + 0x1cc)) HJ3) end.
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
- apply (amem_range_sub_app _ _ _ _ HFhigh HFceil); clear; lia.
- exact HRA3.
- intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 _ _ _ 2 fpos (F + 113) 12 (proj1 HJ3) Hfin3);
[rewrite EFA3; fold F; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; lia | lia].
- exact I. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4 & HSM4).
xsink_intrin Hfr4 HSM4 HSINK. clear HSM4.
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp V14 V15 Hsh14 Hsh15 HRA3.
aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ4) Hfin3) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4.
change (256 / 8) with 32 in HFSpres4. rewrite !EFA3 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
reseat HS HJ4 HP4 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]%nat AG
ltac:(idtac; first [ keptI Hfr4 Hpres4 AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
assert (HRO : region_ok SEGS Ev (ms_mem (restrict (w_H W3) msx))
(YP09.mkRegion (Some 516%nat) 113 125 113 125 [YP09.mkChunk 122 (CVal 1 (SLit 0)); YP09.mkChunk 123 (CVal 1 (SLit 0)); YP09.mkChunk 124 (CVal 1 (SLit 0))]));
[ unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres4 (F + o) ltac:(lia)))
| repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with |- YP09.chunk_ok _ ?Ey ?mx _ (YP09.mkChunk ?off _) =>
apply (chunk_ok_val SEGS Ey mx F off 1 (SLit 0) 0);
[ reflexivity | cbn; lia | cbn; lia
| let VV := fresh "VV" in pose proof (proj1 (val_mem1_of_aview SEGS _ _ _ _ (Heff (off - 113) ltac:(lia)))) as VV;
replace (F + 113 + (off - 113)) with (F + off) in VV by lia; exact VV ] end ]
| pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 113 125 113 125 [YP09.mkChunk 122 (CVal 1 (SLit 0)); YP09.mkChunk 123 (CVal 1 (SLit 0)); YP09.mkChunk 124 (CVal 1 (SLit 0))]) HS eq_refl HRO
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS HRO; rename HS3 into HS ] end.
norm_ss HS. reshok_bx HS 35%nat. clear_frames.
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (E10'' : ew Ev 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10) end.
paj_run_tok RUN HS HJ4 SHOK RBspan; [oblFX HJ4 E10'' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal | awrR AG fpos F EFA3 |].
xsink_stretch HFr HSINK. clear_frames.
psrr_branch_tok RUN BR HS SHOK RBspan.
-
assert (Hsg0 : sgct = 0).
{ pose proof Hcfg as Hc'. cbn [obj_at LAY_RawConfig] in Hc'. destruct Hc' as (_ & _ & _ & _ & _ & _ & [_ R32] & _). cbn [fst snd N.to_nat Z.of_N] in R32.
change (2 ^ (8 * 2)) with 65536 in R32.
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot] in Hc. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hc.
rewrite ?ew_ewset_other in Hc by lia. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.eqb_eq in Hc. exact Hc. }
paj_run_to_tok RUNTO HS HJ4 SHOK RBspan 0x2ac; [awrR AG fpos F EFA3|]. xsink_stretch HFr HSINK. clear_frames.
norm_ss HS.
xrechunk_pk HS ltac:(rewrite Hsg0; cbn [sv_denot]; rewrite unsigned_lit_small by lia; reflexivity).
rn_join HS ss_CX 631%nat rn_deads_C.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos res Sg GCT);
[ exact HPRE | exact Hchne | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_EX_havoc; [clear; lia | repeat (apply rn_EX_ewset; [clear; lia|]); split; [repeat (split; [eassumption|]); eassumption | split; [exact E44 | exact E45]]]
| split; [exact HJ4 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | split; [exact Ares | split; [exact HSINK | exact MLE]]]]]]]]
| exact Hsg | exact HSmax | exact HGCT | exact HS ] | st_ok _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos res Sg GCT);
[ exact HPRE | exact Hchne | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_EX_havoc; [clear; lia | repeat (apply rn_EX_ewset; [clear; lia|]); split; [repeat (split; [eassumption|]); eassumption | split; [exact E44 | exact E45]]]
| split; [exact HJ4 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | split; [exact Ares | split; [exact HSINK | exact MLE]]]]]]]]
| exact Hsg | exact HSmax | exact HGCT | exact HS ]  end.
-
pose proof Hcfg as Hc'. cbn [obj_at LAY_RawConfig] in Hc'. destruct Hc' as (_ & _ & _ & _ & _ & _ & [_ R32] & _). cbn [fst snd N.to_nat Z.of_N] in R32.
change (2 ^ (8 * 2)) with 65536 in R32.
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot] in Hc.
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hc. rewrite ?ew_ewset_other in Hc by lia.
rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.eqb_neq in Hc.
paj_run_to_tok RUNTO HS HJ4 SHOK RBspan 0x278; [awrR AG fpos F EFA3|]. xsink_stretch HFr HSINK. clear_frames.
prreg HS (11%bv : bv 5) Ra0. prreg HS (12%bv : bv 5) Ra1. prreg HS (13%bv : bv 5) Ra2. prreg HS (10%bv : bv 5) Rs5.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (rn_pow2aX B LAWS 9 0 sgct W3 (ms_regs msX) (ms_mem msX) _ TRAWNEW_STK (spZ regs) (asink_fp pf) ly S W mem md [(2, fpos)] ly3 S3 k eq_refl HJ4);
[ exact Ra0 | exact Ra1 | exact Ra2 | rewrite Rs5; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E38
| clear; lia | clear - Hc Hsg R32; lia | change (2 ^ 0) with 1; clear - Hc R32; lia ] end. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & Kp & -> & HJ5 & HK10 & HK13 & HKlo & HKs1 & HKs2 & Hav5 & Hpr5 & [HFS5 HFD5] & Hrg5).
clear Ra0 Ra1 Ra2 Rs5.
lazymatch type of HSINK with asink_at _ _ (mrestrict _ ?mo) ?mdo _ ?SG =>
assert (HSINK5 : asink_at SEGS K (mrestrict (w_H W3) mem5) md5 pf SG);
[ apply (asink_at_model SEGS K _ mdo); [exact HFS5 | exact HFD5 |]; apply (asink_at_frame SEGS K (mrestrict (w_H W3) mo)); [|exact HSINK];
intros a _; apply (mbyte_of_aview SEGS); apply Hav5
| clear HSINK; rename HSINK5 into HSINK ] end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_stretch_hi HS kk regs5 (mrestrict (w_H W3) mem5) POW_CLOB_A 0x28c HS2;
specialize (HS2 Hrg5 (regions_kept_all Ev (w_H W3) (ms_mem msX) mem5 _ Hav5 Hpr5)) | st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_stretch_hi HS kk regs5 (mrestrict (w_H W3) mem5) POW_CLOB_A 0x28c HS2;
specialize (HS2 Hrg5 (regions_kept_all Ev (w_H W3) (ms_mem msX) mem5 _ Hav5 Hpr5))  end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => assert (E578 : ew Ev 578 = Z_to_bv 64 Kp)
by (rewrite HEv; unfold POW_CLOB_A; cbn [map]; rewrite (ew_havoc_new _ 578 [getr regs5 11%bv; getr regs5 14%bv] 0 (Z_to_bv 64 0) ltac:(cbn; lia)); cbn [nth]; exact HK10) end.
clear HEv.
norm_ss HS. reshok_bx HS 35%nat.
paj_run_tok RUN HS HJ5 SHOK RBspan; [awrR AG fpos F EFA3 |]. xsink_stretch HFr HSINK. clear_frames.
psrr_branch_tok RUN BR HS SHOK RBspan.
+ paj_run_to_tok RUNTO HS HJ5 SHOK RBspan 0x2ac; [awrR AG fpos F EFA3|]. xsink_stretch HFr HSINK. clear_frames.
norm_ss HS.
assert (HKnz : 1 <= Kp <= 8).
{ pose proof Hc0 as Hq. unfold branch_taken in Hq. rewrite bv_eqb_unsigned in Hq. cbn [sv_denot] in Hq. rewrite E578, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hq by lia.
apply negb_true_iff, Z.eqb_neq in Hq. lia. }
xrechunk_pk HS ltac:(lazymatch goal with |- bv_unsigned (sv_denot ?Ev _) mod _ = _ =>
rewrite (denot_rn_flags_nz Ev 578%nat Kp ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E578) HKnz) end;
symmetry; apply (rn_pk_of_K Kp sgct HKlo ltac:(lia) HKs1 HKs2)).
rn_join HS ss_CX 631%nat rn_deads_C.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos res Sg GCT);
[ exact HPRE | exact Hchne | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_EX_havoc; [clear; lia | repeat (apply rn_EX_ewset; [clear; lia|]); split; [repeat (split; [eassumption|]); eassumption | split; [exact E44 | exact E45]]]
| split; [exact HJ5 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | split; [exact Ares | split; [exact HSINK | exact MLE]]]]]]]]
| exact Hsg | exact HSmax | exact HGCT | exact HS ] | st_ok _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos res Sg GCT);
[ exact HPRE | exact Hchne | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_EX_havoc; [clear; lia | repeat (apply rn_EX_ewset; [clear; lia|]); split; [repeat (split; [eassumption|]); eassumption | split; [exact E44 | exact E45]]]
| split; [exact HJ5 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | split; [exact Ares | split; [exact HSINK | exact MLE]]]]]]]]
| exact Hsg | exact HSmax | exact HGCT | exact HS ]  end.
+ paj_run_to_tok RUNTO HS HJ5 SHOK RBspan 0x2ac; [awrR AG fpos F EFA3|]. xsink_stretch HFr HSINK. clear_frames.
norm_ss HS.
assert (HK0 : Kp = 0).
{ pose proof Hc0 as Hq. unfold branch_taken in Hq. rewrite bv_eqb_unsigned in Hq. cbn [sv_denot] in Hq. rewrite E578, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hq by lia.
apply negb_false_iff, Z.eqb_eq in Hq. exact Hq. }
xrechunk_pk HS ltac:(cbn [sv_denot]; rewrite unsigned_lit_small by lia; rewrite (rn_pk_of_K Kp sgct HKlo ltac:(lia) HKs1 HKs2), HK0; reflexivity).
rn_join HS ss_CX 631%nat rn_deads_C.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos res Sg GCT);
[ exact HPRE | exact Hchne | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_EX_havoc; [clear; lia | repeat (apply rn_EX_ewset; [clear; lia|]); split; [repeat (split; [eassumption|]); eassumption | split; [exact E44 | exact E45]]]
| split; [exact HJ5 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | split; [exact Ares | split; [exact HSINK | exact MLE]]]]]]]]
| exact Hsg | exact HSmax | exact HGCT | exact HS ] | st_ok _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos res Sg GCT);
[ exact HPRE | exact Hchne | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_EX_havoc; [clear; lia | repeat (apply rn_EX_ewset; [clear; lia|]); split; [repeat (split; [eassumption|]); eassumption | split; [exact E44 | exact E45]]]
| split; [exact HJ5 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | split; [exact Ares | split; [exact HSINK | exact MLE]]]]]]]]
| exact Hsg | exact HSmax | exact HGCT | exact HS ]  end.
Qed.
End e.
End d.
End b.
