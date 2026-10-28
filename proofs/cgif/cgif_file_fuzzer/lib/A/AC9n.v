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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk AC8a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACbd ACab ACam ACai ACaj ACan ACaf ACae.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j YI0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACah.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC85 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6 ACba AC9z ACa3 ACa4 ACa5 ACa6 ACa7.
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
Lemma range_addressable_zero8 : forall (rd : Z -> option Z) Bs p,
rd (shadow_of_addr Bs p) = Some 0 -> p mod 8 = 0 -> range_addressable rd Bs p 8.
Proof.
intros rd Bs p Hz Hp. apply zero_shadow_range; [exact Hp | reflexivity |].
intros i Hi. change (8 / 8) with 1 in Hi. replace i with 0 by lia. rewrite Z.add_0_r. exact Hz.
Qed.
Section f.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Hypothesis TLF : PALibF B.
Hypothesis HGOT9 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 9)) 8 (BASE + AF_asan3_cgif_raw_addframe).
Variable CTX : list (list Z).
Hypothesis HDEEP : forall c, In c CTX -> (2 <= length c)%nat.
Variable KS : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B KS.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Variable XN : xnums.
Hypothesis HXM : forall N idl, 1 <= N <= 100000000 -> 2 <= idl <= 256 -> mo_malloc MT N + xm_lzw XN N idl + 2 * mo_free MT <= xm_rawadd XN N.
Hypothesis HXN : forall N idl, 1 <= N <= 100000000 -> 2 <= idl <= 256 -> mo_malloc MT N + xn_lzw XN N idl + 2 * mo_free MT <= xn_rawadd XN N.
Hypothesis HXMN : forall N idl, 1 <= N <= 100000000 -> 2 <= idl <= 256 -> 0 <= xn_lzw XN N idl <= xm_lzw XN N idl.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Lemma ra_CX_aux : ra_fromX0 KS MT XN B CTX ss_DX (INV_DX MT B) -> ra_fromX0 KS MT XN B CTX ss_CX (INV_CX MT B).
Proof.
intros RD. ra_preludeX.
pose proof HINV as ((Hk3 & Eab3) & HXC & MLE0).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpf_in).
ra_blocks3X Hraw3 Hing3 Hpf3. fold F in HdFR, HdFG.
relowC HS AG E10 E11 E32 E10n E11n E32n.
reshok_bx HS 40%nat.
paj_run_tok RUN HS HJ3 SHOK RABspan; [awrRA AG fpos F EFA3 |]. clear_frames.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRfs; cbn [ms_mem restrict] in HRfs;
lazymatch type of HRfs with region_ok _ _ _ (YP09.mkRegion (Some 529%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi 6 1%N (SLit 0) 0 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V6;
pose proof (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi 7 1%N (SLit 2) 2 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V7 end;
clear HRfs;
pose proof (aview_of_val_mem1 SEGS _ _ _ _ V6 ltac:(lia)) as Hsh6;
pose proof (aview_of_val_mem1 SEGS _ _ _ _ V7 ltac:(lia)) as Hsh7;
assert (HRA3 : range_addressable (aview SEGS (w_H W3) (ms_mem msX)) SHADOW_OFF (F + 49) 9);
[ eapply (range_addressable_sub _ _ (F + 48) 10); [|lia|lia];
change 10 with (8 + 2); apply range_addressable_app; [lia| |];
[ apply range_addressable_zero8; [|rewrite HFq; replace (32 * (F / 32) + 48) with ((4 * (F / 32) + 6) * 8) by lia; apply Z_mod_mult];
rewrite <- Hsh6; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 48) with ((4 * (F / 32) + 6) * 8) by lia; rewrite Z.div_mul by lia; lia
| eapply (range_addressable_partial _ SHADOW_OFF (F + 48 + 8) 2); [|rewrite HFq; replace (32 * (F / 32) + 48 + 8) with ((4 * (F / 32) + 7) * 8) by lia; apply Z_mod_mult|lia];
rewrite <- Hsh7; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 48 + 8) with ((4 * (F / 32) + 7) * 8) by lia; rewrite Z.div_mul by lia; lia ]
| ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRfs; cbn [ms_mem restrict] in HRfs;
lazymatch type of HRfs with region_ok _ _ _ (YP09.mkRegion (Some 529%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi 6 1%N (SLit 0) 0 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V6;
pose proof (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi 7 1%N (SLit 2) 2 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V7 end;
clear HRfs;
pose proof (aview_of_val_mem1 SEGS _ _ _ _ V6 ltac:(lia)) as Hsh6;
pose proof (aview_of_val_mem1 SEGS _ _ _ _ V7 ltac:(lia)) as Hsh7;
assert (HRA3 : range_addressable (aview SEGS (w_H W3) (ms_mem msX)) SHADOW_OFF (F + 49) 9);
[ eapply (range_addressable_sub _ _ (F + 48) 10); [|lia|lia];
change 10 with (8 + 2); apply range_addressable_app; [lia| |];
[ apply range_addressable_zero8; [|rewrite HFq; replace (32 * (F / 32) + 48) with ((4 * (F / 32) + 6) * 8) by lia; apply Z_mod_mult];
rewrite <- Hsh6; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 48) with ((4 * (F / 32) + 6) * 8) by lia; rewrite Z.div_mul by lia; lia
| eapply (range_addressable_partial _ SHADOW_OFF (F + 48 + 8) 2); [|rewrite HFq; replace (32 * (F / 32) + 48 + 8) with ((4 * (F / 32) + 7) * 8) by lia; apply Z_mod_mult|lia];
rewrite <- Hsh7; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 48 + 8) with ((4 * (F / 32) + 7) * 8) by lia; rewrite Z.div_mul by lia; lia ]
| ]  end.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
idtac.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconstsA HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA AS_asan_memset) AMEMSET _ (ms_regs msX) (ms_mem msX) TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [(1, fpos)]
ly3 S3 _ _ (F + 49) 0 9 (-320) (Z_to_bv 64 (BASE + 0x8dc)) HJ3) end.
- rewrite Ra0. evalE AG.
- rewrite Ra1. reflexivity.
- rewrite Ra2. reflexivity.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split; [| unfold ESTACK; lia]. right. right. right. exists 1, fpos. split; [left; reflexivity|]. left.
unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. rewrite EFA3. fold F. lia.
- apply amem_range_high; zone_lia.
- exact HRA3.
- intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 _ _ _ 1 fpos (F + 49) 9 (proj1 HJ3) Hfin3);
[rewrite EFA3; fold F; lia | rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; lia | lia].
- exact I. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp V6 V7 Hsh6 Hsh7 HRA3.
aconstsA HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ4) Hfin3) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4.
change (128 / 8) with 16 in HFSpres4. rewrite !EFA3 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
reseat HS HJ4 HP4 [0; 1; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]%nat AG
ltac:(idtac; first [ keptIA Hfr4 Hpres4 AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
assert (Z49 : val_mem SEGS (mrestrict (w_H W3) mem4) (F + 49) 8 0).
{ apply val_mem_zero8. intros i Hi. replace (F + 49 + i) with (F + 49 + i) by lia. rewrite (Heff i ltac:(lia)). reflexivity. }
assert (Z57 : val_mem SEGS (mrestrict (w_H W3) mem4) (F + 57) 1 0).
{ intros j Hj. destruct j; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
destruct (aview_byte SEGS (w_H W3) mem4 (F + 57) 0 ltac:(replace (F + 57) with (F + 49 + 8) by lia; rewrite (Heff 8 ltac:(lia)); reflexivity)) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 49 58 49 58
[YP09.mkChunk 49 (CVal 8 (SLit 0)); YP09.mkChunk 57 (CVal 1 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres4 (F + o) ltac:(lia)))
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ F 49 8 _ 0); [reflexivity | zside | zside | exact Z49]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ F 57 1 _ 0); [reflexivity | zside | zside | exact Z57]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; unbox; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 49 58 49 58
[YP09.mkChunk 49 (CVal 8 (SLit 0)); YP09.mkChunk 57 (CVal 1 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres4 (F + o) ltac:(lia)))
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ F 49 8 _ 0); [reflexivity | zside | zside | exact Z49]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ F 57 1 _ 0); [reflexivity | zside | zside | exact Z57]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; unbox; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS. relowC HS AG E10 E11 E32 E10n E11n E32n. reshok_bx HS 40%nat. clear_frames.
paj_run_tok RUN HS HJ4 SHOK RABspan; [awrRA AG fpos F EFA3 |]. clear_frames.
psrr_branch_tok RUN BR HS SHOK RABspan.
-
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E49, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.eqb_eq in Hc.
paj_run_to_tok RUNTO HS HJ4 SHOK RABspan 0x954.
all: try (obl_blk HJ4 E10n E40 Hraw3). all: try (oblFAX HJ4 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
1: awrRA AG fpos F EFA3.
clear_frames.
prreg HS (12%bv : bv 5) Qa2. rewrite E37 in Qa2.
prreg HS (13%bv : bv 5) Qa3.
rebaseE HS AG HEv. clear HEv.
slot_val HS (Some 2%nat) (-320) (-264) (Z_to_bv 64 0) ltac:(reflexivity) Qs5.
ra_join_slot HS ss_DX 659%nat ra_deads_D (Some 2%nat) (-320) (-264)
ltac:(idtac;
ra_join_val HS 659%nat 1%nat Qa2 EnC;
ra_join_val HS 659%nat 2%nat Qa3 EFL;
ra_join_val HS 659%nat 3%nat Qs5 EK1;
ra_join_fact HS 660%nat (mkAF 0 256 0) ltac:(rewrite EnC, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - Hsg Rsgct; lia);
ra_join_fact HS 662%nat (mkAF 0 8 0) ltac:(rewrite EK1, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear; lia)).
ra_handX RD HS.
split; [| split; [exact HXC | split; [| exact MLE0]]].
{ split; [exact Hk3|]. split; [exact Eab3|]. exists 0. split; [exact EK1|]. split; [lia|]. intros Hne. exfalso. apply Hne. exact Hc. }
unfold rx_pkl, rx_nc. cbn [c_slct c_sgct]. rewrite Hc, Z.eqb_refl. cbn [negb]. split; [split; [exact EFL | intros Hne; exfalso; apply Hne; reflexivity] | exact EnC].
-
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E49, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.eqb_neq in Hc.
fact_of HS 49%nat F49. rewrite E49, unsigned_lit_small in F49 by lia.
paj_run_to_tok RUNTO HS HJ4 SHOK RABspan 0x8f8; [awrRA AG fpos F EFA3|]. clear_frames.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (23%bv : bv 5) Ra4.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (ra_pow2a B LAWS 9 0 slct W3 (ms_regs msX) (ms_mem msX) _ TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [(1, fpos)] ly3 S3 k eq_refl HJ4);
[ exact Ra0 | exact Ra1 | rewrite Ra4; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E49
| clear; lia | clear - Hc Rslct F49; lia | change (2 ^ 0) with 1; clear - Hc Rslct; lia ] end. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & K & -> & HJ5 & HK12 & HK10 & HK13 & HKlo & HKs1 & HKs2 & Hav5 & Hpr5 & Hrg5).
clear Ra0 Ra1 Ra4.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_stretch_hi HS kk regs5 (mrestrict (w_H W3) mem5) POW_CLOB_RA 0x908 HS2;
specialize (HS2 Hrg5 (regions_kept_all Ev (w_H W3) (ms_mem msX) mem5 _ Hav5 Hpr5));
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS; rebaseE HS AG HEv;
let kk1 := eval vm_compute in (kk + 1)%nat in
lazymatch type of HS with st_ok_pi _ _ ?Ev2 _ _ =>
assert (EKa : ew Ev2 kk1 = Z_to_bv 64 K) by (rewrite HEv; unfold POW_CLOB_RA; cbn [map]; change kk1 with (kk + 1)%nat; rewrite Nat.add_1_r;
rewrite (ew_havoc_new _ kk _ 1 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact HK12) end;
clear HEv end.
norm_ss HS. relowC HS AG E10 E11 E32 E10n E11n E32n. reshok_bx HS 40%nat.
paj_run_to_tok RUNTO HS HJ5 SHOK RABspan 0x954.
all: try (oblFAX HJ5 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
1: awrRA AG fpos F EFA3.
clear_frames.
prreg HS (12%bv : bv 5) Qa2. rewrite E49 in Qa2.
prreg HS (13%bv : bv 5) Qa3. rewrite (denot_ra_flagsL _ _ K EKa HKlo) in Qa3.
rebaseE HS AG HEv. clear HEv.
slot_val HS (Some 2%nat) (-320) (-264) (Z_to_bv 64 (Z.max K 1)) ltac:(exact (denot_K1 _ _ K EKa ltac:(clear - HKlo; lia))) Qs5.
ra_join_slot HS ss_DX 659%nat ra_deads_D (Some 2%nat) (-320) (-264)
ltac:(idtac;
ra_join_val HS 659%nat 1%nat Qa2 EnC;
ra_join_val HS 659%nat 2%nat Qa3 EFL;
ra_join_val HS 659%nat 3%nat Qs5 EK1;
ra_join_fact HS 660%nat (mkAF 0 256 0) ltac:(rewrite EnC, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - F49; lia);
ra_join_fact HS 662%nat (mkAF 0 8 0) ltac:(rewrite EK1, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - HKlo; lia)).
ra_handX RD HS.
split; [| split; [exact HXC | split; [| exact MLE0]]].
{ split; [exact Hk3|]. split; [exact Eab3|]. exists (Z.max K 1). split; [exact EK1|]. split; [clear - HKlo; lia|].
intros _. clear - HKs1 HKlo. destruct (Z_le_gt_dec K 0) as [Hk0 | Hk0].
+ replace (2 ^ K) with 1 in HKs1 by (replace K with 0 by lia; reflexivity).
replace (Z.max K 1) with 1 by lia. change (2 ^ 1) with 2. lia.
+ replace (Z.max K 1) with K by lia. lia. }
pose proof (ra_pal_pow_of_loop K slct HKlo HKs1 HKs2) as HPP.
unfold rx_pkl, rx_nc. cbn [c_slct c_sgct]. replace (slct =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hc). cbn [negb].
split; [| exact EnC]. split; [rewrite EFL, HPP, Z.max_comm; reflexivity | intros _; rewrite EK1, HPP; reflexivity].
Qed.
Lemma ra_CX : ra_fromX0 KS MT XN B CTX ss_DX (INV_DX MT B) -> ra_fromX0 KS MT XN B CTX ss_CX (INV_CX MT B).
Proof. exact ra_CX_aux. Qed.
End f.
End e.
End d.
