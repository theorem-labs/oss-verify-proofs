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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition RBx : sv := SOff 35 0.
Definition RBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rn_extra (g pgct rattr Wd Hd sgct loops ctx wfn hw uar : Z) : list word :=
map (Z_to_bv 64) [g; pgct; rattr; SB; Wd; Hd; sgct; loops; ctx; wfn; hw; uar].
Definition cfg_region : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 40 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 41 0)); YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0));
YP09.mkChunk 24 (CVal 4 (SOff 34 0)); YP09.mkChunk 28 (CVal 2 (SOff 36 0)); YP09.mkChunk 30 (CVal 2 (SOff 37 0));
YP09.mkChunk 32 (CVal 2 (SOff 38 0)); YP09.mkChunk 34 (CVal 2 (SOff 39 0))].
Definition g_region : YP09.region :=
YP09.mkRegion (Some 32%nat) 0 CGIF_SIZE 0 0
[YP09.mkChunk 56 (CVal 8 (SOff 42 0)); YP09.mkChunk 64 (CVal 8 (SOff 40 0)); YP09.mkChunk 80 (CVal 8 (SLit 0))].
Definition rn_regions0 : smem :=
[ stack_region 192; got_regionP; bcell_regionP 35; uar_got_regionP 43; uar_cell_regionP 43; obj8_region 7 (SOff A_TEXT AF_asan3_cgif_raw_newgif);
cfg_region; g_region ].
Definition rn_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 5); (10%nat, HPTR 3); (32%nat, HPTR 4); (33%nat, mkAF 0 (2^64 - 1) 0);
(34%nat, mkAF 0 (2^32 - 1) 0); (35%nat, mkAF SB SB 0); (36%nat, mkAF 0 65535 0); (37%nat, mkAF 0 65535 0);
(38%nat, mkAF 0 65535 0); (39%nat, mkAF 0 65535 0); (40%nat, mkAF 0 (2^64 - 1) 0);
(41%nat, mkAF 0 (2^64 - 1) 1); (42%nat, mkAF 0 (2^64 - 1) 1); (43%nat, mkAF 0x10000 0x5fb000 2) ].
Definition ss_rn0 : sstate := mkSS AF_asan3_cgif_raw_newgif sr_atoms rn_regions0 None (mkFacts rn_atoms0 [] []).
Definition rn_E0 (regs : bvmap 5 word) (cfgp g : Z) (E0 : env) : Prop :=
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr regs r) /\
ew E0 10 = Z_to_bv 64 cfgp /\ ew E0 32 = Z_to_bv 64 g /\ bv_unsigned (ew E0 2) = spZ regs.
Definition rn_E (E0 E : env) (pgct rattr Wd Hd sgct loops ctx F FL res wfn hw uar : Z) : Prop :=
(forall n, (n < 33)%nat -> ew E n = ew E0 n) /\
ew E 33 = Z_to_bv 64 pgct /\ ew E 34 = Z_to_bv 64 rattr /\ ew E 35 = Z_to_bv 64 SB /\ ew E 36 = Z_to_bv 64 Wd /\
ew E 37 = Z_to_bv 64 Hd /\ ew E 38 = Z_to_bv 64 sgct /\ ew E 39 = Z_to_bv 64 loops /\ ew E 40 = Z_to_bv 64 ctx /\
ew E 516 = Z_to_bv 64 F /\ ew E 528 = Z_to_bv 64 FL /\ ew E 529 = Z_to_bv 64 (SB + F / 8) /\ ew E 534 = Z_to_bv 64 res /\
ew E 41 = Z_to_bv 64 wfn /\ ew E 42 = Z_to_bv 64 hw /\ ew E 43 = Z_to_bv 64 uar /\ img_env VAL A_LIM E.
Definition rn_cfg (B : asyms) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (cid pos cfgp : Z) : Prop :=
In (cid, pos) (frames S) /\ 0 <= cid /\ frame_addr ly cid pos mod 8 = 0 /\
frame_addr ly cid pos <= cfgp /\ cfgp + 40 <= frame_addr ly cid pos + fs_frame_bytes cid /\ cfgp mod 8 = 0 /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF cfgp 40.
Definition rn_now (B : asyms) (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (md : Model) (fpos res : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) (k : Z) : Prop :=
ajournal SEGS B TRAWNEW_STK (spZ regs) [] ly S W mem md [(2, fpos)] ly3 S3 W3 (ms_mem ms3) md3 k /\ k <= 2 /\
frames S3 = (2, fpos) :: frames S /\ Permutation (ablocks B ly3 S3) (ablocks B ly S ++ [(res, 48)]) /\ 4096 <= res /\
aftok [] (ablocks B ly S) (res, 48) /\
(forall blc lyq ownq i, In (res, 48) blc -> 0 <= i < 48 -> awr_byte TRAWNEW_STK (spZ regs) [] (ablocks B ly S) blc lyq ownq (res + i)).
Definition rn_post (B : asyms) (wfn : Z) (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (md : Model) (g pgct rattr Wd Hd sgct loops : Z) : world SEGS -> config -> Prop :=
apost_base SEGS B TRAWNEW_STK [] regs ly S W mem md EV_RAWNEW
(fun ly' S' W' regs' mem' md' => exists res : Z, getr regs' 10 = w64 res /\
((res = 0 /\ Permutation (ablocks B ly' S') (ablocks B ly S)) \/
(res <> 0 /\ sgct <= 256 /\
Permutation (ablocks B ly' S') ((res, RAW_SIZE) :: ablocks B ly S) /\
(forall blc i, In (res, RAW_SIZE) blc -> 0 <= i < RAW_SIZE ->
awr_byte TRAWNEW_STK (spZ regs) [] (ablocks B ly S) blc ly' [] (res + i)) /\
aftok [] (ablocks B ly S) (res, RAW_SIZE) /\
obj_at SEGS (mrestrict (w_H W') mem') res LAY_Raw [wfn; g; pgct; rattr; Wd; Hd; sgct; loops; R_PENDING]))).
Lemma rn_E_havoc : forall E0 E pgct rattr Wd Hd sgct loops ctx F FL res wfn hw uar N vs,
(537 <= N)%nat -> rn_E E0 E pgct rattr Wd Hd sgct loops ctx F FL res wfn hw uar -> rn_E E0 (havoc E N vs) pgct rattr Wd Hd sgct loops ctx F FL res wfn hw uar.
Proof.
intros E0 E pgct rattr Wd Hd sgct loops ctx F FL res wfn hw uar N vs HN (AG & H).
unfold rn_E. rewrite !ew_havoc_old by lia. split; [intros n Hn; rewrite ew_havoc_old by lia; apply AG; exact Hn|].
repeat (lazymatch goal with |- img_env _ _ _ => idtac | _ => destruct H as [? H]; split; [assumption|] end).
apply img_env_havoc_hi; [exact H | unfold A_LIM; lia].
Qed.
Lemma rn_E_ewset : forall E0 E pgct rattr Wd Hd sgct loops ctx F FL res wfn hw uar n w,
(537 <= n)%nat -> rn_E E0 E pgct rattr Wd Hd sgct loops ctx F FL res wfn hw uar -> rn_E E0 (ewset E n w) pgct rattr Wd Hd sgct loops ctx F FL res wfn hw uar.
Proof.
intros E0 E pgct rattr Wd Hd sgct loops ctx F FL res wfn hw uar n w HN (AG & H).
unfold rn_E. rewrite !ew_ewset_other by lia. split; [intros m Hm; rewrite ew_ewset_other by lia; apply AG; exact Hm|].
repeat (lazymatch goal with |- img_env _ _ _ => idtac | _ => destruct H as [? H]; split; [assumption|] end).
apply img_env_ewset_hi; [exact H | unfold A_LIM; lia].
Qed.
Definition rn_from (B : asyms) (wfn hw : Z) (ss : sstate) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cfgp g pgct rattr Wd Hd sgct loops ctx : Z) rest (cid pos : Z)
(E0 E : env) W3 ly3 S3 (ms3 : machine_state) md3 (k fpos res : Z),
afn_pre SEGS B TRAWNEW_STK ly S W regs mem md ch -> ch <> [] -> spZ regs mod 32 = 0 ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
rn_cfg B ly S W mem cid pos cfgp ->
obj_at SEGS (mrestrict (w_H W) mem) cfgp LAY_RawConfig [wfn; g; pgct; rattr; Wd; Hd; sgct; loops] ->
Permutation (ablocks B ly S) ((g, CGIF_SIZE) :: rest) ->
st_nev S + EV_RAWNEW <= EV_MAX ->
rn_E0 regs cfgp g E0 -> rn_E E0 E pgct rattr Wd Hd sgct loops ctx (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) res wfn hw (as_uar_cell B) ->
rn_now B regs ly S W mem md fpos res ly3 S3 W3 ms3 md3 k ->
sgct <= 256 ->
st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) ->
SRr SEGS W3 (mkCfg ms3 md3) (rn_post B wfn regs ly S W mem md g pgct rattr Wd Hd sgct loops).
Section RN.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Variables wfn hw : Z.
Hypothesis Rwfn : 0 <= wfn < 2 ^ 64 /\ wfn mod 2 = 0.
Hypothesis Rhw : 0 <= hw < 2 ^ 64 /\ hw mod 2 = 0.
Hypothesis HGOT7 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 7)) 8 (BASE + AF_asan3_cgif_raw_newgif).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Lemma rn_entry : forall W ly S regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx rest,
afn_pre SEGS B TRAWNEW_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 cfgp ->
afobj SEGS B ly S W mem cfgp 40 ->
obj_at SEGS (mrestrict (w_H W) mem) cfgp LAY_RawConfig [wfn; g; pgct; rattr; Wd; Hd; sgct; loops] ->
Permutation (ablocks B ly S) ((g, CGIF_SIZE) :: rest) ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 56) 8 hw ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 80) 8 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (rn_extra g pgct rattr Wd Hd sgct loops ctx wfn hw (as_uar_cell B)))) ss_rn0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_asan3_cgif_raw_newgif)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx rest HPRE Hal32 HROD H10 HFO Hcfg HPerm Mgw Mgf Rctx Mg80.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TRAWNEW_STK = 16576) by reflexivity.
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in *.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
pose proof Hcfg as Hcfg'. cbn [obj_at LAY_RawConfig] in Hcfg'.
destruct Hcfg' as ([V0 R0] & [V8 R8] & [V16 R16] & [V24 R24] & [V28 R28] & [V30 R30] & [V32 R32] & [V34 R34] & _).
cbn [fst snd N.to_nat Z.of_N] in V0, V8, V16, V24, V28, V30, V32, V34, R0, R8, R16, R24, R28, R30, R32, R34.
change (2 ^ (8 * 8)) with (2 ^ 64) in *. change (2 ^ (8 * 4)) with (2 ^ 32) in *. change (2 ^ (8 * 2)) with 65536 in *.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (rn_extra g pgct rattr Wd Hd sgct loops ctx wfn hw (as_uar_cell B)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 cfgp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EX : forall j, (j < 12)%nat -> ew E (32 + j) = nth j (rn_extra g pgct rattr Wd Hd sgct loops ctx wfn hw (as_uar_cell B)) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37. pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
pose proof (EX 8%nat ltac:(lia)) as E40. pose proof (EX 9%nat ltac:(lia)) as E41. pose proof (EX 10%nat ltac:(lia)) as E42. pose proof (EX 11%nat ltac:(lia)) as E43.
cbn [Nat.add nth rn_extra map] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43. clear EX.
assert (E240 : ew E A_TEXT = Z_to_bv 64 BASE) by (subst E; apply Eimg_img; unfold A_TEXT, A_LIM; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E248 : ew E (A_OBJ 7) = Z_to_bv 64 (VAL (A_OBJ 7))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 7 ltac:(lia)) as Hob7.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12. pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
Local Ltac ck HE M := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | first [exact M | rewrite Z.add_0_r; exact M] ].
unfold ss_rn0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rn_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, obj8_region, cfg_region, g_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 35 0) SB);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 43 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite (VB 43%nat (as_uar_cell B) E43) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
+ rewrite (VB (A_OBJ 7) (VAL (A_OBJ 7)) E248) by (pose proof (pa_val_range (A_OBJ 7)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 7)) 0 8 (SOff A_TEXT AF_asan3_cgif_raw_newgif) (BASE + AF_asan3_cgif_raw_newgif));
[cbn [sv_denot]; rewrite E240, unsigned_lit_small by lia; reflexivity | unfold AF_asan3_cgif_raw_newgif; zside | zside |].
rewrite Z.add_0_r. exact (HGOT7 (w_H W) mem HROD).
+ rewrite (VB 10%nat cfgp E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [ck E41 V0|].
constructor; [ck E32 V8|]. constructor; [ck E33 V16|]. constructor; [ck E34 V24|]. constructor; [ck E36 V28|].
constructor; [ck E37 V30|]. constructor; [ck E38 V32|]. constructor; [ck E39 V34|]. constructor.
+ rewrite (VB 32%nat g E32) by lia. unfold CGIF_SIZE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [ck E42 Mgw|].
constructor; [ck E40 Mgf|].
constructor; [apply (chunk_ok_val SEGS E _ g 80 8 _ 0); [reflexivity | zside | zside | exact Mg80] | constructor].
- apply pairwise_disjoint_of_extents.
unfold rn_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, obj8_region, cfg_region, g_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat cfgp E10), (VB 32%nat g E32), (VB 43%nat (as_uar_cell B) E43) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 7) (VAL (A_OBJ 7)) E248) by (pose proof (pa_val_range (A_OBJ 7)); lia).
cbn [base_val]. rewrite Usp. unfold CGIF_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
assert (Hgf : g + 96 <= cfgp \/ cfgp + 40 <= g).
{ pose proof (sep_block_frame SEGS B LAWS ly S W mem md g CGIF_SIZE cid pos HAR Hing Hfin) as Hbf.
unfold zdisjoint in Hbf. cbn [fst snd] in Hbf. change (req_size CGIF_SIZE) with 96 in Hbf. revert Hbf Hflo Hfhi. clear. intros. lia. }
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hfceil Hfhigh Hfhigh_img Hflo Hfhi Hgf C1 C3 FFS Hstk0 Hob0 Hob1 Hob7 Hob12 Huar Hsep. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption)
| (repeat match goal with H : pa_val (A_OBJ _) + 8 <= _ \/ _ |- _ => clear H | H : as_uar_cell _ + 4 <= _ \/ _ |- _ => clear H end; lia) ].
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok rn_atoms0]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. change (2 ^ 1) with 2. rewrite !Z.pow_0_r, !Z.mod_1_r.
assert (Hc8 : cfgp mod 8 = 0) by exact Hcal.
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hg16 Hfceil Hfhigh Hfhigh_img Hflo Hfhi Hal32 Hc8 R0 R8 R16 R24 R28 R30 R32 R34 Rctx C1 C3 FFS Hstk0 Huar Huar4 Rwfn Rhw. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End RN.
End b.
End a.
