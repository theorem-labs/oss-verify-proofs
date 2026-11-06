(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP0d YP0c YI0w YI0x YC4a.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YC80 YC1f YC5d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import APgBase APgCSpec.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition SB : Z := 0x7fff8000.
Definition KBx : sv := SOff 39 0.
Definition KBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition kp_region : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 40 0 40
[YP09.mkChunk 0 (CVal 4 (SOff 32 0)); YP09.mkChunk 4 (CVal 4 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0));
YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 8 (SOff 36 0)); YP09.mkChunk 32 (CVal 4 (SOff 37 0));
YP09.mkChunk 36 (CVal 4 (SOff 38 0))].
Definition step_regions : smem := [ stack_region 16; got_regionP; bcell_regionP 39; kp_region ].
Definition step_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 3);
(32%nat, mkAF 0 4294967295 0); (33%nat, mkAF 0 4294967295 0); (37%nat, mkAF 0 4294967295 0); (38%nat, mkAF 0 4294967295 0);
(39%nat, mkAF SB SB 0) ] [] [].
Definition ss_step : sstate := mkSS AF_asan_reac_knock_step sr_atoms step_regions None step_facts.
Definition step_SH : list shent := [ mkSHE 10 0 40 ].
Definition step_extra (st p1 opened due heard g p2 : Z) : list word :=
map (Z_to_bv 64) [st; p1; opened; due; heard; g; p2; SB].
Definition kzone (sp kp a : Z) : Prop := sp - 16 <= a < sp \/ kp <= a < kp + 40.
Ltac kp_idx rs :=
lazymatch rs with
| cons (YP09.mkRegion (Some 10%nat) _ _ _ _ _) _ => constr:(0%nat)
| cons _ ?t => let i := kp_idx t in constr:(S i)
end.
Lemma U_sx32_eqb : forall E n s c, ew E n = Z_to_bv 64 s -> 0 <= s < 2 ^ 32 -> 0 <= c < 2 ^ 31 ->
(U E (SExt true 32 (SOff n 0)) =? U E (SLit c)) = (s =? c).
Proof.
intros E n s c Hn Hs Hc. rewrite U_SExt. cbv iota beta. rewrite (U_atom E n s Hn) by lia. rewrite U_lit by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small s) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
destruct (Z.ltb_spec s (2 ^ 31)).
- rewrite (Z.mod_small (s + 2 ^ 31)) by lia. replace (s + 2 ^ 31 - 2 ^ 31) with s by lia. rewrite Z.mod_small by lia. reflexivity.
- replace (s + 2 ^ 31) with ((s - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
rewrite (Z.mod_small (s - 2 ^ 31)) by lia.
replace (s - 2 ^ 31 - 2 ^ 31) with ((s + (2 ^ 64 - 2 ^ 32)) + (-1) * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
destruct (Z.eqb_spec (s + (2 ^ 64 - 2 ^ 32)) c); destruct (Z.eqb_spec s c); first [reflexivity | lia].
Qed.
Lemma U_subx : forall E n m x y, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff n 0) (SMd M_MUL (SOff m 0) (SLit (-1)))) = (x - y) mod 2 ^ 64.
Proof.
intros E n m x y Hn Hm Hx Hy. rewrite U_SAlu, U_SMd, (U_atom E n x Hn Hx), (U_atom E m y Hm Hy), U_SLit.
cbn [zalu_raw zmd_raw]. unfold zcanon, M64. change ((-1) mod 2 ^ 64) with 18446744073709551615.
rewrite Z.add_mod_idemp_r by lia. replace (x + y * 18446744073709551615) with ((x - y) + y * 2 ^ 64) by lia.
apply Z_mod_plus_full.
Qed.
Lemma U_offx : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> U E (SOff n c) = (x + c) mod 2 ^ 64.
Proof. intros E n x c Hn Hx. rewrite U_SOff, Hn, unsigned_lit_small by lia. reflexivity. Qed.
Lemma same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg knock_asan_listing}.
#[local] Notation SEGS := (@pa_segs _ knock_asan_listing PI).
#[local] Notation VAL := (@pa_val _ knock_asan_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ knock_asan_listing PI).
#[local] Notation BASE := (@pa_val _ knock_asan_listing PI A_TEXT).
Definition EK (regs : bvmap 5 word) (st p1 opened due heard g p2 : Z) : env :=
Eimg (Ereg regs (step_extra st p1 opened due heard g p2)).
Lemma kept_step : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte) sp kp,
(forall a, 0 <= a < 2 ^ 64 -> ~ kzone sp kp a -> aview SEGS H m1 a = aview SEGS H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> kzone sp kp a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ kzone sp kp a -> aview SEGS H m2 a = aview SEGS H m0 a.
Proof.
intros E rs H m0 m1 m2 sp kp HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
Lemma st_ok_pi_region : forall E ss ms i r, st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. pose proof (st_ok_mem_ok SEGS E _ ms HS) as (_ & HF & _).
eapply Forall_forall; [exact HF|]. exact (nth_error_In _ _ Hi).
Qed.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_knock_asan) (PI := PI).
Lemma area_in_img : forall ly S W mem md x n, AR SEGS B ly S W mem md -> In (x, n) (asyms_areas B) ->
fst (ly_img ly) <= x /\ x + n <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S W mem md x n (M & _) Hin.
pose proof (proj1 (Forall_forall _ _) (aso_cover _ (am_syms _ _ _ _ M)) _ Hin) as X.
apply Exists_exists in X as (r' & Hr' & [S1 S2]).
pose proof (proj1 (Forall_forall _ _) (am_static_img _ _ _ _ M) r' ltac:(apply in_app_iff; left; exact Hr')) as [I1 I2].
cbn [fst snd] in *. lia.
Qed.
Lemma frame_not_img : forall ly S W mem md cid pos a, AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> ~ in_zr a (ly_img ly).
Proof.
intros ly S W mem md cid pos a (M & _) Hin Ha. apply (client_byte_not_img B ly S _ a M).
right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma area_frame_disj : forall ly S W mem md x n cid pos p len, AR SEGS B ly S W mem md -> In (x, n) (asyms_areas B) ->
In (cid, pos) (frames S) -> frame_addr ly cid pos <= p -> p + len <= frame_addr ly cid pos + fs_frame_bytes cid ->
0 < n -> 0 < len -> x + n <= p \/ p + len <= x.
Proof.
intros ly S W mem md x n cid pos p len HAR Hin Hf Hp1 Hp2 Hn Hl.
pose proof (area_in_img ly S W mem md x n HAR Hin) as [I1 I2].
destruct (Z_le_gt_dec (x + n) p) as [|H1]; [left; lia|].
destruct (Z_le_gt_dec (p + len) x) as [|H2]; [right; lia|]. exfalso.
apply (frame_not_img ly S W mem md cid pos (Z.max x p) HAR Hf); [lia|]. unfold in_zr. lia.
Qed.
Lemma step_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (kp : Z) (cid pos : Z)
(st p1 opened due heard g p2 : Z),
as_got_shadow B = VAL (A_OBJ 1) -> as_shadow_cell B = VAL (A_OBJ 7) ->
VAL (A_OBJ 1) + 8 <= VAL (A_OBJ 7) \/ VAL (A_OBJ 7) + 8 <= VAL (A_OBJ 1) ->
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 kp ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - T_step_STK -> spZ regs <= sp0 ->
In (cid, pos) own -> frame_addr lyc cid pos <= kp -> kp + 40 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
kp mod 8 = 0 ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF kp 40 ->
obj_at SEGS (mrestrict (w_H W) memc) kp LAY_Knock [st; p1; opened; due; heard; g; p2] ->
st_ok_pi SEGS VAL (EK regs st p1 opened due heard g p2) ss_step
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_asan_reac_knock_step)) memc (seg_rom SEGS)))
/\ sh_ok SEGS KBx step_SH (EK regs st p1 opened due heard g p2) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs kp cid pos st p1 opened due heard g p2
HBgot HBcell Hgc HJ H10 Hal16 Hwlo Hwhi Hown Hkp1 Hkp2 Hkp8 RA HOBJ.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold T_step_STK in Hwlo.
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hfin) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & HFpres & _).
pose proof (obj_at_nth SEGS _ _ _ _ 0 _ _ HOBJ eq_refl eq_refl) as [Mst Rst].
pose proof (obj_at_nth SEGS _ _ _ _ 1 _ _ HOBJ eq_refl eq_refl) as [Mp1 Rp1].
pose proof (obj_at_nth SEGS _ _ _ _ 2 _ _ HOBJ eq_refl eq_refl) as [Mop Rop].
pose proof (obj_at_nth SEGS _ _ _ _ 3 _ _ HOBJ eq_refl eq_refl) as [Mdue Rdue].
pose proof (obj_at_nth SEGS _ _ _ _ 4 _ _ HOBJ eq_refl eq_refl) as [Mhd Rhd].
pose proof (obj_at_nth SEGS _ _ _ _ 5 _ _ HOBJ eq_refl eq_refl) as [Mg Rg].
pose proof (obj_at_nth SEGS _ _ _ _ 6 _ _ HOBJ eq_refl eq_refl) as [Mp2 Rp2].
cbn [fst snd Z.of_N] in Mst, Rst, Mp1, Rp1, Mop, Rop, Mdue, Rdue, Mhd, Rhd, Mg, Rg, Mp2, Rp2.
change (2 ^ (8 * 8)) with (2 ^ 64) in *. change (2 ^ (8 * 4)) with 4294967296 in *.
pose proof (asyms_area_bound B (as_got_shadow B, 8) (am_syms _ _ _ _ (proj1 HAR)) ltac:(cbn; tauto)) as [Gb1 Gb2].
pose proof (asyms_area_bound B (as_shadow_cell B, 8) (am_syms _ _ _ _ (proj1 HAR)) ltac:(cbn; tauto)) as [Cb1 Cb2].
pose proof (area_frame_disj _ _ _ _ _ (as_got_shadow B) 8 cid pos kp 40 HAR ltac:(cbn; tauto) Hfin Hkp1 Hkp2 ltac:(lia) ltac:(lia)) as Dg.
pose proof (area_frame_disj _ _ _ _ _ (as_shadow_cell B) 8 cid pos kp 40 HAR ltac:(cbn; tauto) Hfin Hkp1 Hkp2 ltac:(lia) ltac:(lia)) as Dc.
cbn [fst snd] in Gb1, Gb2, Cb1, Cb2. rewrite HBgot in Gb1, Gb2, Dg. rewrite HBcell in Cb1, Cb2, Dc. unfold kImgEnd in Gb2, Cb2.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := EK regs st p1 opened due heard g p2).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (step_extra st p1 opened due heard g p2)) n)
by (intros n Hn; subst E; unfold EK; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 kp) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 st) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 p1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 opened) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 due) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 heard) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 g) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 p2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (Eg : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EK; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ec : ew E (A_OBJ 7) = Z_to_bv 64 (VAL (A_OBJ 7))) by (subst E; unfold EK; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_step. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold step_regions, stack_region, got_regionP, bcell_regionP, kp_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eg) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 7) 0) (VAL (A_OBJ 7)));
[cbn [sv_denot]; rewrite Ec, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
* rewrite (VB (A_OBJ 7) (VAL (A_OBJ 7)) Ec) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 7)) 0 8 (SOff 39 0) SB);
[cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
* rewrite (VB 10%nat kp E10) by lia. split; [lia|]. split; [lia|].
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (kp + o) ltac:(lia)))|].
repeat (apply Forall_cons; [|]); [..|apply Forall_nil].
-- apply (chunk_ok_val SEGS E _ kp 0 4 _ st); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mst].
-- apply (chunk_ok_val SEGS E _ kp 4 4 _ p1); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mp1].
-- apply (chunk_ok_val SEGS E _ kp 8 8 _ opened); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mop].
-- apply (chunk_ok_val SEGS E _ kp 16 8 _ due); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mdue].
-- apply (chunk_ok_val SEGS E _ kp 24 8 _ heard); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mhd].
-- apply (chunk_ok_val SEGS E _ kp 32 4 _ g); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mg].
-- apply (chunk_ok_val SEGS E _ kp 36 4 _ p2); [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mp2].
+ apply pairwise_disjoint_of_extents. unfold step_regions, stack_region, got_regionP, bcell_regionP, kp_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 10%nat kp E10) by lia. rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eg) by lia. rewrite (VB (A_OBJ 7) (VAL (A_OBJ 7)) Ec) by lia.
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [step_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E37, E38, E39, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
unfold SB. repeat split; lia.
- unfold sh_ok, step_SH. constructor; [|constructor].
apply shent_ok_of_range with (a := kp) (n := 40) (p := kp); [exact RA | | | lia | lia |].
+ unfold U, KBx. cbn [sv_denot]. rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. unfold SHADOW_OFF. lia.
Qed.
Lemma step_kept_post : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (kp cid pos : Z)
(mem2 : word -> option byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
sp0 - STK <= spZ regs - T_step_STK -> spZ regs <= sp0 ->
In (cid, pos) own -> frame_addr lyc cid pos <= kp -> kp + 40 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
(forall a, 0 <= a < 2 ^ 64 -> ~ kzone (spZ regs) kp a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - T_step_STK <= a < spZ regs) -> ~ (kp <= a < kp + 40) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
aview SEGS (w_H W) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
(forall c p a, In (c, p) (frames Sc) ->
(in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) ->
~ (kp <= a < kp + 40) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) /\
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
~ (as_errno B <= a < as_errno B + 4) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs kp cid pos mem2 HJ Hwlo Hwhi Hown Hkp1 Hkp2 KE.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hfin) as (HF4096 & HFceil & HFapp).
unfold T_step_STK in *. unfold kzone in KE.
split; [|split; [|split]].
- intros a Ha Hn1 Hn2. apply KE; lia.
- intros b m i Hb Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & Hb4096 & Hbceil & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m cid pos HAR Hb Hfin) as D. unfold zdisjoint in D. cbn [fst snd] in D.
apply KE; lia.
- intros c p a Hcp Ha Hn. destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c p HAR Hcp) as (Hc4096 & Hcceil & _).
pose proof (fs_frame_bytes_nonneg c) as Hfb.
assert (Q1 : frame_addr lyc c p / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (Q2 : fs_frame_bytes c / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (Q3 : 0 <= frame_addr lyc c p / 8) by (apply Z.div_pos; lia).
assert (Q4 : 0 <= fs_frame_bytes c / 8) by (apply Z.div_pos; lia).
destruct Ha as [Ha|Ha]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Ha; cbn [fst snd] in Ha; apply KE; lia.
- intros a Himg _ _. pose proof (pa_img_range a Himg) as [I1 I2]. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in I1, I2. apply KE; [lia|].
intros [Hz|Hz]; [lia|].
destruct HAR as (M & LG & HR). pose proof (pa_img_cover lyc Sc mdc LG) as [J1 J2]. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in J1, J2.
apply (frame_not_img lyc Sc W memc mdc cid pos a (conj M (conj LG HR)) Hfin); [lia|]. unfold in_zr. lia.
Qed.
(* Proof speed (common.md Proof-speed (2)): the walk below closes each write-range side goal with lia over the whole
   walk context. Its disjunctions and mod facts are hidden once before the walk, and each `first` tries the cases that
   succeed before `exfalso; lia`, whose failures cost the most (the AU twin's order). *)
Definition rs_hold (A : Prop) : Prop := A.
Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => apply rs_hide in H
  | H : _ mod _ = _ |- _ => apply rs_hide in H end.
Lemma pb_knock_step_core :
as_got_shadow B = VAL (A_OBJ 1) -> as_shadow_cell B = VAL (A_OBJ 7) ->
VAL (A_OBJ 1) + 8 <= VAL (A_OBJ 7) \/ VAL (A_OBJ 7) + 8 <= VAL (A_OBJ 1) ->
tknock_step_specX SEGS B MT (BASE + AF_asan_reac_knock_step).
Proof.
intros HBgot HBcell Hgc. unfold tknock_step_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs kp now cid pos ch st p1 opened due heard g p2
HJ Hra Hra4 Hgp Htp H10 H11 Hnow Hch Hal16 Hwlo Hwhi Hown Hcid Hfal Hkp1 Hkp2 Hkp8 Hkp0 Hkpsp HAF HOBJ Hev.
destruct HAF as (_ & _ & RA).
destruct (step_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs kp cid pos st p1 opened due heard g p2
HBgot HBcell Hgc HJ H10 Hal16 Hwlo Hwhi Hown Hkp1 Hkp2 Hkp8 RA HOBJ) as [HS SHOK].
pose proof (fun m2 => step_kept_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs kp cid pos m2
HJ Hwlo Hwhi Hown Hkp1 Hkp2) as Pkept.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold T_step_STK in Hwlo.
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hfin) as (HF4096 & HFceil & HFapp).
pose proof (obj_at_nth SEGS _ _ _ _ 0 _ _ HOBJ eq_refl eq_refl) as [_ Rst].
pose proof (obj_at_nth SEGS _ _ _ _ 1 _ _ HOBJ eq_refl eq_refl) as [_ Rp1].
pose proof (obj_at_nth SEGS _ _ _ _ 2 _ _ HOBJ eq_refl eq_refl) as [_ Rop].
pose proof (obj_at_nth SEGS _ _ _ _ 3 _ _ HOBJ eq_refl eq_refl) as [_ Rdue].
pose proof (obj_at_nth SEGS _ _ _ _ 4 _ _ HOBJ eq_refl eq_refl) as [_ Rhd].
pose proof (obj_at_nth SEGS _ _ _ _ 5 _ _ HOBJ eq_refl eq_refl) as [_ Rg].
pose proof (obj_at_nth SEGS _ _ _ _ 6 _ _ HOBJ eq_refl eq_refl) as [_ Rp2].
cbn [fst snd Z.of_N] in Rst, Rp1, Rop, Rdue, Rhd, Rg, Rp2.
change (2 ^ (8 * 8)) with (2 ^ 64) in *. change (2 ^ (8 * 4)) with 4294967296 in *.
remember (EK regs st p1 opened due heard g p2) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EK; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (step_extra st p1 opened due heard g p2)) n)
by (intros n Hn; subst E; unfold EK; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 kp) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 now) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 st) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 p1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 opened) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 due) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 heard) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 g) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 p2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (HAE : env_agree 32 (Ereg regs (step_extra st p1 opened due heard g p2)) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (B10 : bv_unsigned (ew E 10) = kp) by (rewrite E10; apply unsigned_lit_small; lia).
assert (Ust0 : (U E (SExt true 32 (SOff 32 0)) =? U E (SLit 0)) = (st =? 0)) by (apply U_sx32_eqb; [exact E32 | lia | lia]).
assert (Ust2 : (U E (SExt true 32 (SOff 32 0)) =? U E (SLit 2)) = (st =? 2)) by (apply U_sx32_eqb; [exact E32 | lia | lia]).
assert (Unow : U E (SOff 11 0) = now) by (apply U_atom; [exact E11 | lia]).
assert (Udue : U E (SOff 35 0) = due) by (apply U_atom; [exact E35 | lia]).
assert (Uhd : U E (SOff 36 0) = heard) by (apply U_atom; [exact E36 | lia]).
assert (Uhdl : U E (SOff 36 500000000) = (heard + 500000000) mod 2 ^ 64) by (apply U_offx; [exact E36 | lia]).
assert (Udiff : U E (SAlu ALU_ADD (SOff 11 0) (SMd M_MUL (SOff 36 0) (SLit (-1)))) = (now - heard) mod 2 ^ 64)
by (apply U_subx; [exact E11 | exact E36 | lia | lia]).
assert (Ulns : U E (SLit 500000000) = 500000000) by (apply U_lit; lia).
clear HE EL.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ kzone (spZ regs) kp a -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a)
by (intros; reflexivity).
rs_hide_all.
unfold cfg_at. change (w64 (BASE + AF_asan_reac_knock_step)) with (Z_to_bv 64 (BASE + AF_asan_reac_knock_step)).
let kawr := idtac;
unfold awr_ok, in_wrange;
let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb);
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; unfold awr_byte, in_frames;
first [ rewrite B2 in Hb; left; lia
| rewrite B10 in Hb; right; right; right; exists cid, pos; split; [exact Hown | left; unfold in_zr; cbn [fst snd]; lia]
| exfalso; lia ]
| ]);
(destruct Hr) in
let kwr := idtac;
unfold in_wrange;
let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb);
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; unfold kzone;
first [ rewrite B2 in Hb; left; lia | rewrite B10 in Hb; right; lia | exfalso; lia ]
| ]);
(destruct Hr) in
let kkeep := idtac;
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, _ -> ~ kzone _ _ a -> _ |- _ =>
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (kept_step _ _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by kwr end;
specialize (KS KW); clear KW KE HFr; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end in
let khc H := idtac;
rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in H;
rewrite ?Ust0, ?Ust2, ?Udiff, ?Uhdl, ?Unow, ?Udue, ?Uhd, ?Ulns in H;
first [ apply (proj1 (negb_true_iff _)) in H | apply (proj1 (negb_false_iff _)) in H | idtac ];
first [ apply (proj1 (Z.eqb_eq _ _)) in H | apply (proj1 (Z.eqb_neq _ _)) in H
| apply (proj1 (Z.ltb_lt _ _)) in H | apply (proj1 (Z.ltb_ge _ _)) in H | idtac ] in
let kdenot := idtac;
first [ reflexivity
| rewrite denot_lit_U; f_equal; rewrite U_SOff; rewrite ?E32, ?E33, ?E34, ?E35, ?E36, ?E37, ?E38;
rewrite unsigned_lit_small by lia; unfold zcanon, M64; rewrite ?Z.add_0_r; first [reflexivity | apply Z.mod_small; lia] ] in
let kfield := idtac;
lazymatch goal with |- val_mem _ ?m (?b + ?off) (N.to_nat ?w) ?v =>
lazymatch goal with Hc : YP09.chunk_ok _ _ _ _ (YP09.mkChunk off (CVal _ ?e)) |- _ =>
apply (val_of_chunk_ok SEGS _ m b off w e v Hc); [kdenot | zside | zside]
end end in
let rec kio := idtac; first [ apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio ] in
let leaf := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
KE : forall a, _ -> ~ kzone _ _ a -> _ |- _ =>
let R10 := fresh "R10" in let R1 := fresh "R1" in
prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
let rs := eval vm_compute in (ss_mem ssx) in
let i := kp_idx rs in
let ro := eval vm_compute in (nth_error rs i) in
lazymatch ro with Some ?rr =>
let HR := fresh "HR" in let HCs := fresh "HCs" in
pose proof (st_ok_pi_region _ _ _ i rr HS ltac:(vm_compute; reflexivity)) as HR;
unfold region_ok in HR; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict] in HR;
rewrite B10 in HR; destruct HR as (_ & _ & _ & HCs);
repeat (let Hc1 := fresh "HCk" in apply Forall_cons_iff in HCs; destruct HCs as [Hc1 HCs]); clear HCs
end;
let K1 := fresh "K1" in let K2 := fresh "K2" in let K3 := fresh "K3" in let K4 := fresh "K4" in
destruct (Pkept _ KE) as (K1 & K2 & K3 & K4);
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold kn_post_step; exists lyc, Sc; eexists _, _, _;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [replace (k + EV_step) with k by (unfold EV_step; lia); apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (step_extra st p1 opened due heard g p2) HS); [exact HAE | vm_compute; reflexivity]|];
split; [reflexivity|];
split; [apply Permutation_refl|];
split; [kio|];
split; [exact (mo_le_refl MT MTL Sc)|];
split; [exact K1|]; split; [exact K2|]; split; [exact K3|]; split; [exact K4|];
repeat match goal with H : branch_taken _ _ _ = _ |- _ => khc H end;
repeat match goal with H : context [?x mod 2 ^ 64] |- _ => rewrite (Z.mod_small x (2 ^ 64)) in H by lia end;
unfold knock_step_f, L_NS;
repeat match goal with
| |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
| |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
| |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
end; cbn [orb];
try (exfalso; lia);
try rewrite (Z.mod_small (heard + 500000000) (2 ^ 64)) by lia;
(split; [rewrite R10; reflexivity|]);
unfold LAY_Knock; cbn [obj_at]; unfold field_ok; cbn [fst snd];
repeat split; first [kfield | zside]
end in
let rec go := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK KBspan; [kawr | kkeep;
lazymatch goal with
| HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM KBx step_SH ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K KBx KBspan step_SH (start K KBx KBspan step_SH ss) end in
lazymatch why with
| SR_jalr _ => leaf
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' KBspan; [go | go]
| _ => fail "STUCK" why
end
end ]
end in
go.
Qed.
Hypothesis TL : PALib B.
Theorem pb_knock_stepX : tknock_step_specX SEGS B MT (BASE + AF_asan_reac_knock_step).
Proof. exact (pb_knock_step_core (pal_got_shadow B TL) (pal_cell B TL) (pal_got_cell B TL)). Qed.
End h.
End f.
End d.
