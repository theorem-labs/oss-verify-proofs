(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, position-abstract walk, leaf return) and lib/A/ACjv.v lines 136-238 (the aj_intrin_atS memset call, the reseat after it and the zeroed destination region) at c8557374ad2e to libreac/fuzz_knock: cmpPixel -> reac_knock_init, A_cmpPixel -> BASE + AF_asan_reac_knock_init (lib/Reusable/YI0x.v), lib_asan3_0_listing -> knock_asan_listing, AS_memcmp -> AS___asan_memset, TCMP_STK = 16 + ESTACK -> T_init_STK = 48 + ESTACK (lib/A/APgCSpec.v), the donor's blocks (cmp_regions over three malloc blocks) -> knock's single 40-byte struct kp inside the caller's own ASan frame, written through awr_byte's in_frames case by In (cid, pos) own for any frame class cid (knock's harness frame is class 1, not the donor's class 2), its addressability from afobj (lib/A/APgBase.v), and the donor's image top 0x5fb000 -> knock's 0x5f3000 through lib/Reusable/YImgTop.v. Local copies, in the position-abstract form over SEGS, of donor lib/YC1h.v frm_off_imgP, lib/A/AC8j.v st_ok_region_nth / field_of_region / writable_kept / region_kept_aview / val_mem_zero8 and lib/A/ACjv.v val_mem_zero4: knock's lib/A/ACep.v and ACem.v state them for tfibsegs only. Every address is re-derived from fuzz_knock.asan. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
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
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YC80 YC1f YC5d YC85.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import APgBase APgCSpec ACem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg knock_asan_listing}.
#[local] Notation SEGS := (@pa_segs _ knock_asan_listing PI).
#[local] Notation VAL := (@pa_val _ knock_asan_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ knock_asan_listing PI).
#[local] Notation BASE := (@pa_val _ knock_asan_listing PI A_TEXT).
Definition SB : Z := 0x7fff8000.
Definition KBx : sv := SOff 32 0.
Definition KBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition kn_regions : smem := [ stack_region 48; got_regionP; bcell_regionP 32 ].
Definition kn_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 3); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_kn_init : sstate := mkSS AF_asan_reac_knock_init sr_atoms kn_regions None kn_facts.
Definition kn_SH : list shent := [ mkSHE 10 0 40 ].
Definition kn_extra : list word := [Z_to_bv 64 SB].
Definition EK (regs : bvmap 5 word) : env := Eimg (Ereg regs kn_extra).
Definition kn_zero_region : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 40 0 40
[YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0));
YP09.mkChunk 16 (CVal 8 (SLit 0)); YP09.mkChunk 24 (CVal 8 (SLit 0)); YP09.mkChunk 32 (CVal 4 (SLit 0));
YP09.mkChunk 36 (CVal 4 (SLit 0))].
Lemma st_ok_region_nthP : forall E ss ms i r,
st_ok SEGS E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok SEGS E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma st_ok_pi_region_nthP : forall E ss ms i r,
st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. apply (st_ok_region_nthP E (abs_ss VAL ss) ms i r HS). destruct ss; exact Hi.
Qed.
Lemma field_of_regionP : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem SEGS m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok SEGS E m b od w e v Hck He Hv Hw).
Qed.
Lemma writable_keptP : forall H (m m2 : word -> option byte) a,
(apresent H m a -> apresent H m2 a) -> writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H m2) a.
Proof.
intros H m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; intros Hw; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma region_kept_aviewP : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, apresent H m a -> apresent H m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- apply writable_keptP. apply Hp.
Qed.
Lemma val_mem_zero8P : forall H (m : word -> option byte) a,
(forall i, 0 <= i < 8 -> aview SEGS H m (a + i) = Some 0) -> val_mem SEGS (mrestrict H m) a 8 0.
Proof.
intros H m a Hz j Hj. destruct (aview_byte SEGS H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.
Lemma val_mem_zero4P : forall H (m : word -> option byte) a,
(forall i, 0 <= i < 4 -> aview SEGS H m (a + i) = Some 0) -> val_mem SEGS (mrestrict H m) a 4 0.
Proof.
intros H m a Hz j Hj. destruct (aview_byte SEGS H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.
Lemma frm_off_imgP : forall B ly S (W : world SEGS) mem md cid pos,
AR SEGS B ly S W mem md -> In (cid, pos) (frames S) -> off_img (frame_addr ly cid pos) (fs_frame_bytes cid).
Proof.
intros B ly S W mem md cid pos (M & LG & _) Hin. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP.
pose proof (pa_img_cover ly S md LG) as [C1 C2]. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in C1, C2.
pose proof (frame_facts B ly S _ cid pos M Hin) as (Fc & Fp & _ & _ & _ & _ & _ & _ & F64 & _).
destruct (Z.le_gt_cases (frame_addr ly cid pos + fs_frame_bytes cid) 0x10000) as [|H1]; [left; lia|].
destruct (Z.le_gt_cases 0x5f3000 (frame_addr ly cid pos)) as [|H2]; [right; lia|]. exfalso.
apply (client_byte_not_img B ly S _ (Z.max (frame_addr ly cid pos) 0x10000) M).
- right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia.
- unfold in_zr. lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS___asan_memset).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PI := PI).
Lemma kn_entry : forall ly S W0 mem0 md0 own lyc Sc W memc mdc k STK sp0 FP (regs : bvmap 5 word) kp now cid pos,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 kp -> getr regs 11 = w64 now -> 0 <= now < 2 ^ 64 ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - T_init_STK -> spZ regs <= sp0 ->
In (cid, pos) (frames Sc) -> 0 <= cid ->
frame_addr lyc cid pos <= kp -> kp + 40 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
kp mod 8 = 0 ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF kp 40 ->
st_ok_pi SEGS VAL (EK regs) ss_kn_init
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_asan_reac_knock_init)) memc (seg_rom SEGS)))
/\ sh_ok SEGS KBx kn_SH (EK regs) (mrestrict (w_H W) memc).
Proof.
intros ly S W0 mem0 md0 own lyc Sc W memc mdc k STK sp0 FP regs kp now cid pos
HJ G10 G11 Rnow Hal16 Hwlo Hwhi Hfin Hcid Hflo Hfhi Hkp8 HRA.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_init_STK = 4144) by reflexivity.
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hfin) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hfin) as (_ & _ & HFpres & _).
pose proof (fs_frame_bytes_nonneg cid) as HFB.
assert (Hkplo : 4096 <= kp) by lia.
assert (Hkphi : kp + 40 <= alloc_ceiling) by lia.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 1%nat ltac:(lia)) as HO1. pose proof (pa_obj_img 7%nat ltac:(lia)) as HO7.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HO1, HO7.
pose proof (pal_got_cell B TL) as HGC.
pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hfin) as HFimg.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFimg.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (EK regs) n = ew (Ereg regs kn_extra) n)
by (intros n Hn; unfold EK; apply Eimg_low; exact Hn).
assert (E2 : ew (EK regs) 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew (EK regs) 10 = Z_to_bv 64 kp) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (E32 : ew (EK regs) 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs kn_extra 0)).
assert (EO1 : ew (EK regs) (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (unfold EK; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO7 : ew (EK regs) (A_OBJ 7) = Z_to_bv 64 (VAL (A_OBJ 7))) by (unfold EK; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew (EK regs) 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew (EK regs) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val (EK regs) (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
rewrite restrict_mkst_fx.
split.
- unfold ss_kn_init. apply pa_entry_st_ok_full.
+ unfold EK. apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold kn_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS (EK regs) _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 7) 0) (VAL (A_OBJ 7)));
[cbn [sv_denot]; rewrite EO7, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 7)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
* rewrite (VB (A_OBJ 7) (VAL (A_OBJ 7)) EO7) by (pose proof (pa_val_range (A_OBJ 7)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS (EK regs) _ (VAL (A_OBJ 7)) 0 8 KBx SB);
[cbn [sv_denot KBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
+ apply pairwise_disjoint_of_extents. unfold kn_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 7) (VAL (A_OBJ 7)) EO7) by (pose proof (pa_val_range (A_OBJ 7)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [kn_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; unfold SB; lia.
- unfold sh_ok, kn_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) memc (EK regs) KBx 10 kp 40 kp 0 40 HRA).
+ unfold KBx, U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ lia.
+ cbn [Z.min Z.max]. intros x Hx. unfold in_app in HFapp.
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.
Theorem pb_knock_initX : tknock_init_specX SEGS B MT (BASE + AF_asan_reac_knock_init).
Proof.
unfold tknock_init_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs kp now cid pos ch
HJ Hra Hra4 Hgp Htp G10 G11 Rnow Hch Hal16 Hwlo Hwhi Hown Hcid Hfal Hflo Hfhi Hkp8 Hkpnz Hkpsp HFOBJ Hev.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_init_STK = 4144) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct HFOBJ as (_ & _ & HRA).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hfin) as (HF4096 & HFceil & HFapp).
pose proof (fs_frame_bytes_nonneg cid) as HFB.
assert (Hkplo : 4096 <= kp) by lia.
assert (Hkphi : kp + 40 <= alloc_ceiling) by lia.
destruct (kn_entry ly S W0 mem0 md0 own lyc Sc W memc mdc k STK sp0 FP regs kp now cid pos
HJ G10 G11 Rnow Hal16 Hwlo Hwhi Hfin Hcid Hflo Hfhi Hkp8 HRA) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (EK regs)) by (unfold EK; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew (EK regs) n = ew (Ereg regs kn_extra) n)
by (intros n Hn; unfold EK; apply Eimg_low; exact Hn).
assert (Ew1 : ew (EK regs) 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew (EK regs) 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew (EK regs) 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew (EK regs) 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew (EK regs) 10 = Z_to_bv 64 kp) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (E11 : ew (EK regs) 11 = Z_to_bv 64 now) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact G11).
assert (E32 : ew (EK regs) 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs kn_extra 0)).
assert (Usp : bv_unsigned (ew (EK regs) 2) = spZ regs) by (rewrite E2; reflexivity).
assert (EO1 : ew (EK regs) (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (unfold EK; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO7 : ew (EK regs) (A_OBJ 7) = Z_to_bv 64 (VAL (A_OBJ 7))) by (unfold EK; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 1%nat ltac:(lia)) as HO1. pose proof (pa_obj_img 7%nat ltac:(lia)) as HO7.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HO1, HO7.
pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hfin) as HFimg.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFimg.
assert (HAE : env_agree 32 (Ereg regs kn_extra) (EK regs))
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | unfold EK; reflexivity]).
assert (AG : forall n, (n < 33)%nat -> ew (EK regs) n = ew (EK regs) n) by (intros; reflexivity).
unfold cfg_at. change (w64 (BASE + AF_asan_reac_knock_init)) with (Z_to_bv 64 (BASE + AF_asan_reac_knock_init)).
change memc with (ms_mem (mkst regs (Z_to_bv 64 (BASE + AF_asan_reac_knock_init)) memc (seg_rom SEGS))) in HJ.
paj_run_tok RUN HS HJ SHOK KBspan.
{ lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp0v ?fp ?b0 ?bc ?lyv ?ownv =>
let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp0v fp b0 bc lyv ownv) end;
intros a (r & Hin & Ha); cbn [In] in Hin;
destruct Hin as [<-|[<-|[<-|[]]]];
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ?Usp in Ha; [left; lia | lia | lia]. }
lazymatch goal with HS1 : st_ok _ _ ?ssv (restrict _ ?msv) |- _ =>
assert (KE1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem msv) a = aview SEGS (w_H W) memc a);
[ intros a Ha Hna; apply aview_eq_of;
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => apply HFr end;
rewrite unsigned_lit_small by lia;
intros (r & Hin & Hw); unfold ss_kn_init, kn_regions, stack_region, got_regionP, bcell_regionP in Hin;
cbn [ss_mem In] in Hin; destruct Hin as [<-|[<-|[<-|[]]]];
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hw; rewrite ?Usp in Hw; lia | ];
assert (HRA1 : range_addressable (aview SEGS (w_H W) (ms_mem msv)) SHADOW_OFF kp 40);
[ intros x Hx; destruct (HRA x Hx) as (s & Hs & Hok); exists s; split; [|exact Hok];
assert (Hd : 0 <= x / 8 /\ 8 * (x / 8) <= x)
by (split; [apply Z.div_pos; lia | pose proof (Z.mul_div_le x 8 ltac:(lia)); lia]);
rewrite KE1; [exact Hs | unfold shadow_of_addr, SHADOW_OFF in *; lia
| unfold shadow_of_addr, SHADOW_OFF in *; lia] | ]
end.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_atS SEGS B LAWS Hsegs OSet (SIGMA AS___asan_memset) AMEMSET _ (ms_regs msX) (ms_mem msX)
STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k kp 0 40 (spZ regs - 48 - sp0) (Z_to_bv 64 (BASE + 1464))) end.
- lazymatch goal with HJ1 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact HJ1 end.
- rewrite Ra0, E10. reflexivity.
- rewrite Ra1. reflexivity.
- rewrite Ra2. reflexivity.
- lia.
- lia.
- lia.
- unfold spZ at 1. rewrite Rsp, Usp. rewrite unsigned_lit_small by lia. lia.
- replace (spZ regs - 48 - sp0) with (spZ regs - sp0 + (-3) * 16) by lia.
rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al. reflexivity.
- lia.
- lia.
- rewrite Rgp, E3. exact Hgp.
- rewrite Rtp, E4. exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split.
+ right. right. right. exists cid, pos. split; [exact Hown|]. left. unfold in_zr. cbn [fst snd]. lia.
+ unfold ESTACK. lia.
- apply amem_range_high; [lia | | lia].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia.
- exact HRA1.
- intros _. lazymatch goal with HJ1 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
eapply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W _ _ cid pos kp 40 (proj1 HJ1) Hfin) end; lia.
- exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff & Hfr2 & Hpres2 & HSM2).
lazymatch goal with HS1 : st_ok _ _ ?ssv (restrict _ ?msv) |- _ =>
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_init_STK <= a < spZ regs) -> ~ (kp <= a < kp + 40) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem msv) a);
[ intros a Ha H1 H2; apply Hfr2; [lia | exact H2 | unfold ESTACK; lia] | ];
destruct (al_const _ _ LAWS lyc Sc W (ms_mem msv) _ (proj1 HJ)) as (Kcell1 & _ & Kgot1 & _)
end.
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot1. rewrite (pal_cell B TL) in Kcell1.
destruct (al_const _ _ LAWS lyc Sc W mem2 md2 (proj1 HJ2)) as (Kcell2 & _ & Kgot2 & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot2. rewrite (pal_cell B TL) in Kcell2.
destruct (al_frames _ _ LAWS lyc Sc W mem2 md2 cid pos (proj1 HJ2) Hfin) as (_ & _ & HFpres2 & _).
assert (HRA2 : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF kp 40).
{ intros x Hx. destruct (HRA1 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
assert (Hd : 0 <= x / 8 /\ 8 * (x / 8) <= x)
by (split; [apply Z.div_pos; lia | pose proof (Z.mul_div_le x 8 ltac:(lia)); lia]).
rewrite KE2; [exact Hs
| unfold shadow_of_addr, SHADOW_OFF in *; lia
| unfold shadow_of_addr, SHADOW_OFF in *; lia
| unfold shadow_of_addr, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia]. }
rename HJ into HJr1. rename HF into HFA. rename HFr into HFrA. rename HG into HGA. rename SHOK into SHOKA.
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0;1;2]%nat HS2.
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in assert (HQ : Q);
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
[ eapply (region_kept_aviewP (EK regs) (w_H W) _ _ 2%nat (spZ regs) (-48) 0 (-48) 0 _);
[ exact Usp | intros a Ha; apply Hfr2; [lia | lia | unfold ESTACK; lia] | exact Hpres2 ]
| eapply (region_kept_val_at (EK regs) _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (VAL (A_OBJ 7)) 0 0 _);
[ rewrite EO1; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)); lia
| exact (val_mem_of_rdword SEGS (w_H W) _ _ _ Kgot1)
| exact (val_mem_of_rdword SEGS (w_H W) _ _ _ Kgot2) | lia ]
| eapply (region_kept_val_at (EK regs) _ _ (A_OBJ 7) (VAL (A_OBJ 7)) 8 SHADOW_OFF 0 0 _);
[ rewrite EO7; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 7)); lia
| exact (val_mem_of_rdword SEGS (w_H W) _ _ _ Kcell1)
| exact (val_mem_of_rdword SEGS (w_H W) _ _ _ Kcell2) | lia ] ]
| specialize (HS2 HQ); clear HQ ] end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => remember Ev as E1 eqn:HE1 in HS end.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbn; unfold A_TEXT; lia]).
assert (E1_1 : ew E1 1 = getr regs 1) by (rewrite HE1, ew_havoc_old by lia; exact Ew1).
assert (E1_2 : ew E1 2 = getr regs 2) by (rewrite HE1, ew_havoc_old by lia; exact E2).
assert (E1_10 : ew E1 10 = Z_to_bv 64 kp) by (rewrite HE1, ew_havoc_old by lia; exact E10).
assert (E1_11 : ew E1 11 = Z_to_bv 64 now) by (rewrite HE1, ew_havoc_old by lia; exact E11).
assert (E1_32 : ew E1 32 = Z_to_bv 64 SB) by (rewrite HE1, ew_havoc_old by lia; exact E32).
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite E1_2; reflexivity).
assert (HAE1 : env_agree 32 (Ereg regs kn_extra) E1)
by (split; [intros n Hn; rewrite HE1, ew_havoc_old by lia; apply EL; unfold A_TEXT; lia
| rewrite HE1; unfold EK; reflexivity]).
assert (Z8 : forall off, 0 <= off -> off + 8 <= 40 -> val_mem SEGS (mrestrict (w_H W) mem2) (kp + off) 8 0).
{ intros off H1 H2. apply val_mem_zero8P. intros i Hi.
replace (kp + off + i) with (kp + (off + i)) by lia. rewrite (Heff (off + i)) by lia. reflexivity. }
assert (Z4 : forall off, 0 <= off -> off + 4 <= 40 -> val_mem SEGS (mrestrict (w_H W) mem2) (kp + off) 4 0).
{ intros off H1 H2. apply val_mem_zero4P. intros i Hi.
replace (kp + off + i) with (kp + (off + i)) by lia. rewrite (Heff (off + i)) by lia. reflexivity. }
assert (EV1 : bv_unsigned (ew E1 242%nat) = VAL (A_OBJ 1))
by (apply (HEI1 (A_OBJ 1)); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EV7 : bv_unsigned (ew E1 248%nat) = VAL (A_OBJ 7))
by (apply (HEI1 (A_OBJ 7)); unfold A_OBJ, A_TEXT, A_LIM; lia).
lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
pose proof (st_ok_pi_add_region E1 ssv msv kn_zero_region HS eq_refl
ltac:(unfold kn_zero_region, region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E1_10, unsigned_lit_small by lia;
split; [lia|]; split; [lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres2 (kp + o) ltac:(lia)))|];
repeat apply Forall_cons; try apply Forall_nil;
[ apply (chunk_ok_val SEGS E1 _ kp 0 4 (SLit 0) 0); [reflexivity | zside | zside | apply Z4; lia]
| apply (chunk_ok_val SEGS E1 _ kp 4 4 (SLit 0) 0); [reflexivity | zside | zside | apply Z4; lia]
| apply (chunk_ok_val SEGS E1 _ kp 8 8 (SLit 0) 0); [reflexivity | zside | zside | apply Z8; lia]
| apply (chunk_ok_val SEGS E1 _ kp 16 8 (SLit 0) 0); [reflexivity | zside | zside | apply Z8; lia]
| apply (chunk_ok_val SEGS E1 _ kp 24 8 (SLit 0) 0); [reflexivity | zside | zside | apply Z8; lia]
| apply (chunk_ok_val SEGS E1 _ kp 32 4 (SLit 0) 0); [reflexivity | zside | zside | apply Z4; lia]
| apply (chunk_ok_val SEGS E1 _ kp 36 4 (SLit 0) 0); [reflexivity | zside | zside | apply Z4; lia] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, kn_zero_region;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E1_10, EV1, EV7, Usp1; rewrite unsigned_lit_small by lia;
repeat split; lia)) as HS3; clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
assert (SHOK2 : sh_ok SEGS KBx kn_SH E1 (mrestrict (w_H W) mem2)).
{ unfold sh_ok, kn_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem2 E1 KBx 10 kp 40 kp 0 40 HRA2).
- unfold KBx, U. cbn [sv_denot]. rewrite E1_32, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E1_10, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by lia. reflexivity.
- lia.
- lia.
- cbn [Z.min Z.max]. intros x Hx.
unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
paj_run_tok RUN HS HJ2 SHOK2 KBspan.
{ lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp0v ?fp ?b0 ?bc ?lyv ?ownv =>
let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp0v fp b0 bc lyv ownv) end;
intros a (r & Hin & Ha); cbn [In] in Hin;
destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ?Usp1, ?E1_10 in Ha;
rewrite ?unsigned_lit_small in Ha by lia;
[ right; right; right; exists cid, pos; split; [exact Hown|];
left; unfold in_zr; cbn [fst snd]; lia
| left; lia | lia | lia ]. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msv) =>
assert (KE3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_init_STK <= a < spZ regs) -> ~ (kp <= a < kp + 40) ->
aview SEGS (w_H W) (ms_mem msv) a = aview SEGS (w_H W) mem2 a);
[ intros a Ha H1 H2; apply aview_eq_of; apply HFr; rewrite unsigned_lit_small by lia;
intros (r & Hin & Hw); cbn [In ss_mem] in Hin; destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hw; rewrite ?Usp1, ?E1_10 in Hw;
rewrite ?unsigned_lit_small in Hw by lia; lia | ];
assert (KEF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_init_STK <= a < spZ regs) -> ~ (kp <= a < kp + 40) ->
aview SEGS (w_H W) (ms_mem msv) a = aview SEGS (w_H W) memc a);
[ intros a Ha H1 H2; rewrite (KE3 a Ha H1 H2), (KE2 a Ha H1 H2); apply KE1; lia | ]
end.
assert (HIO : same_io mdc md2).
{ eapply same_io_trans; [apply same_io_materialized, same_but_materialized_wvb_any
| apply same_io_materialized; exact HSM2]. }
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_pi_region_nthP Ex ssx (restrict (w_H W) msX) 0 _ HS eq_refl) as HRg;
cbn [ms_mem restrict] in HRg end.
assert (Bkp : bv_unsigned (ew E1 10) = kp) by (rewrite E1_10; apply unsigned_lit_small; lia).
assert (Dnow : sv_denot E1 (SOff 11 0) = Z_to_bv 64 now)
by (cbn [sv_denot]; rewrite E1_11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (Ddue : sv_denot E1 (SOff 11 500000000) = Z_to_bv 64 ((now + L_NS) mod 2 ^ 64)).
{ cbn [sv_denot]. rewrite E1_11, unsigned_lit_small by lia. apply bv_eq.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
unfold L_NS. rewrite Z.mod_mod by lia. reflexivity. }
pose proof (field_of_regionP E1 _ 10 kp _ 0 40 0 40 0 4 (SLit 0) 0 HRg Bkp
ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as U0.
pose proof (field_of_regionP E1 _ 10 kp _ 0 40 0 40 4 4 (SLit 0) 0 HRg Bkp
ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as U4.
pose proof (field_of_regionP E1 _ 10 kp _ 0 40 0 40 8 8 (SOff 11 0) now HRg Bkp
ltac:(cbn; tauto) Dnow ltac:(cbn; lia) ltac:(cbn; lia)) as U8.
pose proof (field_of_regionP E1 _ 10 kp _ 0 40 0 40 16 8 (SOff 11 500000000) ((now + L_NS) mod 2 ^ 64) HRg Bkp
ltac:(cbn; tauto) Ddue ltac:(cbn; pose proof (Z.mod_pos_bound (now + L_NS) (2 ^ 64) ltac:(lia)); lia)
ltac:(cbn; lia)) as U16.
pose proof (field_of_regionP E1 _ 10 kp _ 0 40 0 40 24 8 (SLit 0) 0 HRg Bkp
ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as U24.
pose proof (field_of_regionP E1 _ 10 kp _ 0 40 0 40 32 4 (SLit 0) 0 HRg Bkp
ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as U32.
pose proof (field_of_regionP E1 _ 10 kp _ 0 40 0 40 36 4 (SLit 0) 0 HRg Bkp
ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as U36.
cbn [N.to_nat] in U0, U4, U8, U16, U24, U32, U36.
prreg HS (1%bv : bv 5) Rra3.
eapply (RET W E1 _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat2.
unfold kn_post_init.
exists lyc, Sc. eexists. eexists. eexists.
split.
{ rewrite Rra3, E1_1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ replace (k + EV_init) with k by (unfold EV_init; lia).
apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ2. }
split.
{ eapply (aregs_preserved_of_st_ok SEGS (w_H W) E1 _ _ regs kn_extra HS HAE1). vm_compute. reflexivity. }
split; [reflexivity|].
split; [apply Permutation_refl|].
split.
{ eapply same_io_trans; [exact HIO|].
repeat first [ apply same_io_materialized, same_but_materialized_wvb_any
| eapply same_io_trans; [apply same_io_materialized, same_but_materialized_wvb_any|] ]. }
split; [exact (mo_le_refl MT MTL Sc)|].
split.
{ intros a Ha1 Ha2 Ha3. apply KEF; [lia | exact Ha2 | exact Ha3]. }
split.
{ intros b m i Hb Hi.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & Hb4096 & Hbceil & _ & _ & _).
pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc b m cid pos HAR Hb Hfin) as Hdb.
unfold zdisjoint in Hdb. cbn [fst snd] in Hdb.
apply KEF; lia. }
split.
{ intros c p a Hcp Hzr Hnkp.
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc c p HAR Hcp) as (Hc1 & Hc2 & _).
pose proof (fs_frame_bytes_nonneg c) as Hcb.
assert (Hd1 : 0 <= frame_addr lyc c p / 8 /\ 8 * (frame_addr lyc c p / 8) <= frame_addr lyc c p)
by (split; [apply Z.div_pos; lia | pose proof (Z.mul_div_le (frame_addr lyc c p) 8 ltac:(lia)); lia]).
assert (Hd2 : 0 <= fs_frame_bytes c / 8 /\ 8 * (fs_frame_bytes c / 8) <= fs_frame_bytes c)
by (split; [apply Z.div_pos; lia | pose proof (Z.mul_div_le (fs_frame_bytes c) 8 ltac:(lia)); lia]).
unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hzr. cbn [fst snd] in Hzr.
apply KEF; [lia | lia | exact Hnkp]. }
split.
{ intros a Himg Hstat Herr.
pose proof (pa_img_range a Himg) as Hir. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hir.
apply KEF; [lia | lia |].
intros Hkpa.
destruct (al_client_img _ _ LAWS lyc Sc W memc mdc a HAR
ltac:(right; left; exists cid, pos; split; [exact Hfin | lia])) as [_ Hni].
exact (Hni Himg). }
cbn [obj_at LAY_Knock field_ok fst snd].
repeat split; try exact U0; try exact U4; try exact U8; try exact U16; try exact U24; try exact U32; try exact U36;
try (pose proof (Z.mod_pos_bound (now + L_NS) (2 ^ 64) ltac:(lia)); cbn; lia).
Qed.
End h.
End f.
End d.
