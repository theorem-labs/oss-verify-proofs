(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACes.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition RFC_MS : Z := 0x80b94.
Definition RFC_RD1 : Z := 0x80c68.
Definition RFC_RD2 : Z := 0x80d24.
Definition RFC_RD3 : Z := 0x80de0.
Definition RFC_RD4 : Z := 0x80e5c.
Definition RFC_RD5 : Z := 0x80f14.
Definition RFC_J : Z := 0x80f44.
Definition RFC_PAL : Z := 0x80f48.
Definition RFC_PM : Z := 0x80f68.
Definition RFC_PRD : Z := 0x80fec.
Definition RFC_I : Z := 0x80ffc.
Definition RFC_IM : Z := 0x81004.
Definition RFC_IRD : Z := 0x81078.
Definition RFC_F1 : Z := 0x8109c.
Definition RFC_F2 : Z := 0x810b4.
Definition RFC_EPI : Z := 0x810b8.
Definition RFC_RET : Z := 0x810ec.
Definition A_asan_memset_tfb : Z := 0x51a78.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Definition RBx : sv := SOff 32 0.
Definition RBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition st_region (sta : nat) (pv nv curv : sv) : YP09.region := YP09.mkRegion (Some sta) 0 24 16 24
[YP09.mkChunk 0 (CVal 8 pv); YP09.mkChunk 8 (CVal 8 nv); YP09.mkChunk 16 (CVal 8 curv)].
Definition rfc_facts0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF (2^46) (2^47 - 24) 3); (11%nat, mkAF 4096 0x7fffff800000 3);
(12%nat, mkAF 1 100000000 0); (32%nat, mkAF SB SB 0); (33%nat, mkAF 4096 0x7fffff800000 4);
(34%nat, mkAF 1 (2^28) 0); (35%nat, mkAF 0 (2^28) 0) ].
Definition ss_rfc : sstate :=
mkSS A_read_frameconfig sr_atoms [stack_region 96; got_region; bcell_region 32] None (mkFacts rfc_facts0 [] []).
Definition ss_rfc_c : sstate := Eval vm_compute in ss_rfc.
Definition rfc_extra (pdata nb cur : Z) : list word := map (Z_to_bv 64) [SB; pdata; nb; cur].
Lemma denot_shx : forall E n m c v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb -> 0 <= v -> 0 <= c -> v + c < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (sb + (v + c) / 8).
Proof.
intros E n m c v sb Hn Hm Hv Hc0 Hc Hsb.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)))). f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = sb + (v + c) / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm. rewrite !unsigned_lit_small by lia. rewrite Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small (v + c)) by lia. rewrite (zcanon_small ((v + c) / 8)) by lia. rewrite (zcanon_small sb) by lia. rewrite zcanon_small by lia. lia.
Qed.
Lemma val_mem_kept : forall H H' (m m' : word -> option byte) a n v,
val_mem tfibsegs (mrestrict H m) a n v -> (forall i, 0 <= i < Z.of_nat n -> aview tfibsegs H' m' (a + i) = aview tfibsegs H m (a + i)) ->
val_mem tfibsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hv Heq k Hk. rewrite <- (Hv k Hk). apply (mbyte_of_aview tfibsegs). apply Heq. lia.
Qed.
Section e.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma mres_kept : forall lyc Sc W memT W2 mem2 ly2 S2 slo shi res n,
(res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ acall_kept tfibsegs B lyc Sc W memT W2 mem2 slo shi (fun _ => False))
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept tfibsegs B lyc Sc W memT W2 mem2 slo shi (fun a => res <= a < res + req_size n)) ->
acall_kept tfibsegs B lyc Sc W memT W2 mem2 slo shi (fun a => res <> 0 /\ res <= a < res + req_size n) /\
(forall b, In b (ablocks B lyc Sc) -> In b (ablocks B ly2 S2)) /\
(res <> 0 -> In (res, n) (ablocks B ly2 S2)).
Proof.
intros lyc Sc W memT W2 mem2 ly2 S2 slo shi res n [(Hz & Ebl & HK) | (Hnz & Ebl & HK)].
- split; [eapply acall_kept_mono_E; [exact HK | intros a []]|]. split; [intros b Hb; rewrite Ebl; exact Hb | intros H; lia].
- split; [eapply acall_kept_mono_E; [exact HK | intros a Ha; split; [lia | exact Ha]]|].
split; [intros b Hb; rewrite Ebl; apply in_app_iff; left; exact Hb | intros _; rewrite Ebl; apply in_app_iff; right; left; reflexivity].
Qed.
Lemma mres_range : forall ly2 S2 W2 mem2 md2 lyc Sc (res n : Z) (P Q : Prop),
AR tfibsegs B ly2 S2 W2 mem2 md2 ->
(res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ P) \/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\ Q) ->
res = 0 \/ (4096 <= res /\ ((res + req_size n <= 65536 \/ 6270976 <= res) /\ (res + req_size n <= 2147446784 \/ 17594333495296 <= res))
/\ res + req_size n <= alloc_ceiling /\ res mod 16 = 0 /\ In (res, n) (ablocks B ly2 S2)).
Proof.
intros ly2 S2 W2 mem2 md2 lyc Sc res n P Q HAR [(-> & _ & _) | (Hr & Ebl & _)]; [left; reflexivity | right].
assert (Hin : In (res, n) (ablocks B ly2 S2)) by (rewrite Ebl; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res n HAR Hin) as (H16 & _ & Hc & [Hh Happ] & _).
pose proof (blk_off_img _ _ _ _ _ _ res n HAR Hin) as Hh_img.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, Hh_img; lia|]. split; [exact Hc|]. split; [exact H16 | exact Hin].
Qed.
Lemma rfc_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bb : list (Z * Z))
(st dst N pdata nb cur : Z) (cid pos : Z),
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
Permutation (ablocks B lyc Sc) Bb -> In (pdata, nb) Bb ->
getr regs 10 = w64 st -> getr regs 11 = w64 dst -> getr regs 12 = w64 N ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TRFC_STK -> spZ regs <= sp0 ->
In (cid, pos) own -> 0 <= cid ->
frame_addr lyc cid pos <= dst -> dst + 32 <= frame_addr lyc cid pos + fs_frame_bytes cid -> dst mod 8 = 0 ->
spZ regs <= st -> st + 24 <= sp0 -> st mod 8 = 0 ->
1 <= N <= 100000000 -> 0 <= cur <= nb -> 0 < nb ->
val_mem tfibsegs (mrestrict (w_H W) memc) st 8 pdata -> val_mem tfibsegs (mrestrict (w_H W) memc) (st + 8) 8 nb ->
val_mem tfibsegs (mrestrict (w_H W) memc) (st + 16) 8 cur ->
st_ok tfibsegs (Ereg regs (rfc_extra pdata nb cur)) ss_rfc_c (restrict (w_H W) (mkst regs (Z_to_bv 64 A_read_frameconfig) memc (seg_rom tfibsegs))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
HJ HPerm Hpd G10 G11 G12 Hal16 Hwlo Hwhi Hown Hcid Hdst1 Hdst2 Hdst8 Hst1 Hst2 Hst8 HN Hcur Hnb Wp Wn Wc.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TRFC_STK = 112 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (Hpdc : In (pdata, nb) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hpd]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pdata nb HAR Hpdc) as (Hp16 & Hp4096 & Hpceil & Hph_ia & _ & _ & HnbM). pose proof (proj1 Hph_ia) as Hph.
pose proof (req_size_pos nb ltac:(lia)) as [Hrq1 Hrq2]. unfold MALLOC_MAX in HnbM.
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & [HFhi1 HFhi2] & HFpres & _). ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFhi2.
pose proof (fs_frame_bytes_nonneg cid) as HFB.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx. change ss_rfc_c with ss_rfc.
set (E := Ereg regs (rfc_extra pdata nb cur)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 st) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (E11 : ew E 11 = Z_to_bv 64 dst) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact G11).
assert (E12 : ew E 12 = Z_to_bv 64 N) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact G12).
assert (EX : forall j, ew E (32 + j) = nth j (rfc_extra pdata nb cur) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
pose proof (EX 0%nat) as E32. pose proof (EX 1%nat) as E33. pose proof (EX 2%nat) as E34. pose proof (EX 3%nat) as E35.
cbn [Nat.add nth rfc_extra map] in E32, E33, E34, E35. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_rfc. apply (entry_st_ok_full tfibsegs); change (Ereg regs (rfc_extra pdata nb cur)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_region, bcell_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
+ cbn [base_val]. unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0x9df98) at 1.
apply (chunk_ok_val tfibsegs E _ 0 0x9df98 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) memc _ _ Kgot).
+ cbn [base_val]. unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0xa5ff8) at 1.
apply (chunk_ok_val tfibsegs E _ 0 0xa5ff8 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) memc _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold stack_region, got_region, bcell_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hwlo Hwhi C1 C3 HTS Has Hstk0 Hst1 Hst2. clear. ceil; unfold ASAN_CEIL. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms rfc_facts0 atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E11, E12, E32, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hwlo Hwhi Hal16 Hst1 Hst2 Hdst1 Hdst2 Hst8 Hdst8 HN Hcur Hnb Hp16 Hp4096 Hpceil Hph HnbM Hrq1 Hrq2 HFhi1 HFhi2 C1 C3 HTS Has Hstk0. clear.
ceil; unfold SB, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat match goal with |- _ /\ _ => split end; try lia.
all: match goal with |- ?g => idtac "ENTRYFACT" g end; fail.
Qed.
Definition rfc_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26].
Definition rfc_frame (m : word -> option byte) (sp : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error rfc_saved j = Some r -> val_mem tfibsegs m (sp - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Definition rfc_kept (W : world tfibsegs) (memc : word -> option byte) (W1 : world tfibsegs) (mem1 : word -> option byte)
(sp : Z) (Bb : list (Z * Z)) (lyc : alayout) (Sc : astate) (st dst : Z) : Prop :=
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - TRFC_STK <= a < sp) -> ~ (dst <= a < dst + 32) -> ~ (st + 16 <= a < st + 24) ->
aview tfibsegs (w_H W1) mem1 a = aview tfibsegs (w_H W) memc a) /\
(forall b m i, In (b, m) Bb -> 0 <= i < req_size m -> aview tfibsegs (w_H W1) mem1 (b + i) = aview tfibsegs (w_H W) memc (b + i)) /\
(forall c p a, In (c, p) (frames Sc) ->
(in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) ->
~ (dst <= a < dst + 32) -> ~ (st + 16 <= a < st + 24) ->
aview tfibsegs (w_H W1) mem1 a = aview tfibsegs (w_H W) memc a) /\
(forall a, in_img tfibsegs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview tfibsegs (w_H W1) mem1 a = aview tfibsegs (w_H W) memc a).
Lemma rfc_kept_refl : forall W memc sp Bb lyc Sc st dst, rfc_kept W memc W memc sp Bb lyc Sc st dst.
Proof. intros. repeat split; intros; reflexivity. Qed.
Definition rfc_sep (sp : Z) (Bb : list (Z * Z)) (lyc : alayout) (Sc : astate) (st dst : Z) : Prop :=
(forall b m i, In (b, m) Bb -> 0 <= i < req_size m ->
0 <= b + i < alloc_ceiling /\ ~ (dst <= b + i < dst + 32) /\ ~ (st <= b + i < st + 24)) /\
(forall c p a, In (c, p) (frames Sc) ->
(in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) -> 0 <= a < alloc_ceiling) /\
(forall a, dst <= a < dst + 32 -> ~ in_img tfibsegs a) /\ alloc_ceiling <= st.
Lemma rfc_sep_intro : forall ly S W mem md (Bb : list (Z * Z)) st dst cid pos sp,
AR tfibsegs B ly S W mem md -> Permutation (ablocks B ly S) Bb -> In (cid, pos) (frames S) ->
alloc_ceiling <= st ->
frame_addr ly cid pos <= dst -> dst + 32 <= frame_addr ly cid pos + fs_frame_bytes cid ->
(dst + 32 <= 0x10000 \/ 0x5fb000 <= dst) ->
rfc_sep sp Bb ly S st dst.
Proof.
intros ly S W mem md Bb st dst cid pos sp HAR HPerm Hfin Hst1 Hdst1 Hdst2 Hdimg. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|split; [|split; [intros a Ha Him; pose proof (tfib_img_range a Him); lia | exact Hst1]]].
- intros b m i Hb Hi. assert (Hin : In (b, m) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & Hb4096 & Hbceil & _).
pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ b m cid pos HAR Hin Hfin) as D. unfold zdisjoint in D. cbn [fst snd] in D.
split; [lia|]. split; lia.
- intros c p a Hcp Ha. destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ c p HAR Hcp) as (F0 & Fc & Fh).
pose proof (fs_frame_bytes_nonneg c) as Fn. unfold frame_rng, in_zr in Ha. cbn [fst snd] in Ha.
destruct Ha as [Ha|Ha]; [lia|].
pose proof (shadow_range_end (frame_addr ly c p) (fs_frame_bytes c) Fn) as SE.
pose proof (shadow_addr_bounds (frame_addr ly c p) ltac:(lia)) as SB1.
pose proof (shadow_addr_bounds (frame_addr ly c p + fs_frame_bytes c) ltac:(lia)) as SB2.
lia.
Qed.
Lemma rfc_kept_step : forall W memc W1 mem1 mem2 sp Bb lyc Sc st dst (Wr : Z -> Prop),
rfc_kept W memc W1 mem1 sp Bb lyc Sc st dst -> rfc_sep sp Bb lyc Sc st dst ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H W1) mem2 a = aview tfibsegs (w_H W1) mem1 a) ->
(forall a, Wr a -> (sp - TRFC_STK <= a < sp) \/ (dst <= a < dst + 32) \/ (st + 16 <= a < st + 24)) ->
alloc_ceiling <= sp - TRFC_STK ->
rfc_kept W memc W1 mem2 sp Bb lyc Sc st dst.
Proof.
intros W memc W1 mem1 mem2 sp Bb lyc Sc st dst Wr (K1 & K2 & K3 & K4) (SP1 & SP2 & SP3 & SP4) Hun Hwr Hsp. pose proof asan_consts as (C1 & _).
split; [|split; [|split]].
- intros a Ha N1 N2 N3. rewrite <- (K1 a Ha N1 N2 N3). apply Hun; [lia|]. intros Hw. destruct (Hwr a Hw) as [X|[X|X]]; tauto.
- intros b m i Hb Hi. rewrite <- (K2 b m i Hb Hi). destruct (SP1 b m i Hb Hi) as (X1 & X2 & X3). apply Hun; [lia|]. intros Hw. destruct (Hwr _ Hw) as [X|[X|X]]; lia.
- intros c p a Hcp Ha N2 N3. rewrite <- (K3 c p a Hcp Ha N2 N3). pose proof (SP2 c p a Hcp Ha) as X1. apply Hun; [lia|]. intros Hw. destruct (Hwr _ Hw) as [X|[X|X]]; lia.
- intros a Him Hns He. rewrite <- (K4 a Him Hns He). pose proof (tfib_img_range a Him) as X1. apply Hun; [lia|]. intros Hw.
destruct (Hwr _ Hw) as [X|[X|X]]; [lia | exact (SP3 a X Him) | lia].
Qed.
Lemma rfc_kept_stepE : forall W memc W1 mem1 mem2 sp Bb lyc Sc st dst (Wr Er : Z -> Prop),
rfc_kept W memc W1 mem1 sp Bb lyc Sc st dst -> rfc_sep sp Bb lyc Sc st dst ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H W1) mem2 a = aview tfibsegs (w_H W1) mem1 a) ->
(forall a, Wr a -> (sp - TRFC_STK <= a < sp) \/ (dst <= a < dst + 32) \/ (st + 16 <= a < st + 24) \/ Er a) ->
alloc_ceiling <= sp - TRFC_STK -> (forall a, Er a -> a < alloc_ceiling) ->
(forall b m i, In (b, m) Bb -> 0 <= i < req_size m -> ~ Er (b + i)) ->
(forall c p a, In (c, p) (frames Sc) -> (in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) -> ~ Er a) ->
(forall a, Er a -> ~ in_img tfibsegs a) ->
rfc_kept W memc W1 mem2 sp Bb lyc Sc st dst.
Proof.
intros W memc W1 mem1 mem2 sp Bb lyc Sc st dst Wr Er (K1 & K2 & K3 & K4) (SP1 & SP2 & SP3 & SP4) Hun Hwr Hsp HEc HEb HEf HEi. pose proof asan_consts as (C1 & _).
split; [|split; [|split]].
- intros a Ha N1 N2 N3. rewrite <- (K1 a Ha N1 N2 N3). apply Hun; [lia|]. intros Hw.
destruct (Hwr a Hw) as [X|[X|[X|X]]]; [tauto|tauto|tauto|]. pose proof (HEc a X). lia.
- intros b m i Hb Hi. rewrite <- (K2 b m i Hb Hi). destruct (SP1 b m i Hb Hi) as (X1 & X2 & X3). apply Hun; [lia|]. intros Hw.
destruct (Hwr _ Hw) as [X|[X|[X|X]]]; [lia|lia|lia|exact (HEb b m i Hb Hi X)].
- intros c p a Hcp Ha N2 N3. rewrite <- (K3 c p a Hcp Ha N2 N3). pose proof (SP2 c p a Hcp Ha) as X1. apply Hun; [lia|]. intros Hw.
destruct (Hwr _ Hw) as [X|[X|[X|X]]]; [lia|lia|lia|exact (HEf c p a Hcp Ha X)].
- intros a Him Hns He. rewrite <- (K4 a Him Hns He). pose proof (tfib_img_range a Him) as X1. apply Hun; [lia|]. intros Hw.
destruct (Hwr _ Hw) as [X|[X|[X|X]]]; [lia | exact (SP3 a X Him) | lia | exact (HEi a X Him)].
Qed.
Lemma rfc_kept_call : forall W memc W1 mem1 W2 mem2 sp Bb lyc Sc lyc' Sc' st dst slo shi (Er : Z -> Prop),
rfc_kept W memc W1 mem1 sp Bb lyc Sc st dst ->
acall_kept tfibsegs B lyc' Sc' W1 mem1 W2 mem2 slo shi Er ->
sp - TRFC_STK <= slo -> shi <= sp ->
(forall b m, In (b, m) Bb -> In (b, m) (ablocks B lyc' Sc')) -> (forall b m i, In (b, m) Bb -> 0 <= i < req_size m -> ~ Er (b + i)) ->
frames Sc' = frames Sc -> (forall c p, frame_addr lyc' c p = frame_addr lyc c p) ->
(forall c p a, In (c, p) (frames Sc) -> (in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) -> ~ Er a) ->
rfc_kept W memc W2 mem2 sp Bb lyc Sc st dst.
Proof.
intros W memc W1 mem1 W2 mem2 sp Bb lyc Sc lyc' Sc' st dst slo shi Er (K1 & K2 & K3 & K4) (A1 & A2 & A3 & A4 & _) Hslo Hshi HBb HnE Hfr EFA HnF.
split; [|split; [|split]].
- intros a Ha N1 N2 N3. rewrite <- (K1 a Ha N1 N2 N3). apply A1; [exact Ha | lia].
- intros b m i Hb Hi. rewrite <- (K2 b m i Hb Hi). apply (A2 b m i (HBb b m Hb) Hi). exact (HnE b m i Hb Hi).
- intros c p a Hcp Ha N2 N3. rewrite <- (K3 c p a Hcp Ha N2 N3).
apply (A4 c p a); [rewrite Hfr; exact Hcp | unfold frame_rng; cbn [fst snd]; rewrite !EFA; exact Ha | apply (HnF c p a Hcp Ha)].
- intros a Him Hns He. rewrite <- (K4 a Him Hns He). exact (A3 a Him Hns He).
Qed.
Lemma kept_of_frame : forall E rs H (m m' : word -> option byte) (Zs : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros E rs H m m' Zs HFR Hw a Ha Hn. apply (aview_eq_of tfibsegs). apply HFR. rewrite unsigned_lit_small by lia.
intros Hin. destruct (in_wrange_windows E rs a Hin) as (b & wlo & whi & Hi & Hr). exact (Hn (Hw b wlo whi a Hi Hr)).
Qed.
Lemma RA_kept_low : forall (rd1 rd2 : Z -> option Z) x n,
(forall a, 2147450880 <= a < kHighShadowEnd -> rd2 a = rd1 a) -> 0 <= x -> x + n <= kHighMemEnd ->
range_addressable rd1 SHADOW_OFF x n -> range_addressable rd2 SHADOW_OFF x n.
Proof.
intros rd1 rd2 x n Heq Hx1 Hx2 HRA. eapply range_addressable_agree; [|exact HRA]. intros y Hy. apply Heq.
pose proof (shadow_addr_bounds y ltac:(lia)). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold shadow_of_addr, shadow_addr in *. lia.
Qed.
Lemma RA_kept_frame : forall (rd1 rd2 : Z -> option Z) F cid x n,
(forall a, in_zr a (shadow_addr F, fs_frame_bytes cid / 8) -> rd2 a = rd1 a) ->
0 <= cid -> F mod 8 = 0 -> F <= x -> x + n <= F + fs_frame_bytes cid ->
range_addressable rd1 SHADOW_OFF x n -> range_addressable rd2 SHADOW_OFF x n.
Proof.
intros rd1 rd2 F cid x n Heq Hcid Hfal Hx1 Hx2 HRA. eapply range_addressable_agree; [|exact HRA]. intros y Hy. apply Heq.
unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
pose proof (Z.div_mod F 8 ltac:(lia)) as EF. rewrite Hfal, Z.add_0_r in EF.
unfold fs_frame_bytes in *. rewrite Z.shiftl_mul_pow2 in * by lia. replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) in * by lia. rewrite Z.div_mul in * by lia.
split.
- apply Zplus_le_compat_l. apply Z.div_le_lower_bound; lia.
- enough (y / 8 < F / 8 + 8 * 2 ^ cid) by lia. apply Z.div_lt_upper_bound; lia.
Qed.
Lemma frame_shadow_low : forall F cid a, 0 <= F -> F + fs_frame_bytes cid <= alloc_ceiling ->
in_zr a (shadow_addr F, fs_frame_bytes cid / 8) -> 2147450880 <= a < kHighShadowEnd.
Proof.
intros F cid a HF1 HF2 Ha. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (fs_frame_bytes_nonneg cid) as HFB.
unfold in_zr in Ha. cbn [fst snd] in Ha.
pose proof (shadow_range_end F (fs_frame_bytes cid) HFB) as SE.
pose proof (shadow_addr_bounds F ltac:(lia)) as SB1.
pose proof (shadow_addr_bounds (F + fs_frame_bytes cid) ltac:(lia)) as SB2. unfold kLowMemEnd in SB1, SB2. lia.
Qed.
Lemma RA_kept_call : forall ly S W1 m1 W2 m2 slo shi (Er : Z -> Prop) cid pos x n,
acall_kept tfibsegs B ly S W1 m1 W2 m2 slo shi Er -> In (cid, pos) (frames S) ->
(forall a, Er a -> a < 2147446784 \/ 17594333495296 <= a) -> 0 <= cid -> frame_addr ly cid pos mod 8 = 0 ->
0 <= frame_addr ly cid pos -> frame_addr ly cid pos + fs_frame_bytes cid <= alloc_ceiling ->
frame_addr ly cid pos <= x -> x + n <= frame_addr ly cid pos + fs_frame_bytes cid ->
range_addressable (aview tfibsegs (w_H W1) m1) SHADOW_OFF x n -> range_addressable (aview tfibsegs (w_H W2) m2) SHADOW_OFF x n.
Proof.
intros ly S W1 m1 W2 m2 slo shi Er cid pos x n (_ & _ & _ & K4 & _) Hfin HEr Hcid Hfal HF1 HF2 Hx1 Hx2 HRA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
eapply (RA_kept_frame _ _ (frame_addr ly cid pos) cid x n); [|exact Hcid|exact Hfal|exact Hx1|exact Hx2|exact HRA].
intros a Ha. apply (K4 cid pos a Hfin); [right; exact Ha|]. intros HE.
pose proof (frame_shadow_low _ _ _ HF1 HF2 Ha). pose proof (HEr a HE). pose proof (fs_frame_bytes_nonneg cid).
pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(unfold kHighMemEnd; lia)).
unfold in_zr, kLowMemEnd, kHighShadowEnd, kHighMemBeg, kHighMemEnd in *. cbn [fst snd] in Ha. lia.
Qed.
Lemma stack_cells8 : forall lo hi x, lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= x -> x + 8 <= hi -> lo mod 8 = 0 /\ (hi - lo) mod 8 = 0.
Proof.
intros lo hi x Hlo Hhi H1 H2.
pose proof (Z.div_mod lo 4096 ltac:(lia)) as A. pose proof (Z.div_mod hi 4096 ltac:(lia)) as C.
rewrite Hlo, Z.add_0_r in A. rewrite Hhi, Z.add_0_r in C. split.
- rewrite A. replace (4096 * (lo / 4096)) with ((512 * (lo / 4096)) * 8) by lia. apply Z_mod_mult.
- rewrite A, C. replace (4096 * (hi / 4096) - 4096 * (lo / 4096)) with ((512 * (hi / 4096) - 512 * (lo / 4096)) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma RA_stack : forall ly S W mem md x n,
AR tfibsegs B ly S W mem md -> ly_stk_lo ly <= x -> x + n <= ly_stk_hi ly -> x mod 8 = 0 -> n mod 8 = 0 -> 8 <= n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros ly S W mem md x n HAR Hlo Hhi Hx8 Hn8 Hn.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _). unfold page_aligned in Hpal, Hpah.
pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
destruct (stack_cells8 _ _ x Hpal Hpah ltac:(lia) ltac:(lia)) as [Hm1 Hm2].
eapply range_addressable_sub; [apply zero_shadow_range; [exact Hm1 | exact Hm2 | exact Hz] | lia | lia].
Qed.
End e.
End d.
Definition rboxed (P : Prop) : Prop := P.
Ltac rbox H := lazymatch type of H with ?T => change T with (rboxed T) in H end.
Ltac runbox := unfold rboxed in *.
Ltac evalER AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB;
first [ reflexivity
| lazymatch goal with |- _ = _ => lia | |- _ <= _ => lia | |- _ < _ => lia | |- _ <= _ < _ => lia | |- _ <= _ <= _ => lia | |- _ < _ <= _ => lia
| |- _ <> _ => lia | |- _ > _ => lia | |- _ >= _ => lia | |- ~ _ => lia | |- False => lia end
| idtac ].
Ltac awr_frame_obj n En Hown EFA :=
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ n);
[ reflexivity
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite En; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; eexists; eexists; split;
[exact Hown | left; unfold in_zr, frame_rng; cbn [fst snd]; try rewrite EFA; lia] | ].
Ltac awr_band_obj n En :=
lazymatch goal with |- awr_ok ?E _ _ ?sp0 _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ n (bv_unsigned (ew E n) - sp0));
[ reflexivity | lia
| cbn [YP09.r_wlo ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite En, unsigned_lit_small by lia; lia
| cbn [YP09.r_whi ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite En, unsigned_lit_small by lia; lia | ] end.
Ltac awrRFC Usp E10 E11 Hown EFA :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| lazymatch goal with
| |- awr_ok ?E (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (bv_unsigned (ew E 2%nat) - sp0));
[ reflexivity | lia
| cbn [YP09.r_wlo ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia
| cbn [YP09.r_whi ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia | ]
| |- awr_ok _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ => awr_band_obj 10%nat E10
| |- awr_ok _ (YP09.mkRegion (Some 11%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ => awr_frame_obj 11%nat E11 Hown EFA
end ].
Ltac awrI Usp Est Edst Hown EFA :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| lazymatch goal with
| |- awr_ok ?E (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (bv_unsigned (ew E 2%nat) - sp0));
[ reflexivity | lia
| cbn [YP09.r_wlo ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia
| cbn [YP09.r_whi ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia | ]
| |- awr_ok _ (YP09.mkRegion (Some 19%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ => awr_band_obj 19%nat Est
| |- awr_ok _ (YP09.mkRegion (Some 8%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ => awr_frame_obj 8%nat Edst Hown EFA
end ].
Ltac io_now :=
lazymatch goal with |- same_io _ ?m => first [is_evar m; fail 1 "io_now: the model is not determined yet" | idtac] end;
repeat (apply same_io_wvb); first [assumption | apply same_io_refl].
Ltac io_after H := eapply same_io_trans; [|exact H]; io_now.
