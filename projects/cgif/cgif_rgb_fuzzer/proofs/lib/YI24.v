(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YO3l YO3m YI00 YI02 YI01 YI03
YI1e YI1c YI39 YI1i YI20 YI2r YI59 YI56 YI0x YI57
YI1h YI16 YI1z YI1k YI21 YI22 YI23.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition t2_stk : list YQ0b.chunk := fl_stk_saved 32 ++ [mkChunk 112 (CVal 8 (SOff 45 0))].
Definition ss_p2x : sstate :=
mkSS FL_P2X sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 272 0 168 t2_stk ] None
(mkFacts [(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (12%nat, mkAF 0 16 0); (15%nat, mkAF 0 65535 0)] [] []).
Definition ss_T (z : bool) : sstate :=
mkSS FL_T sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 272 0 0 t2_stk ] None
(mkFacts [(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (15%nat, mkAF 0 65535 0)]
[mkAC (if z then BC_EQ else BC_NE) (SAlu ALU_AND (SOff 11 0) (SLit 1)) (SLit 0)] []).
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Hypothesis RAWADD : rawadd_spec API.
Definition t2_pre L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f : frame_st) (gen1 : Z)
(rest FP tmp : list (Z * Z)) (pTmp Nt tv w h top left : Z) : Prop :=
let sp0 := spZ regs0 in
journal src2_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac memc mdc /\ st_init_done Ac = true /\
YK0s.ret_ok (getr regs0 1) /\ sp0 mod 16 = 0 /\ getr regs0 4 = Z_to_bv 64 (ms_tp src2_msyms) /\
cgif_at memc g (flush_upd s i gen1 (rw_cur s)) /\ cgif_wf s N /\ (i = 1%nat \/ i = 2%nat) /\ nth_error (cg_frames s) i = Some (Some f) /\
(forall b' n a, In (b', n) (cgif_blocks g s N) -> b' <= a < b' + n -> inFP FP a) /\
Permutation (blocks Lc Ac) (tmp ++ cgif_blocks g s N ++ rest) /\
((tmp = [] /\ pTmp = 0) \/ (tmp = [(pTmp, Nt)] /\ pTmp <> 0 /\ w * h <= Nt)) /\
(In (pTmp, Nt) (blocks L A) -> forall k, 0 <= k < Nt -> inFP FP (pTmp + k)) /\
1 <= w /\ 0 <= left /\ left + w <= cg_W s /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H s /\ 0 <= tv < 2 ^ 64 /\
fl_saved_ok memc sp0 regs0 /\
word_mem src2segs memc (sp0 - 272 + 112) tv /\
getr regs1 2 = Z_to_bv 64 (sp0 - 272) /\ getr regs1 8 = Z_to_bv 64 g /\ getr regs1 9 = Z_to_bv 64 (fr_ptr f) /\
getr regs1 20 = Z_to_bv 64 (fr_ptr f + 26) /\ getr regs1 22 = Z_to_bv 64 pTmp /\
getr regs1 19 = Z_to_bv 64 (Z.land (fr_attr f) 1) /\ getr regs1 27 = Z_to_bv 64 (cg_W s) /\ getr regs1 14 = Z_to_bv 64 (cg_H s) /\
getr regs1 26 = Z_to_bv 64 h /\ getr regs1 16 = Z_to_bv 64 w /\ getr regs1 17 = Z_to_bv 64 top /\ getr regs1 5 = Z_to_bv 64 left /\
fl_untouched regs0 regs1.
Lemma fl_t2 :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st) (gen1 : Z)
(rest FP tmp : list (Z * Z)) (pTmp Nt tv w h top left p np : Z),
t2_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s i f gen1 rest FP tmp pTmp Nt tv w h top left ->
nth_error (cg_frames s) (i - 1) = Some (Some b) -> getr regs1 18 = Z_to_bv 64 (fr_ptr b) ->
getr regs1 12 = Z_to_bv 64 p -> 0 <= p <= 16 -> getr regs1 15 = Z_to_bv 64 np -> 0 <= np <= 65535 ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_P2X) memc (seg_rom src2segs)) mdc) (fl_post API regs0 g s N i rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tmp pTmp Nt tv w h top left p np
(HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & HFP & HB & Htmp & Htmp_fp & Hw & Hl0 & Hlw & Hh & Ht0 & Hth & Htv & HSV & Wtv
& G2 & G8 & G9 & G20 & G22 & G19 & G27 & G14 & G26 & G16 & G17 & G5 & G3 & G4) Hb G18 G12 Hp G15 Hnp.
set (sp0 := spZ regs0) in *.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & _).
pose proof Hat as (Hobj & _ & _). rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s)) in Hobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. cbn [nth snd LAY_CGIF Z.of_N] in RW.
set (E := Ereg regs1 (map (Z_to_bv 64) (fl_saved_vals regs0 ++ [tv]) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HA : forall j v, nth_error (fl_saved_vals regs0 ++ [tv]) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HK : forall j v, nth_error (fl_saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. apply HA. rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate. }
assert (HE45 : ew E 45 = Z_to_bv 64 tv) by (apply (HA 13%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HR0 : region_ok src2segs E memc (YQ0b.mkRegion (Some 2%nat) 0 272 0 168 t2_stk)).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
unfold t2_stk. apply Forall_app; split; [apply (fl_saved_chunks_ok E memc sp0 regs0 32 HSV); intros j v Hj; exact (HK j v Hj)|].
constructor; [| constructor].
eapply (chunk_ok_val _ _ _ _ _ _ _ tv); [cbn [sv_denot]; rewrite Z.add_0_r, HE45, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wtv]. }
assert (HFA : atoms_ok E [(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (12%nat, mkAF 0 16 0); (15%nat, mkAF 0 65535 0)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, (HE 12%nat 12%bv eq_refl), (HE 15%nat 15%bv eq_refl), G12, G15, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. try pose proof (proj1 alloc_ceiling_val) as HacR; clear - HacR Hceil Hsp063 Hal16 Hp Hnp HFSv. repeat split; try lia.
replace (sp0 - 272) with (sp0 + (-17) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HS : st_ok src2segs E ss_p2x (mkst regs1 (Z_to_bv 64 FL_P2X) memc (seg_rom src2segs))).
{ unfold ss_p2x. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [exact HR0 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | split; [exact HFA | split; exact I]]. }
clear HR0 HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_P2X) memc (seg_rom src2segs))) in HJ.
assert (WR : forall E0 cs, bv_unsigned (ew E0 2) = sp0 - 272 -> wr_ok E0 [YQ0b.mkRegion (Some 2%nat) 0 272 0 168 cs] FLUSH_STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E0 cs H2. eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; lia | apply wr_ok_nil]. }
assert (GO : forall ss ms' rg0 (e : sv), st_ok src2segs E ss ms' -> ss_pc ss = FL_T2B -> ss_resv ss = None ->
nth_error (ss_mem ss) 0 = Some rg0 -> r_base rg0 = Some 2%nat ->
In (mkChunk 112 (CVal 8 e)) (r_chunks rg0) ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [2; 3; 4; 17; 5; 8; 9; 14; 26; 16; 18; 20; 22; 27; 19]%bv = true ->
journal src2_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte src2segs (ms_mem ms') a = mbyte src2segs memc a) ->
SR src2segs (mkCfg ms' mdc) (fl_post API regs0 g s N i rest FP L A mem md)).
{ intros ss ms' rg0 e HS' Hpc Hrv Hrg0 Hb0 Hin112 Hkl HJ' K.
pose proof (regs_kept_of_st_ok src2segs _ ss ms' regs1 _ _ HS' (env_agree_refl _ _) Hkl) as R.
pose proof (st_region_chunks src2segs E ss ms' 0 rg0 2%nat (sp0 - 272) HS' Hrg0 Hb0 HU2) as Hcs.
rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc.
eapply (fl_t2b API IMG RAWADD L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s i f b gen1 rest FP tmp pTmp Nt (U E e) w h top left);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hi | exact Hf | exact Hb | exact HFP | exact HB | exact Htmp | exact Htmp_fp
| exact Hw | exact Hl0 | exact Hlw | exact Hh | exact Ht0 | exact Hth | apply U_range
| apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply K; clear - Ha Hceil Hsp063 HFSv Hac; lia]
| apply (chunk_word E _ _ 112 _ _ (proj1 (Forall_forall _ _) Hcs _ Hin112)); [apply denot_of_U'; reflexivity | apply U_range]
| rewrite (R 2%bv ltac:(cbv; auto 50)); exact G2 | rewrite (R 8%bv ltac:(cbv; auto 50)); exact G8 | rewrite (R 9%bv ltac:(cbv; auto 50)); exact G9
| rewrite (R 18%bv ltac:(cbv; auto 50)); exact G18 | rewrite (R 20%bv ltac:(cbv; auto 50)); exact G20 | rewrite (R 22%bv ltac:(cbv; auto 50)); exact G22
| rewrite (R 19%bv ltac:(cbv; auto 50)); exact G19 | rewrite (R 27%bv ltac:(cbv; auto 50)); exact G27 | rewrite (R 14%bv ltac:(cbv; auto 50)); exact G14
| rewrite (R 26%bv ltac:(cbv; auto 50)); exact G26 | rewrite (R 16%bv ltac:(cbv; auto 50)); exact G16 | rewrite (R 17%bv ltac:(cbv; auto 50)); exact G17
| rewrite (R 5%bv ltac:(cbv; auto 50)); exact G5
| split; [rewrite (R 3%bv ltac:(cbv; auto 50)); exact G3 | rewrite (R 4%bv ltac:(cbv; auto 50)); exact G4] ].
assert (KB : forall bb nn k, In (bb, nn) (cgif_blocks g s N) -> 0 <= k < nn -> mbyte src2segs (ms_mem ms') (bb + k) = mbyte src2segs memc (bb + k)).
{ intros bb nn k Hbn Hk.
assert (Hbn' : In (bb, nn) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; right; apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0 R1]. apply K; clear - R0 R1 Hk Hceil HFSv Hac; lia. }
eapply (cgif_at_kept memc _ g (flush_upd s i gen1 (rw_cur s)) N (cgif_blocks g s N ++ []) []); [rewrite (cgif_blocks_flush_upd g s N i gen1 (rw_cur s) f Hf); apply Permutation_refl | exact Hat |].
intros bb nn k Hbn Hk. rewrite app_nil_r in Hbn. exact (KB bb nn k Hbn Hk). }
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte src2segs memc a = mbyte src2segs memc a) by (intros; reflexivity).
br_tree ltac:(idtac; runW LAWS FL_T2B ltac:(apply WR; exact HU2) HU2 (sp0 - 272) (sp0 - 272 + 168))
ltac:(idtac; let HS := get_HS in let HJ := get_HJ in
lazymatch goal with K : forall a, _ -> _ -> mbyte src2segs _ a = mbyte src2segs memc a |- _ =>
eapply (GO _ _ _ _ HS); [ reflexivity | reflexivity | reflexivity | reflexivity
| cbn [r_chunks]; repeat (first [left; reflexivity | right])
| vm_compute; reflexivity | exact HJ | exact K ] end)
4%nat.
Qed.
Lemma fl_trans :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f : frame_st) (gen1 : Z)
(rest FP tmp : list (Z * Z)) (pTmp Nt tv w h top left np : Z),
t2_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s i f gen1 rest FP tmp pTmp Nt tv w h top left ->
forall g13, getr regs1 11 = Z_to_bv 64 g13 -> 0 <= g13 < 2 ^ 64 -> getr regs1 15 = Z_to_bv 64 np -> 0 <= np <= 65535 ->
(Z.land g13 1 <> 0 -> exists b, nth_error (cg_frames s) (i - 1) = Some (Some b) /\ getr regs1 18 = Z_to_bv 64 (fr_ptr b)) ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_T) memc (seg_rom src2segs)) mdc) (fl_post API regs0 g s N i rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f gen1 rest FP tmp pTmp Nt tv w h top left np PRE g13 G11 Hgen G15 Hnp Hbx.
pose proof PRE as (HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & HFP & HB & Htmp & Htmp_fp & Hw & Hl0 & Hlw & Hh & Ht0 & Hth & Htv & HSV & Wtv
& G2 & G8 & G9 & G20 & G22 & G19 & G27 & G14 & G26 & G16 & G17 & G5 & G3 & G4).
set (sp0 := spZ regs0) in *.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & _).
pose proof Hat as (Hobj & _ & _). rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s)) in Hobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. cbn [nth snd LAY_CGIF Z.of_N] in RW.
set (E := Ereg regs1 (map (Z_to_bv 64) (fl_saved_vals regs0 ++ [tv]) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HA : forall j v, nth_error (fl_saved_vals regs0 ++ [tv]) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HK : forall j v, nth_error (fl_saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. apply HA. rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate. }
assert (HE45 : ew E 45 = Z_to_bv 64 tv) by (apply (HA 13%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HR0 : region_ok src2segs E memc (YQ0b.mkRegion (Some 2%nat) 0 272 0 0 t2_stk)).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
unfold t2_stk. apply Forall_app; split; [apply (fl_saved_chunks_ok E memc sp0 regs0 32 HSV); intros j v Hj; exact (HK j v Hj)|].
constructor; [| constructor].
eapply (chunk_ok_val _ _ _ _ _ _ _ tv); [cbn [sv_denot]; rewrite Z.add_0_r, HE45, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wtv]. }
assert (HFA : atoms_ok E [(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (15%nat, mkAF 0 65535 0)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, (HE 15%nat 15%bv eq_refl), G15, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. try pose proof (proj1 alloc_ceiling_val) as HacR; clear - HacR Hceil Hsp063 Hal16 Hnp HFSv. repeat split; try lia.
replace (sp0 - 272) with (sp0 + (-17) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HCF : forall z : bool, (if z then Z.land g13 1 = 0 else Z.land g13 1 <> 0) ->
conds_ok E [mkAC (if z then BC_EQ else BC_NE) (SAlu ALU_AND (SOff 11 0) (SLit 1)) (SLit 0)]).
{ intros z Hz. cbn [conds_ok]. split; [|exact I]. unfold acond_ok.
destruct z; cbn [ac_c ac_a ac_b]; rewrite ?branch_eq_U, ?branch_ne_U, U_and_lit, U_lit, (U_atom _ 11 g13 ltac:(rewrite (HE 11%nat 11%bv eq_refl); exact G11)) by lia;
[rewrite Hz; reflexivity | destruct (Z.eqb_spec (Z.land g13 1) 0); [lia | reflexivity]]. }
assert (MK : forall z : bool, (if z then Z.land g13 1 = 0 else Z.land g13 1 <> 0) ->
st_ok src2segs E (ss_T z) (mkst regs1 (Z_to_bv 64 FL_T) memc (seg_rom src2segs))).
{ intros z Hz. unfold ss_T. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; destruct z; reflexivity | constructor; [exact HR0 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | split; [exact HFA | split; [exact (HCF z Hz) | exact I]]]. }
clear HR0 HFA HCF.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_T) memc (seg_rom src2segs))) in HJ.
destruct (Z.eq_dec (Z.land g13 1) 0) as [Hz | Hz].
-
pose proof (MK true Hz) as HS. clear MK.
jrun_to LAWS src2tbl_ok HS HJ FL_RAW. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs Ef ssf msf regs1 _ [2; 3; 4; 8; 9; 26; 16; 20; 22; 19]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as R end.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply (fl_tail API IMG RAWADD L A mem md regs0 (ms_regs ms) Lc Ac (ms_mem ms) mdc g N s i f gen1 rest FP tmp pTmp Nt tv w h FL_RAW);
[ exact HJ | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hi | exact Hf | exact HFP | exact HB
| destruct Htmp as [[A1 A2] | (A1 & A2 & A3)]; [left; split; [exact A1 | split; [exact A2 | rewrite HN; clear - Hw Hlw Hl0 Hh Hth Ht0; nia]] | right; auto]
| exact Htmp_fp | left; reflexivity
| clear - Hw Hlw Hl0; lia | clear - Hh Hth Ht0; lia | exact Htv
| apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply mbyte_of_eq; exact K1]
| intros k Hk; rewrite (mbyte_of_eq _ _ _ _ K1); exact (Wtv k Hk)
| rewrite (R 2%bv ltac:(cbv; auto 50)); exact G2 | rewrite (R 8%bv ltac:(cbv; auto 50)); exact G8 | rewrite (R 9%bv ltac:(cbv; auto 50)); exact G9
| rewrite (R 20%bv ltac:(cbv; auto 50)); exact G20 | rewrite (R 22%bv ltac:(cbv; auto 50)); exact G22 | rewrite (R 19%bv ltac:(cbv; auto 50)); exact G19
| rewrite (R 16%bv ltac:(cbv; auto 50)); exact G16 | rewrite (R 26%bv ltac:(cbv; auto 50)); exact G26
| split; [rewrite (R 3%bv ltac:(cbv; auto 50)); exact G3 | rewrite (R 4%bv ltac:(cbv; auto 50)); exact G4] ].
eapply (cgif_at_kept memc _ g (flush_upd s i gen1 (rw_cur s)) N (cgif_blocks g s N ++ []) []); [rewrite (cgif_blocks_flush_upd g s N i gen1 (rw_cur s) f Hf); apply Permutation_refl | exact Hat |].
intros bb nn k Hbn Hk. apply mbyte_of_eq. exact K1.
-
destruct (Hbx Hz) as (b & Hb & G18).
pose proof (MK false Hz) as HS. clear MK.
jrun_to LAWS src2tbl_ok HS HJ FL_P2. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs Ef ssf msf regs1 _ [2; 3; 4; 17; 5; 8; 9; 14; 15; 26; 16; 18; 20; 22; 27; 19]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as R end.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (fl_pow2 API IMG 17%nat 0 FLUSH_STK sp0 FP L A mem md Lc Ac mdc (ms_regs ms) (ms_mem ms) np HJ ltac:(clear; lia) eq_refl Hnp).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(reflexivity).
- rewrite (R 15%bv ltac:(cbv; auto 50)). exact G15. }
cbv beta. intros c' (regs2 & mem2 & p & -> & Hm2 & HJ2 & Gp & Hp & HK2).
assert (R2 : forall r : reg, In r [2; 3; 4; 17; 5; 8; 9; 14; 15; 26; 16; 18; 20; 22; 27; 19]%bv -> getr regs2 r = getr regs1 r).
{ intros rr Hrr. rewrite <- (R rr Hrr). apply HK2. cbv in Hrr. repeat (destruct Hrr as [<- | Hrr]; [cbv; auto 50 |]). destruct Hrr. }
assert (Km : forall x, mem2 x = memc x) by (intros x; rewrite Hm2; apply K1).
eapply (fl_t2 L A mem md regs0 regs2 Lc Ac mem2 mdc g N s i f b gen1 rest FP tmp pTmp Nt tv w h top left p np); [| exact Hb | | exact Gp | exact Hp | | exact Hnp].
2:{ rewrite (R2 18%bv ltac:(cbv; auto 50)). exact G18. }
2:{ rewrite (R2 15%bv ltac:(cbv; auto 50)). exact G15. }
split; [exact HJ2|]. split; [exact Hid|]. split; [exact Hra0|]. split; [exact Hal16|]. split; [exact Htp0|].
split.
{ eapply (cgif_at_kept memc _ g (flush_upd s i gen1 (rw_cur s)) N (cgif_blocks g s N ++ []) []); [rewrite (cgif_blocks_flush_upd g s N i gen1 (rw_cur s) f Hf); apply Permutation_refl | exact Hat |].
intros bb nn k Hbn Hk. apply mbyte_of_eq. exact Km. }
split; [exact Hwf|]. split; [exact Hi|]. split; [exact Hf|]. split; [exact HFP|]. split; [exact HB|]. split; [exact Htmp|]. split; [exact Htmp_fp|].
split; [exact Hw|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh|]. split; [exact Ht0|]. split; [exact Hth|]. split; [exact Htv|].
split; [apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply mbyte_of_eq; exact Km]|].
split; [intros k Hk; rewrite (mbyte_of_eq _ _ _ _ Km); exact (Wtv k Hk)|].
split; [rewrite (R2 2%bv ltac:(cbv; auto 50)); exact G2|]. split; [rewrite (R2 8%bv ltac:(cbv; auto 50)); exact G8|]. split; [rewrite (R2 9%bv ltac:(cbv; auto 50)); exact G9|].
split; [rewrite (R2 20%bv ltac:(cbv; auto 50)); exact G20|]. split; [rewrite (R2 22%bv ltac:(cbv; auto 50)); exact G22|].
split; [rewrite (R2 19%bv ltac:(cbv; auto 50)); exact G19|]. split; [rewrite (R2 27%bv ltac:(cbv; auto 50)); exact G27|]. split; [rewrite (R2 14%bv ltac:(cbv; auto 50)); exact G14|].
split; [rewrite (R2 26%bv ltac:(cbv; auto 50)); exact G26|]. split; [rewrite (R2 16%bv ltac:(cbv; auto 50)); exact G16|].
split; [rewrite (R2 17%bv ltac:(cbv; auto 50)); exact G17|]. split; [rewrite (R2 5%bv ltac:(cbv; auto 50)); exact G5|].
split; [rewrite (R2 3%bv ltac:(cbv; auto 50)); exact G3 | rewrite (R2 4%bv ltac:(cbv; auto 50)); exact G4].
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
