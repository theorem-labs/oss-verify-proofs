(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3l UO3m YI00 YI02 YI01 YI03
UI1e UI1c UI39 UI1i UI20 UI2r UI59 UI56 YI0x UI57
UI1h UI16 UI1z UI1k UI21 UI22 UI23.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition t2_stk : list YQ0b.chunk := fl_stk_saved 32.
Definition ss_p2x : sstate :=
mkSS FL_P2X sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 272 0 0 t2_stk ] None
(mkFacts [(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (10%nat, mkAF 0 16 0); (20%nat, mkAF 0 65535 0)] [] []).
Definition ss_T (z : bool) : sstate :=
mkSS FL_T sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 272 0 0 t2_stk ] None
(mkFacts [(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (20%nat, mkAF 0 65535 0)]
[mkAC (if z then BC_EQ else BC_NE) (SAlu ALU_AND (SOff 11 0) (SLit 1)) (SLit 0)] []).
Lemma t2_chk : forall E p, ew E 10 = Z_to_bv 64 p -> 0 <= p <= 16 ->
branch_taken BC_GE (sv_denot E (SAluw ALU_ADD (SAluw ALU_SLL (SLit 1) (SAlu ALU_AND (SOff 10 0) (SLit 255))) (SLit (-1)))) (sv_denot E (SAluw ALU_SLL (SLit 1) (SAlu ALU_AND (SOff 10 0) (SLit 255)))) = false /\
branch_taken BC_LT (sv_denot E (SAluw ALU_ADD (SAluw ALU_SLL (SLit 1) (SAlu ALU_AND (SOff 10 0) (SLit 255))) (SLit (-1)))) (sv_denot E (SAluw ALU_SLL (SLit 1) (SAlu ALU_AND (SOff 10 0) (SLit 255)))) = true /\
branch_taken BC_GE (sv_denot E (SAluw ALU_ADD (SAluw ALU_SLL (SLit 2) (SAlu ALU_AND (SOff 10 0) (SLit 255))) (SLit (-1)))) (sv_denot E (SAluw ALU_SLL (SLit 2) (SAlu ALU_AND (SOff 10 0) (SLit 255)))) = false /\
branch_taken BC_LT (sv_denot E (SAluw ALU_ADD (SAluw ALU_SLL (SLit 2) (SAlu ALU_AND (SOff 10 0) (SLit 255))) (SLit (-1)))) (sv_denot E (SAluw ALU_SLL (SLit 2) (SAlu ALU_AND (SOff 10 0) (SLit 255)))) = true /\
U E (SAluw ALU_ADD (SAluw ALU_SLL (SLit 1) (SAlu ALU_AND (SOff 10 0) (SLit 255))) (SLit (-1))) = 2 ^ p - 1 /\
U E (SAluw ALU_ADD (SAluw ALU_SLL (SLit 2) (SAlu ALU_AND (SOff 10 0) (SLit 255))) (SLit (-1))) = 2 ^ (p + 1) - 1.
Proof.
intros E p H10 Hp. unfold U. cbn [sv_denot]. rewrite H10.
assert (Hk : exists k, p = Z.of_nat k /\ (k <= 16)%nat) by (exists (Z.to_nat p); split; lia).
destruct Hk as (k & -> & Hk). clear Hp.
do 17 (destruct k as [|k]; [vm_compute; repeat split; reflexivity|]). exfalso; lia.
Qed.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis RAWADD : rawadd_spec API.
Definition t2_pre L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f : frame_st) (gen1 : Z)
(rest FP tmp : list (Z * Z)) (pTmp Nt tv w h top left : Z) : Prop :=
let sp0 := spZ regs0 in
journal ubs2_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac memc mdc /\ st_init_done Ac = true /\
YK0s.ret_ok (getr regs0 1) /\ sp0 mod 16 = 0 /\ getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) /\
cgif_at memc g (flush_upd s i gen1 (rw_cur s)) /\ cgif_wf s N /\ (i = 1%nat \/ i = 2%nat) /\ nth_error (cg_frames s) i = Some (Some f) /\
(forall b' n a, In (b', n) (cgif_blocks g s N) -> b' <= a < b' + n -> inFP FP a) /\
Permutation (blocks Lc Ac) (tmp ++ cgif_blocks g s N ++ rest) /\
((tmp = [] /\ pTmp = 0) \/ (tmp = [(pTmp, Nt)] /\ pTmp <> 0 /\ w * h <= Nt)) /\
(In (pTmp, Nt) (blocks L A) -> forall k, 0 <= k < Nt -> inFP FP (pTmp + k)) /\
1 <= w /\ 0 <= left /\ left + w <= cg_W s /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H s /\ 0 <= tv < 2 ^ 64 /\
fl_saved_ok memc sp0 regs0 /\
getr regs1 9 = Z_to_bv 64 tv /\
getr regs1 2 = Z_to_bv 64 (sp0 - 272) /\ word_mem ubs2segs memc (sp0 - 272 + 112) g /\ word_mem ubs2segs memc (sp0 - 272 + 120) (fr_ptr f) /\
getr regs1 8 = Z_to_bv 64 pTmp /\
word_mem ubs2segs memc (sp0 - 272 + 56) (Z.land (fr_attr f) 1) /\ getr regs1 27 = Z_to_bv 64 (cg_W s) /\ word_mem ubs2segs memc (sp0 - 272 + 104) (cg_W s) /\
getr regs1 19 = Z_to_bv 64 (cg_H s) /\
getr regs1 16 = Z_to_bv 64 h /\ getr regs1 23 = Z_to_bv 64 w /\ word_mem ubs2segs memc (sp0 - 272 + 96) top /\ getr regs1 22 = Z_to_bv 64 left /\
fl_untouched regs0 regs1.
Lemma fl_t2 :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st) (gen1 : Z)
(rest FP tmp : list (Z * Z)) (pTmp Nt tv w h top left p np : Z),
t2_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s i f gen1 rest FP tmp pTmp Nt tv w h top left ->
nth_error (cg_frames s) (i - 1) = Some (Some b) -> getr regs1 18 = Z_to_bv 64 (fr_ptr b) ->
getr regs1 10 = Z_to_bv 64 p -> 0 <= p <= 16 -> getr regs1 20 = Z_to_bv 64 np -> 0 <= np <= 65535 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_P2X) memc (seg_rom ubs2segs)) mdc) (fl_post API regs0 g s N i rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tmp pTmp Nt tv w h top left p np
(HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & HFP & HB & Htmp & Htmp_fp & Hw & Hl0 & Hlw & Hh & Ht0 & Hth & Htv & HSV & G9
& G2 & W112 & W120 & G8 & W56 & G27 & W104 & G19 & G16 & G23 & W96 & G22 & G3 & G4) Hb G18 G10 Hp G20 Hnp.
set (sp0 := spZ regs0) in *.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & _).
pose proof Hat as (Hobj & _ & _). rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s)) in Hobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. cbn [nth snd LAY_CGIF Z.of_N] in RW.
set (E := Ereg regs1 (map (Z_to_bv 64) (fl_saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HK : forall j v, nth_error (fl_saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 0 272 0 0 t2_stk)).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
unfold t2_stk. apply (fl_saved_chunks_ok E memc sp0 regs0 32 HSV); intros j v Hj; exact (HK j v Hj). }
assert (HFA : atoms_ok E [(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (10%nat, mkAF 0 16 0); (20%nat, mkAF 0 65535 0)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, (HE 10%nat 10%bv eq_refl), (HE 20%nat 20%bv eq_refl), G10, G20, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. try pose proof (proj1 alloc_ceiling_val) as HacR; clear - HacR Hceil Hsp063 Hal16 Hp Hnp HFSv. repeat split; try lia.
replace (sp0 - 272) with (sp0 + (-17) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HS : st_ok ubs2segs E ss_p2x (mkst regs1 (Z_to_bv 64 FL_P2X) memc (seg_rom ubs2segs))).
{ unfold ss_p2x. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [exact HR0 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | split; [exact HFA | split; exact I]]. }
clear HR0 HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_P2X) memc (seg_rom ubs2segs))) in HJ.
assert (WR : forall E0 cs, bv_unsigned (ew E0 2) = sp0 - 272 -> wr_ok E0 [YQ0b.mkRegion (Some 2%nat) 0 272 0 0 cs] FLUSH_STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E0 cs H2. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (HE10 : ew E 10 = Z_to_bv 64 p) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
pose proof (t2_chk E p HE10 Hp) as (K1g & _ & K2g & _ & _ & _).
assert (GO : forall ss ms', st_ok ubs2segs E ss ms' -> ss_pc ss = FL_T2B -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [2; 3; 4; 8; 16; 18; 19; 22; 23; 27]%bv = true ->
journal ubs2_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272) -> mbyte ubs2segs (ms_mem ms') a = mbyte ubs2segs memc a) ->
SR ubs2segs (mkCfg ms' mdc) (fl_post API regs0 g s N i rest FP L A mem md)).
{ intros ss ms' HS' Hpc Hrv Hkl HJ' K.
pose proof (regs_kept_of_st_ok ubs2segs _ ss ms' regs1 _ _ HS' (env_agree_refl _ _) Hkl) as R.
assert (KW : forall o v, word_mem ubs2segs memc (sp0 - 272 + o) v -> 0 <= o <= 264 -> word_mem ubs2segs (ms_mem ms') (sp0 - 272 + o) v).
{ intros o v Hv Ho k Hk. rewrite <- (Hv k Hk). apply K; clear - Ho Hk Hceil Hsp063 HFSv Hac; lia. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc.
eapply (fl_t2b API IMG RAWADD L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s i f b gen1 rest FP tmp pTmp Nt (U E (sr_get (ss_regs ss) 9%bv)) w h top left);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hi | exact Hf | exact Hb | exact HFP | exact HB | exact Htmp | exact Htmp_fp
| exact Hw | exact Hl0 | exact Hlw | exact Hh | exact Ht0 | exact Hth | apply U_range
| apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply K; clear - Ha Hceil Hsp063 HFSv Hac; lia]
| rewrite (st_ok_reg ubs2segs E ss ms' 9%bv HS'); apply denot_of_U'; reflexivity
| rewrite (R 2%bv ltac:(cbv; auto 50)); exact G2 | apply KW; [exact W112 | lia] | apply KW; [exact W120 | lia]
| rewrite (R 18%bv ltac:(cbv; auto 50)); exact G18 | rewrite (R 8%bv ltac:(cbv; auto 50)); exact G8
| apply KW; [exact W56 | lia] | rewrite (R 27%bv ltac:(cbv; auto 50)); exact G27 | apply KW; [exact W104 | lia]
| rewrite (R 19%bv ltac:(cbv; auto 50)); exact G19
| rewrite (R 16%bv ltac:(cbv; auto 50)); exact G16 | rewrite (R 23%bv ltac:(cbv; auto 50)); exact G23 | apply KW; [exact W96 | lia]
| rewrite (R 22%bv ltac:(cbv; auto 50)); exact G22
| split; [rewrite (R 3%bv ltac:(cbv; auto 50)); exact G3 | rewrite (R 4%bv ltac:(cbv; auto 50)); exact G4] ].
assert (KB : forall bb nn k, In (bb, nn) (cgif_blocks g s N) -> 0 <= k < nn -> mbyte ubs2segs (ms_mem ms') (bb + k) = mbyte ubs2segs memc (bb + k)).
{ intros bb nn k Hbn Hk.
assert (Hbn' : In (bb, nn) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; right; apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0 R1]. apply K; clear - R0 R1 Hk Hceil HFSv Hac; lia. }
eapply (cgif_at_kept memc _ g (flush_upd s i gen1 (rw_cur s)) N (cgif_blocks g s N ++ []) []); [rewrite (cgif_blocks_flush_upd g s N i gen1 (rw_cur s) f Hf); apply Permutation_refl | exact Hat |].
intros bb nn k Hbn Hk. rewrite app_nil_r in Hbn. exact (KB bb nn k Hbn Hk). }
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272) -> mbyte ubs2segs memc a = mbyte ubs2segs memc a) by (intros; reflexivity).
br_tree ltac:(idtac; runW LAWS FL_T2B ltac:(apply WR; exact HU2) HU2 (sp0 - 272) (sp0 - 272))
ltac:(idtac; let HS := get_HS in let HJ := get_HJ in
lazymatch goal with K : forall a, _ -> _ -> mbyte ubs2segs _ a = mbyte ubs2segs memc a |- _ =>
first
[ eapply (GO _ _ HS); [ reflexivity | reflexivity | vm_compute; reflexivity | exact HJ | exact K ]
| solve [ exfalso; generalize (proj1 (proj2 (st_ok_facts_ok ubs2segs E _ _ HS))); cbn [ss_facts f_conds conds_ok]; unfold acond_ok; cbn [ac_c ac_a ac_b];
rewrite ?K1g, ?K2g; intros Hcs; repeat (lazymatch type of Hcs with _ /\ _ => let X := fresh "X" in destruct Hcs as [X Hcs]; try discriminate X end) ] ] end)
6%nat.
Qed.
Lemma fl_trans :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f : frame_st) (gen1 : Z)
(rest FP tmp : list (Z * Z)) (pTmp Nt tv w h top left np : Z),
t2_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s i f gen1 rest FP tmp pTmp Nt tv w h top left ->
forall g13, getr regs1 11 = Z_to_bv 64 g13 -> 0 <= g13 < 2 ^ 64 -> getr regs1 20 = Z_to_bv 64 np -> 0 <= np <= 65535 ->
(Z.land g13 1 <> 0 -> exists b, nth_error (cg_frames s) (i - 1) = Some (Some b) /\ getr regs1 18 = Z_to_bv 64 (fr_ptr b)) ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_T) memc (seg_rom ubs2segs)) mdc) (fl_post API regs0 g s N i rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f gen1 rest FP tmp pTmp Nt tv w h top left np PRE g13 G11 Hgen G20 Hnp Hbx.
pose proof PRE as (HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & HFP & HB & Htmp & Htmp_fp & Hw & Hl0 & Hlw & Hh & Ht0 & Hth & Htv & HSV & G9
& G2 & W112 & W120 & G8 & W56 & G27 & W104 & G19 & G16 & G23 & W96 & G22 & G3 & G4).
set (sp0 := spZ regs0) in *.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & _).
pose proof Hat as (Hobj & _ & _). rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s)) in Hobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. cbn [nth snd LAY_CGIF Z.of_N] in RW.
set (E := Ereg regs1 (map (Z_to_bv 64) (fl_saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HK : forall j v, nth_error (fl_saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 0 272 0 0 t2_stk)).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
unfold t2_stk. apply (fl_saved_chunks_ok E memc sp0 regs0 32 HSV); intros j v Hj; exact (HK j v Hj). }
assert (HFA : atoms_ok E [(2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (20%nat, mkAF 0 65535 0)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, (HE 20%nat 20%bv eq_refl), G20, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. try pose proof (proj1 alloc_ceiling_val) as HacR; clear - HacR Hceil Hsp063 Hal16 Hnp HFSv. repeat split; try lia.
replace (sp0 - 272) with (sp0 + (-17) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HCF : forall z : bool, (if z then Z.land g13 1 = 0 else Z.land g13 1 <> 0) ->
conds_ok E [mkAC (if z then BC_EQ else BC_NE) (SAlu ALU_AND (SOff 11 0) (SLit 1)) (SLit 0)]).
{ intros z Hz. cbn [conds_ok]. split; [|exact I]. unfold acond_ok.
destruct z; cbn [ac_c ac_a ac_b]; rewrite ?branch_eq_U, ?branch_ne_U, U_and_lit, U_lit, (U_atom _ 11 g13 ltac:(rewrite (HE 11%nat 11%bv eq_refl); exact G11)) by lia;
[rewrite Hz; reflexivity | destruct (Z.eqb_spec (Z.land g13 1) 0); [lia | reflexivity]]. }
assert (MK : forall z : bool, (if z then Z.land g13 1 = 0 else Z.land g13 1 <> 0) ->
st_ok ubs2segs E (ss_T z) (mkst regs1 (Z_to_bv 64 FL_T) memc (seg_rom ubs2segs))).
{ intros z Hz. unfold ss_T. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; destruct z; reflexivity | constructor; [exact HR0 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | split; [exact HFA | split; [exact (HCF z Hz) | exact I]]]. }
clear HR0 HFA HCF.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_T) memc (seg_rom ubs2segs))) in HJ.
destruct (Z.eq_dec (Z.land g13 1) 0) as [Hz | Hz].
-
pose proof (MK true Hz) as HS. clear MK.
jrun_to LAWS ubs2tbl_ok HS HJ FL_RAW. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
assert (KW : forall a v, word_mem ubs2segs memc a v -> word_mem ubs2segs (ms_mem ms) a v) by (intros a v Hv k Hk; rewrite (mbyte_of_eq _ _ _ _ K1); exact (Hv k Hk)).
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs1 _ [2; 3; 4; 8; 9; 16; 22; 23]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as R end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply (fl_tail API IMG RAWADD) with (f := f) (gen1 := gen1) (tmp := tmp) (pTmp := pTmp) (Nt := Nt) (tv := tv) (w := w) (h := h) (pc := FL_RAW) (top := top) (left := left).
all: first
[ exact HJ | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | exact Hwf | exact Hi | exact Hf | exact HFP | exact HB | exact Htmp_fp | exact Htv
| left; reflexivity
| destruct Htmp as [[A1 A2] | (A1 & A2 & A3)]; [left; split; [exact A1 | split; [exact A2 | rewrite HN; clear - Hw Hlw Hl0 Hh Hth Ht0; nia]] | right; auto]
| clear - Hw Hlw Hl0 Hh Hth Ht0; lia
| apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply mbyte_of_eq; exact K1]
| apply KW; assumption
| intros Hc; exfalso; unfold FL_RAW, FL_RAW2 in Hc; lia
| intros _; repeat split; lazymatch goal with |- getr _ ?r = _ => rewrite (R r ltac:(cbv; auto 50)); assumption end
| lazymatch goal with |- getr _ ?r = _ => rewrite (R r ltac:(cbv; auto 50)); assumption end
| split; lazymatch goal with |- getr _ ?r = _ => rewrite (R r ltac:(cbv; auto 50)); assumption end
| eapply (cgif_at_kept memc _ g (flush_upd s i gen1 (rw_cur s)) N (cgif_blocks g s N ++ []) []);
[rewrite (cgif_blocks_flush_upd g s N i gen1 (rw_cur s) f Hf); apply Permutation_refl | exact Hat | intros bb nn k Hbn Hk; apply mbyte_of_eq; exact K1] ].
-
destruct (Hbx Hz) as (b & Hb & G18).
pose proof (MK false Hz) as HS. clear MK.
jrun_to LAWS ubs2tbl_ok HS HJ FL_P2. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs1 _ [2; 3; 4; 8; 9; 16; 18; 19; 20; 22; 23; 27]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as R end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (fl_pow2 API IMG 17%nat 0 FLUSH_STK sp0 FP L A mem md Lc Ac mdc (ms_regs ms) (ms_mem ms) np HJ ltac:(clear; lia) eq_refl Hnp).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(reflexivity).
- rewrite (R 20%bv ltac:(cbv; auto 50)). exact G20. }
cbv beta. intros c' (regs2 & mem2 & p & -> & Hm2 & HJ2 & Gp & Hp & HK2).
assert (R2 : forall r : reg, In r [2; 3; 4; 8; 9; 16; 18; 19; 20; 22; 23; 27]%bv -> getr regs2 r = getr regs1 r).
{ intros rr Hrr. rewrite <- (R rr Hrr). apply HK2. cbv in Hrr. repeat (destruct Hrr as [<- | Hrr]; [cbv; auto 50 |]). destruct Hrr. }
assert (Km : forall x, mem2 x = memc x) by (intros x; rewrite Hm2; apply K1).
assert (KW2 : forall a v, word_mem ubs2segs memc a v -> word_mem ubs2segs mem2 a v) by (intros a v Hv k Hk; rewrite (mbyte_of_eq _ _ _ _ Km); exact (Hv k Hk)).
eapply (fl_t2 L A mem md regs0 regs2 Lc Ac mem2 mdc g N s i f b gen1 rest FP tmp pTmp Nt tv w h top left p np); [| exact Hb | | exact Gp | exact Hp | | exact Hnp].
2:{ rewrite (R2 18%bv ltac:(cbv; auto 50)). exact G18. }
2:{ rewrite (R2 20%bv ltac:(cbv; auto 50)). exact G20. }
split; [exact HJ2|]. split; [exact Hid|]. split; [exact Hra0|]. split; [exact Hal16|]. split; [exact Htp0|].
split.
{ eapply (cgif_at_kept memc _ g (flush_upd s i gen1 (rw_cur s)) N (cgif_blocks g s N ++ []) []); [rewrite (cgif_blocks_flush_upd g s N i gen1 (rw_cur s) f Hf); apply Permutation_refl | exact Hat |].
intros bb nn k Hbn Hk. apply mbyte_of_eq. exact Km. }
split; [exact Hwf|]. split; [exact Hi|]. split; [exact Hf|]. split; [exact HFP|]. split; [exact HB|]. split; [exact Htmp|]. split; [exact Htmp_fp|].
split; [exact Hw|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh|]. split; [exact Ht0|]. split; [exact Hth|]. split; [exact Htv|].
split; [apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply mbyte_of_eq; exact Km]|].
split; [rewrite (R2 9%bv ltac:(cbv; auto 50)); exact G9|].
split; [rewrite (R2 2%bv ltac:(cbv; auto 50)); exact G2|]. split; [apply KW2; exact W112|]. split; [apply KW2; exact W120|].
split; [rewrite (R2 8%bv ltac:(cbv; auto 50)); exact G8|].
split; [apply KW2; exact W56|]. split; [rewrite (R2 27%bv ltac:(cbv; auto 50)); exact G27|]. split; [apply KW2; exact W104|].
split; [rewrite (R2 19%bv ltac:(cbv; auto 50)); exact G19|].
split; [rewrite (R2 16%bv ltac:(cbv; auto 50)); exact G16|]. split; [rewrite (R2 23%bv ltac:(cbv; auto 50)); exact G23|].
split; [apply KW2; exact W96|]. split; [rewrite (R2 22%bv ltac:(cbv; auto 50)); exact G22|].
split; [rewrite (R2 3%bv ltac:(cbv; auto 50)); exact G3 | rewrite (R2 4%bv ltac:(cbv; auto 50)); exact G4].
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
