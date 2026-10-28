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
UI1h UI16 UI1z UI1k UI21 UI22
UI23 UI24 UI1w UI1j UI1s UI1t UI1l UI1m UI1n UI1o UI1v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis RAWADD : rawadd_spec API.
Definition ss_fast : sstate :=
mkSS FL_FAST sr_atoms [ YQ0b.mkRegion (Some 18%nat) 8 16 0 0 [mkChunk 8 (CVal 8 (SOff 32 0))] ;
YQ0b.mkRegion (Some 2%nat) 48 112 48 56 [mkChunk 104 (CVal 8 (SOff 33 0))] ] None
(mkFacts [ (19%nat, mkAF 1 65535 0); (18%nat, mkAF 4096 CEIL_MAX 3); (2%nat, mkAF CEIL_MIN (2^63) 4);
(9%nat, mkAF 4096 CEIL_MAX 0); (32%nat, mkAF 4096 CEIL_MAX 0); (33%nat, mkAF 1 65535 0) ] [] []).
Definition ss_fid : sstate :=
mkSS FL_FID sr_atoms [ YQ0b.mkRegion (Some 2%nat) 48 104 96 104 [mkChunk 48 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Definition ss_f4f : sstate :=
mkSS FL_F4F sr_atoms [ YQ0b.mkRegion (Some 2%nat) 48 104 96 104 [mkChunk 48 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (13%nat, mkAF 0 65534 0); (26%nat, mkAF 0 65534 0); (8%nat, mkAF 0 65534 0) ] [] []).
Lemma fl_fast :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st) (gen1 : Z)
(rest FP : list (Z * Z)) (tv np u23 u24 u25 : Z),
dv_pre API L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_FAST) memc (seg_rom ubs2segs)) mdc) (fl_post API regs0 g s N i rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE.
destruct (dv_ctx API L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE) as (ctcur & ctbef & HC & Hfi & Hbi).
pose proof PRE as (HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & Hb & HFP & HB & Htv & Hnp & Hu23 & Hu24 & Hu25
& HSV & W112 & W120 & W72 & W80 & W104 & W56 & W32 & W16 & W24 & G2 & G9 & G18 & G19 & G20 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRWv : RAW_SIZE = 48) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & _ & _ & Hngp & _ & Hfwf).
set (sp0 := spZ regs0) in *. set (spv := sp0 - 272) in *.
set (s1 := flush_upd s i gen1 (rw_cur s)) in *. set (f1 := set_fr_gen f gen1) in *.
dctx_open HC.
assert (Hbin : In (Some b) (cg_frames s)) by (eapply nth_error_In; exact Hb).
assert (Hfr1 : cg_frames s1 = list_set (cg_frames s) i (Some f1)) by (subst s1 f1; apply cg_frames_flush_upd; exact Hf).
assert (Hb1in : In (Some b) (cg_frames s1)).
{ rewrite Hfr1. eapply (nth_error_In _ (i - 1)). rewrite nth_error_list_set_other by lia. exact Hb. }
pose proof Hat as (_ & _ & Hfrs).
pose proof (Hfrs b Hb1in) as Hbobj.
destruct (af_cgif_geom API Lc Ac memc mdc g s N _ HH0 HB) as (_ & Hfgeom & _).
pose proof (fl_dgo API IMG RAWADD L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE) as GO. fold sp0 in GO. fold spv in GO.
assert (HN1 : 1 <= N) by (rewrite HN; clear - HW HH; nia).
destruct (Hfgeom b Hbin) as (Hq0 & Hq1 & Hqg).
assert (WRS : forall m', journal ubs2_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac m' mdc -> forall a, spv <= a < spv + 272 -> writable_at ubs2segs m' a).
{ intros m' HJm a Ha. pose proof HJm as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hw) & _). apply Hw. clear - Ha HFSv. subst spv. lia. }
set (E := Ereg regs1 (map (Z_to_bv 64) [fr_img b; cg_W s] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (fr_img b)) by (subst E; apply (Ereg_vals regs1 [fr_img b; cg_W s] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 (cg_W s)) by (subst E; apply (Ereg_vals regs1 [fr_img b; cg_W s] [] 1%nat); reflexivity).
assert (HU18 : bv_unsigned (ew E 18) = fr_ptr b) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; clear - Hq0 Hq1 Hac HFRv; lia).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HU9 : bv_unsigned (ew E 9) = fr_img f) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Hfimg0 Hfimg1 Hac HN1; lia).
assert (HU19 : bv_unsigned (ew E 19) = cg_H s) by (rewrite (HE 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; clear - HH; lia).
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 18%nat) 8 16 0 0 [mkChunk 8 (CVal 8 (SOff 32 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [clear - Hq1 Hac HFRv; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_img b)); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by (clear - Hbimg0 Hbimg1 Hac HN1; lia); reflexivity | cbn; clear - Hbimg0 Hbimg1 Hac HN1; lia | cbn; lia |].
exact (proj1 (obj_at_nth ubs2segs memc (fr_ptr b) LAY_Frame (frame_vals b) 1 (8, 8%N) (fr_img b) Hbobj eq_refl eq_refl)). }
assert (HR1 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 48 112 48 56 [mkChunk 104 (CVal 8 (SOff 33 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|]. split; [intros o Ho; apply (WRS _ HJ); clear - Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_W s)); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by (clear - HW; lia); reflexivity | cbn; clear - HW; lia | cbn; lia |].
apply val_mem_word_mem. exact W104. }
assert (HFA : atoms_ok E [ (19%nat, mkAF 1 65535 0); (18%nat, mkAF 4096 CEIL_MAX 3); (2%nat, mkAF CEIL_MIN (2^63) 4);
(9%nat, mkAF 4096 CEIL_MAX 0); (32%nat, mkAF 4096 CEIL_MAX 0); (33%nat, mkAF 1 65535 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU19, HU18, HU2, HU9, HE32, HE33.
rewrite !unsigned_lit_small by (clear - HW Hbimg0 Hbimg1 Hac HN1; lia).
change (2 ^ 0) with 1. change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
clear - HH HW Hq0 Hq1 B8 Hac HFRv Hsp0 Hsp1 Hsp16 Hfimg0 Hfimg1 Hbimg0 Hbimg1 HN1. repeat split; lia. }
assert (HPD : pairwise_disjoint E (ss_mem ss_fast)).
{ cbn [ss_mem ss_fast pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU18, HU2.
clear - Hq1 Hsp0 Hac HFRv. repeat split; try exact I; lia. }
assert (HS : st_ok ubs2segs E ss_fast (mkst regs1 (Z_to_bv 64 FL_FAST) memc (seg_rom ubs2segs))).
{ unfold ss_fast. subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HR0 | constructor; [exact HR1 | constructor]] | exact HPD | exact HFA]. }
clear HR0 HR1 HFA HPD.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_FAST) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ FL_F1L. { apply wr_ok_cons_ro; [cbn; lia|]. eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; clear - HFSv; subst spv; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (K1 : KD memc spv (ms_mem ms)).
{ apply (KD_frame _ _ _ _ (KD_refl memc spv)). intros a Ha Hna1 Hna2 Hna3 Hna4. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | [<- | []]]; cbn [r_base r_wlo r_whi base_val]; rewrite ?HU18, ?HU2; clear - Hna2; lia. }
clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks ubs2segs E ssx msx 1 _ 2%nat spv HS eq_refl eq_refl HU2) as Hcs;
pose proof (regs_kept_of_st_ok ubs2segs E ssx msx regs1 _ [2; 3; 4; 9; 18]%bv HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR0;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew E nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hvv; rewrite (st_ok_reg ubs2segs E ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E sv)
by (intros r sv Hr; rewrite (st_ok_reg ubs2segs E ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs.
assert (WNP : word_mem ubs2segs (ms_mem ms) (spv + 48) np).
{ apply (chunk_word E _ _ 48 (SOff 20 0) _ (proj1 (Forall_forall _ _) Hcs (mkChunk 48 (CVal 8 (SOff 20 0))) ltac:(cbn [In]; tauto)));
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE 20%nat 20%bv eq_refl); exact G20 | clear - Hnp; lia]. }
clear Hcs.
assert (A1_2 : getr (ms_regs ms) 2 = Z_to_bv 64 spv) by (rewrite (HKR0 2%bv ltac:(cbv; auto 20)); exact G2).
assert (A1_9 : getr (ms_regs ms) 9 = Z_to_bv 64 (fr_img f)) by (rewrite (HKR0 9%bv ltac:(cbv; auto 20)); exact G9).
assert (A1_18 : getr (ms_regs ms) 18 = Z_to_bv 64 (fr_ptr b)) by (rewrite (HKR0 18%bv ltac:(cbv; auto 20)); exact G18).
assert (A1_3 : getr (ms_regs ms) 3 = getr regs0 3) by (rewrite (HKR0 3%bv ltac:(cbv; auto 20)); exact G3).
assert (A1_4 : getr (ms_regs ms) 4 = getr regs0 4) by (rewrite (HKR0 4%bv ltac:(cbv; auto 20)); exact G4).
assert (A1_20 : getr (ms_regs ms) 20 = Z_to_bv 64 (fr_img b)) by (apply (RG 20%bv 32%nat _ eq_refl); exact HE32).
assert (A1_27 : getr (ms_regs ms) 27 = Z_to_bv 64 (cg_W s)) by (apply (RG 27%bv 33%nat _ eq_refl); exact HE33).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (fl_f1l API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
(Z.to_nat (cg_H s)) 0 FLUSH_STK sp0 FP L A mem md Lc Ac mdc _ _ HJ K1 Hfi Hbi
ltac:(clear; lia) ltac:(clear - HH; lia) ltac:(clear - HH; lia) A1_2).
- rewrite (RGX 8%bv (SLit 0) eq_refl). reflexivity.
- rewrite (RGX 19%bv (SLit 0) eq_refl). rewrite Z.mul_0_l. reflexivity.
- exact A1_9.
- exact A1_20.
- rewrite (RGX 21%bv (SLit 1) eq_refl). reflexivity.
- rewrite (RGX 22%bv (SLit 1) eq_refl). reflexivity.
- exact A1_27. }
cbv beta. intros c' (regs2 & mem2 & pc2 & -> & HJ2 & K2 & Hpc2 & HK2). clear HS HJ RG RGX.
assert (K2' : KD memc spv mem2) by (exact (KD_eq _ _ _ _ K1 K2)).
assert (WNP2 : word_mem ubs2segs mem2 (spv + 48) np) by (intros k Hk; rewrite (mbyte_of_eq _ _ _ _ K2); exact (WNP k Hk)).
assert (A2_2 : getr regs2 2 = Z_to_bv 64 spv) by (rewrite (HK2 2%bv ltac:(cbv; auto 20)); exact A1_2).
assert (A2_9 : getr regs2 9 = Z_to_bv 64 (fr_img f)) by (rewrite (HK2 9%bv ltac:(cbv; auto 20)); exact A1_9).
assert (A2_18 : getr regs2 18 = Z_to_bv 64 (fr_ptr b)) by (rewrite (HK2 18%bv ltac:(cbv; auto 20)); exact A1_18).
assert (A2_20 : getr regs2 20 = Z_to_bv 64 (fr_img b)) by (rewrite (HK2 20%bv ltac:(cbv; auto 20)); exact A1_20).
assert (A2_3 : getr regs2 3 = getr regs0 3) by (rewrite (HK2 3%bv ltac:(cbv; auto 20)); exact A1_3).
assert (A2_4 : getr regs2 4 = getr regs0 4) by (rewrite (HK2 4%bv ltac:(cbv; auto 20)); exact A1_4).
clear HK2 HKR0 A1_2 A1_9 A1_18 A1_20 A1_27 A1_3 A1_4 K1 K2 WNP ms.
destruct Hpc2 as [[-> (top & c0 & Htop & Hc0 & Hne & Q8 & Q27)] | [-> Q27]].
-
eapply SR_bind.
{ eapply (fl_f2 API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
FLUSH_STK sp0 FP L A mem md Lc Ac mdc regs2 mem2 top HJ2 K2' Hfi Hbi eq_refl ltac:(clear - HFSv; lia) Htop A2_2 A2_9 A2_20 Q27 Q8). }
cbv beta. intros c' (regs3 & mem3 & hrow & -> & HJ3 & K3 & Hhr & Q19 & Q21 & Q27' & HK3).
assert (K3' : KD memc spv mem3) by (exact (KD_eq _ _ _ _ K2' K3)).
eapply SR_bind.
{ eapply (fl_f3 API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
FLUSH_STK sp0 FP L A mem md Lc Ac mdc regs3 mem3 top hrow c0 HJ3 K3' Hfi Hbi ltac:(clear - Htop Hhr; lia) ltac:(clear - Hhr; lia) Hc0 Hne Q19).
- rewrite (HK3 8%bv ltac:(cbv; auto 20)). exact Q8.
- exact Q21.
- rewrite (HK3 9%bv ltac:(cbv; auto 20)). exact A2_9.
- rewrite (HK3 20%bv ltac:(cbv; auto 20)). exact A2_20.
- exact Q27'.
- rewrite (HK3 2%bv ltac:(cbv; auto 20)). exact A2_2. }
cbv beta. intros c' (regs4 & mem4 & left & -> & HJ4 & K4 & Hleft & Q26 & Q10 & Q22 & Q12 & Q11 & HK4).
assert (K4' : KD memc spv mem4) by (exact (KD_eq _ _ _ _ K3' K4)).
set (h := hrow + 1 - top) in *.
assert (Hh : 1 <= h /\ top + h <= cg_H s) by (subst h; clear - Hhr Htop; lia).
eapply SR_bind.
{ eapply (fl_f4 API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
FLUSH_STK sp0 FP L A mem md Lc Ac mdc regs4 mem4 top h c0 HJ4 K4' Hfi Hbi ltac:(clear - Htop; lia) ltac:(clear - Hh; lia) ltac:(clear - Hh; lia) Hc0 Hne Q10 Q11 Q12 Q22).
- rewrite (HK4 8%bv ltac:(cbv; auto 20)), (HK3 8%bv ltac:(cbv; auto 20)). exact Q8.
- rewrite (HK4 9%bv ltac:(cbv; auto 20)), (HK3 9%bv ltac:(cbv; auto 20)). exact A2_9.
- rewrite (HK4 20%bv ltac:(cbv; auto 20)), (HK3 20%bv ltac:(cbv; auto 20)). exact A2_20.
- rewrite (HK4 27%bv ltac:(cbv; auto 20)). exact Q27'.
- rewrite (HK4 2%bv ltac:(cbv; auto 20)), (HK3 2%bv ltac:(cbv; auto 20)). exact A2_2. }
cbv beta. intros c' (regs5 & mem5 & xr & -> & HJ5 & K5 & Hxr & Q13 & Q27'' & HK5).
assert (K5' : KD memc spv mem5) by (exact (KD_eq _ _ _ _ K4' K5)).
assert (WNP5 : word_mem ubs2segs mem5 (spv + 48) np)
by (intros k Hk; rewrite (mbyte_of_eq _ _ _ _ K5), (mbyte_of_eq _ _ _ _ K4), (mbyte_of_eq _ _ _ _ K3); exact (WNP2 k Hk)).
set (E5 := Ereg regs5 (map (Z_to_bv 64) [np] ++ [])).
assert (HE5 : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E5 m = getr regs5 rr) by (intros; subst E5; apply ew_Ereg_nat; assumption).
assert (HE5_32 : ew E5 32 = Z_to_bv 64 np) by (subst E5; apply (Ereg_vals regs5 [np] [] 0%nat); reflexivity).
assert (A5_2 : getr regs5 2 = Z_to_bv 64 spv) by (rewrite (HK5 2%bv ltac:(cbv; auto 20)), (HK4 2%bv ltac:(cbv; auto 20)), (HK3 2%bv ltac:(cbv; auto 20)); exact A2_2).
assert (A5_8 : getr regs5 8 = Z_to_bv 64 top) by (rewrite (HK5 8%bv ltac:(cbv; auto 20)), (HK4 8%bv ltac:(cbv; auto 20)), (HK3 8%bv ltac:(cbv; auto 20)); exact Q8).
assert (A5_26 : getr regs5 26 = Z_to_bv 64 left) by (rewrite (HK5 26%bv ltac:(cbv; auto 20)); exact Q26).
assert (HU5_2 : bv_unsigned (ew E5 2) = spv) by (rewrite (HE5 2%nat 2%bv eq_refl), A5_2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR5 : region_ok ubs2segs E5 mem5 (YQ0b.mkRegion (Some 2%nat) 48 104 96 104 [mkChunk 48 (CVal 8 (SOff 32 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU5_2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|]. split; [intros o Ho; apply (WRS _ HJ5); clear - Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ np); [cbn [sv_denot]; rewrite Z.add_0_r, HE5_32, unsigned_lit_small by (clear - Hnp; lia); reflexivity | cbn; clear - Hnp; lia | cbn; lia |].
apply val_mem_word_mem. exact WNP5. }
assert (HFA5 : atoms_ok E5 [ (2%nat, mkAF CEIL_MIN (2^63) 4); (13%nat, mkAF 0 65534 0); (26%nat, mkAF 0 65534 0); (8%nat, mkAF 0 65534 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU5_2, (HE5 13%nat 13%bv eq_refl), (HE5 26%nat 26%bv eq_refl), (HE5 8%nat 8%bv eq_refl), Q13, A5_26, A5_8.
rewrite !unsigned_lit_small by (clear - Hxr Hleft Hc0 Htop HW HH; lia). change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
clear - Hsp0 Hsp1 Hsp16 Hxr Hleft Hc0 Htop HW HH Hac. repeat split; lia. }
assert (HS : st_ok ubs2segs E5 ss_f4f (mkst regs5 (Z_to_bv 64 FL_F4F) mem5 (seg_rom ubs2segs))).
{ unfold ss_f4f. subst E5. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HR5 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | exact HFA5]. }
clear HR5 HFA5.
change mem5 with (ms_mem (mkst regs5 (Z_to_bv 64 FL_F4F) mem5 (seg_rom ubs2segs))) in HJ5.
jrun_to LAWS ubs2tbl_ok HS HJ5 FL_DT. { eapply wr_ok_cons_win; [reflexivity | exact HU5_2 | cbn [r_wlo r_whi]; intros _; clear - HFSv; subst spv; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (KF : KD memc spv (ms_mem ms)).
{ apply (KD_frame _ _ _ _ K5'). intros a Ha Hna1 Hna2 Hna3 Hna4. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | []]. cbn [r_base r_wlo r_whi base_val]. rewrite HU5_2. clear - Hna4. lia. }
clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks ubs2segs E5 ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU5_2) as Hcs;
pose proof (regs_kept_of_st_ok ubs2segs E5 ssx msx regs5 _ [2; 3; 4; 9; 18; 22; 26; 27]%bv HS ltac:(subst E5; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E5 sv)
by (intros r sv Hr; rewrite (st_ok_reg ubs2segs E5 ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
apply (GO (ms_regs ms) (ms_mem ms) (xr + 1 - left) h top left HJ5 KF).
+ apply (chunk_word E5 _ _ 96 (SOff 8 0) _ (proj1 (Forall_forall _ _) Hcs (mkChunk 96 (CVal 8 (SOff 8 0))) ltac:(cbn [In]; tauto)));
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE5 8%nat 8%bv eq_refl); exact A5_8 | clear - Htop HH; lia].
+ clear - Hxr Hleft; lia.
+ clear - Hleft; lia.
+ clear - Hxr Hleft; lia.
+ clear - Hh; lia.
+ clear - Htop; lia.
+ clear - Hh; lia.
+ rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact A5_2.
+ rewrite (HKR 9%bv ltac:(cbv; auto 20)), (HK5 9%bv ltac:(cbv; auto 20)), (HK4 9%bv ltac:(cbv; auto 20)), (HK3 9%bv ltac:(cbv; auto 20)). exact A2_9.
+ rewrite (HKR 18%bv ltac:(cbv; auto 20)), (HK5 18%bv ltac:(cbv; auto 20)), (HK4 18%bv ltac:(cbv; auto 20)), (HK3 18%bv ltac:(cbv; auto 20)). exact A2_18.
+ rewrite (HKR 27%bv ltac:(cbv; auto 20)). exact Q27''.
+ rewrite (RGX 20%bv (SOff 32 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact HE5_32.
+ rewrite (HKR 26%bv ltac:(cbv; auto 20)). exact A5_26.
+ rewrite (RGX 19%bv _ eq_refl). eval_sr_get. apply denot_of_U'.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, (U_atom_off E5 13 xr 1), (U_atom E5 26 left)
by first [rewrite (HE5 13%nat 13%bv eq_refl); exact Q13 | rewrite (HE5 26%nat 26%bv eq_refl); exact A5_26 | clear - Hxr Hleft Hc0 HW; lia].
replace (xr + 1 - left) with ((xr + 1) - left) by (clear; lia). apply zcanon_add_mulm1; clear - Hxr Hleft Hc0 HW; lia.
+ rewrite (HKR 22%bv ltac:(cbv; auto 20)), (HK5 22%bv ltac:(cbv; auto 20)). exact Q22.
+ rewrite (HKR 3%bv ltac:(cbv; auto 20)), (HK5 3%bv ltac:(cbv; auto 20)), (HK4 3%bv ltac:(cbv; auto 20)), (HK3 3%bv ltac:(cbv; auto 20)). exact A2_3.
+ rewrite (HKR 4%bv ltac:(cbv; auto 20)), (HK5 4%bv ltac:(cbv; auto 20)), (HK4 4%bv ltac:(cbv; auto 20)), (HK3 4%bv ltac:(cbv; auto 20)). exact A2_4.
-
set (E2 := Ereg regs2 (map (Z_to_bv 64) [np] ++ [])).
assert (HE2 : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E2 m = getr regs2 rr) by (intros; subst E2; apply ew_Ereg_nat; assumption).
assert (HE2_32 : ew E2 32 = Z_to_bv 64 np) by (subst E2; apply (Ereg_vals regs2 [np] [] 0%nat); reflexivity).
assert (HU2_2 : bv_unsigned (ew E2 2) = spv) by (rewrite (HE2 2%nat 2%bv eq_refl), A2_2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR2 : region_ok ubs2segs E2 mem2 (YQ0b.mkRegion (Some 2%nat) 48 104 96 104 [mkChunk 48 (CVal 8 (SOff 32 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2_2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|]. split; [intros o Ho; apply (WRS _ HJ2); clear - Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ np); [cbn [sv_denot]; rewrite Z.add_0_r, HE2_32, unsigned_lit_small by (clear - Hnp; lia); reflexivity | cbn; clear - Hnp; lia | cbn; lia |].
apply val_mem_word_mem. exact WNP2. }
assert (HFA2 : atoms_ok E2 [ (2%nat, mkAF CEIL_MIN (2^63) 4) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2_2. change (2 ^ 4) with 16. clear - Hsp0 Hsp1 Hsp16 Hac. repeat split; lia. }
assert (HS : st_ok ubs2segs E2 ss_fid (mkst regs2 (Z_to_bv 64 FL_FID) mem2 (seg_rom ubs2segs))).
{ unfold ss_fid. subst E2. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HR2 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | exact HFA2]. }
clear HR2 HFA2.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 FL_FID) mem2 (seg_rom ubs2segs))) in HJ2.
jrun_to LAWS ubs2tbl_ok HS HJ2 FL_DT. { eapply wr_ok_cons_win; [reflexivity | exact HU2_2 | cbn [r_wlo r_whi]; intros _; clear - HFSv; subst spv; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (KF : KD memc spv (ms_mem ms)).
{ apply (KD_frame _ _ _ _ K2'). intros a Ha Hna1 Hna2 Hna3 Hna4. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | []]. cbn [r_base r_wlo r_whi base_val]. rewrite HU2_2. clear - Hna4. lia. }
clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks ubs2segs E2 ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU2_2) as Hcs;
pose proof (regs_kept_of_st_ok ubs2segs E2 ssx msx regs2 _ [2; 3; 4; 9; 18; 27]%bv HS ltac:(subst E2; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E2 sv)
by (intros r sv Hr; rewrite (st_ok_reg ubs2segs E2 ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
apply (GO (ms_regs ms) (ms_mem ms) 1 1 0 0 HJ2 KF).
+ apply (chunk_word E2 _ _ 96 (SLit 0) _ (proj1 (Forall_forall _ _) Hcs (mkChunk 96 (CVal 8 (SLit 0))) ltac:(cbn [In]; tauto))); [reflexivity | clear; lia].
+ clear; lia.
+ clear; lia.
+ clear - HW; lia.
+ clear; lia.
+ clear; lia.
+ clear - HH; lia.
+ rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact A2_2.
+ rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact A2_9.
+ rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact A2_18.
+ rewrite (HKR 27%bv ltac:(cbv; auto 20)). exact Q27.
+ rewrite (RGX 20%bv (SOff 32 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact HE2_32.
+ rewrite (RGX 26%bv (SLit 0) eq_refl). reflexivity.
+ rewrite (RGX 19%bv (SLit 1) eq_refl). reflexivity.
+ rewrite (RGX 22%bv (SLit 1) eq_refl). reflexivity.
+ rewrite (HKR 3%bv ltac:(cbv; auto 20)). exact A2_3.
+ rewrite (HKR 4%bv ltac:(cbv; auto 20)). exact A2_4.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
