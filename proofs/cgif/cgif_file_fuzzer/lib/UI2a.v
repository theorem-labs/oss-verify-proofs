(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3a UN3b YI06 UI5b YI09 YI08 YI0r UI1w UI1v UI4l UI21 UI2m UI3t UI5o UI5l YI6b UI5n UI20 UI1d UI2l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25 UI2o UI2p UI2h UI24 UI2d UI2e UI26 UI27 UI28 UI29.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI2q UI2r UI2g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI01 UI3u UI22 YI5a UI5d YI0f YI2w UI2v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0d YI0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI2s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis RAWADDX : rawadd_specX API.
Lemma dv_HDf : forall memc s N f b GPAL cur befr,
cgif_wf s N -> fl_vals memc s N f (Some b) GPAL cur (Some befr) ->
YO07.flag (YO07.f_attr befr) 1 = false -> YO07.flag (YO07.f_attr cur) 1 = false ->
YO07.flag (YO07.f_attr befr) 4 = false -> YO07.flag (YO07.f_attr cur) 4 = false ->
forall p, 0 <= p < cg_W s * cg_H s ->
(DIFb memc (fr_img f) (fr_img b) p <->
YO07.px_ne (gcfg_of s GPAL) cur befr (nth (Z.to_nat p) (YO07.f_img cur) 0) (nth (Z.to_nat p) (YO07.f_img befr) 0) = true).
Proof using.
intros memc s N f b GPAL cur befr Hwf HVALS F1 F2 F3 F4 p Hp. pose proof Hwf as (_ & _ & _ & HN & _).
pose proof HVALS as (_ & HVf & HVb & _). pose proof HVf as (_ & _ & _ & _ & _ & _ & _ & XVI & XVIl & _).
cbn [oframe_relb] in HVb. pose proof HVb as (_ & _ & _ & _ & _ & _ & _ & XBI & XBIl & _).
rewrite (px_ne_fast (gcfg_of s GPAL) cur befr F1 F2 F3 F4). unfold DIFb.
rewrite (byte_at_garr8 memc (fr_img f) (YO07.f_img cur) p XVI) by (rewrite XVIl, HN; exact Hp).
rewrite (byte_at_garr8 memc (fr_img b) (YO07.f_img befr) p XBI) by (rewrite XBIl, HN; exact Hp).
rewrite Bool.negb_true_iff, Z.eqb_neq. tauto.
Qed.
Definition ss_fast : sstate :=
mkSS FL_FAST sr_atoms [ YP09.mkRegion (Some 2%nat) 48 112 48 56 [mkChunk 104 (CVal 8 (SOff 27 0))] ;
YP09.mkRegion (Some 18%nat) 8 16 0 0 [mkChunk 8 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (19%nat, mkAF 1 65535 0); (9%nat, mkAF 4096 CEIL_MAX 0); (32%nat, mkAF 4096 CEIL_MAX 0); (18%nat, mkAF 4096 CEIL_MAX 3) ] [] []).
Definition ss_fexit (pc : Z) : sstate :=
mkSS pc sr_atoms [ YP09.mkRegion (Some 2%nat) 48 104 96 104 [mkChunk 48 (CVal 8 (SOff 32 0))] ] None (mkFacts [] [] []).
Lemma fl_fast :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st)
(rest FP FPw : list (Z * Z)) (tv np u23 u24 u25 : Z) (S GPAL : list Z) (cur befr : YO07.frame) (brb bc : rbound),
let gen1 := fl_gen3 (gcfg_of s GPAL) cur (Some befr) in
dv_pre API L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 ->
fl_sink g s N rest FP FPw S L A mem md (spZ regs0) ->
fl_vals memc s N f (Some b) GPAL cur (Some befr) ->
u23 = fr_disp f -> u24 = Z.land (fr_attr f) 4 -> u25 = (if fl_hasAlpha (gcfg_of s GPAL) cur then 1 else 0) ->
np = fl_npal (gcfg_of s GPAL) cur -> tv mod 256 = YO07.f_trans cur ->
YO07.flag (fl_gen3 (gcfg_of s GPAL) cur (Some befr)) 2 = true ->
(forall n, 0 < n <= N -> room bc n /\ rawadd_room (rb_malloc bc n) n /\ rb_le (rb_free (rawadd_rb (rb_malloc bc n)) n) (flush_rb brb)) -> res_ok Ac bc ->
YO07.flag (YO07.f_attr befr) 1 = false -> YO07.flag (YO07.f_attr cur) 1 = false ->
YO07.flag (YO07.f_attr befr) 4 = false -> YO07.flag (YO07.f_attr cur) 4 = false ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_FAST) memc (seg_rom ubs0segs)) mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur (Some befr) brb L A mem md).
Proof using IMG RAWADDX.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b rest FP FPw tv np u23 u24 u25 S GPAL cur befr brb bc gen1 PRE
HSINK HVALS Xu23 Xu24 Xu25 Xnp Xtv0 XG2 HNUM HRq F1 F2 F3 F4.
pose proof PRE as (_ & _ & _ & _ & _ & _ & HwfX & _).
destruct (dv_ctx API L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE) as (ctcur & ctbef & HC & Hfi & Hbi).
pose proof PRE as (HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & Hb & HFP & HB & Htv & Hnp & Hu23 & Hu24 & Hu25
& HSV & W112 & W120 & W72 & W80 & W104 & W56 & W32 & W16 & W24 & G2 & G9 & G18 & G27 & G20 & G19 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs0) in *. set (spv := sp0 - 272) in *.
set (s1 := flush_upd s i gen1 (rw_cur s)) in *. set (f1 := set_fr_gen f gen1) in *.
dctx_open HC.
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
assert (Hfr1 : cg_frames s1 = list_set (cg_frames s) i (Some f1)) by (subst s1 f1; apply cg_frames_flush_upd; exact Hf).
assert (Hb1in : In (Some b) (cg_frames s1)).
{ rewrite Hfr1. eapply (nth_error_In _ (i - 1)). rewrite nth_error_list_set_other by lia. exact Hb. }
pose proof Hat as (_ & _ & Hfrs).
pose proof (Hfrs b Hb1in) as Hbobj.
pose proof (fl_dgo API IMG RAWADDX L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b rest FP FPw tv np u23 u24 u25 S GPAL cur befr brb bc PRE HSINK HVALS Xu23 Xu24 Xu25 Xnp Xtv0 XG2 HNUM HRq) as GO.
fold sp0 in GO. fold spv in GO.
pose proof (dv_HDf memc s N f b GPAL cur befr HwfX HVALS F1 F2 F3 F4) as HD.
assert (HN1 : 1 <= N) by (rewrite HN; clear - HW HH; nia).
assert (WRS : forall m', journal ubs0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac m' mdc -> forall a, spv <= a < spv + 272 -> writable_at ubs0segs m' a).
{ intros m' HJm a Ha. pose proof HJm as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hw) & _). apply Hw. clear - Ha HFSv. subst spv. lia. }
set (E := Ereg regs1 (map (Z_to_bv 64) [fr_img b] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (fr_img b)) by (subst E; apply (Ereg_vals regs1 [fr_img b] [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HU18 : bv_unsigned (ew E 18) = fr_ptr b) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; clear - B0 B1 Hac; lia).
assert (HRS : region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 48 112 48 56 [mkChunk 104 (CVal 8 (SOff 27 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|]. split; [intros o Ho; apply (WRS _ HJ); clear - Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_W s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HE 27%nat 27%bv eq_refl), G27, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - HW; lia | cbn; lia | apply val_mem_word_mem; exact W104]. }
assert (HR18 : region_ok ubs0segs E memc (YP09.mkRegion (Some 18%nat) 8 16 0 0 [mkChunk 8 (CVal 8 (SOff 32 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [clear - B1 Hac; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_img b)); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by (clear - Hbimg0 Hbimg1 Hac HN1; lia); reflexivity | cbn; clear - Hbimg0 Hbimg1 Hac HN1; lia | cbn; lia |].
exact (proj1 (obj_at_nth ubs0segs memc (fr_ptr b) LAY_Frame (frame_vals b) 1 (8, 8%N) (fr_img b) Hbobj eq_refl eq_refl)). }
assert (HFA : atoms_ok E [ (19%nat, mkAF 1 65535 0); (9%nat, mkAF 4096 CEIL_MAX 0); (32%nat, mkAF 4096 CEIL_MAX 0); (18%nat, mkAF 4096 CEIL_MAX 3) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU18, (HE 19%nat 19%bv eq_refl), (HE 9%nat 9%bv eq_refl), HE32, G19, G9.
rewrite !unsigned_lit_small by (clear - HH Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hac HN1; lia).
change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r. clear - HH B0 B1 B8 Hac Hfimg0 Hfimg1 Hbimg0 Hbimg1 HN1. repeat split; lia. }
assert (HS : st_ok ubs0segs E ss_fast (mkst regs1 (Z_to_bv 64 FL_FAST) memc (seg_rom ubs0segs))).
{ unfold ss_fast. subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HRS | constructor; [exact HR18 | constructor]] | | exact HFA].
cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU18.
clear - B1 Hsp0 Hac. repeat split; try exact I; lia. }
clear HRS HR18 HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_FAST) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ FL_F1L.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; clear - HFSv; subst spv; lia | apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]]. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 48 <= a < spv + 56) -> mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs memc a).
{ intros a Ha Hna; apply (mbyte_of_frame _ _ _ _ a HF Ha); intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; rewrite ?HU2; lia |]); destruct Hr. }
clear HF HG.
assert (KD1 : KD memc spv (ms_mem ms)).
{ apply (KD_frame memc spv memc); [apply KD_refl|]. intros a Ha Hn1 Hn2 Hn3 Hn4. apply K1; [exact Ha | clear - Hn2; lia]. }
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks ubs0segs E ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU2) as Hcs;
pose proof (regs_kept_of_st_ok ubs0segs E ssx msx regs1 _ [2; 3; 4; 9; 18; 27]%bv HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR0;
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E sv)
by (intros r sv Hr; rewrite (st_ok_reg ubs0segs E ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs.
assert (W48 : word_mem ubs0segs (ms_mem ms) (spv + 48) np).
{ apply (chunk_word _ _ _ 48 _ _ (proj1 (Forall_forall _ _) Hcs (mkChunk 48 (CVal 8 (SOff 20 0))) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))));
[cbn [sv_denot]; rewrite Z.add_0_r, (HE 20%nat 20%bv eq_refl), G20, Z_to_bv_bv_unsigned; reflexivity | clear - Hnp; lia]. }
clear Hcs.
assert (A1_2 : getr (ms_regs ms) 2 = Z_to_bv 64 spv) by (rewrite (HKR0 2%bv ltac:(cbv; auto 20)); exact G2).
assert (A1_9 : getr (ms_regs ms) 9 = Z_to_bv 64 (fr_img f)) by (rewrite (HKR0 9%bv ltac:(cbv; auto 20)); exact G9).
assert (A1_18 : getr (ms_regs ms) 18 = Z_to_bv 64 (fr_ptr b)) by (rewrite (HKR0 18%bv ltac:(cbv; auto 20)); exact G18).
assert (A1_27 : getr (ms_regs ms) 27 = Z_to_bv 64 (cg_W s)) by (rewrite (HKR0 27%bv ltac:(cbv; auto 20)); exact G27).
assert (A1_3 : getr (ms_regs ms) 3 = getr regs0 3) by (rewrite (HKR0 3%bv ltac:(cbv; auto 20)); exact G3).
assert (A1_4 : getr (ms_regs ms) 4 = getr regs0 4) by (rewrite (HKR0 4%bv ltac:(cbv; auto 20)); exact G4).
assert (A1_20 : getr (ms_regs ms) 20 = Z_to_bv 64 (fr_img b)) by (rewrite (RGX 20%bv (SOff 32 0) eq_refl); cbn [sv_denot]; rewrite Z.add_0_r, HE32, Z_to_bv_bv_unsigned; reflexivity).
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (fl_f1lV API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
(Z.to_nat (cg_H s)) 0 FLUSH_STK sp0 FP L A mem md Lc Ac mdc _ _ HJ KD1 Hfi Hbi
ltac:(clear; lia) ltac:(clear - HH; lia) ltac:(clear - HH; lia) A1_2).
- rewrite (RGX 8%bv (SLit 0) eq_refl). reflexivity.
- rewrite (RGX 19%bv (SLit 0) eq_refl). rewrite Z.mul_0_l. reflexivity.
- exact A1_9.
- rewrite (RGX 20%bv (SOff 32 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, HE32, Z_to_bv_bv_unsigned. reflexivity.
- exact A1_27.
- rewrite (RGX 21%bv (SLit 1) eq_refl). reflexivity.
- rewrite (RGX 22%bv (SLit 1) eq_refl). reflexivity.
- intros p Hp. exfalso. clear - Hp. lia. }
cbv beta. intros c' (regs2 & mem2 & pc2 & -> & HJ2 & K2 & Hpc2 & HK2). clear HS HJ RGX.
assert (KD2 : KD memc spv mem2) by (exact (KD_eq _ _ _ _ KD1 K2)).
assert (W48b : word_mem ubs0segs mem2 (spv + 48) np) by (intros k Hk; rewrite (mbyte_of_eq _ _ _ _ K2); exact (W48 k Hk)).
assert (A2_2 : getr regs2 2 = Z_to_bv 64 spv) by (rewrite (HK2 2%bv ltac:(cbv; auto 20)); exact A1_2).
assert (A2_9 : getr regs2 9 = Z_to_bv 64 (fr_img f)) by (rewrite (HK2 9%bv ltac:(cbv; auto 20)); exact A1_9).
assert (A2_18 : getr regs2 18 = Z_to_bv 64 (fr_ptr b)) by (rewrite (HK2 18%bv ltac:(cbv; auto 20)); exact A1_18).
assert (A2_3 : getr regs2 3 = getr regs0 3) by (rewrite (HK2 3%bv ltac:(cbv; auto 20)); exact A1_3).
assert (A2_4 : getr regs2 4 = getr regs0 4) by (rewrite (HK2 4%bv ltac:(cbv; auto 20)); exact A1_4).
assert (A2_20 : getr regs2 20 = Z_to_bv 64 (fr_img b)) by (rewrite (HK2 20%bv ltac:(cbv; auto 20)); exact A1_20).
clear HK2 HKR0 A1_2 A1_9 A1_18 A1_27 A1_3 A1_4 A1_20 K1 K2 W48 KD1 ms.
destruct Hpc2 as [[-> (top & c0 & Htop & Hc0 & Hne & Q8 & Q27 & VT0)] | (-> & Q27 & VID)].
-
eapply SR_bind.
{ eapply (fl_f2V API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
FLUSH_STK sp0 FP L A mem md Lc Ac mdc regs2 mem2 top HJ2 KD2 Hfi Hbi eq_refl ltac:(clear - HFSv; lia) Htop A2_2 A2_9 A2_20 Q27 Q8).
exists c0. split; [exact Hc0 | exact Hne]. }
cbv beta. intros c' (regs3 & mem3 & hrow & -> & HJ3 & K3 & Hhr & Q19 & Q8' & Q21 & Q27' & HK3 & VH1 & VH2).
set (h := hrow + 1 - top).
assert (Hh : 1 <= h /\ top + h <= cg_H s) by (subst h; clear - Hhr Htop; lia).
assert (K3' : KD memc spv mem3) by (exact (KD_eq _ _ _ _ KD2 K3)).
eapply SR_bind.
{ eapply (fl_f3V API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
FLUSH_STK sp0 FP L A mem md Lc Ac mdc regs3 mem3 top hrow c0 HJ3 K3' Hfi Hbi ltac:(clear - Htop Hhr; lia) ltac:(clear - Hhr; lia) Hc0 Hne Q19 Q8' Q21).
- rewrite (HK3 9%bv ltac:(cbv; auto 20)). exact A2_9.
- rewrite (HK3 20%bv ltac:(cbv; auto 20)). exact A2_20.
- exact Q27'. }
cbv beta. intros c' (regs4 & mem4 & left & -> & HJ4 & K4 & Hleft & Q26 & Q10 & Q22 & Q12 & Q11 & HK4 & (VL1 & VL2)).
assert (K4' : KD memc spv mem4) by (exact (KD_eq _ _ _ _ K3' K4)).
eapply SR_bind.
{ eapply (fl_f4V API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
FLUSH_STK sp0 FP L A mem md Lc Ac mdc regs4 mem4 top h c0 HJ4 K4' Hfi Hbi ltac:(clear - Htop; lia) ltac:(clear - Hh; lia) ltac:(clear - Hh; lia) Hc0 Hne Q10 Q11 Q12).
- rewrite (HK4 8%bv ltac:(cbv; auto 50)). exact Q8'.
- rewrite (HK4 9%bv ltac:(cbv; auto 50)), (HK3 9%bv ltac:(cbv; auto 20)). exact A2_9.
- rewrite (HK4 20%bv ltac:(cbv; auto 50)), (HK3 20%bv ltac:(cbv; auto 20)). exact A2_20.
- rewrite (HK4 27%bv ltac:(cbv; auto 50)). exact Q27'. }
cbv beta. intros c' (regs5 & mem5 & xr & -> & HJ5 & K5 & Hxr & Q13 & Q27'' & HK5 & (VR1 & VR2)).
assert (KD5 : KD memc spv mem5) by (exact (KD_eq _ _ _ _ K4' K5)).
assert (W48c : word_mem ubs0segs mem5 (spv + 48) np).
{ intros k Hk. rewrite (mbyte_of_eq _ _ _ _ K5), (mbyte_of_eq _ _ _ _ K4), (mbyte_of_eq _ _ _ _ K3). exact (W48b k Hk). }
assert (A5_2 : getr regs5 2 = Z_to_bv 64 spv) by (rewrite (HK5 2%bv ltac:(cbv; auto 50)), (HK4 2%bv ltac:(cbv; auto 50)), (HK3 2%bv ltac:(cbv; auto 20)); exact A2_2).
assert (A5_8 : getr regs5 8 = Z_to_bv 64 top) by (rewrite (HK5 8%bv ltac:(cbv; auto 50)), (HK4 8%bv ltac:(cbv; auto 50)); exact Q8').
assert (A5_26 : getr regs5 26 = Z_to_bv 64 left) by (rewrite (HK5 26%bv ltac:(cbv; auto 50)); exact Q26).
assert (A5_22 : getr regs5 22 = Z_to_bv 64 h) by (rewrite (HK5 22%bv ltac:(cbv; auto 50)); exact Q22).
set (E5 := Ereg regs5 (map (Z_to_bv 64) [np] ++ [])).
assert (HE5 : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E5 m = getr regs5 rr) by (intros; subst E5; apply ew_Ereg_nat; assumption).
assert (HE5_32 : ew E5 32 = Z_to_bv 64 np) by (subst E5; apply (Ereg_vals regs5 [np] [] 0%nat); reflexivity).
assert (HU5_2 : bv_unsigned (ew E5 2) = spv) by (rewrite (HE5 2%nat 2%bv eq_refl), A5_2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR5 : region_ok ubs0segs E5 mem5 (YP09.mkRegion (Some 2%nat) 48 104 96 104 [mkChunk 48 (CVal 8 (SOff 32 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU5_2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|]. split; [intros o Ho; apply (WRS _ HJ5); clear - Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ np); [cbn [sv_denot]; rewrite Z.add_0_r, HE5_32, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Hnp; lia | cbn; lia | apply val_mem_word_mem; exact W48c]. }
assert (HS : st_ok ubs0segs E5 (ss_fexit FL_F4F) (mkst regs5 (Z_to_bv 64 FL_F4F) mem5 (seg_rom ubs0segs))).
{ unfold ss_fexit. subst E5. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HR5 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | exact I]. }
clear HR5.
change mem5 with (ms_mem (mkst regs5 (Z_to_bv 64 FL_F4F) mem5 (seg_rom ubs0segs))) in HJ5.
jrun_to LAWS ubs0tbl_ok HS HJ5 FL_DT. { eapply wr_ok_cons_win; [reflexivity | exact HU5_2 | cbn [r_wlo r_whi]; intros _; clear - HFSv; subst spv; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 96 <= a < spv + 104) -> mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs mem5 a).
{ intros a Ha Hna. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr. destruct Hr as [<- | []]. cbn [r_base r_wlo r_whi base_val]. rewrite HU5_2. clear - Hna. lia. }
clear HF HG.
assert (KDF : KD memc spv (ms_mem ms)).
{ apply (KD_frame memc spv mem5); [exact KD5|]. intros a Ha Hn1 Hn2 Hn3 Hn4. apply KF; [exact Ha | clear - Hn4; lia]. }
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks ubs0segs E5 ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU5_2) as Hcs;
pose proof (regs_kept_of_st_ok ubs0segs E5 ssx msx regs5 _ [2; 3; 4; 9; 18; 22; 26; 27]%bv HS ltac:(subst E5; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E5 sv)
by (intros r sv Hr; rewrite (st_ok_reg ubs0segs E5 ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs.
assert (WT : word_mem ubs0segs (ms_mem ms) (spv + 96) top).
{ apply (chunk_word _ _ _ 96 _ _ (proj1 (Forall_forall _ _) Hcs (mkChunk 96 (CVal 8 (SOff 8 0))) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))));
[cbn [sv_denot]; rewrite Z.add_0_r, (HE5 8%nat 8%bv eq_refl), A5_8, Z_to_bv_bv_unsigned; reflexivity | clear - Htop HH; lia]. }
clear Hcs.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
apply (GO (ms_regs ms) (ms_mem ms) (xr + 1 - left) h top left HJ5 KDF WT).
+ clear - Hxr Hleft; lia.
+ clear - Hleft; lia.
+ clear - Hxr Hleft; lia.
+ clear - Hh; lia.
+ clear - Htop; lia.
+ clear - Hh; lia.
+ rewrite (HKR 2%bv ltac:(cbv; auto 50)). exact A5_2.
+ rewrite (HKR 9%bv ltac:(cbv; auto 50)), (HK5 9%bv ltac:(cbv; auto 50)), (HK4 9%bv ltac:(cbv; auto 50)), (HK3 9%bv ltac:(cbv; auto 20)). exact A2_9.
+ rewrite (HKR 18%bv ltac:(cbv; auto 50)), (HK5 18%bv ltac:(cbv; auto 50)), (HK4 18%bv ltac:(cbv; auto 50)), (HK3 18%bv ltac:(cbv; auto 20)). exact A2_18.
+ rewrite (HKR 27%bv ltac:(cbv; auto 50)). exact Q27''.
+ rewrite (RGX 20%bv (SOff 32 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, HE5_32, Z_to_bv_bv_unsigned. reflexivity.
+ rewrite (HKR 26%bv ltac:(cbv; auto 50)). exact A5_26.
+ rewrite (RGX 19%bv _ eq_refl). eval_sr_get. apply denot_of_U'.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, (U_atom_off E5 13 xr 1), (U_atom E5 26 left)
by first [rewrite (HE5 13%nat 13%bv eq_refl); exact Q13 | rewrite (HE5 26%nat 26%bv eq_refl); exact A5_26 | clear - Hxr Hleft Hc0 HW; lia].
replace (xr + 1 - left) with ((xr + 1) - left) by (clear; lia). apply zcanon_add_mulm1; clear - Hxr Hleft Hc0 HW; lia.
+ rewrite (HKR 22%bv ltac:(cbv; auto 50)). exact A5_22.
+ rewrite (HKR 3%bv ltac:(cbv; auto 50)), (HK5 3%bv ltac:(cbv; auto 50)), (HK4 3%bv ltac:(cbv; auto 50)), (HK3 3%bv ltac:(cbv; auto 20)). exact A2_3.
+ rewrite (HKR 4%bv ltac:(cbv; auto 50)), (HK5 4%bv ltac:(cbv; auto 50)), (HK4 4%bv ltac:(cbv; auto 50)), (HK3 4%bv ltac:(cbv; auto 20)). exact A2_4.
+ unfold fl_dims. rewrite XG2.
rewrite (diff_area_scan (gcfg_of s GPAL) cur befr (cg_W s) (cg_H s) _ (proj1 HW) (proj1 HH) eq_refl ltac:(pose proof HVALS as (_ & (_ & _ & _ & _ & _ & _ & _ & _ & XL & _) & _ & _); rewrite XL; exact HN)
ltac:(pose proof HVALS as (_ & _ & HVb & _); cbn [oframe_relb] in HVb; pose proof HVb as (_ & _ & _ & _ & _ & _ & _ & _ & XL & _); rewrite XL; exact HN)
HD top hrow left xr ltac:(clear - Htop Hhr; lia) ltac:(clear - Hhr; lia) ltac:(clear - Hleft Hxr Hc0; lia) ltac:(clear - Hxr; lia)).
* subst h. reflexivity.
* exists c0. split; [exact Hc0 | exact Hne].
* exact VT0.
* exact VH1.
* intros p Hp. apply VH2. rewrite HN. exact Hp.
* destruct VL1 as (i2 & Hi2 & Hd). exists i2. split; [subst h; exact Hi2 | exact Hd].
* intros i2 x2 Hi2 Hx2. apply (VL2 i2 x2); [subst h; exact Hi2 | exact Hx2].
* destruct VR1 as (i2 & Hi2 & Hd). exists i2. split; [subst h; exact Hi2 | exact Hd].
* intros i2 x2 Hi2 Hx2. apply (VR2 i2 x2); [subst h; exact Hi2 | exact Hx2].
-
set (E2 := Ereg regs2 (map (Z_to_bv 64) [np] ++ [])).
assert (HE2 : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E2 m = getr regs2 rr) by (intros; subst E2; apply ew_Ereg_nat; assumption).
assert (HE2_32 : ew E2 32 = Z_to_bv 64 np) by (subst E2; apply (Ereg_vals regs2 [np] [] 0%nat); reflexivity).
assert (HU2_2 : bv_unsigned (ew E2 2) = spv) by (rewrite (HE2 2%nat 2%bv eq_refl), A2_2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR2 : region_ok ubs0segs E2 mem2 (YP09.mkRegion (Some 2%nat) 48 104 96 104 [mkChunk 48 (CVal 8 (SOff 32 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2_2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|]. split; [intros o Ho; apply (WRS _ HJ2); clear - Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ np); [cbn [sv_denot]; rewrite Z.add_0_r, HE2_32, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Hnp; lia | cbn; lia | apply val_mem_word_mem; exact W48b]. }
assert (HS : st_ok ubs0segs E2 (ss_fexit FL_FIDENT) (mkst regs2 (Z_to_bv 64 FL_FIDENT) mem2 (seg_rom ubs0segs))).
{ unfold ss_fexit. subst E2. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HR2 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | exact I]. }
clear HR2.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 FL_FIDENT) mem2 (seg_rom ubs0segs))) in HJ2.
jrun_to LAWS ubs0tbl_ok HS HJ2 FL_DT. { eapply wr_ok_cons_win; [reflexivity | exact HU2_2 | cbn [r_wlo r_whi]; intros _; clear - HFSv; subst spv; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 96 <= a < spv + 104) -> mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs mem2 a).
{ intros a Ha Hna. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr. destruct Hr as [<- | []]. cbn [r_base r_wlo r_whi base_val]. rewrite HU2_2. clear - Hna. lia. }
clear HF HG.
assert (KDF : KD memc spv (ms_mem ms)).
{ apply (KD_frame memc spv mem2); [exact KD2|]. intros a Ha Hn1 Hn2 Hn3 Hn4. apply KF; [exact Ha | clear - Hn4; lia]. }
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks ubs0segs E2 ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU2_2) as Hcs;
pose proof (regs_kept_of_st_ok ubs0segs E2 ssx msx regs2 _ [2; 3; 4; 9; 18; 27]%bv HS ltac:(subst E2; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E2 sv)
by (intros r sv Hr; rewrite (st_ok_reg ubs0segs E2 ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs.
assert (WT : word_mem ubs0segs (ms_mem ms) (spv + 96) 0).
{ apply (chunk_word _ _ _ 96 _ _ (proj1 (Forall_forall _ _) Hcs (mkChunk 96 (CVal 8 (SLit 0))) ltac:(cbn [In]; repeat (first [left; reflexivity | right])))); [reflexivity | clear; lia]. }
clear Hcs.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
apply (GO (ms_regs ms) (ms_mem ms) 1 1 0 0 HJ2 KDF WT).
+ clear; lia.
+ clear; lia.
+ clear - HW; lia.
+ clear; lia.
+ clear; lia.
+ clear - HH; lia.
+ rewrite (HKR 2%bv ltac:(cbv; auto 50)). exact A2_2.
+ rewrite (HKR 9%bv ltac:(cbv; auto 50)). exact A2_9.
+ rewrite (HKR 18%bv ltac:(cbv; auto 50)). exact A2_18.
+ rewrite (HKR 27%bv ltac:(cbv; auto 50)). exact Q27.
+ rewrite (RGX 20%bv (SOff 32 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, HE2_32, Z_to_bv_bv_unsigned. reflexivity.
+ rewrite (RGX 26%bv (SLit 0) eq_refl). reflexivity.
+ rewrite (RGX 19%bv (SLit 1) eq_refl). reflexivity.
+ rewrite (RGX 22%bv (SLit 1) eq_refl). reflexivity.
+ rewrite (HKR 3%bv ltac:(cbv; auto 50)). exact A2_3.
+ rewrite (HKR 4%bv ltac:(cbv; auto 50)). exact A2_4.
+ unfold fl_dims. rewrite XG2.
rewrite (diff_area_ident (gcfg_of s GPAL) cur befr (cg_W s) (cg_H s) _ (proj1 HW) (proj1 HH) eq_refl ltac:(pose proof HVALS as (_ & (_ & _ & _ & _ & _ & _ & _ & _ & XL & _) & _ & _); rewrite XL; exact HN)
ltac:(pose proof HVALS as (_ & _ & HVb & _); cbn [oframe_relb] in HVb; pose proof HVb as (_ & _ & _ & _ & _ & _ & _ & _ & XL & _); rewrite XL; exact HN)
HD); [reflexivity|].
intros p Hp. apply VID. rewrite HN. exact Hp.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
