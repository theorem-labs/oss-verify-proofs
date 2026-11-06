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
YI1h YI16 YI1z YI1k YI21 YI22
YI23 YI24 YI1w YI1j YI1s YI1t YI1l YI1m YI1n YI1o YI1v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Hypothesis RAWADD : rawadd_spec API.
Definition ss_fast : sstate :=
mkSS FL_FAST sr_atoms [ YQ0b.mkRegion (Some 18%nat) 8 16 0 0 [mkChunk 8 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (14%nat, mkAF 1 65535 0); (18%nat, mkAF 4096 CEIL_MAX 3) ] [] []).
Definition ss_f4f : sstate :=
mkSS FL_F4F sr_atoms [ YQ0b.mkRegion (Some 2%nat) 120 128 124 128 [] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (11%nat, mkAF 0 65534 0); (20%nat, mkAF 0 65534 0); (26%nat, mkAF 0 65534 0) ] [] []).
Lemma fl_fast :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st) (gen1 : Z)
(rest FP : list (Z * Z)) (tv np u23 u24 u25 : Z),
dv_pre API L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_FAST) memc (seg_rom src2segs)) mdc) (fl_post API regs0 g s N i rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE.
destruct (dv_ctx API L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE) as (ctcur & ctbef & HC & Hfi & Hbi).
pose proof PRE as (HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & Hb & HFP & HB & Htv & Hnp & Hu23 & Hu24 & Hu25
& HSV & W112 & W96 & W0 & W48 & W40 & W32 & W24 & W16 & G2 & G8 & G9 & G18 & G22 & G27 & G14 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRWv : RAW_SIZE = 48) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & _ & _ & Hngp & _ & Hfwf).
set (sp0 := spZ regs0) in *. set (spv := sp0 - 272) in *.
set (s1 := flush_upd s i gen1 (rw_cur s)) in *. set (f1 := set_fr_gen f gen1) in *.
dctx_open HC.
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hbin : In (Some b) (cg_frames s)) by (eapply nth_error_In; exact Hb).
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
assert (Hfr1 : cg_frames s1 = list_set (cg_frames s) i (Some f1)) by (subst s1 f1; apply cg_frames_flush_upd; exact Hf).
assert (Hb1in : In (Some b) (cg_frames s1)).
{ rewrite Hfr1. eapply (nth_error_In _ (i - 1)). rewrite nth_error_list_set_other by lia. exact Hb. }
pose proof Hat as (Hobj & Hraw & Hfrs).
pose proof (Hfrs b Hb1in) as Hbobj.
destruct (af_cgif_geom API Lc Ac memc mdc g s N _ HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & _).
assert (KB : forall m, KD memc spv m -> forall bb nn k, In (bb, nn) (cgif_blocks g s N) -> 0 <= k < nn -> mbyte src2segs m (bb + k) = mbyte src2segs memc (bb + k)).
{ intros m K bb nn k Hbn Hk. assert (Hbn' : In (bb, nn) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0 R1]. apply K; clear - R0 R1 Hk Hsp0 Hac; lia. }
assert (CGAT : forall m, (forall bb nn k, In (bb, nn) (cgif_blocks g s N) -> 0 <= k < nn -> mbyte src2segs m (bb + k) = mbyte src2segs memc (bb + k)) -> cgif_at m g s1).
{ intros m KBm. split; [| split].
- eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk; apply (KBm g CGIF_SIZE k); [left; reflexivity | clear - Hk HGSv; lia]].
- change (cg_raw s1) with (cg_raw s).
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) | intros k Hk; apply (KBm (cg_raw s) RAW_SIZE k); [right; left; reflexivity | clear - Hk HRWv; lia]].
- intros x Hx. assert (Hx1 : In (Some x) (cg_frames s1)) by exact Hx.
destruct (In_frames_flush_upd s i gen1 (rw_cur s) f x Hf Hx) as [-> | [Hin _]].
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KBm (fr_ptr f) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif g s N f _ _ Hfin). left. reflexivity.
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KBm (fr_ptr x) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif g s N x _ _ Hin). left. reflexivity. }
assert (SVK : forall m, KD memc spv m -> fl_saved_ok m sp0 regs0).
{ intros m K. apply (fl_saved_ok_kept memc); [exact HSV|]. intros a Ha. apply K; clear - Ha Hsp0 Hsp1 Hac; lia. }
pose proof (fl_dgo API IMG RAWADD L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE) as GO. fold sp0 in GO. fold spv in GO.
assert (HN1 : 1 <= N) by (rewrite HN; clear - HW HH; nia).
destruct (Hfgeom b Hbin) as (Hq0 & Hq1 & Hqg).
set (E := Ereg regs1 (map (Z_to_bv 64) [fr_img b] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (fr_img b)) by (subst E; apply (Ereg_vals regs1 [fr_img b] [] 0%nat); reflexivity).
assert (HU18 : bv_unsigned (ew E 18) = fr_ptr b) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; clear - Hq0 Hq1 Hac HFRv; lia).
assert (HR0 : region_ok src2segs E memc (YQ0b.mkRegion (Some 18%nat) 8 16 0 0 [mkChunk 8 (CVal 8 (SOff 32 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [clear - Hq1 Hac HFRv; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_img b)); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by (clear - Hbimg0 Hbimg1 Hac HN1; lia); reflexivity | cbn; clear - Hbimg0 Hbimg1 Hac HN1; lia | cbn; lia |].
exact (proj1 (obj_at_nth src2segs memc (fr_ptr b) LAY_Frame (frame_vals b) 1 (8, 8%N) (fr_img b) Hbobj eq_refl eq_refl)). }
assert (HFA : atoms_ok E [ (14%nat, mkAF 1 65535 0); (18%nat, mkAF 4096 CEIL_MAX 3) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU18, (HE 14%nat 14%bv eq_refl), G14, unsigned_lit_small by (clear - HH; lia).
change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r. clear - HH Hq0 Hq1 B8 Hac HFRv. repeat split; lia. }
assert (HS : st_ok src2segs E ss_fast (mkst regs1 (Z_to_bv 64 FL_FAST) memc (seg_rom src2segs))).
{ unfold ss_fast. subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HR0 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | exact HFA]. }
clear HR0 HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_FAST) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ FL_F1L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (regs_kept_of_st_ok src2segs E ssx msx regs1 _ [2; 3; 4; 8; 9; 18; 22; 27]%bv HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR0;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew E nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hvv; rewrite (st_ok_reg src2segs E ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E sv)
by (intros r sv Hr; rewrite (st_ok_reg src2segs E ssx msx r HS), Hr; reflexivity) end.
assert (A1_2 : getr (ms_regs ms) 2 = Z_to_bv 64 (sp0 - 272)) by (rewrite (HKR0 2%bv ltac:(cbv; auto 20)); exact G2).
assert (A1_8 : getr (ms_regs ms) 8 = Z_to_bv 64 g) by (rewrite (HKR0 8%bv ltac:(cbv; auto 20)); exact G8).
assert (A1_9 : getr (ms_regs ms) 9 = Z_to_bv 64 (fr_ptr f)) by (rewrite (HKR0 9%bv ltac:(cbv; auto 20)); exact G9).
assert (A1_18 : getr (ms_regs ms) 18 = Z_to_bv 64 (fr_ptr b)) by (rewrite (HKR0 18%bv ltac:(cbv; auto 20)); exact G18).
assert (A1_22 : getr (ms_regs ms) 22 = Z_to_bv 64 (fr_img f)) by (rewrite (HKR0 22%bv ltac:(cbv; auto 20)); exact G22).
assert (A1_27 : getr (ms_regs ms) 27 = Z_to_bv 64 (cg_W s)) by (rewrite (HKR0 27%bv ltac:(cbv; auto 20)); exact G27).
assert (A1_3 : getr (ms_regs ms) 3 = getr regs0 3) by (rewrite (HKR0 3%bv ltac:(cbv; auto 20)); exact G3).
assert (A1_4 : getr (ms_regs ms) 4 = getr regs0 4) by (rewrite (HKR0 4%bv ltac:(cbv; auto 20)); exact G4).
assert (A1_23 : getr (ms_regs ms) 23 = Z_to_bv 64 (fr_img b)) by (apply (RG 23%bv 32%nat _ eq_refl); exact HE32).
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc ss_fast].
eapply SR_bind.
{ eapply (fl_f1l API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
(Z.to_nat (cg_H s)) 0 FLUSH_STK sp0 FP L A mem md Lc Ac mdc _ _ HJ (KD_eq _ _ _ _ (KD_refl memc spv) K1) Hfi Hbi
ltac:(clear; lia) ltac:(clear - HH; lia) ltac:(clear - HH; lia) A1_2).
- apply (RG 20%bv 22%nat _ eq_refl). rewrite (HE 22%nat 22%bv eq_refl), G22. f_equal. clear; lia.
- apply (RG 21%bv 32%nat _ eq_refl). rewrite HE32. f_equal. clear; lia.
- rewrite (RGX 26%bv (SLit 0) eq_refl). reflexivity.
- exact A1_27. }
cbv beta. intros c' (regs2 & mem2 & pc2 & -> & HJ2 & K2 & Hpc2 & HK2). clear HS HJ RG RGX.
assert (K2' : KD memc spv mem2) by (exact (KD_eq _ _ _ _ (KD_eq _ _ _ _ (KD_refl memc spv) K1) K2)).
assert (A2_2 : getr regs2 2 = Z_to_bv 64 (sp0 - 272)) by (rewrite (HK2 2%bv ltac:(cbv; auto 20)); exact A1_2).
assert (A2_8 : getr regs2 8 = Z_to_bv 64 g) by (rewrite (HK2 8%bv ltac:(cbv; auto 20)); exact A1_8).
assert (A2_9 : getr regs2 9 = Z_to_bv 64 (fr_ptr f)) by (rewrite (HK2 9%bv ltac:(cbv; auto 20)); exact A1_9).
assert (A2_18 : getr regs2 18 = Z_to_bv 64 (fr_ptr b)) by (rewrite (HK2 18%bv ltac:(cbv; auto 20)); exact A1_18).
assert (A2_22 : getr regs2 22 = Z_to_bv 64 (fr_img f)) by (rewrite (HK2 22%bv ltac:(cbv; auto 20)); exact A1_22).
assert (A2_23 : getr regs2 23 = Z_to_bv 64 (fr_img b)) by (rewrite (HK2 23%bv ltac:(cbv; auto 20)); exact A1_23).
assert (A2_3 : getr regs2 3 = getr regs0 3) by (rewrite (HK2 3%bv ltac:(cbv; auto 20)); exact A1_3).
assert (A2_4 : getr regs2 4 = getr regs0 4) by (rewrite (HK2 4%bv ltac:(cbv; auto 20)); exact A1_4).
clear HK2 HKR0 A1_2 A1_8 A1_9 A1_18 A1_22 A1_27 A1_3 A1_4 A1_23 K1 K2 ms.
assert (WRS : forall m', journal src2_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac m' mdc -> forall a, spv + 124 <= a < spv + 128 -> writable_at src2segs m' a).
{ intros m' HJm a Ha. pose proof HJm as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hw) & _). apply Hw. clear - Ha HFSv. subst spv. lia. }
destruct Hpc2 as [[-> (top & c0 & Htop & Hc0 & Hne & Q26 & Q27)] | [-> Q27]].
-
eapply SR_bind.
{ eapply (fl_f2 API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
FLUSH_STK sp0 FP L A mem md Lc Ac mdc regs2 mem2 top HJ2 K2' Hfi Hbi eq_refl ltac:(clear - HFSv; lia) Htop A2_2 A2_22 A2_23 Q27 Q26). }
cbv beta. intros c' (regs3 & mem3 & hrow & -> & HJ3 & K3 & Hhr & Q20 & Q21 & Q27' & HK3).
set (h := hrow + 1 - top).
assert (Hh : 1 <= h /\ top + h <= cg_H s) by (subst h; clear - Hhr Htop; lia).
eapply SR_bind.
{ eapply (fl_f3 API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
FLUSH_STK sp0 FP L A mem md Lc Ac mdc regs3 mem3 top hrow c0 HJ3 K3 Hfi Hbi ltac:(clear - Htop Hhr; lia) ltac:(clear - Hhr; lia) Hc0 Hne Q21 Q20).
- rewrite (HK3 22%bv ltac:(cbv; auto 20)). exact A2_22.
- rewrite (HK3 23%bv ltac:(cbv; auto 20)). exact A2_23.
- exact Q27'.
- rewrite (HK3 26%bv ltac:(cbv; auto 20)). exact Q26. }
cbv beta. intros c' (regs4 & mem4 & left & -> & HJ4 & K4 & Hleft & Q20' & Q10 & Q5 & Q21' & HK4).
assert (K4' : KD memc spv mem4) by (exact (KD_eq _ _ _ _ K3 K4)).
eapply SR_bind.
{ eapply (fl_f4 API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
FLUSH_STK sp0 FP L A mem md Lc Ac mdc regs4 mem4 top h c0 HJ4 K4' Hfi Hbi ltac:(clear - Htop; lia) ltac:(clear - Hh; lia) ltac:(clear - Hh; lia) Hc0 Hne).
- rewrite Q5. subst h. reflexivity.
- exact Q10.
- exact Q21'.
- rewrite (HK4 22%bv ltac:(cbv; auto 50)), (HK3 22%bv ltac:(cbv; auto 20)). exact A2_22.
- rewrite (HK4 23%bv ltac:(cbv; auto 50)), (HK3 23%bv ltac:(cbv; auto 20)). exact A2_23.
- rewrite (HK4 27%bv ltac:(cbv; auto 50)). exact Q27'.
- rewrite (HK4 26%bv ltac:(cbv; auto 50)), (HK3 26%bv ltac:(cbv; auto 20)). exact Q26. }
cbv beta. intros c' (regs5 & mem5 & xr & -> & HJ5 & K5 & Hxr & Q11 & Q27'' & HK5).
assert (K5' : KD memc spv mem5) by (exact (KD_eq _ _ _ _ K4' K5)).
set (E5 := Ereg regs5 ([] : list word)).
assert (HE5 : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E5 m = getr regs5 rr) by (intros; subst E5; apply ew_Ereg_nat; assumption).
assert (A5_2 : getr regs5 2 = Z_to_bv 64 (sp0 - 272)) by (rewrite (HK5 2%bv ltac:(cbv; auto 50)), (HK4 2%bv ltac:(cbv; auto 50)), (HK3 2%bv ltac:(cbv; auto 20)); exact A2_2).
assert (A5_26 : getr regs5 26 = Z_to_bv 64 top) by (rewrite (HK5 26%bv ltac:(cbv; auto 50)), (HK4 26%bv ltac:(cbv; auto 50)), (HK3 26%bv ltac:(cbv; auto 20)); exact Q26).
assert (A5_20 : getr regs5 20 = Z_to_bv 64 left) by (rewrite (HK5 20%bv ltac:(cbv; auto 50)); exact Q20').
assert (HU5_2 : bv_unsigned (ew E5 2) = spv) by (rewrite (HE5 2%nat 2%bv eq_refl), A5_2; subst spv; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR5 : region_ok src2segs E5 mem5 (YQ0b.mkRegion (Some 2%nat) 120 128 124 128 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU5_2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply (WRS _ HJ5); lia | constructor]. }
assert (HFA5 : atoms_ok E5 [ (2%nat, mkAF CEIL_MIN (2^63) 4); (11%nat, mkAF 0 65534 0); (20%nat, mkAF 0 65534 0); (26%nat, mkAF 0 65534 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU5_2, (HE5 11%nat 11%bv eq_refl), (HE5 20%nat 20%bv eq_refl), (HE5 26%nat 26%bv eq_refl), Q11, A5_20, A5_26.
rewrite !unsigned_lit_small by (clear - Hxr Hleft Hc0 Htop Hh HW HH; lia). change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
clear - Hsp0 Hsp1 Hsp16 Hxr Hleft Hc0 Htop Hh HW HH Hac. repeat split; lia. }
assert (HS : st_ok src2segs E5 ss_f4f (mkst regs5 (Z_to_bv 64 FL_F4F) mem5 (seg_rom src2segs))).
{ unfold ss_f4f. subst E5. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HR5 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | exact HFA5]. }
clear HR5 HFA5.
change mem5 with (ms_mem (mkst regs5 (Z_to_bv 64 FL_F4F) mem5 (seg_rom src2segs))) in HJ5.
jrun_to LAWS src2tbl_ok HS HJ5 FL_DT. { eapply wr_ok_cons_win; [reflexivity | exact HU5_2 | cbn [r_wlo r_whi]; intros _; clear - HFSv; subst spv; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 124 <= a < spv + 128) -> mbyte src2segs (ms_mem ms) a = mbyte src2segs mem5 a).
{ intros a Ha Hna. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr. destruct Hr as [<- | []]. cbn [r_base r_wlo r_whi base_val]. rewrite HU5_2. clear - Hna. lia. }
clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks src2segs E5 ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU5_2) as Hcs;
pose proof (regs_kept_of_st_ok src2segs E5 ssx msx regs5 _ [2; 3; 4; 5; 8; 9; 18; 22; 26; 20; 27]%bv HS ltac:(subst E5; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew E5 nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hvv; rewrite (st_ok_reg src2segs E5 ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E5 sv)
by (intros r sv Hr; rewrite (st_ok_reg src2segs E5 ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
apply (GO (ms_regs ms) mem5 (ms_mem ms) (xr + 1 - left) h top left HJ5 K5' KF).
+ eapply (val_of_chunk_ok src2segs E5 _ _ 124 2%N (SOff 20 0)); [subst spv; exact (proj1 (Forall_forall _ _) Hcs (mkChunk 124 (CVal 2 (SOff 20 0))) ltac:(cbn [In]; tauto)) | cbn [sv_denot]; rewrite Z.add_0_r, (HE5 20%nat 20%bv eq_refl), A5_20, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Hleft Hc0 HW Hxr; lia | cbn; lia].
+ eapply (val_of_chunk_ok src2segs E5 _ _ 126 2%N (SOff 26 0)); [subst spv; exact (proj1 (Forall_forall _ _) Hcs (mkChunk 126 (CVal 2 (SOff 26 0))) ltac:(cbn [In]; tauto)) | cbn [sv_denot]; rewrite Z.add_0_r, (HE5 26%nat 26%bv eq_refl), A5_26, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Htop Hh HH; lia | cbn; lia].
+ clear - Hxr Hleft; lia.
+ clear - Hleft; lia.
+ clear - Hxr Hleft; lia.
+ clear - Hh; lia.
+ clear - Htop; lia.
+ clear - Hh; lia.
+ rewrite (HKR 2%bv ltac:(cbv; auto 50)). exact A5_2.
+ rewrite (HKR 8%bv ltac:(cbv; auto 50)), (HK5 8%bv ltac:(cbv; auto 50)), (HK4 8%bv ltac:(cbv; auto 50)), (HK3 8%bv ltac:(cbv; auto 20)). exact A2_8.
+ rewrite (HKR 9%bv ltac:(cbv; auto 50)), (HK5 9%bv ltac:(cbv; auto 50)), (HK4 9%bv ltac:(cbv; auto 50)), (HK3 9%bv ltac:(cbv; auto 20)). exact A2_9.
+ rewrite (HKR 18%bv ltac:(cbv; auto 50)), (HK5 18%bv ltac:(cbv; auto 50)), (HK4 18%bv ltac:(cbv; auto 50)), (HK3 18%bv ltac:(cbv; auto 20)). exact A2_18.
+ rewrite (HKR 22%bv ltac:(cbv; auto 50)), (HK5 22%bv ltac:(cbv; auto 50)), (HK4 22%bv ltac:(cbv; auto 50)), (HK3 22%bv ltac:(cbv; auto 20)). exact A2_22.
+ rewrite (HKR 27%bv ltac:(cbv; auto 50)). exact Q27''.
+ rewrite (HKR 26%bv ltac:(cbv; auto 50)). exact A5_26.
+ rewrite (HKR 20%bv ltac:(cbv; auto 50)). exact A5_20.
+ rewrite (RGX 12%bv _ eq_refl). eval_sr_get. apply denot_of_U'.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, (U_atom_off E5 11 xr 1), (U_atom E5 20 left)
by first [rewrite (HE5 11%nat 11%bv eq_refl); exact Q11 | rewrite (HE5 20%nat 20%bv eq_refl); exact A5_20 | clear - Hxr Hleft Hc0 HW; lia].
replace (xr + 1 - left) with ((xr + 1) - left) by (clear; lia). apply zcanon_add_mulm1; clear - Hxr Hleft Hc0 HW; lia.
+ apply (RG 19%bv 5%nat _ eq_refl). rewrite (HE5 5%nat 5%bv eq_refl), (HK5 5%bv ltac:(cbv; auto 50)). rewrite Q5. subst h. reflexivity.
+ rewrite (HKR 3%bv ltac:(cbv; auto 50)), (HK5 3%bv ltac:(cbv; auto 50)), (HK4 3%bv ltac:(cbv; auto 50)), (HK3 3%bv ltac:(cbv; auto 20)). exact A2_3.
+ rewrite (HKR 4%bv ltac:(cbv; auto 50)), (HK5 4%bv ltac:(cbv; auto 50)), (HK4 4%bv ltac:(cbv; auto 50)), (HK3 4%bv ltac:(cbv; auto 20)). exact A2_4.
-
set (E2 := Ereg regs2 ([] : list word)).
assert (HE2 : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E2 m = getr regs2 rr) by (intros; subst E2; apply ew_Ereg_nat; assumption).
assert (HU2_2 : bv_unsigned (ew E2 2) = spv) by (rewrite (HE2 2%nat 2%bv eq_refl), A2_2; subst spv; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR2 : region_ok src2segs E2 mem2 (YQ0b.mkRegion (Some 2%nat) 120 128 124 128 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2_2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply (WRS _ HJ2); lia| constructor]. }
assert (HFA2 : atoms_ok E2 [ (2%nat, mkAF CEIL_MIN (2^63) 4) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2_2. change (2 ^ 4) with 16. clear - Hsp0 Hsp1 Hsp16 Hac. repeat split; lia. }
assert (HS : st_ok src2segs E2 ss_ident (mkst regs2 (Z_to_bv 64 FL_IDENT) mem2 (seg_rom src2segs))).
{ unfold ss_ident. subst E2. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HR2 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | exact HFA2]. }
clear HR2 HFA2.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 FL_IDENT) mem2 (seg_rom src2segs))) in HJ2.
jrun_to LAWS src2tbl_ok HS HJ2 FL_DT. { eapply wr_ok_cons_win; [reflexivity | exact HU2_2 | cbn [r_wlo r_whi]; intros _; clear - HFSv; subst spv; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 124 <= a < spv + 128) -> mbyte src2segs (ms_mem ms) a = mbyte src2segs mem2 a).
{ intros a Ha Hna. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr. destruct Hr as [<- | []]. cbn [r_base r_wlo r_whi base_val]. rewrite HU2_2. clear - Hna. lia. }
clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks src2segs E2 ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU2_2) as Hcs;
pose proof (regs_kept_of_st_ok src2segs E2 ssx msx regs2 _ [2; 3; 4; 8; 9; 18; 22; 27]%bv HS ltac:(subst E2; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E2 sv)
by (intros r sv Hr; rewrite (st_ok_reg src2segs E2 ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
apply (GO (ms_regs ms) mem2 (ms_mem ms) 1 1 0 0 HJ2 K2' KF).
+ eapply (val_of_chunk_ok src2segs E2 _ _ 124 2%N (SLit 0)); [subst spv; exact (proj1 (Forall_forall _ _) Hcs (mkChunk 124 (CVal 2 (SLit 0))) ltac:(cbn [In]; tauto)) | reflexivity | cbn; lia | cbn; lia].
+ eapply (val_of_chunk_ok src2segs E2 _ _ 126 2%N (SLit 0)); [subst spv; exact (proj1 (Forall_forall _ _) Hcs (mkChunk 126 (CVal 2 (SLit 0))) ltac:(cbn [In]; tauto)) | reflexivity | cbn; lia | cbn; lia].
+ clear; lia.
+ clear; lia.
+ clear - HW; lia.
+ clear; lia.
+ clear; lia.
+ clear - HH; lia.
+ rewrite (HKR 2%bv ltac:(cbv; auto 50)). exact A2_2.
+ rewrite (HKR 8%bv ltac:(cbv; auto 50)). exact A2_8.
+ rewrite (HKR 9%bv ltac:(cbv; auto 50)). exact A2_9.
+ rewrite (HKR 18%bv ltac:(cbv; auto 50)). exact A2_18.
+ rewrite (HKR 22%bv ltac:(cbv; auto 50)). exact A2_22.
+ rewrite (HKR 27%bv ltac:(cbv; auto 50)). exact Q27.
+ rewrite (RGX 26%bv (SLit 0) eq_refl). reflexivity.
+ rewrite (RGX 20%bv (SLit 0) eq_refl). reflexivity.
+ rewrite (RGX 12%bv (SLit 1) eq_refl). reflexivity.
+ rewrite (RGX 19%bv (SLit 1) eq_refl). reflexivity.
+ rewrite (HKR 3%bv ltac:(cbv; auto 50)). exact A2_3.
+ rewrite (HKR 4%bv ltac:(cbv; auto 50)). exact A2_4.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
