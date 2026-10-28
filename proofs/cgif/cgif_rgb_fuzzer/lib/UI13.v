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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3l YI00 YI02 YI01 YI03
UI1e UI1d UI39 UI1i UI20 UI59 UI56 YI0x UI57
UI1h UI1g UI16 UI19 UI17 UI18 UI11
UI12 UI15.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Ltac lia_try := rc_inst; first [ solve [YN03.lf_prune0; YN03.lf_lia_orig] | solve [YN03.lf_prune1; YN03.lf_lia_orig] ].
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition AF_SLOW : Z := Eval vm_compute in (ubs2_A_cgif_addframe + 0x158).
Definition AF_FAST : Z := Eval vm_compute in (ubs2_A_cgif_addframe + 0x25c).
Definition AF_BCMPRET : Z := Eval vm_compute in (ubs2_A_cgif_addframe + 0x274).
Definition BCMP_CLOB : list reg := [10; 11; 12; 13; 14]%bv.
End c.
Ltac reg_nowG HS tac :=
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
lazymatch goal with |- getr _ ?rr = _ =>
let T := fresh "T" in
pose proof (st_ok_reg ubs2segs Ec ssc msc rr HS) as T; eval_sr_get_in T; cbn [sv_denot] in T;
repeat (rewrite ew_havoc_old in T; [|nat_lt_lit]); rewrite ?Z.add_0_r in T;
cbn [ms_regs mkst] in T; cbn [ms_regs mkst]; rewrite T; clear T; tac
end
end.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition B_regions (ih : Z) : list YQ0b.region :=
[ YQ0b.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) ; af_Rg None None None (Some ih) ; af_Rcf ;
af_Rfr_part 12 68 0 40 0 0 ].
Definition B_facts : list (nat * afact) :=
af_facts ++ cf_facts ++ [(58%nat, mkAF 1 65535 0); (59%nat, mkAF 1 65535 0); (12%nat, mkAF 4096 (CEIL_MAX - 40) 4);
(69%nat, mkAF 4096 CEIL_MAX 0); (70%nat, mkAF 0 4294967295 0); (72%nat, mkAF 0 65535 0)].
Definition ss_slow (ih : Z) : sstate := mkSS AF_SLOW sr_atoms (B_regions ih) None (mkFacts B_facts [] []).
Definition ss_fast (ih : Z) : sstate := mkSS AF_FAST sr_atoms (B_regions ih) None (mkFacts B_facts [] []).
Definition ss_slowU : sstate :=
mkSS AF_SLOW sr_atoms [af_Rg None None None None] None (mkFacts [(58%nat, mkAF 1 65535 0); (59%nat, mkAF 1 65535 0); (67%nat, mkAF 1 2 0)] [] []).
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis FLUSH : flush_spec API.
Definition B_pre (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (regs0 regs1 : bvmap 5 word) (Lc : layout) (Ac : astate)
(memc : word -> option byte) (mdc : Model) (g N : Z) (s0 s : cgif_st) (rest FP : list (Z * Z)) (fh : frame_st)
(cfp lpal lpa img fattr fgen delay nlp tidx : Z) : Prop :=
let sp0 := spZ regs0 in
let CB := [(img, N)] in
journal ubs2_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc /\ st_init_done Ac = true /\
YK0s.ret_ok (getr regs0 1) /\ sp0 mod 16 = 0 /\ getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) /\
cgif_at memc g s /\ cgif_wf s N /\ same_geom s s0 /\
nth_error (cg_frames s) (Z.to_nat (cg_ihead s)) = Some (Some fh) /\
(Z.land fattr 1 = 0 -> Z.land (cg_attr s) 4 = 0) /\
obj_at ubs2segs memc cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] /\
cfp mod 8 = 0 /\ sp0 <= cfp /\ cfp + 32 <= 2 ^ 63 /\
pal_ok mem sp0 fattr lpal nlp /\
(forall b n a, In (b, n) (cgif_blocks g s N) -> b <= a < b + n -> inFP FP a) /\
Permutation (blocks Lc Ac) (cgif_blocks g s N ++ CB ++ rest) /\
af_saved_ok memc sp0 regs0 /\
getr regs1 2 = Z_to_bv 64 (sp0 - 64) /\ getr regs1 8 = Z_to_bv 64 g /\ getr regs1 9 = Z_to_bv 64 cfp /\
getr regs1 12 = Z_to_bv 64 (fr_ptr fh) /\
getr regs1 19 = Z_to_bv 64 (Z.land fattr 4) /\ getr regs1 20 = Z_to_bv 64 (cg_ihead s) /\
af_untouched regs0 regs1.
Lemma af_slow :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (rest FP : list (Z * Z)) (fh : frame_st)
(cfp lpal lpa img fattr fgen delay nlp tidx : Z),
B_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP fh cfp lpal lpa img fattr fgen delay nlp tidx ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_SLOW) memc (seg_rom ubs2segs)) mdc)
(af_post API regs0 g N s0 [(img, N)] rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP fh cfp lpal lpa img fattr fgen delay nlp tidx
(HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hgeom & Hfh & HnoCT & Hcf & Hcf8 & Hcflo & Hcfhi & Hlpa & HFP & HB & HSV & G2 & G8 & G9 & G12 & G19 & G20 & HUT).
pose proof HUT as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & Hih & Hfwf).
assert (HN1 : 1 <= N) by (rewrite HN; clear - HW1 HH1; nia).
assert (Hfin : In (Some fh) (cg_frames s)) by (eapply nth_error_In; exact Hfh).
destruct (af_cgif_geom API Lc Ac memc mdc g s N _ HH0 HB) as (_ & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom fh Hfin) as (Hf0 & Hf1 & Hfg).
destruct (af_frame_geom API Lc Ac memc mdc g s N _ fh HH0 HB Hfin) as (Hfblk & Hfimgblk & Hflpal).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr fh) FRAME_SIZE HH0 Hfblk ltac:(lia)) as (_ & _ & Hf16).
assert (Himgin : In (img, N) (blocks Lc Ac)).
{ apply (Permutation_in _ (Permutation_sym HB)). apply in_app_iff. right. left. reflexivity. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc img N HH0 Himgin) as [Him0 Him1].
destruct (blocks_range _ _ LAWS Lc Ac memc mdc (fr_img fh) N HH0 Hfimgblk) as [Hfi0 Hfi1].
pose proof Hat as (Hobj & Hraw & Hfrs). pose proof (Hfrs fh Hfin) as Hfobj.
pose proof (obj_at_range _ _ _ _ _ Hcf) as Rcf. pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (obj_at_range _ _ _ _ _ Hfobj) as Rf.
pose proof (Rcf 2%nat fattr eq_refl) as Rfattr. pose proof (Rcf 0%nat lpal eq_refl) as Rlpal. pose proof (Rcf 5%nat nlp eq_refl) as Rnlp.
cbn [nth snd LAY_FrameConfig Z.of_N] in Rfattr, Rlpal, Rnlp.
pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. cbn [nth snd LAY_CGIF Z.of_N] in RW, RH.
pose proof (Rf 2%nat (fr_attr fh) eq_refl) as Rfa. pose proof (Rf 4%nat (fr_delay fh) eq_refl) as Rfd. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfa, Rfd.
set (E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s (frame_vals fh)).
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HK regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (af_HC regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n j v, _ -> _ -> ew E n = _) as HC.
pose proof (af_HX regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n j v, _ -> _ -> ew E n = _) as HX.
pose proof (af_HM regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n j v, _ -> _ -> ew E n = _) as HM.
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HFA : atoms_ok E [(58%nat, mkAF 1 65535 0); (59%nat, mkAF 1 65535 0); (67%nat, mkAF 1 2 0)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (HX 58%nat 7%nat _ eq_refl eq_refl), (HX 59%nat 8%nat _ eq_refl eq_refl), (HX 67%nat 16%nat _ eq_refl eq_refl).
rewrite !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
assert (HS : st_ok ubs2segs E ss_slowU (mkst regs1 (Z_to_bv 64 AF_SLOW) memc (seg_rom ubs2segs))).
{ unfold ss_slowU. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | | split; [exact HFA | split; exact I]].
- constructor; [|constructor]. exact (af_Rg_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) memc g None None None None HU8 ltac:(lia) ltac:(lia) Hobj I I I I).
- cbn [pairwise_disjoint all_disjoint]. split; exact I. }
assert (CTB : forall attr lp nl, 0 <= lp < 2 ^ 64 -> 0 <= nl ->
(Z.land attr 1 = 0 -> Z.land (cg_attr s) 4 = 0) ->
(Z.land attr 1 <> 0 -> exists lp', Z_to_bv 64 lp' = Z_to_bv 64 lp /\ In (lp', 3 * nl) (blocks Lc Ac)) ->
In (ct_sel attr lp (cg_pal s), 3 * ct_sel attr nl (cg_ngp s)) (blocks Lc Ac)).
{ intros attr lp nl Rlp Rnl0 Hg Hl. unfold ct_sel. destruct (Z.eqb_spec (Z.land attr 1) 0) as [Hz|Hz].
- apply (Permutation_in _ (Permutation_sym HB)). apply in_app_iff. left. right. right. apply in_app_iff. left.
unfold pal_blocks. rewrite (Hg Hz). cbn. left. reflexivity.
- destruct (Hl Hz) as (lp' & Heq & Hin). destruct (blocks_range _ _ LAWS Lc Ac memc mdc lp' (3 * nl) HH0 Hin) as [R0 R1].
assert (lp' = lp).
{ apply (f_equal bv_unsigned) in Heq. rewrite !unsigned_lit_small in Heq by lia. exact Heq. }
subst lp'. exact Hin. }
assert (CTb : In (ct_sel (fr_attr fh) (fr_lpal fh) (cg_pal s), 3 * ct_sel (fr_attr fh) (fr_nlp fh) (cg_ngp s)) (blocks Lc Ac)).
{ pose proof (Rf 0%nat (fr_lpal fh) eq_refl) as Rflp. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rflp.
pose proof (Rf 5%nat (fr_nlp fh) eq_refl) as Rfnl0. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfnl0.
apply CTB; [lia | lia | exact (proj1 (Hfwf fh Hfin)) |]. intros Hz. exists (fr_lpal fh). split; [reflexivity | exact (Hflpal Hz)]. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 CTb) as [Sb0 Sb1'].
assert (Sb1 : ct_sel (fr_attr fh) (fr_lpal fh) (cg_pal s) + 3 * ct_sel (fr_attr fh) (fr_nlp fh) (cg_ngp s) <= 2 ^ 63) by (clear - Sb1' Hac; lia).
pose proof (Rcf 5%nat nlp eq_refl) as Rnl. pose proof (Rf 5%nat (fr_nlp fh) eq_refl) as Rfnl. pose proof (Rg 9%nat (cg_ngp s) eq_refl) as Rngp.
cbn [nth snd LAY_Frame LAY_FrameConfig LAY_CGIF app Z.of_N] in Rnl, Rfnl, Rngp.
assert (Hszb : 0 <= 3 * ct_sel (fr_attr fh) (fr_nlp fh) (cg_ngp s)) by (unfold ct_sel; destruct (Z.land (fr_attr fh) 1 =? 0); lia).
destruct (rdn_of_present ubs2_msyms memc (Z.to_nat (3 * ct_sel (fr_attr fh) (fr_nlp fh) (cg_ngp s))) (ct_sel (fr_attr fh) (fr_lpal fh) (cg_pal s))
ltac:(intros i Hi; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc _ _ i HH0 CTb ltac:(lia)))) ltac:(lia) ltac:(lia)) as (ctbef & Rbt & _).
assert (CTcur : 4096 <= ct_sel fattr lpal (cg_pal s) /\
ct_sel fattr lpal (cg_pal s) + 3 * ct_sel fattr nlp (cg_ngp s) <= 2 ^ 63 /\
0 <= 3 * ct_sel fattr nlp (cg_ngp s) /\
exists ctcur, rdn ubs2segs memc (Z_to_bv 64 (ct_sel fattr lpal (cg_pal s))) (Z.to_nat (3 * ct_sel fattr nlp (cg_ngp s))) = Some ctcur).
{ destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Hz|Hz].
- assert (CTc : In (ct_sel fattr lpal (cg_pal s), 3 * ct_sel fattr nlp (cg_ngp s)) (blocks Lc Ac)).
{ apply CTB; [lia | lia | exact HnoCT |]. intros Hz'. exfalso. exact (Hz' Hz). }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 CTc) as [Sc0 Sc1].
assert (Hszc : 0 <= 3 * ct_sel fattr nlp (cg_ngp s)) by (unfold ct_sel; destruct (Z.land fattr 1 =? 0); lia).
destruct (rdn_of_present ubs2_msyms memc (Z.to_nat (3 * ct_sel fattr nlp (cg_ngp s))) (ct_sel fattr lpal (cg_pal s))
ltac:(intros i Hi; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc _ _ i HH0 CTc ltac:(lia)))) ltac:(lia) ltac:(lia)) as (ctcur & Rct & _).
split; [exact Sc0|]. split; [clear - Sc1 Hac; lia|]. split; [exact Hszc|]. exists ctcur. exact Rct.
- destruct (pal_ok_now MR ADDFRAME_STK _ FP L A mem md _ _ _ _ fattr lpal nlp HJ Hlpa Hz) as (P0 & P1 & P2 & _).
assert (E1 : (Z.land fattr 1 =? 0) = false) by (apply Z.eqb_neq; exact Hz).
unfold ct_sel. rewrite E1. cbv beta iota.
destruct (rdn_of_mbyteG memc (Z.to_nat (3 * nlp)) lpal ltac:(intros i Hi; apply P2; clear - Hi Rnl; lia) ltac:(clear - P0 Hceil HASv Hac; lia) ltac:(clear - P1 Rnl; lia)) as (ctcur & Rct & _).
split; [clear - P0 Hceil HASv Hac; lia|]. split; [exact P1|]. split; [clear - Rnl; lia|]. exists ctcur. exact Rct. }
destruct CTcur as (Sc0 & Sc1 & Hszc & ctcur & Rct).
assert (Dif : img + N <= fr_img fh \/ fr_img fh + N <= img).
{ pose proof (heap_sep_app API Lc Ac memc mdc (cgif_blocks g s N) ([(img, N)] ++ rest) (fr_img fh, N) (img, N) HH0 HB
ltac:(apply (frame_blocks_in_cgif g s N fh); [exact Hfin | right; left; reflexivity]) ltac:(left; reflexivity)) as Hs. cbn [fst snd] in Hs. lia. }
assert (Hfhcf : obj_at ubs2segs memc (fr_ptr fh) LAY_FrameConfig (firstn 7 (frame_vals fh))).
{ rewrite LAY_Frame_split in Hfobj. apply (proj1 (obj_at_app ubs2segs memc (fr_ptr fh) LAY_FrameConfig [(32, 1%N); (33, 1%N)] (firstn 7 (frame_vals fh)) (skipn 7 (frame_vals fh)) eq_refl)). exact Hfobj. }
assert (Hfg' : g + CGIF_SIZE <= fr_ptr fh \/ fr_ptr fh + 29 <= g) by (clear - Hfg HFSv; lia).
assert (Hf8 : fr_ptr fh mod 8 = 0).
{ clear - Hf16 Hf0. rewrite <- (Z.mod_mod_divide (fr_ptr fh) 16 8) by (exists 2; reflexivity). rewrite Hf16. reflexivity. }
assert (Ofr : nth_error (cgif_vals s) (Z.to_nat (cg_ihead s)) = Some (fr_ptr fh)).
{ destruct Hih as [Hi | [Hi _]]; rewrite Hi in Hfh |- *; [change (Z.to_nat 1) with 1%nat in Hfh |- * | change (Z.to_nat 2) with 2%nat in Hfh |- *];
unfold cgif_vals; cbn [nth_error]; rewrite (@nth_error_nth _ (cg_frames s) _ (Some fh) None Hfh); reflexivity. }
assert (Hih' : cg_ihead s = 1 \/ cg_ihead s = 2) by (destruct Hih as [Hi | [Hi _]]; [left | right]; exact Hi).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_SLOW) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ AF_LOOP. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
name_ms HS ms0. cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms0 x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF.
assert (KM : forall a, mbyte ubs2segs (ms_mem ms0) a = mbyte ubs2segs memc a) by (intros a; apply mbyte_of_eq; exact K1).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (af_loop API IMG (ms_mem ms0) g cfp (fr_ptr fh) img (fr_img fh) (cg_W s) (cg_H s) N (cg_ihead s) (cgif_vals s) [lpal; img; fattr; fgen; delay; nlp; tidx] (firstn 7 (frame_vals fh))
fattr tidx nlp lpal (fr_attr fh) (fr_ctidx fh) (fr_nlp fh) (fr_lpal fh) (cg_ngp s) (cg_pal s) ctcur ctbef) with (n := Z.to_nat N) (k := 0);
[ eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros i Hi; apply KM]
| reflexivity | reflexivity
| eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros i Hi; apply KM]
| reflexivity | reflexivity | reflexivity | reflexivity
| eapply obj_at_transport_range; [exact Hfhcf | exact lay_inside_FrameConfig | intros i Hi; apply KM]
| reflexivity | reflexivity | reflexivity | reflexivity
| exact Hg0 | exact Hg1 | exact Hg16 | lia | exact Hcfhi | exact Hcf8 | exact Hf0 | lia | exact Hf8
| lia | exact Hfg' | lia
| rewrite (rdn_ext ubs2segs (ms_mem ms0) memc) by exact K1; exact Rct
| rewrite (rdn_ext ubs2segs (ms_mem ms0) memc) by exact K1; exact Rbt
| exact Sc0 | exact Sc1 | exact Sb0 | exact Sb1
| intros i Hi; unfold present; rewrite K1; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc img N i HH0 Himgin Hi))
| intros i Hi; unfold present; rewrite K1; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc (fr_img fh) N i HH0 Hfimgblk Hi))
| exact Him0 | exact Him1 | exact Hfi0 | exact Hfi1 | lia | exact Dif
| exact Ofr | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact HN | exact Hih'
| exact HJ | intros x; reflexivity | lia | clear - HN1; rewrite Z2Nat.id by lia; lia | clear - HN1; lia
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 8%nat 8%bv eq_refl); exact G8)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 9%nat 9%bv eq_refl); exact G9)
| reg_nowF HS ltac:(reflexivity)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; exact (HX 67%nat 16%nat _ eq_refl eq_refl))
| reg_nowF HS ltac:(reflexivity) ]. }
cbv beta. intros c' (regs' & mem' & pc' & -> & Hpc' & HJ' & K' & HK').
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (regs_kept_of_st_ok ubs2segs Ec ssc msc regs1 _ [2; 3; 4; 8; 9; 19; 21; 23; 24; 25; 26; 27]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HKR end.
cbn [ms_regs mkst] in HKR.
assert (KF : forall a, mbyte ubs2segs mem' a = mbyte ubs2segs memc a) by (intros a; unfold mbyte; rewrite K', K1; reflexivity).
assert (RR : forall r : reg, In r [2; 3; 4; 8; 9; 19; 21; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs1 r).
{ intros r Hr. rewrite (HK' r) by (revert Hr; clear; intros Hr; cbv in Hr |- *; tauto). apply (HKR r Hr). }
assert (Q20 : getr regs' 20 = Z_to_bv 64 (cg_ihead s)).
{ rewrite (HK' 20%bv ltac:(cbv; auto 20)). reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; exact (HX 67%nat 16%nat _ eq_refl eq_refl)). }
assert (UT : af_untouched regs0 regs').
{ split; [|split; [|split; [|split; [|split; [|split]]]]];
[ rewrite (RR 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (RR 4%bv ltac:(cbv; auto 20)); exact G4
| rewrite (RR 23%bv ltac:(cbv; auto 20)); exact G23 | rewrite (RR 24%bv ltac:(cbv; auto 20)); exact G24
| rewrite (RR 25%bv ltac:(cbv; auto 20)); exact G25 | rewrite (RR 26%bv ltac:(cbv; auto 20)); exact G26
| rewrite (RR 27%bv ltac:(cbv; auto 20)); exact G27 ]. }
destruct Hpc' as [-> | ->]; cycle 1.
-
eapply (af_same API IMG L A mem md regs0 regs' Lc Ac mem' mdc g N s0 s _ rest FP (Z.to_nat (cg_ihead s)) fh);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | | exact Hwf | exact Hgeom | exact Hfh
| intros a Ha; apply (HFP (fr_ptr fh) FRAME_SIZE a); [apply (frame_blocks_in_cgif g s N fh); [exact Hfin | left; reflexivity] | exact Ha]
| exact HB | apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply KF]
| rewrite (RR 2%bv ltac:(cbv; auto 20)); exact G2 | rewrite (RR 8%bv ltac:(cbv; auto 20)); exact G8
| rewrite Q20, Z2Nat.id by lia; reflexivity | exact UT ].
eapply (cgif_at_kept memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply KF].
-
eapply (af_C API IMG FLUSH L A mem md regs0 regs' Lc Ac mem' mdc g N s0 s rest FP cfp lpal lpa img fattr fgen delay nlp tidx (Z.land fattr 4));
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hgeom | exact HnoCT
| eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply KF] | exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact HFP | exact HB
| apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply KF]
| rewrite (RR 2%bv ltac:(cbv; auto 20)); exact G2 | rewrite (RR 8%bv ltac:(cbv; auto 20)); exact G8 | rewrite (RR 9%bv ltac:(cbv; auto 20)); exact G9
| rewrite (RR 19%bv ltac:(cbv; auto 20)); exact G19 | pose proof (land_le fattr 4 ltac:(lia)); lia | exact Q20 | exact UT ].
eapply (cgif_at_kept memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply KF].
Qed.
Lemma af_fast :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (rest FP : list (Z * Z)) (fh : frame_st)
(cfp lpal lpa img fattr fgen delay nlp tidx : Z),
B_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP fh cfp lpal lpa img fattr fgen delay nlp tidx ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_FAST) memc (seg_rom ubs2segs)) mdc)
(af_post API regs0 g N s0 [(img, N)] rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP fh cfp lpal lpa img fattr fgen delay nlp tidx
(HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hgeom & Hfh & HnoCT & Hcf & Hcf8 & Hcflo & Hcfhi & Hlpa & HFP & HB & HSV & G2 & G8 & G9 & G12 & G19 & G20 & HUT).
pose proof HUT as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & Hih & Hfwf).
assert (HN1 : 1 <= N) by (rewrite HN; clear - HW1 HH1; nia).
assert (Hfin : In (Some fh) (cg_frames s)) by (eapply nth_error_In; exact Hfh).
destruct (af_cgif_geom API Lc Ac memc mdc g s N _ HH0 HB) as (_ & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom fh Hfin) as (Hf0 & Hf1 & Hfg).
destruct (af_frame_geom API Lc Ac memc mdc g s N _ fh HH0 HB Hfin) as (Hfblk & Hfimgblk & Hflpal).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr fh) FRAME_SIZE HH0 Hfblk ltac:(lia)) as (_ & _ & Hf16).
assert (Himgin : In (img, N) (blocks Lc Ac)).
{ apply (Permutation_in _ (Permutation_sym HB)). apply in_app_iff. right. left. reflexivity. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc img N HH0 Himgin) as [Him0 Him1].
destruct (blocks_range _ _ LAWS Lc Ac memc mdc (fr_img fh) N HH0 Hfimgblk) as [Hfi0 Hfi1].
pose proof Hat as (Hobj & Hraw & Hfrs). pose proof (Hfrs fh Hfin) as Hfobj.
pose proof (obj_at_range _ _ _ _ _ Hcf) as Rcf. pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (obj_at_range _ _ _ _ _ Hfobj) as Rf.
pose proof (Rcf 2%nat fattr eq_refl) as Rfattr. pose proof (Rcf 0%nat lpal eq_refl) as Rlpal. pose proof (Rcf 5%nat nlp eq_refl) as Rnlp.
cbn [nth snd LAY_FrameConfig Z.of_N] in Rfattr, Rlpal, Rnlp.
pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. cbn [nth snd LAY_CGIF Z.of_N] in RW, RH.
pose proof (Rf 2%nat (fr_attr fh) eq_refl) as Rfa. pose proof (Rf 4%nat (fr_delay fh) eq_refl) as Rfd. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfa, Rfd.
set (E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s (frame_vals fh)).
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HK regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (af_HC regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n j v, _ -> _ -> ew E n = _) as HC.
pose proof (af_HX regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n j v, _ -> _ -> ew E n = _) as HX.
pose proof (af_HM regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n j v, _ -> _ -> ew E n = _) as HM.
assert (HU2 : bv_unsigned (ew E 2) = spZ regs0 - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = cfp) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HU12 : bv_unsigned (ew E 12) = fr_ptr fh) by (rewrite (HE 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; lia).
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32))).
{ pose proof (af_Rstk_ok _ memc (spZ regs0) regs0 32 HU2 ltac:(lia) ltac:(lia) HSV (fun j v Hj => HK _ j v eq_refl Hj) (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4]. }
pose proof (af_Rg_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) memc g None None None (Some (cg_ihead s)) HU8 ltac:(lia) ltac:(lia) Hobj I I I eq_refl) as HR1.
pose proof (af_Rcf_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) memc cfp HU9 ltac:(lia) ltac:(lia) Hcf) as HR2.
assert (HR3 : region_ok ubs2segs E memc (af_Rfr_part 12 68 0 40 0 0)).
{ eapply (af_Rfr_part_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) memc 12 (fr_ptr fh) fh 68);
[exact HU12 | reflexivity | lia | lia | exact Hfobj | lia | intros j v Hj; rewrite Nat.sub_diag; exact Hj | lia | lia | intros k Hk; lia]. }
assert (HPD : pairwise_disjoint E (B_regions (cg_ihead s))).
{ unfold B_regions, af_Rg, af_Rcf, af_Rfr_part. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU8, HU9, HU12. clear - Hg1 Hf1 Hfg Hceil Hcflo HASv HGSv HFSv Hac. repeat split; lia. }
assert (HFA : atoms_ok E B_facts).
{ unfold B_facts. apply atoms_ok_app; [| apply atoms_ok_app; [exact (cf_facts_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) memc cfp Hcf) |]].
- cbn [atoms_ok af_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, HU9.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia_try.
replace (spZ regs0 - 64) with (spZ regs0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (HX 58%nat 7%nat _ eq_refl eq_refl), (HX 59%nat 8%nat _ eq_refl eq_refl), HU12,
(HM 69%nat 1%nat (fr_img fh) eq_refl eq_refl), (HM 70%nat 2%nat (fr_attr fh) eq_refl eq_refl), (HM 72%nat 4%nat (fr_delay fh) eq_refl eq_refl).
rewrite !unsigned_lit_small by lia. change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
clear - RW RH HW1 HH1 Hf0 Hf1 Hf16 Hfi0 Hfi1 Rfa Rfd HFSv HN HNle Hac. repeat split; try lia; nia. }
assert (HS : st_ok ubs2segs E (ss_fast (cg_ihead s)) (mkst regs1 (Z_to_bv 64 AF_FAST) memc (seg_rom ubs2segs))).
{ unfold ss_fast. apply entry_st_ok_full; [apply regs_ok_Ereg | destruct Hih as [H1|[H2 _]]; rewrite ?H1, ?H2; vm_compute; reflexivity | | exact HPD | split; [exact HFA | split; exact I]].
unfold B_regions. constructor; [exact HR0|]. constructor; [exact HR1|]. constructor; [exact HR2|]. constructor; [exact HR3|]. constructor. }
clear HR0 HR1 HR2 HR3 HPD HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_FAST) memc (seg_rom ubs2segs))) in HJ.
assert (GO_SAME : forall E' ss ms', st_ok ubs2segs E' ss ms' -> env_agree 32 E E' -> ss_pc ss = AF_SAME -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 20%bv = SOff 20 0 -> sr_get (ss_regs ss) 21%bv = SOff 21 0 ->
sr_get (ss_regs ss) 23%bv = SOff 23 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 -> sr_get (ss_regs ss) 25%bv = SOff 25 0 ->
sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
journal ubs2_msyms MR ADDFRAME_STK (spZ regs0) FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, mbyte ubs2segs (ms_mem ms') a = mbyte ubs2segs memc a) ->
SR ubs2segs (mkCfg ms' mdc) (af_post API regs0 g N s0 [(img, N)] rest FP L A mem md)).
{ intros E' ss ms' HS' HA Hpc Hrv Q2 Q3 Q4 Q8 Q20 Q21 Q23 Q24 Q25 Q26 Q27 HJ' K. rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> (n < 32)%nat -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hn Hw. rewrite (st_ok_reg ubs2segs E' ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, <- Hw. apply (proj1 HA). exact Hn. }
eapply (af_same API IMG L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s0 s _ rest FP (Z.to_nat (cg_ihead s)) fh);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | | exact Hwf | exact Hgeom | exact Hfh
| intros a Ha; apply (HFP (fr_ptr fh) FRAME_SIZE a); [apply (frame_blocks_in_cgif g s N fh); [exact Hfin | left; reflexivity] | exact Ha]
| exact HB | apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply K]
| apply (RG _ _ _ Q2 ltac:(lia)); rewrite (HE 2%nat 2%bv eq_refl); exact G2
| apply (RG _ _ _ Q8 ltac:(lia)); rewrite (HE 8%nat 8%bv eq_refl); exact G8
| apply (RG _ _ _ Q20 ltac:(lia)); rewrite (HE 20%nat 20%bv eq_refl), G20, Z2Nat.id by (clear - Hih; lia); reflexivity
| split; [|split; [|split; [|split; [|split; [|split]]]]]; [ apply (RG _ _ _ Q3 ltac:(lia)); rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG _ _ _ Q4 ltac:(lia)); rewrite (HE 4%nat 4%bv eq_refl); exact G4
| apply (RG _ _ _ Q23 ltac:(lia)); rewrite (HE 23%nat 23%bv eq_refl); exact G23
| apply (RG _ _ _ Q24 ltac:(lia)); rewrite (HE 24%nat 24%bv eq_refl); exact G24
| apply (RG _ _ _ Q25 ltac:(lia)); rewrite (HE 25%nat 25%bv eq_refl); exact G25
| apply (RG _ _ _ Q26 ltac:(lia)); rewrite (HE 26%nat 26%bv eq_refl); exact G26
| apply (RG _ _ _ Q27 ltac:(lia)); rewrite (HE 27%nat 27%bv eq_refl); exact G27 ] ].
eapply (cgif_at_kept memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply K]. }
assert (GO_C : forall E' ss ms', st_ok ubs2segs E' ss ms' -> env_agree 32 E E' -> ss_pc ss = AF_C -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 -> sr_get (ss_regs ss) 19%bv = SOff 19 0 -> sr_get (ss_regs ss) 20%bv = SOff 20 0 ->
sr_get (ss_regs ss) 23%bv = SOff 23 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 -> sr_get (ss_regs ss) 25%bv = SOff 25 0 ->
sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
journal ubs2_msyms MR ADDFRAME_STK (spZ regs0) FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, mbyte ubs2segs (ms_mem ms') a = mbyte ubs2segs memc a) ->
SR ubs2segs (mkCfg ms' mdc) (af_post API regs0 g N s0 [(img, N)] rest FP L A mem md)).
{ intros E' ss ms' HS' HA Hpc Hrv Q2 Q3 Q4 Q8 Q9 Q19 Q20 Q23 Q24 Q25 Q26 Q27 HJ' K. rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> (n < 32)%nat -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hn Hw. rewrite (st_ok_reg ubs2segs E' ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, <- Hw. apply (proj1 HA). exact Hn. }
pose proof (land_le fattr 4 ltac:(lia)) as Rt4.
eapply (af_C API IMG FLUSH L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s0 s rest FP cfp lpal lpa img fattr fgen delay nlp tidx (Z.land fattr 4));
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hgeom | exact HnoCT
| eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply K] | exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact HFP | exact HB
| apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply K]
| apply (RG _ _ _ Q2 ltac:(lia)); rewrite (HE 2%nat 2%bv eq_refl); exact G2
| apply (RG _ _ _ Q8 ltac:(lia)); rewrite (HE 8%nat 8%bv eq_refl); exact G8
| apply (RG _ _ _ Q9 ltac:(lia)); rewrite (HE 9%nat 9%bv eq_refl); exact G9
| apply (RG _ _ _ Q19 ltac:(lia)); rewrite (HE 19%nat 19%bv eq_refl); exact G19
| lia
| apply (RG _ _ _ Q20 ltac:(lia)); rewrite (HE 20%nat 20%bv eq_refl); exact G20
| split; [|split; [|split; [|split; [|split; [|split]]]]]; [ apply (RG _ _ _ Q3 ltac:(lia)); rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG _ _ _ Q4 ltac:(lia)); rewrite (HE 4%nat 4%bv eq_refl); exact G4
| apply (RG _ _ _ Q23 ltac:(lia)); rewrite (HE 23%nat 23%bv eq_refl); exact G23
| apply (RG _ _ _ Q24 ltac:(lia)); rewrite (HE 24%nat 24%bv eq_refl); exact G24
| apply (RG _ _ _ Q25 ltac:(lia)); rewrite (HE 25%nat 25%bv eq_refl); exact G25
| apply (RG _ _ _ Q26 ltac:(lia)); rewrite (HE 26%nat 26%bv eq_refl); exact G26
| apply (RG _ _ _ Q27 ltac:(lia)); rewrite (HE 27%nat 27%bv eq_refl); exact G27 ] ].
eapply (cgif_at_kept memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply K]. }
assert (CTB : forall attr lp nl, 0 <= lp < 2 ^ 64 -> 0 <= nl ->
(Z.land attr 1 = 0 -> Z.land (cg_attr s) 4 = 0) ->
(Z.land attr 1 <> 0 -> exists lp', Z_to_bv 64 lp' = Z_to_bv 64 lp /\ In (lp', 3 * nl) (blocks Lc Ac)) ->
In (ct_sel attr lp (cg_pal s), 3 * ct_sel attr nl (cg_ngp s)) (blocks Lc Ac)).
{ intros attr lp nl Rlp Rnl0 Hg Hl. unfold ct_sel. destruct (Z.eqb_spec (Z.land attr 1) 0) as [Hz|Hz].
- apply (Permutation_in _ (Permutation_sym HB)). apply in_app_iff. left. right. right. apply in_app_iff. left.
unfold pal_blocks. rewrite (Hg Hz). cbn. left. reflexivity.
- destruct (Hl Hz) as (lp' & Heq & Hin). destruct (blocks_range _ _ LAWS Lc Ac memc mdc lp' (3 * nl) HH0 Hin) as [R0 R1].
assert (lp' = lp).
{ apply (f_equal bv_unsigned) in Heq. rewrite !unsigned_lit_small in Heq by lia. exact Heq. }
subst lp'. exact Hin. }
assert (CTb : In (ct_sel (fr_attr fh) (fr_lpal fh) (cg_pal s), 3 * ct_sel (fr_attr fh) (fr_nlp fh) (cg_ngp s)) (blocks Lc Ac)).
{ pose proof (Rf 0%nat (fr_lpal fh) eq_refl) as Rflp. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rflp.
pose proof (Rf 5%nat (fr_nlp fh) eq_refl) as Rfnl0. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfnl0.
apply CTB; [lia | lia | exact (proj1 (Hfwf fh Hfin)) |]. intros Hz. exists (fr_lpal fh). split; [reflexivity | exact (Hflpal Hz)]. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 CTb) as [Sb0 Sb1'].
assert (Sb1 : ct_sel (fr_attr fh) (fr_lpal fh) (cg_pal s) + 3 * ct_sel (fr_attr fh) (fr_nlp fh) (cg_ngp s) <= 2 ^ 63) by (clear - Sb1' Hac; lia).
pose proof (Rcf 5%nat nlp eq_refl) as Rnl. pose proof (Rf 5%nat (fr_nlp fh) eq_refl) as Rfnl. pose proof (Rg 9%nat (cg_ngp s) eq_refl) as Rngp.
cbn [nth snd LAY_Frame LAY_FrameConfig LAY_CGIF app Z.of_N] in Rnl, Rfnl, Rngp.
assert (Hszb : 0 <= 3 * ct_sel (fr_attr fh) (fr_nlp fh) (cg_ngp s)) by (unfold ct_sel; destruct (Z.land (fr_attr fh) 1 =? 0); lia).
destruct (rdn_of_present ubs2_msyms memc (Z.to_nat (3 * ct_sel (fr_attr fh) (fr_nlp fh) (cg_ngp s))) (ct_sel (fr_attr fh) (fr_lpal fh) (cg_pal s))
ltac:(intros i Hi; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc _ _ i HH0 CTb ltac:(lia)))) ltac:(lia) ltac:(lia)) as (ctbef & Rbt & _).
assert (CTcur : 4096 <= ct_sel fattr lpal (cg_pal s) /\
ct_sel fattr lpal (cg_pal s) + 3 * ct_sel fattr nlp (cg_ngp s) <= 2 ^ 63 /\
0 <= 3 * ct_sel fattr nlp (cg_ngp s) /\
exists ctcur, rdn ubs2segs memc (Z_to_bv 64 (ct_sel fattr lpal (cg_pal s))) (Z.to_nat (3 * ct_sel fattr nlp (cg_ngp s))) = Some ctcur).
{ destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Hz|Hz].
- assert (CTc : In (ct_sel fattr lpal (cg_pal s), 3 * ct_sel fattr nlp (cg_ngp s)) (blocks Lc Ac)).
{ apply CTB; [lia | lia | exact HnoCT |]. intros Hz'. exfalso. exact (Hz' Hz). }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 CTc) as [Sc0 Sc1].
assert (Hszc : 0 <= 3 * ct_sel fattr nlp (cg_ngp s)) by (unfold ct_sel; destruct (Z.land fattr 1 =? 0); lia).
destruct (rdn_of_present ubs2_msyms memc (Z.to_nat (3 * ct_sel fattr nlp (cg_ngp s))) (ct_sel fattr lpal (cg_pal s))
ltac:(intros i Hi; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc _ _ i HH0 CTc ltac:(lia)))) ltac:(lia) ltac:(lia)) as (ctcur & Rct & _).
split; [exact Sc0|]. split; [clear - Sc1 Hac; lia|]. split; [exact Hszc|]. exists ctcur. exact Rct.
- destruct (pal_ok_now MR ADDFRAME_STK _ FP L A mem md _ _ _ _ fattr lpal nlp HJ Hlpa Hz) as (P0 & P1 & P2 & _).
assert (E1 : (Z.land fattr 1 =? 0) = false) by (apply Z.eqb_neq; exact Hz).
unfold ct_sel. rewrite E1. cbv beta iota.
destruct (rdn_of_mbyteG memc (Z.to_nat (3 * nlp)) lpal ltac:(intros i Hi; apply P2; clear - Hi Rnl; lia) ltac:(clear - P0 Hceil HASv Hac; lia) ltac:(clear - P1 Rnl; lia)) as (ctcur & Rct & _).
split; [clear - P0 Hceil HASv Hac; lia|]. split; [exact P1|]. split; [clear - Rnl; lia|]. exists ctcur. exact Rct. }
destruct CTcur as (Sc0 & Sc1 & Hszc & ctcur & Rct).
assert (Dif : img + N <= fr_img fh \/ fr_img fh + N <= img).
{ pose proof (heap_sep_app API Lc Ac memc mdc (cgif_blocks g s N) ([(img, N)] ++ rest) (fr_img fh, N) (img, N) HH0 HB
ltac:(apply (frame_blocks_in_cgif g s N fh); [exact Hfin | right; left; reflexivity]) ltac:(left; reflexivity)) as Hs. cbn [fst snd] in Hs. lia. }
assert (Hfhcf : obj_at ubs2segs memc (fr_ptr fh) LAY_FrameConfig (firstn 7 (frame_vals fh))).
{ rewrite LAY_Frame_split in Hfobj. apply (proj1 (obj_at_app ubs2segs memc (fr_ptr fh) LAY_FrameConfig [(32, 1%N); (33, 1%N)] (firstn 7 (frame_vals fh)) (skipn 7 (frame_vals fh)) eq_refl)). exact Hfobj. }
destruct (rdn_of_present ubs2_msyms memc (Z.to_nat N) img ltac:(intros i Hi; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc img N i HH0 Himgin ltac:(lia)))) ltac:(lia) ltac:(lia)) as (bl & Rbl & Lbl).
destruct (rdn_of_present ubs2_msyms memc (Z.to_nat N) (fr_img fh) ltac:(intros i Hi; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc (fr_img fh) N i HH0 Hfimgblk ltac:(lia)))) ltac:(lia) ltac:(lia)) as (br & Rbr & Lbr).
destruct Hih as [Hih1 | [Hih2 _]].
- rewrite Hih1 in HS.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_bcmp. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K0 : forall x, ms_mem ms x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF.
jreg HS (10%bv:reg) as Hb0. rewrite (HC 45%nat 1%nat _ eq_refl eq_refl) in Hb0.
jreg HS (11%bv:reg) as Hb1. rewrite (HM 69%nat 1%nat _ eq_refl eq_refl) in Hb1.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg ubs2segs Ec ssc msc 12%bv HS) as Hb2; eval_sr_get_in Hb2; rewrite ?denot_add0 in Hb2;
first [ rewrite (denot_mul_atoms _ 59 58 (cg_H s) (cg_W s) (HX 59%nat 8%nat _ eq_refl eq_refl) (HX 58%nat 7%nat _ eq_refl eq_refl)) in Hb2 by (clear - RW RH HN HNle; nia)
| rewrite (denot_mul_atoms _ 58 59 (cg_W s) (cg_H s) (HX 58%nat 7%nat _ eq_refl eq_refl) (HX 59%nat 8%nat _ eq_refl eq_refl)) in Hb2 by (clear - RW RH HN HNle; nia) ] end.
replace (cg_H s * cg_W s) with N in Hb2 by (clear - HN; lia). replace (cg_W s * cg_H s) with N in Hb2 by (clear - HN; lia).
jreg HS (1%bv:reg) as Hbra.
destruct (ubs2_bcmp bl br _ _ _ (ms_mem ms) (seg_rom ubs2segs) (ms_regs ms) Hb0 Hb1 Hb2) as (regs2 & Hms & Hres & Hfr2);
[ rewrite unsigned_lit_small by lia; rewrite Lbl; lia | rewrite Lbr, Lbl; reflexivity
| rewrite Lbl, (rdn_ext ubs2segs (ms_mem ms) memc) by exact K0; exact Rbl
| rewrite Lbl, (rdn_ext ubs2segs (ms_mem ms) memc) by exact K0; exact Rbr
| rewrite unsigned_lit_small, Lbl by lia; lia | rewrite unsigned_lit_small, Lbl by lia; lia | ].
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc ss_fast].
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |].
replace (v_jalr (getr (ms_regs ms) 1) 0) with (Z_to_bv 64 AF_BCMPRET).
2:{ rewrite Hbra. symmetry. apply ret_ok_even. vm_compute. reflexivity. }
jafter_stretch_keep HS 77%nat regs2 (ms_mem ms) BCMP_CLOB AF_BCMPRET [0%nat; 1%nat; 2%nat; 3%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr5 : P); [| assert (HKm5 : Q); [| specialize (HS2 HKr5 HKm5); clear HKr5 HKm5]] end.
{ intros rr Hrr. apply Hfr2; intros ->; vm_compute in Hrr; discriminate Hrr. }
{ unfold af_Rg, af_Rcf, af_Rfr_part. repeat (apply Forall_cons); try apply Forall_nil;
(eapply (region_kept_out ubs2segs _ _ _ _ 0 0); [intros x _; reflexivity | apply mem_grows_of_eq; intros x; reflexivity
| cbn [r_base r_lo base_val]; ew_havocA; rewrite ?HU2, ?HU8, ?HU9, ?HU12; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite ?HU2, ?HU8, ?HU9, ?HU12; lia
| intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
change (ms_mem ms) with (ms_mem (mkst regs2 (Z_to_bv 64 AF_BCMPRET) (ms_mem ms) (seg_rom ubs2segs))) in HJ.
assert (EA : env_agree 32 E (havoc E 77 (map (getr regs2) BCMP_CLOB))) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
jbranch ubs2tbl HS; clear Hc.
+ jrun_to LAWS ubs2tbl_ok HS HJ AF_SAME. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (GO_SAME _ _ _ HS EA eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ).
intros a. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. rewrite K0. reflexivity.
+ jrun_to LAWS ubs2tbl_ok HS HJ AF_C. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (GO_C _ _ _ HS EA eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ).
intros a. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. rewrite K0. reflexivity.
- rewrite Hih2 in HS.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_bcmp. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K0 : forall x, ms_mem ms x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF.
jreg HS (10%bv:reg) as Hb0. rewrite (HC 45%nat 1%nat _ eq_refl eq_refl) in Hb0.
jreg HS (11%bv:reg) as Hb1. rewrite (HM 69%nat 1%nat _ eq_refl eq_refl) in Hb1.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg ubs2segs Ec ssc msc 12%bv HS) as Hb2; eval_sr_get_in Hb2; rewrite ?denot_add0 in Hb2;
first [ rewrite (denot_mul_atoms _ 59 58 (cg_H s) (cg_W s) (HX 59%nat 8%nat _ eq_refl eq_refl) (HX 58%nat 7%nat _ eq_refl eq_refl)) in Hb2 by (clear - RW RH HN HNle; nia)
| rewrite (denot_mul_atoms _ 58 59 (cg_W s) (cg_H s) (HX 58%nat 7%nat _ eq_refl eq_refl) (HX 59%nat 8%nat _ eq_refl eq_refl)) in Hb2 by (clear - RW RH HN HNle; nia) ] end.
replace (cg_H s * cg_W s) with N in Hb2 by (clear - HN; lia). replace (cg_W s * cg_H s) with N in Hb2 by (clear - HN; lia).
jreg HS (1%bv:reg) as Hbra.
destruct (ubs2_bcmp bl br _ _ _ (ms_mem ms) (seg_rom ubs2segs) (ms_regs ms) Hb0 Hb1 Hb2) as (regs2 & Hms & Hres & Hfr2);
[ rewrite unsigned_lit_small by lia; rewrite Lbl; lia | rewrite Lbr, Lbl; reflexivity
| rewrite Lbl, (rdn_ext ubs2segs (ms_mem ms) memc) by exact K0; exact Rbl
| rewrite Lbl, (rdn_ext ubs2segs (ms_mem ms) memc) by exact K0; exact Rbr
| rewrite unsigned_lit_small, Lbl by lia; lia | rewrite unsigned_lit_small, Lbl by lia; lia | ].
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc ss_fast].
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |].
replace (v_jalr (getr (ms_regs ms) 1) 0) with (Z_to_bv 64 AF_BCMPRET).
2:{ rewrite Hbra. symmetry. apply ret_ok_even. vm_compute. reflexivity. }
jafter_stretch_keep HS 77%nat regs2 (ms_mem ms) BCMP_CLOB AF_BCMPRET [0%nat; 1%nat; 2%nat; 3%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr5 : P); [| assert (HKm5 : Q); [| specialize (HS2 HKr5 HKm5); clear HKr5 HKm5]] end.
{ intros rr Hrr. apply Hfr2; intros ->; vm_compute in Hrr; discriminate Hrr. }
{ unfold af_Rg, af_Rcf, af_Rfr_part. repeat (apply Forall_cons); try apply Forall_nil;
(eapply (region_kept_out ubs2segs _ _ _ _ 0 0); [intros x _; reflexivity | apply mem_grows_of_eq; intros x; reflexivity
| cbn [r_base r_lo base_val]; ew_havocA; rewrite ?HU2, ?HU8, ?HU9, ?HU12; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite ?HU2, ?HU8, ?HU9, ?HU12; lia
| intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
change (ms_mem ms) with (ms_mem (mkst regs2 (Z_to_bv 64 AF_BCMPRET) (ms_mem ms) (seg_rom ubs2segs))) in HJ.
assert (EA : env_agree 32 E (havoc E 77 (map (getr regs2) BCMP_CLOB))) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
jbranch ubs2tbl HS; clear Hc.
+ jrun_to LAWS ubs2tbl_ok HS HJ AF_SAME. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (GO_SAME _ _ _ HS EA eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ).
intros a. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. rewrite K0. reflexivity.
+ jrun_to LAWS ubs2tbl_ok HS HJ AF_C. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (GO_C _ _ _ HS EA eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ).
intros a. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. rewrite K0. reflexivity.
Qed.
End S.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
