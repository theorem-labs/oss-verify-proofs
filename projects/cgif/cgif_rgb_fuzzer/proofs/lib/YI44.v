(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03
YI1e YI1i YI57 YI07 YP14 YP15 YP13 YI08 YI0c YI0g YI3h YI3d
YO3l YI4v YI46.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma U_mul3_add : forall E n m i b,
ew E n = Z_to_bv 64 i -> 0 <= i -> ew E m = Z_to_bv 64 b -> 0 <= b -> b + 3 * i < 2 ^ 64 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 3)) (SOff m 0)) = b + 3 * i.
Proof.
intros E n m i b Hn Hi Hm Hb Hnw. rewrite <- (U_add_mul3' E n m i b Hn Hi Hm Hb Hnw).
rewrite !U_SAlu. cbn [zalu_raw]. rewrite Z.add_comm. reflexivity.
Qed.
Definition l_smem : smem :=
[ YQ0b.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 33%nat 0))] ].
Definition l_atoms : list (nat * afact) :=
[ (2%nat, mkAF CEIL_MIN (2^63) 4); (19%nat, mkAF 0 (2^24 - 1) 0); (25%nat, mkAF 0 10000 0); (24%nat, mkAF 521 (2^24) 0);
(33%nat, mkAF 0 1 0) ].
Definition l_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 18%nat 0) (sv_nextz 19 24), SOff 32%nat 0) ].
Definition ss_L : sstate := mkSS PC_L sr_atoms l_smem None (mkFacts l_atoms [] l_alias).
Definition L_BRET : Z := 0x1371c.
Definition L_CLOB : list reg := [10; 11; 12; 13; 14]%bv.
Definition L_KEPT : list reg := [2; 3; 4; 22; 23; 18; 24; 27; 26; 20; 9; 8; 21]%bv.
Ltac wr_l := apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil.
Section c.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation RINV := (rgba_inv API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest).
Local Notation HM := (hist_mem regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest).
Local Notation POST := (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Local Notation SP := (sp regs0).
Local Notation BASE0 := (BASE r g N img fmt rest s bef beffmt).
Local Notation AT_L := (at_L API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_PX := (at_PX API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Section d.
Variables (i ha : Z) (Lc : layout) (Ac : astate) (mdc : Model) (pnew fimg : Z) (imgl : list Z) (C : cht) (js : Z).
Hypothesis Ejs : find_off (ch_H C) (pxc fmt imgl i) = Some js.
Hypothesis KPX : forall regs1 memc, AT_PX regs1 Lc Ac memc mdc i ha pnew fimg imgl C js ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_PX) memc (seg_rom src2segs)) mdc) POST.
Lemma L_body : forall j regs1 memc, AT_L regs1 Lc Ac memc mdc i ha pnew fimg imgl C j ->
(forall regs' mem', j + 1 <= js -> AT_L regs' Lc Ac mem' mdc i ha pnew fimg imgl C (j + 1) ->
SR src2segs (mkCfg (mkst regs' (Z_to_bv 64 PC_L) mem' (seg_rom src2segs)) mdc) POST) ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_L) memc (seg_rom src2segs)) mdc) POST.
Proof.
intros j regs1 memc HAT K.
destruct HAT as (HINV & HREGS & Hfmt & Hi & Hha & Hop & (js' & Ejs' & Hjj) & Hused & G19 & G25 & PR & BR & HMEM).
rewrite Ejs in Ejs'. injection Ejs' as <-.
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
destruct HREGS as (G2 & G3 & G4).
pose proof PR as (G22 & G23 & G18 & G24 & G27 & G26).
pose proof BR as (G20 & G9 & G8 & G21).
pose proof HMEM as (Hslots & S16 & S104 & S64 & S80 & S88 & S96 & Hfc & Hobj & Hcg & [Himg Hlen] & Hcht & EhS & EuS & ETS & Hz & Hpn & Hfi & HB).
pose proof Hcht as (Hobjc & (Af & Ah & Au & Ap & Ax) & Hinv & HT & Hch & _).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1.
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & (C1 & C2 & C3) & (B1 & B2 & B3) & I4 & _). rewrite HT in L1, L2, L3, L4, L5, C1, B1.
set (T := ch_T C) in *. set (col := pxc fmt imgl i) in *. set (h0 := hash0 T col) in *.
set (hj := cyc T h0 j) in *.
assert (Rhj : 0 <= hj < T) by (subst hj; apply cyc_range; lia).
set (nx := probe_next T hj). assert (Rnx : 0 <= nx < T) by (subst nx; apply probe_next_range; exact Rhj).
assert (Enx : cyc T h0 (j + 1) = nx) by (subst nx hj; apply cyc_succ; lia).
assert (Hjs_cnt : js <= ht_cnt (ch_H C)) by exact (find_off_le_cnt (ch_H C) (ch_ent C) Hinv col js Ejs).
assert (Hcnt_i : ht_cnt (ch_H C) <= i).
{ pose proof (zsum_ge_length (ch_ent C) (ent_freq_pos (ch_H C) (ch_ent C) Hinv)). lia. }
unfold RGB_NMAX in HNmax.
assert (Hcol : colour_ok col).
{ subst col. unfold pxc, colour_ok, cR, cG, cB, mkcol. cbn [fst snd].
assert (PX2 : fmt * i + fmt <= fmt * N) by nia.
pose proof (fun k (Hk : 0 <= k < 3) => proj2 (arr8_getz src2segs memc img imgl (fmt * i + k) Himg ltac:(nia))) as R.
pose proof (R 0 ltac:(lia)) as R0. rewrite Z.add_0_r in R0. pose proof (R 1 ltac:(lia)). pose proof (R 2 ltac:(lia)). lia. }
assert (U1 : usedz (ch_H C) hj = 1) by (destruct (B1 hj Rhj); [exfalso; exact (Hused ltac:(assumption)) | assumption]).
destruct (arr8_getz src2segs memc (ch_u C) (ht_used (ch_H C)) nx Au ltac:(lia)) as [Bn Rn].
change (getz (ht_used (ch_H C)) nx) with (usedz (ch_H C) nx) in Bn, Rn.
set (unx := usedz (ch_H C) nx) in *.
assert (Un01 : unx = 0 \/ unx = 1) by (subst unx; apply B1; exact Rnx).
assert (INB : forall b, In b (cht_blks C) -> In b (blocks Lc Ac)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. apply in_app_iff. right. exact Hb. }
assert (E2 : nth_error (cht_blks C) 2 = Some (ch_h C, 3 * T)) by reflexivity.
assert (E3 : nth_error (cht_blks C) 3 = Some (ch_u C, T)) by reflexivity.
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac memc mdc (ch_h C) (3 * T) HHc (INB _ (nth_error_In _ _ E2)) ltac:(lia)) as (Rk0 & Rk1 & _).
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac memc mdc (ch_u C) T HHc (INB _ (nth_error_In _ _ E3)) ltac:(lia)) as (Ru0 & Ru1 & _).
assert (Hyimg : In (img, fmt * N) (BASE0 ++ [(pnew, fmt * N); (fimg, N)])).
{ apply in_app_iff. left. unfold BASE. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
unfold img_block, fmt_okb. destruct Hfmt as [-> | ->]; left; reflexivity. }
assert (Himgb : In (img, fmt * N) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. rewrite app_assoc. apply in_app_iff. left. exact Hyimg. }
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac memc mdc img (fmt * N) HHc Himgb ltac:(lia)) as (Ri0 & Ri1 & _).
set (pix := img + fmt * i) in *.
assert (PX1 : 0 <= fmt * i) by nia. assert (PX2 : fmt * i + fmt <= fmt * N) by nia.
set (E := Ereg regs1 (map (Z_to_bv 64) [ch_u C + nx; unx] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall jj v, nth_error [ch_u C + nx; unx] jj = Some v -> ew E (32 + jj) = Z_to_bv 64 v)
by (intros jj v Hjv; subst E; apply Ereg_vals; exact Hjv).
assert (HE32 : ew E 32 = Z_to_bv 64 (ch_u C + nx)) by exact (HV 0%nat _ eq_refl).
assert (HE33 : ew E 33 = Z_to_bv 64 unx) by exact (HV 1%nat _ eq_refl).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HU32 : bv_unsigned (ew E 32) = ch_u C + nx) by (rewrite HE32; apply unsigned_lit_small; lia).
assert (HE19 : ew E 19 = Z_to_bv 64 hj) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (HE25 : ew E 25 = Z_to_bv 64 j) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (HE22 : ew E 22 = Z_to_bv 64 pix) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (HE18 : ew E 18 = Z_to_bv 64 (ch_u C)) by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (HE24 : ew E 24 = Z_to_bv 64 T) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (HE23 : ew E 23 = Z_to_bv 64 (ch_h C)) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HS : st_ok src2segs E ss_L (mkst regs1 (Z_to_bv 64 PC_L) memc (seg_rom src2segs))).
{ unfold ss_L. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold l_smem. constructor; [|constructor]. unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HU32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ unx); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. rewrite Z.add_0_r. apply val_mem_byte; [exact Bn | lia].
- unfold l_smem. cbn [pairwise_disjoint all_disjoint]. repeat split; exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [| split; [exact I|]].
+ cbn [atoms_ok l_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, (ew_Ereg_nat regs1 _ 19 19%bv eq_refl), G19, (ew_Ereg_nat regs1 _ 25 25%bv eq_refl), G25, (ew_Ereg_nat regs1 _ 24 24%bv eq_refl), G24, HE33.
unfold sp, sp0 in *. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
assert (Hsp16 : (spZ regs0 - RGBA_FRAME) mod 16 = 0).
{ unfold RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.
+ cbn [alias_ok l_alias]. split; [|exact I].
apply U_inj. rewrite (U_atom _ 32 (ch_u C + nx) HE32) by lia. subst nx.
apply (U_u_next _ 18 19 24 (ch_u C) hj T); [exact HE18 | exact HE19 | exact HE24 | exact Rhj | lia | lia | lia]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_L) memc (seg_rom src2segs))) in HJ.
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
clearbody E. clear HV.
jrun_to LAWS src2tbl_ok HS HJ src2_A_bcmp. { wr_l. }
cbn [ms_mem mkst] in HF.
assert (Hm0 : ms_mem ms = memc) by (apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF x0); reflexivity).
jreg HS (10%bv:reg) as Hb0. rewrite HE22 in Hb0.
assert (Hb1 : getr (ms_regs ms) 11 = Z_to_bv 64 (ch_h C + 3 * hj)).
{ eapply (getr_of_U src2segs); [exact HS|]. eval_sr_get. apply (U_mul3_add E 19 23 hj (ch_h C) HE19 ltac:(lia) HE23 ltac:(lia) ltac:(lia)). }
jreg HS (12%bv:reg) as Hb2. jreg HS (1%bv:reg) as Hbra.
assert (PB : forall k, 0 <= k < 3 -> mbyte src2segs (ms_mem ms) (pix + k) = Some (Z_to_bv 8 (getz imgl (fmt * i + k))) /\ 0 <= getz imgl (fmt * i + k) < 256).
{ intros k Hk. rewrite Hm0. subst pix. rewrite <- Z.add_assoc. apply (arr8_getz src2segs memc img imgl); [exact Himg | clear - Hk PX1 PX2 Hfmt Hlen; nia]. }
assert (KB : forall k, 0 <= k < 3 -> mbyte src2segs (ms_mem ms) (ch_h C + 3 * hj + k) = Some (Z_to_bv 8 (getz (ht_keys (ch_H C)) (3 * hj + k))) /\ 0 <= getz (ht_keys (ch_H C)) (3 * hj + k) < 256).
{ intros k Hk. rewrite Hm0. rewrite <- Z.add_assoc. apply (arr8_getz src2segs memc (ch_h C) (ht_keys (ch_H C))); [exact Ah | clear - Hk Rhj L2; lia]. }
pose proof (PB 0 ltac:(lia)) as [P0 _]. pose proof (PB 1 ltac:(lia)) as [P1 _]. pose proof (PB 2 ltac:(lia)) as [P2 _]. rewrite !Z.add_0_r in P0.
pose proof (KB 0 ltac:(lia)) as [Q0 RQ0]. pose proof (KB 1 ltac:(lia)) as [Q1 RQ1]. pose proof (KB 2 ltac:(lia)) as [Q2 RQ2]. rewrite !Z.add_0_r in Q0. rewrite !Z.add_0_r in RQ0.
set (lb := [Z_to_bv 8 (cR col); Z_to_bv 8 (cG col); Z_to_bv 8 (cB col)]).
set (rb := [Z_to_bv 8 (getz (ht_keys (ch_H C)) (3 * hj)); Z_to_bv 8 (getz (ht_keys (ch_H C)) (3 * hj + 1)); Z_to_bv 8 (getz (ht_keys (ch_H C)) (3 * hj + 2))]).
destruct (src2_bcmp lb rb _ _ _ (ms_mem ms) (seg_rom src2segs) (ms_regs ms) Hb0 Hb1 Hb2) as (regs2 & Hms & Hres & Hfr2).
{ rewrite unsigned_lit_small by lia. reflexivity. }
{ reflexivity. }
{ change (length lb) with 3%nat. subst lb col. unfold pxc, cR, cG, cB, mkcol. cbn [fst snd]. apply rdn3_of_mbytes; assumption. }
{ change (length lb) with 3%nat. apply rdn3_of_mbytes; assumption. }
{ rewrite unsigned_lit_small by lia. change (length lb) with 3%nat. lia. }
{ rewrite unsigned_lit_small by lia. change (length lb) with 3%nat. lia. }
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |].
replace (v_jalr (getr (ms_regs ms) 1) 0) with (Z_to_bv 64 L_BRET).
2:{ rewrite Hbra. symmetry. apply ret_ok_even. vm_compute. reflexivity. }
jafter_stretch_keep HS 34%nat regs2 (ms_mem ms) L_CLOB L_BRET [0%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2; intros ->; vm_compute in Hrr; discriminate Hrr. }
{ repeat (apply Forall_cons); try apply Forall_nil; apply (region_kept_same src2segs). }
clear HS. rename HS2 into HS.
change (ms_mem ms) with (ms_mem (mkst regs2 (Z_to_bv 64 L_BRET) (ms_mem ms) (seg_rom src2segs))) in HJ.
assert (EA1 : env_agree 34 E (havoc E 34 (map (getr regs2) L_CLOB))) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (H34 : ew (havoc E 34 (map (getr regs2) L_CLOB)) 34 = Z_to_bv 64 (memcmp_spec lb rb)).
{ rewrite <- Hres. etransitivity; [apply (ew_havoc_new E 34 _ 0%nat (Z_to_bv 64 0)); cbn; lia | reflexivity]. }
assert (Hzero : Z_to_bv 64 (memcmp_spec lb rb) = Z_to_bv 64 0 <-> key (ch_H C) hj = col).
{ rewrite (src2_memcmp_zero_iff lb rb eq_refl). subst lb rb. unfold key. apply key_bytes_eq_iff; [exact Hcol | lia | lia | lia]. }
destruct (find_off_spec (ch_H C) (ch_ent C) Hinv col js Ejs) as (Rjs & Hstop & Hbefore). rewrite HT in Rjs, Hstop, Hbefore.
assert (TOPX : forall ss ms', st_ok src2segs (havoc E 34 (map (getr regs2) L_CLOB)) ss ms' -> ms_mem ms' = memc -> ss_resv ss = None -> ss_pc ss = PC_PX ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) L_KEPT = true ->
U (havoc E 34 (map (getr regs2) L_CLOB)) (sr_get (ss_regs ss) 19) = cyc T h0 js -> U (havoc E 34 (map (getr regs2) L_CLOB)) (sr_get (ss_regs ss) 25) = js ->
SR src2segs (mkCfg ms' mdc) POST).
{ intros ss ms' HS' Hmm Hrv Hpc QK Q19 Q25.
assert (EA2 : env_agree 32 (Ereg regs1 []) (havoc E 34 (map (getr regs2) L_CLOB))) by (eapply env_agree_trans; [exact EA0 | eapply env_agree_le; [| exact EA1]; lia]).
pose proof (regs_kept_of_st_ok src2segs _ ss ms' regs1 [] L_KEPT HS' EA2 QK) as GK.
rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc.
apply (KPX (ms_regs ms') (ms_mem ms')). unfold at_PX. rewrite Hmm.
split; [exact HINV|].
split. { split; [rewrite (GK 2%bv ltac:(cbv; auto 20)); exact G2|]. split; [rewrite (GK 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (GK 4%bv ltac:(cbv; auto 20)); exact G4]. }
split; [exact Hfmt|]. split; [exact Hi|]. split; [exact Hha|]. split; [exact Hop|]. split; [exact Ejs|].
split; [exact (getr_of_U src2segs _ ss ms' 19%bv _ HS' Q19)|].
split; [exact (getr_of_U src2segs _ ss ms' 25%bv _ HS' Q25)|].
split. { unfold probe_regs. rewrite (GK 22%bv ltac:(cbv; auto 20)), (GK 23%bv ltac:(cbv; auto 20)), (GK 18%bv ltac:(cbv; auto 20)), (GK 24%bv ltac:(cbv; auto 20)),
(GK 27%bv ltac:(cbv; auto 20)), (GK 26%bv ltac:(cbv; auto 20)). exact PR. }
split. { unfold body_regs. rewrite (GK 20%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)). exact BR. }
exact HMEM. }
jbranch src2tbl HS.
-
cbn [branch_taken sv_denot] in Hc. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, H34 in Hc. apply bv_eqb_eq in Hc. apply Hzero in Hc.
assert (Ej : j = js).
{ destruct (Z_lt_le_dec j js) as [Hlt|]; [|lia]. exfalso. specialize (Hbefore j ltac:(lia)). change (cyc T (hash0 T col) j) with hj in Hbefore.
unfold slot_stop in Hbefore. rewrite Hc, colour_eqb_refl, orb_true_r in Hbefore. discriminate Hbefore. }
jrun_to LAWS src2tbl_ok HS HJ PC_PX. { wr_l. }
cbn [ms_mem mkst] in HF0.
assert (Hm1 : ms_mem ms0 = memc) by (rewrite <- Hm0; apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF0 x0); reflexivity).
apply (TOPX _ _ HS Hm1 eq_refl eq_refl ltac:(vm_compute; reflexivity)).
+ eval_sr_get. rewrite <- Ej. apply (U_atom _ 19 hj); [ew_havoc; exact HE19 | lia].
+ eval_sr_get. rewrite <- Ej. apply (U_atom _ 25 j); [ew_havoc; exact HE25 | lia].
-
cbn [branch_taken sv_denot] in Hc. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, H34 in Hc.
assert (Hne : key (ch_H C) hj <> col) by (intros Ek; apply Hzero in Ek; rewrite Ek, bv_eqb_refl in Hc; discriminate Hc).
assert (Hjs' : j + 1 <= js).
{ destruct (Z.eq_dec j js) as [Ej|]; [|lia]. exfalso. rewrite <- Ej in Hstop. change (cyc T (hash0 T col) j) with hj in Hstop.
unfold slot_stop in Hstop. rewrite U1 in Hstop. cbn [Z.eqb orb] in Hstop. apply (proj1 (colour_eqb_spec _ _)) in Hstop. exact (Hne Hstop). }
clear Hc Hzero H34 Hstop.
jrun LAWS src2tbl_ok HS HJ. { wr_l. }
cbn [ms_mem mkst] in HF0.
assert (Hm1 : ms_mem ms0 = memc) by (rewrite <- Hm0; apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF0 x0); reflexivity).
jbranch src2tbl HS.
+
rewrite branch_ne_U, U_lit in Hc by lia. rewrite (U_atom _ 33 unx) in Hc; [| ew_havoc; exact HE33 | lia]. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc.
jrun_to LAWS src2tbl_ok HS HJ PC_L. { wr_l. }
cbn [ms_mem mkst] in HF1.
assert (Hm2 : ms_mem ms1 = memc) by (rewrite <- Hm1; apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF1 x0); reflexivity).
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
assert (EA2 : env_agree 32 (Ereg regs1 []) Ef) by (eapply env_agree_trans; [exact EA0 | eapply env_agree_le; [| exact EA1]; lia]);
pose proof (regs_kept_of_st_ok src2segs Ef ssf msf regs1 [] L_KEPT HS EA2 ltac:(vm_compute; reflexivity)) as GK end.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc]. change (Z_to_bv 64 79612) with (Z_to_bv 64 PC_L).
apply (K (ms_regs ms1) (ms_mem ms1) Hjs'). unfold at_L. rewrite Hm2.
split; [exact HINV|].
split. { split; [rewrite (GK 2%bv ltac:(cbv; auto 20)); exact G2|]. split; [rewrite (GK 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (GK 4%bv ltac:(cbv; auto 20)); exact G4]. }
split; [exact Hfmt|]. split; [exact Hi|]. split; [exact Hha|]. split; [exact Hop|].
split; [exists js; split; [exact Ejs | lia]|].
replace (cyc (ch_T C) (hash0 (ch_T C) (pxc fmt imgl i)) (j + 1)) with nx by (symmetry; exact Enx).
split; [exact Hc|].
split. { eapply (getr_of_U src2segs); [exact HS|]. eval_sr_get. subst nx.
apply (U_sv_next _ 19 24 hj T); [ew_havoc; exact HE19 | ew_havoc; exact HE24 | exact Rhj | lia]. }
split. { eapply (getr_of_U src2segs); [exact HS|]. eval_sr_get. apply (U_atom_off _ 25 j 1); [ew_havoc; exact HE25 | lia | lia]. }
split. { unfold probe_regs. rewrite (GK 22%bv ltac:(cbv; auto 20)), (GK 23%bv ltac:(cbv; auto 20)), (GK 18%bv ltac:(cbv; auto 20)), (GK 24%bv ltac:(cbv; auto 20)),
(GK 27%bv ltac:(cbv; auto 20)), (GK 26%bv ltac:(cbv; auto 20)). exact PR. }
split. { unfold body_regs. rewrite (GK 20%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)). exact BR. }
exact HMEM.
+
rewrite branch_ne_U, U_lit in Hc by lia. rewrite (U_atom _ 33 unx) in Hc; [| ew_havoc; exact HE33 | lia]. apply negb_false_iff in Hc. apply Z.eqb_eq in Hc.
assert (Ej : j + 1 = js).
{ destruct (Z_lt_le_dec (j + 1) js) as [Hlt|]; [|lia]. exfalso. specialize (Hbefore (j + 1) ltac:(lia)). change (cyc T (hash0 T col) (j + 1)) with (cyc T h0 (j + 1)) in Hbefore. rewrite Enx in Hbefore.
unfold slot_stop in Hbefore. change (usedz (ch_H C) nx) with unx in Hbefore. rewrite Hc in Hbefore. cbn [Z.eqb orb] in Hbefore. discriminate Hbefore. }
jrun_to LAWS src2tbl_ok HS HJ PC_PX. { wr_l. }
cbn [ms_mem mkst] in HF1.
assert (Hm2 : ms_mem ms1 = memc) by (rewrite <- Hm1; apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF1 x0); reflexivity).
apply (TOPX _ _ HS Hm2 eq_refl eq_refl ltac:(vm_compute; reflexivity)).
* eval_sr_get. rewrite <- Ej, Enx. subst nx. apply (U_sv_next _ 19 24 hj T); [ew_havoc; exact HE19 | ew_havoc; exact HE24 | exact Rhj | lia].
* eval_sr_get. rewrite <- Ej. apply (U_atom_off _ 25 j 1); [ew_havoc; exact HE25 | lia | lia].
Qed.
Lemma L_loop : forall n j regs1 memc, js - j <= Z.of_nat n -> AT_L regs1 Lc Ac memc mdc i ha pnew fimg imgl C j ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_L) memc (seg_rom src2segs)) mdc) POST.
Proof.
induction n as [|n IH]; intros j regs1 memc Hn HA.
- apply (L_body j regs1 memc HA). intros regs' mem' Hj' _. exfalso. cbn in Hn. lia.
- apply (L_body j regs1 memc HA). intros regs' mem' Hj' HA'. apply (IH (j + 1)); [rewrite Nat2Z.inj_succ in Hn; lia | exact HA'].
Qed.
End d.
Theorem L_stretch : forall i ha Lc Ac mdc pnew fimg imgl C,
(forall js regs1 memc, AT_PX regs1 Lc Ac memc mdc i ha pnew fimg imgl C js ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_PX) memc (seg_rom src2segs)) mdc) POST) ->
forall regs1 memc, AT_L regs1 Lc Ac memc mdc i ha pnew fimg imgl C 0 ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_L) memc (seg_rom src2segs)) mdc) POST.
Proof.
intros i ha Lc Ac mdc pnew fimg imgl C KPX regs1 memc HA.
pose proof HA as (_ & _ & _ & _ & _ & _ & (js & Ejs & Hjs) & _).
apply (L_loop i ha Lc Ac mdc pnew fimg imgl C js Ejs (KPX js) (Z.to_nat js) 0); [lia | exact HA].
Qed.
End c.
End a.
