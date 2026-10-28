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
UI23 UI24 UI1w UI1j UI1r UI1s UI1t UI1u.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma zcanon_add_mulm1 : forall a b, 0 <= b <= a -> a < 2 ^ 64 -> zcanon (a + zcanon (b * zcanon 18446744073709551615)) = a - b.
Proof.
intros a b Hb Ha. unfold zcanon, M64. change (18446744073709551615 mod 2 ^ 64) with 18446744073709551615. nia.
Qed.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma af_frames_blocks_img_in : forall N fs f, In (Some f) fs -> In (fr_img f, N) (frames_blocks N fs).
Proof. intros N fs f H. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact H | right; left; reflexivity]. Qed.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis RAWADD : rawadd_spec API.
Lemma af_imgs_sep : forall L A m md g s N rest j1 j2 f1 f2,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks g s N ++ rest) ->
nth_error (cg_frames s) j1 = Some (Some f1) -> nth_error (cg_frames s) j2 = Some (Some f2) -> j1 <> j2 ->
fr_img f1 + N <= fr_img f2 \/ fr_img f2 + N <= fr_img f1.
Proof.
intros L A m md g s N rest j1 j2 f1 f2 HH HB H1 H2 Hne.
destruct (nth_error_split _ _ H1) as (l1 & l2 & Hfr & Hl1).
assert (Hf2 : In (Some f2) (l1 ++ l2)).
{ rewrite Hfr in H2. destruct (Nat.lt_ge_cases j2 (length l1)) as [Hlt|Hge].
- apply in_app_iff. left. rewrite nth_error_app1 in H2 by exact Hlt. eapply nth_error_In. exact H2.
- apply in_app_iff. right. rewrite nth_error_app2 in H2 by exact Hge.
destruct (j2 - length l1)%nat as [|k] eqn:Hk; [lia|]. cbn in H2. eapply nth_error_In. exact H2. }
assert (HP : Permutation (cgif_blocks g s N ++ rest)
((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: (fr_img f1, N) ::
(pal_blocks s ++ frames_blocks N l1 ++ (fr_ptr f1, FRAME_SIZE) :: (if Z.land (fr_attr f1) 1 =? 0 then [] else [(fr_lpal f1, 3 * fr_nlp f1)]) ++ frames_blocks N l2) ++ rest)).
{ unfold cgif_blocks. rewrite Hfr, frames_blocks_app. cbn [frames_blocks flat_map]. fold (frames_blocks N l2). unfold frame_blocks at 1.
apply perm_img_front. }
assert (HP' : Permutation (blocks L A) ((fr_img f1, N) :: (cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) ::
(pal_blocks s ++ frames_blocks N l1 ++ (fr_ptr f1, FRAME_SIZE) :: (if Z.land (fr_attr f1) 1 =? 0 then [] else [(fr_lpal f1, 3 * fr_nlp f1)]) ++ frames_blocks N l2) ++ rest)).
{ eapply Permutation_trans; [exact (Permutation_trans HB HP)|].
eapply Permutation_trans; [apply perm_skip; apply perm_swap|]. apply perm_swap. }
pose proof (heap_sep_perm _ _ LAWS L A m md (fr_img f1, N) _ (fr_img f2, N) HH HP') as Hs.
cbn [fst snd] in Hs. apply Hs. right. right. apply in_app_iff. left. apply in_app_iff. right.
apply in_app_iff in Hf2 as [Hf2|Hf2].
- apply in_app_iff. left. apply af_frames_blocks_img_in. exact Hf2.
- apply in_app_iff. right. right. apply in_app_iff. right. apply af_frames_blocks_img_in. exact Hf2.
Qed.
Definition dv_pre L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st) (gen1 : Z)
(rest FP : list (Z * Z)) (tv np u23 u24 u25 : Z) : Prop :=
let sp0 := spZ regs0 in
journal ubs2_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac memc mdc /\ st_init_done Ac = true /\
YK0s.ret_ok (getr regs0 1) /\ sp0 mod 16 = 0 /\ getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) /\
cgif_at memc g (flush_upd s i gen1 (rw_cur s)) /\ cgif_wf s N /\ (i = 1%nat \/ i = 2%nat) /\ nth_error (cg_frames s) i = Some (Some f) /\
nth_error (cg_frames s) (i - 1) = Some (Some b) /\
(forall b' n a, In (b', n) (cgif_blocks g s N) -> b' <= a < b' + n -> inFP FP a) /\
Permutation (blocks Lc Ac) (cgif_blocks g s N ++ rest) /\ 0 <= tv < 2 ^ 64 /\ 0 <= np <= 65535 /\
0 <= u23 < 2 ^ 64 /\ 0 <= u24 < 2 ^ 64 /\ 0 <= u25 < 2 ^ 64 /\
fl_saved_ok memc sp0 regs0 /\
word_mem ubs2segs memc (sp0 - 272 + 112) g /\ word_mem ubs2segs memc (sp0 - 272 + 120) (fr_ptr f) /\
word_mem ubs2segs memc (sp0 - 272 + 72) tv /\ word_mem ubs2segs memc (sp0 - 272 + 80) (cg_H s) /\
word_mem ubs2segs memc (sp0 - 272 + 104) (cg_W s) /\ word_mem ubs2segs memc (sp0 - 272 + 56) (Z.land (fr_attr f) 1) /\
word_mem ubs2segs memc (sp0 - 272 + 32) u23 /\ word_mem ubs2segs memc (sp0 - 272 + 16) u24 /\
word_mem ubs2segs memc (sp0 - 272 + 24) u25 /\
getr regs1 2 = Z_to_bv 64 (sp0 - 272) /\ getr regs1 9 = Z_to_bv 64 (fr_img f) /\
getr regs1 18 = Z_to_bv 64 (fr_ptr b) /\ getr regs1 19 = Z_to_bv 64 (cg_H s) /\ getr regs1 20 = Z_to_bv 64 np /\
fl_untouched regs0 regs1.
Lemma dv_ctx : forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st) (gen1 : Z)
(rest FP : list (Z * Z)) (tv np u23 u24 u25 : Z),
dv_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 ->
exists ctcur ctbef,
dctx memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N (spZ regs0 - 272)
(cgif_vals s) (firstn 7 (frame_vals (set_fr_gen f gen1))) (firstn 7 (frame_vals b))
(fr_attr f) (fr_ctidx f) (fr_nlp f) (fr_lpal f) (fr_attr b) (fr_ctidx b) (fr_nlp b) (fr_lpal b) (cg_ngp s) (cg_pal s) ctcur ctbef /\
In (fr_img f, N) (blocks Lc Ac) /\ In (fr_img b, N) (blocks Lc Ac).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25
(HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & Hb & HFP & HB & Htv & Hnp & Hu23 & Hu24 & Hu25
& HSV & W112 & W120 & W72 & W80 & W104 & W56 & W32 & W16 & W24 & G2 & G9 & G18 & G19 & G20 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRWv : RAW_SIZE = 48) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & _ & Hfwf).
set (sp0 := spZ regs0) in *.
set (s1 := flush_upd s i gen1 (rw_cur s)) in Hat. set (f1 := set_fr_gen f gen1).
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hbin : In (Some b) (cg_frames s)) by (eapply nth_error_In; exact Hb).
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
assert (Hfr1 : cg_frames s1 = list_set (cg_frames s) i (Some f1)) by (subst s1 f1; apply cg_frames_flush_upd; exact Hf).
assert (Hf1in : In (Some f1) (cg_frames s1)) by (rewrite Hfr1; eapply nth_error_In; apply nth_error_list_set_same; exact Hilt).
assert (Hb1in : In (Some b) (cg_frames s1)).
{ rewrite Hfr1. eapply (nth_error_In _ (i - 1)). rewrite nth_error_list_set_other by lia. exact Hb. }
destruct (af_cgif_geom API Lc Ac memc mdc g s N _ HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom f Hfin) as (Hp0 & Hp1 & Hpg). destruct (Hfgeom b Hbin) as (Hq0 & Hq1 & Hqg).
destruct (fl_img_geom API Lc Ac memc mdc g s N _ f HH0 HB Hfin ltac:(rewrite HN; clear - HW1 HH1; nia)) as [Him0 Him1].
destruct (fl_img_geom API Lc Ac memc mdc g s N _ b HH0 HB Hbin ltac:(rewrite HN; clear - HW1 HH1; nia)) as [Hbi0 Hbi1].
pose proof (af_frames_sep API Lc Ac memc mdc g s N _ i (i - 1) f b HH0 HB Hf Hb ltac:(lia)) as Hfb.
pose proof (af_imgs_sep Lc Ac memc mdc g s N _ i (i - 1) f b HH0 HB Hf Hb ltac:(lia)) as Dfb.
pose proof Hat as (Hobj & Hraw & Hfrs). rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s) : cgif_vals s1 = cgif_vals s) in Hobj.
pose proof (Hfrs f1 Hf1in) as Hfobj. change (fr_ptr f1) with (fr_ptr f) in Hfobj.
pose proof (Hfrs b Hb1in) as Hbobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (obj_at_range _ _ _ _ _ Hfobj) as Rf. pose proof (obj_at_range _ _ _ _ _ Hbobj) as Rb.
pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. cbn [nth snd LAY_CGIF Z.of_N] in RW, RH.
pose proof (Rg 9%nat (cg_ngp s) eq_refl) as Rngp. cbn [nth snd LAY_CGIF Z.of_N] in Rngp.
pose proof (Rf 5%nat (fr_nlp f) eq_refl) as Rfnlp. pose proof (Rb 5%nat (fr_nlp b) eq_refl) as Rbnlp.
cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfnlp, Rbnlp.
assert (M16 : forall fr, In (Some fr) (cg_frames s) -> fr_ptr fr mod 8 = 0).
{ intros fr Hfr.
pose proof (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr fr) FRAME_SIZE HH0 ltac:(apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; apply (frame_blocks_in_cgif g s N fr); [exact Hfr | left; reflexivity]) ltac:(lia)) as (_ & _ & H16).
clear - H16. apply Z.mod_divide in H16; [|lia]. apply Z.mod_divide; [lia|]. destruct H16 as [q Hq]. exists (q * 2). lia. }
assert (CTB : forall fr, In (Some fr) (cg_frames s) -> 0 <= fr_nlp fr ->
In (ct_sel (fr_attr fr) (fr_lpal fr) (cg_pal s), 3 * ct_sel (fr_attr fr) (fr_nlp fr) (cg_ngp s)) (cgif_blocks g s N) /\
0 <= 3 * ct_sel (fr_attr fr) (fr_nlp fr) (cg_ngp s)).
{ intros fr Hfr Hnl. unfold ct_sel. destruct (Z.eqb_spec (Z.land (fr_attr fr) 1) 0) as [Hz|Hz].
- split; [| clear - Rngp; lia]. unfold cgif_blocks. right. right. apply in_app_iff. left. unfold pal_blocks.
rewrite (proj1 (Hfwf fr Hfr) Hz). cbn. left. reflexivity.
- split; [| clear - Hnl; lia]. apply (frame_blocks_in_cgif g s N fr _ _ Hfr). unfold frame_blocks. right. right.
destruct (Z.eqb_spec (Z.land (fr_attr fr) 1) 0); [lia|]. left. reflexivity. }
destruct (CTB f Hfin ltac:(clear - Rfnlp; lia)) as [CTf Sf0]. destruct (CTB b Hbin ltac:(clear - Rbnlp; lia)) as [CTb Sb0]. clear CTB.
assert (CTf' : In (ct_sel (fr_attr f) (fr_lpal f) (cg_pal s), 3 * ct_sel (fr_attr f) (fr_nlp f) (cg_ngp s)) (blocks Lc Ac))
by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact CTf).
assert (CTb' : In (ct_sel (fr_attr b) (fr_lpal b) (cg_pal s), 3 * ct_sel (fr_attr b) (fr_nlp b) (cg_ngp s)) (blocks Lc Ac))
by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact CTb).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 CTf') as [Sc0 Sc1].
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 CTb') as [Sd0 Sd1].
destruct (rdn_of_present ubs2_msyms memc (Z.to_nat (3 * ct_sel (fr_attr f) (fr_nlp f) (cg_ngp s))) (ct_sel (fr_attr f) (fr_lpal f) (cg_pal s))
ltac:(intros k Hk; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc _ _ k HH0 CTf' ltac:(lia)))) ltac:(lia) ltac:(lia)) as (ctcur & Rct & _).
destruct (rdn_of_present ubs2_msyms memc (Z.to_nat (3 * ct_sel (fr_attr b) (fr_nlp b) (cg_ngp s))) (ct_sel (fr_attr b) (fr_lpal b) (cg_pal s))
ltac:(intros k Hk; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc _ _ k HH0 CTb' ltac:(lia)))) ltac:(lia) ltac:(lia)) as (ctbef & Rbt & _).
assert (Oc1 : obj_at ubs2segs memc (fr_ptr f) LAY_FrameConfig (firstn 7 (frame_vals f1))).
{ rewrite LAY_Frame_split in Hfobj.
apply (proj1 (obj_at_app ubs2segs _ (fr_ptr f) LAY_FrameConfig [(32, 1%N); (33, 1%N)] (firstn 7 (frame_vals f1)) (skipn 7 (frame_vals f1)) eq_refl)). exact Hfobj. }
assert (Ob1 : obj_at ubs2segs memc (fr_ptr b) LAY_FrameConfig (firstn 7 (frame_vals b))).
{ pose proof Hbobj as Hbobj'. rewrite LAY_Frame_split in Hbobj'.
apply (proj1 (obj_at_app ubs2segs _ (fr_ptr b) LAY_FrameConfig [(32, 1%N); (33, 1%N)] (firstn 7 (frame_vals b)) (skipn 7 (frame_vals b)) eq_refl)). exact Hbobj'. }
destruct (af_frame_geom API Lc Ac memc mdc g s N _ f HH0 HB Hfin) as (_ & Hfimgin & _).
destruct (af_frame_geom API Lc Ac memc mdc g s N _ b HH0 HB Hbin) as (_ & Hbimgin & _).
exists ctcur, ctbef. split; [| split; [exact Hfimgin | exact Hbimgin]].
unfold dctx.
repeat match goal with |- _ /\ _ => split end;
first [ exact Hobj | exact Oc1 | exact Ob1 | exact Rct | exact Rbt | reflexivity | exact Hg0 | exact Hg1 | exact Hg16 | exact Hp0 | exact Hq0
| exact (M16 f Hfin) | exact (M16 b Hbin) | exact Sc0 | exact Sc1 | exact Sd0 | exact Sd1 | exact Sf0 | exact Sb0
| exact Him0 | exact Him1 | exact Hbi0 | exact Hbi1 | exact Dfb | exact HN | exact HNle | exact W80 | exact W104 | exact W112 | exact W120
| clear - Hp1 HFRv; lia | clear - Hq1 HFRv; lia | clear - Hpg HGSv HFRv; lia | clear - Hqg HGSv HFRv; lia | clear - Hfb HFRv; lia
| clear - HW1 RW; lia | clear - HH1 RH; lia | clear - Hceil HFSv; lia | clear - Hsp063; lia
| replace (sp0 - 272) with (sp0 + (-17) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16
| idtac ].
all: fail "dctx leaf".
Qed.
Definition ss_ident : sstate :=
mkSS FL_IDENT sr_atoms [ YQ0b.mkRegion (Some 2%nat) 120 128 124 128 [] ] None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Lemma fl_dgo :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st) (gen1 : Z)
(rest FP : list (Z * Z)) (tv np u23 u24 u25 : Z),
dv_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 ->
forall (regsF : bvmap 5 word) (memF : word -> option byte) w h top left,
journal ubs2_msyms MR FLUSH_STK (spZ regs0) FP L A mem md Lc Ac memF mdc -> KD memc (spZ regs0 - 272) memF ->
word_mem ubs2segs memF (spZ regs0 - 272 + 96) top ->
1 <= w -> 0 <= left -> left + w <= cg_W s -> 1 <= h -> 0 <= top -> top + h <= cg_H s ->
getr regsF 2 = Z_to_bv 64 (spZ regs0 - 272) -> getr regsF 9 = Z_to_bv 64 (fr_img f) -> getr regsF 18 = Z_to_bv 64 (fr_ptr b) ->
getr regsF 27 = Z_to_bv 64 (cg_W s) -> getr regsF 20 = Z_to_bv 64 np ->
getr regsF 26 = Z_to_bv 64 left -> getr regsF 19 = Z_to_bv 64 w -> getr regsF 22 = Z_to_bv 64 h ->
getr regsF 3 = getr regs0 3 -> getr regsF 4 = getr regs0 4 ->
SR ubs2segs (mkCfg (mkst regsF (Z_to_bv 64 FL_DT) memF (seg_rom ubs2segs)) mdc) (fl_post API regs0 g s N i rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE.
destruct (dv_ctx L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE) as (ctcur & ctbef & HC & Hfi & Hbi).
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
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hbin : In (Some b) (cg_frames s)) by (eapply nth_error_In; exact Hb).
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
assert (Hfr1 : cg_frames s1 = list_set (cg_frames s) i (Some f1)) by (subst s1 f1; apply cg_frames_flush_upd; exact Hf).
assert (Hb1in : In (Some b) (cg_frames s1)).
{ rewrite Hfr1. eapply (nth_error_In _ (i - 1)). rewrite nth_error_list_set_other by lia. exact Hb. }
pose proof Hat as (Hobj & Hraw & Hfrs).
pose proof (Hfrs b Hb1in) as Hbobj.
destruct (af_cgif_geom API Lc Ac memc mdc g s N _ HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & _).
assert (KB : forall m, KD memc spv m -> forall bb nn k, In (bb, nn) (cgif_blocks g s N) -> 0 <= k < nn -> mbyte ubs2segs m (bb + k) = mbyte ubs2segs memc (bb + k)).
{ intros m K bb nn k Hbn Hk. assert (Hbn' : In (bb, nn) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0 R1]. apply K; clear - R0 R1 Hk Hsp0 Hac; lia. }
assert (CGAT : forall m, (forall bb nn k, In (bb, nn) (cgif_blocks g s N) -> 0 <= k < nn -> mbyte ubs2segs m (bb + k) = mbyte ubs2segs memc (bb + k)) -> cgif_at m g s1).
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
intros regsF memF w h top left HJF KF V96 Hw Hl0 Hlw Hh Ht0 Hth R2 R9 R18 R27 R20 R26 R19 R22 R3 R4.
assert (WF : forall off v, word_mem ubs2segs memc (sp0 - 272 + off) v -> 0 <= off -> off + 8 <= 272 ->
(off + 8 <= 8 \/ (16 <= off /\ off + 8 <= 40) \/ (56 <= off /\ off + 8 <= 64) \/ (72 <= off /\ off + 8 <= 88) \/ 104 <= off) ->
word_mem ubs2segs memF (sp0 - 272 + off) v).
{ intros off v Hw' H1 H2 H3 k Hk. rewrite <- (Hw' k Hk). apply KF; clear - H1 H2 H3 Hk Hsp0 Hsp1 Hac; subst spv; lia. }
apply (fl_dt API IMG RAWADD L A mem md regs0 regsF Lc Ac memF mdc g N s i f b gen1 rest FP tv np u23 u24 u25 w h top left).
split; [exact HJF|]. split; [exact Hid|]. split; [exact Hra0|]. split; [exact Hal16|]. split; [exact Htp0|].
split.
{ apply CGAT. intros bb nn k Hbn Hk. assert (Hbn' : In (bb, nn) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0 R1]. apply KF; clear - R0 R1 Hk Hsp0 Hac; subst spv; lia. }
split; [exact Hwf|]. split; [exact Hi|]. split; [exact Hf|]. split; [exact Hb|]. split; [exact HFP|]. split; [exact HB|].
split; [exact Htv|]. split; [exact Hnp|]. split; [exact Hu23|]. split; [exact Hu24|]. split; [exact Hu25|].
split; [exact Hw|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh|]. split; [exact Ht0|]. split; [exact Hth|].
split; [apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply KF; clear - Ha Hsp0 Hsp1 Hac; subst spv; lia]|].
split; [apply WF; [exact W112 | clear; lia | clear; lia | clear; lia]|].
split; [apply WF; [exact W120 | clear; lia | clear; lia | clear; lia]|].
split; [apply WF; [exact W72 | clear; lia | clear; lia | clear; lia]|].
split; [apply WF; [exact W80 | clear; lia | clear; lia | clear; lia]|].
split; [apply WF; [exact W104 | clear; lia | clear; lia | clear; lia]|].
split; [exact V96|].
split; [apply WF; [exact W56 | clear; lia | clear; lia | clear; lia]|].
split; [apply WF; [exact W32 | clear; lia | clear; lia | clear; lia]|].
split; [apply WF; [exact W16 | clear; lia | clear; lia | clear; lia]|].
split; [apply WF; [exact W24 | clear; lia | clear; lia | clear; lia]|].
split; [exact R2|]. split; [exact R9|]. split; [exact R18|]. split; [exact R27|]. split; [exact R20|].
split; [exact R26|]. split; [exact R19|]. split; [exact R22|]. split; [exact R3 | exact R4].
Qed.
Definition sse_slow : sstate :=
mkSS FL_SLOW sr_atoms [ YQ0b.mkRegion (Some 18%nat) 8 16 0 0 [mkChunk 8 (CVal 8 (SOff 32 0))] ;
YQ0b.mkRegion (Some 2%nat) 48 56 48 56 [] ; YQ0b.mkRegion (Some 2%nat) 88 112 88 96 [mkChunk 104 (CVal 8 (SOff 33 0))] ] None
(mkFacts [ (19%nat, mkAF 1 65535 0); (18%nat, mkAF 4096 CEIL_MAX 3); (2%nat, mkAF CEIL_MIN (2^63) 4);
(9%nat, mkAF 4096 CEIL_MAX 0); (32%nat, mkAF 4096 CEIL_MAX 0); (33%nat, mkAF 1 65535 0) ] [] []).
Definition sse_post L A mem md (regs0 : bvmap 5 word) Lc Ac memc mdc (s : cgif_st) (f b : frame_st) (FP : list (Z * Z)) (np : Z) (c' : config) : Prop :=
exists (regs : bvmap 5 word) (m : word -> option byte),
c' = mkCfg (mkst regs (Z_to_bv 64 FL_S1O) m (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR FLUSH_STK (spZ regs0) FP L A mem md Lc Ac m mdc /\ KD memc (spZ regs0 - 272) m /\
word_mem ubs2segs m (spZ regs0 - 272 + 48) np /\ word_mem ubs2segs m (spZ regs0 - 272 + 88) 1 /\
getr regs 2 = Z_to_bv 64 (spZ regs0 - 272) /\ getr regs 18 = Z_to_bv 64 (fr_ptr b) /\
getr regs 9 = Z_to_bv 64 (fr_img f) /\ getr regs 8 = Z_to_bv 64 (fr_img b) /\
getr regs 25 = Z_to_bv 64 (fr_img f) /\ getr regs 24 = Z_to_bv 64 (fr_img f) /\
getr regs 27 = Z_to_bv 64 (fr_img b) /\ getr regs 20 = Z_to_bv 64 (fr_img b) /\
getr regs 23 = Z_to_bv 64 1 /\ getr regs 10 = Z_to_bv 64 (cg_W s) /\ getr regs 11 = Z_to_bv 64 0 /\
getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4.
Lemma fl_sse :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st) (gen1 : Z)
(rest FP : list (Z * Z)) (tv np u23 u24 u25 : Z),
dv_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_SLOW) memc (seg_rom ubs2segs)) mdc) (sse_post L A mem md regs0 Lc Ac memc mdc s f b FP np).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE.
destruct (dv_ctx L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE) as (ctcur & ctbef & HC & Hfi & Hbi).
pose proof PRE as (HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & Hb & HFP & HB & Htv & Hnp & Hu23 & Hu24 & Hu25
& HSV & W112 & W120 & W72 & W80 & W104 & W56 & W32 & W16 & W24 & G2 & G9 & G18 & G19 & G20 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
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
assert (HR1 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 48 56 48 56 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|]. split; [intros o Ho; apply (WRS _ HJ); clear - Ho; lia | constructor]. }
assert (HR2 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 88 112 88 96 [mkChunk 104 (CVal 8 (SOff 33 0))])).
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
assert (HPD : pairwise_disjoint E (ss_mem sse_slow)).
{ cbn [ss_mem sse_slow pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU18, HU2.
clear - Hq1 Hsp0 Hac HFRv. repeat split; try exact I; lia. }
assert (HS : st_ok ubs2segs E sse_slow (mkst regs1 (Z_to_bv 64 FL_SLOW) memc (seg_rom ubs2segs))).
{ unfold sse_slow. subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HR0 | constructor; [exact HR1 | constructor; [exact HR2 | constructor]]] | exact HPD | exact HFA]. }
clear HR0 HR1 HR2 HFA HPD.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_SLOW) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ FL_S1O.
{ apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; clear - HFSv; subst spv; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; clear - HFSv; subst spv; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (K1 : KD memc spv (ms_mem ms)).
{ apply (KD_frame _ _ _ _ (KD_refl memc spv)). intros a Ha Hna1 Hna2 Hna3 Hna4. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [r_base r_wlo r_whi base_val]; rewrite ?HU18, ?HU2; clear - Hna2 Hna4; lia. }
clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks ubs2segs E ssx msx 1 _ 2%nat spv HS eq_refl eq_refl HU2) as Hcs48;
pose proof (st_region_chunks ubs2segs E ssx msx 2 _ 2%nat spv HS eq_refl eq_refl HU2) as Hcs88;
pose proof (regs_kept_of_st_ok ubs2segs E ssx msx regs1 _ [2; 3; 4; 9; 18]%bv HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR0;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew E nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hvv; rewrite (st_ok_reg ubs2segs E ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E sv)
by (intros r sv Hr; rewrite (st_ok_reg ubs2segs E ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs48, Hcs88.
assert (WNP : word_mem ubs2segs (ms_mem ms) (spv + 48) np).
{ apply (chunk_word E _ _ 48 (SOff 20 0) _ (proj1 (Forall_forall _ _) Hcs48 (mkChunk 48 (CVal 8 (SOff 20 0))) ltac:(cbn [In]; tauto)));
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE 20%nat 20%bv eq_refl); exact G20 | clear - Hnp; lia]. }
assert (W88 : word_mem ubs2segs (ms_mem ms) (spv + 88) 1).
{ apply (chunk_word E _ _ 88 (SLit 1) _ (proj1 (Forall_forall _ _) Hcs88 (mkChunk 88 (CVal 8 (SLit 1))) ltac:(cbn [In]; tauto))); [reflexivity | clear; lia]. }
clear Hcs48 Hcs88.
assert (HE9 : ew E 9 = Z_to_bv 64 (fr_img f)) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
apply SR_ret. unfold sse_post. exists (ms_regs ms), (ms_mem ms).
split; [reflexivity|]. split; [exact HJ|]. split; [exact K1|]. split; [exact WNP|]. split; [exact W88|].
split; [rewrite (HKR0 2%bv ltac:(cbv; auto 20)); exact G2|].
split; [rewrite (HKR0 18%bv ltac:(cbv; auto 20)); exact G18|].
split; [rewrite (HKR0 9%bv ltac:(cbv; auto 20)); exact G9|].
split; [apply (RG 8%bv 32%nat _ eq_refl); exact HE32|].
split; [apply (RG 25%bv 9%nat _ eq_refl); exact HE9|].
split; [apply (RG 24%bv 9%nat _ eq_refl); exact HE9|].
split; [apply (RG 27%bv 32%nat _ eq_refl); exact HE32|].
split; [apply (RG 20%bv 32%nat _ eq_refl); exact HE32|].
split; [rewrite (RGX 23%bv (SLit 1) eq_refl); reflexivity|].
split; [apply (RG 10%bv 33%nat _ eq_refl); exact HE33|].
split; [rewrite (RGX 11%bv (SLit 0) eq_refl); reflexivity|].
split; [rewrite (HKR0 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (HKR0 4%bv ltac:(cbv; auto 20)); exact G4].
Qed.
Definition ss_sid : sstate :=
mkSS FL_IDENT sr_atoms [ YQ0b.mkRegion (Some 2%nat) 48 104 96 104 [mkChunk 48 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Lemma fl_sid :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st) (gen1 : Z)
(rest FP : list (Z * Z)) (tv np u23 u24 u25 : Z),
dv_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 ->
forall (regs : bvmap 5 word) (m : word -> option byte),
journal ubs2_msyms MR FLUSH_STK (spZ regs0) FP L A mem md Lc Ac m mdc -> KD memc (spZ regs0 - 272) m ->
word_mem ubs2segs m (spZ regs0 - 272 + 48) np ->
getr regs 2 = Z_to_bv 64 (spZ regs0 - 272) -> getr regs 9 = Z_to_bv 64 (fr_img f) -> getr regs 18 = Z_to_bv 64 (fr_ptr b) ->
getr regs 10 = Z_to_bv 64 (cg_W s) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 FL_IDENT) m (seg_rom ubs2segs)) mdc) (fl_post API regs0 g s N i rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE regs m HJm Km W48 R2 R9 R18 R10 R3 R4.
destruct (dv_ctx L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE) as (ctcur & ctbef & HC & Hfi & Hbi).
pose proof PRE as (HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & Hb & HFP & HB & Htv & Hnp & Hu23 & Hu24 & Hu25
& HSV & W112 & W120 & W72 & W80 & W104 & W56 & W32 & W16 & W24 & G2 & G9 & G18 & G19 & G20 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
pose proof Hwf as (Hlen & HW1 & HH1 & _).
set (sp0 := spZ regs0) in *. set (spv := sp0 - 272) in *.
dctx_open HC.
set (E := Ereg regs (map (Z_to_bv 64) [np] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 np) by (subst E; apply (Ereg_vals regs [np] [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), R2; subst spv; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR : region_ok ubs2segs E m (YQ0b.mkRegion (Some 2%nat) 48 104 96 104 [mkChunk 48 (CVal 8 (SOff 32 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|].
split; [intros o Ho; pose proof HJm as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hw) & _); apply Hw; clear - Ho HFSv; subst spv; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ np);
[cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by (clear - Hnp; lia); reflexivity | cbn; clear - Hnp; lia | cbn; lia |].
apply val_mem_word_mem. exact W48. }
assert (HFA : atoms_ok E [ (2%nat, mkAF CEIL_MIN (2^63) 4) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2. change (2 ^ 4) with 16. clear - Hsp0 Hsp1 Hsp16 Hac. repeat split; lia. }
assert (HS : st_ok ubs2segs E ss_sid (mkst regs (Z_to_bv 64 FL_IDENT) m (seg_rom ubs2segs))).
{ unfold ss_sid. subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HR | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | exact HFA]. }
clear HR HFA.
change m with (ms_mem (mkst regs (Z_to_bv 64 FL_IDENT) m (seg_rom ubs2segs))) in HJm.
jrun_to LAWS ubs2tbl_ok HS HJm FL_DT. { eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; clear - HFSv; subst spv; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (KF : KD memc spv (ms_mem ms)).
{ apply (KD_frame _ _ _ _ Km). intros a Ha Hn1 Hn2 Hn3 Hn4. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | []]. cbn [r_base r_wlo r_whi base_val]. rewrite HU2. clear - Hn4. lia. }
clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks ubs2segs E ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU2) as Hcs;
pose proof (regs_kept_of_st_ok ubs2segs E ssx msx regs _ [2; 3; 4; 9; 18]%bv HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew E nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hvv; rewrite (st_ok_reg ubs2segs E ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E sv)
by (intros r sv Hr; rewrite (st_ok_reg ubs2segs E ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs.
assert (V96 : word_mem ubs2segs (ms_mem ms) (spv + 96) 0).
{ apply val_mem_word_mem.
eapply (val_of_chunk_ok ubs2segs E _ _ 96 8%N (SLit 0)); [exact (proj1 (Forall_forall _ _) Hcs (mkChunk 96 (CVal 8 (SLit 0))) ltac:(cbn [In]; tauto)) | reflexivity | cbn; lia | cbn; lia]. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
apply (fl_dgo L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE (ms_regs ms) (ms_mem ms) 1 1 0 0 HJm KF V96).
- clear; lia.
- clear; lia.
- clear - HW1; lia.
- clear; lia.
- clear; lia.
- clear - HH1; lia.
- rewrite (HKR 2%bv ltac:(cbv; auto 50)). exact R2.
- rewrite (HKR 9%bv ltac:(cbv; auto 50)). exact R9.
- rewrite (HKR 18%bv ltac:(cbv; auto 50)). exact R18.
- apply (RG 27%bv 10%nat _ eq_refl). rewrite (HE 10%nat 10%bv eq_refl). exact R10.
- apply (RG 20%bv 32%nat _ eq_refl). exact HE32.
- rewrite (RGX 26%bv (SLit 0) eq_refl). reflexivity.
- rewrite (RGX 19%bv (SLit 1) eq_refl). reflexivity.
- rewrite (RGX 22%bv (SLit 1) eq_refl). reflexivity.
- rewrite (HKR 3%bv ltac:(cbv; auto 50)). exact R3.
- rewrite (HKR 4%bv ltac:(cbv; auto 50)). exact R4.
Qed.
Definition ss_s4fd : sstate :=
mkSS FL_S4F sr_atoms [ YQ0b.mkRegion (Some 2%nat) 48 112 0 0 [mkChunk 48 (CVal 8 (SOff 32 0)); mkChunk 64 (CVal 8 (SOff 33 0)); mkChunk 104 (CVal 8 (SOff 34 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Lemma fl_s4fd :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st) (gen1 : Z)
(rest FP : list (Z * Z)) (tv np u23 u24 u25 : Z),
dv_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 ->
forall (regs : bvmap 5 word) (m : word -> option byte) (top h left right : Z),
journal ubs2_msyms MR FLUSH_STK (spZ regs0) FP L A mem md Lc Ac m mdc -> KD memc (spZ regs0 - 272) m ->
word_mem ubs2segs m (spZ regs0 - 272 + 48) np -> word_mem ubs2segs m (spZ regs0 - 272 + 64) h ->
word_mem ubs2segs m (spZ regs0 - 272 + 96) top ->
0 <= left <= right -> right < cg_W s -> 0 <= top -> 1 <= h -> top + h <= cg_H s ->
getr regs 2 = Z_to_bv 64 (spZ regs0 - 272) -> getr regs 9 = Z_to_bv 64 (fr_img f) -> getr regs 18 = Z_to_bv 64 (fr_ptr b) ->
getr regs 25 = Z_to_bv 64 right -> getr regs 26 = Z_to_bv 64 left ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 FL_S4F) m (seg_rom ubs2segs)) mdc) (fl_post API regs0 g s N i rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE regs m top h left right HJm Km W48 W64 W96
Hlr HrW Ht0 Hh1 Hth R2 R9 R18 R25 R26 R3 R4.
destruct (dv_ctx L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE) as (ctcur & ctbef & HC & Hfi & Hbi).
pose proof PRE as (HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & Hb & HFP & HB & Htv & Hnp & Hu23 & Hu24 & Hu25
& HSV & W112 & W120 & W72 & W80 & W104 & W56 & W32 & W16 & W24 & G2 & G9 & G18 & G19 & G20 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
set (sp0 := spZ regs0) in *. set (spv := sp0 - 272) in *.
dctx_open HC.
assert (W104m : word_mem ubs2segs m (spv + 104) (cg_W s)).
{ intros k Hk. rewrite <- (W104 k Hk). apply Km; clear - Hk Hsp0 Hsp1 Hac; lia. }
set (E := Ereg regs (map (Z_to_bv 64) [np; h; cg_W s] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 np) by (subst E; apply (Ereg_vals regs [np; h; cg_W s] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 h) by (subst E; apply (Ereg_vals regs [np; h; cg_W s] [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 (cg_W s)) by (subst E; apply (Ereg_vals regs [np; h; cg_W s] [] 2%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), R2; subst spv; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR : region_ok ubs2segs E m (YQ0b.mkRegion (Some 2%nat) 48 112 0 0
[mkChunk 48 (CVal 8 (SOff 32 0)); mkChunk 64 (CVal 8 (SOff 33 0)); mkChunk 104 (CVal 8 (SOff 34 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ np);
[cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by (clear - Hnp; lia); reflexivity | cbn; clear - Hnp; lia | cbn; lia |].
apply val_mem_word_mem. exact W48.
- eapply (chunk_ok_val _ _ _ _ _ _ _ h);
[cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by (clear - Hh1 Ht0 Hth HH; lia); reflexivity | cbn; clear - Hh1 Ht0 Hth HH; lia | cbn; lia |].
apply val_mem_word_mem. exact W64.
- eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_W s));
[cbn [sv_denot]; rewrite Z.add_0_r, HE34, unsigned_lit_small by (clear - HW; lia); reflexivity | cbn; clear - HW; lia | cbn; lia |].
apply val_mem_word_mem. exact W104m. }
assert (HFA : atoms_ok E [ (2%nat, mkAF CEIL_MIN (2^63) 4) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2. change (2 ^ 4) with 16. clear - Hsp0 Hsp1 Hsp16 Hac. repeat split; lia. }
assert (HS : st_ok ubs2segs E ss_s4fd (mkst regs (Z_to_bv 64 FL_S4F) m (seg_rom ubs2segs))).
{ unfold ss_s4fd. subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HR | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | exact HFA]. }
clear HR HFA.
change m with (ms_mem (mkst regs (Z_to_bv 64 FL_S4F) m (seg_rom ubs2segs))) in HJm.
jrun_to LAWS ubs2tbl_ok HS HJm FL_DT. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (FR : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs m a).
{ intros a Ha. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | []]. cbn [r_base r_wlo r_whi base_val]. rewrite HU2. clear - Ha. lia. }
assert (KF : KD memc spv (ms_mem ms)) by (apply (KD_frame _ _ _ _ Km); intros a Ha _ _ _ _; exact (FR a Ha)).
assert (V96 : word_mem ubs2segs (ms_mem ms) (spv + 96) top).
{ intros k Hk. rewrite FR by (clear - Hk Hsp0 Hsp1 Hac; lia). exact (W96 k Hk). }
clear HF HG FR.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (regs_kept_of_st_ok ubs2segs E ssx msx regs _ [2; 3; 4; 9; 18; 26]%bv HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew E nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hvv; rewrite (st_ok_reg ubs2segs E ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E sv)
by (intros r sv Hr; rewrite (st_ok_reg ubs2segs E ssx msx r HS), Hr; reflexivity) end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
apply (fl_dgo L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE (ms_regs ms) (ms_mem ms) (right + 1 - left) h top left HJm KF V96).
- clear - Hlr; lia.
- clear - Hlr; lia.
- clear - Hlr HrW; lia.
- exact Hh1.
- exact Ht0.
- exact Hth.
- rewrite (HKR 2%bv ltac:(cbv; auto 50)). exact R2.
- rewrite (HKR 9%bv ltac:(cbv; auto 50)). exact R9.
- rewrite (HKR 18%bv ltac:(cbv; auto 50)). exact R18.
- apply (RG 27%bv 34%nat _ eq_refl). exact HE34.
- apply (RG 20%bv 32%nat _ eq_refl). exact HE32.
- rewrite (HKR 26%bv ltac:(cbv; auto 50)). exact R26.
- rewrite (RGX 19%bv _ eq_refl). eval_sr_get. apply denot_of_U'.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, (U_atom_off E 25 right 1), (U_atom E 26 left)
by first [rewrite (HE 25%nat 25%bv eq_refl); exact R25 | rewrite (HE 26%nat 26%bv eq_refl); exact R26 | clear - Hlr HrW HW; lia].
apply zcanon_add_mulm1; clear - Hlr HrW HW; lia.
- apply (RG 22%bv 33%nat _ eq_refl). exact HE33.
- rewrite (HKR 3%bv ltac:(cbv; auto 50)). exact R3.
- rewrite (HKR 4%bv ltac:(cbv; auto 50)). exact R4.
Qed.
Lemma fl_slow :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st) (gen1 : Z)
(rest FP : list (Z * Z)) (tv np u23 u24 u25 : Z),
dv_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_SLOW) memc (seg_rom ubs2segs)) mdc) (fl_post API regs0 g s N i rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE.
destruct (dv_ctx L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE) as (ctcur & ctbef & HC & Hfi & Hbi).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
set (sp0 := spZ regs0) in *. set (spv := sp0 - 272) in *.
dctx_open HC.
eapply SR_bind; [exact (fl_sse L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE)|].
cbv beta. intros c1 (regs2 & m2 & -> & HJ2 & K2 & W48 & W88 & R2 & R18 & R9 & R8 & R25 & R24 & R27 & R20 & R23 & R10 & R11 & R3 & R4).
eapply SR_bind.
{ exact (fl_s1o API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
(Z.to_nat (cg_H s)) 0 FLUSH_STK sp0 FP L A mem md Lc Ac mdc regs2 m2 HJ2 K2 Hfi Hbi eq_refl ltac:(clear - HFSv; lia)
ltac:(clear; lia) ltac:(clear - HH; lia) ltac:(clear - HH; lia) R2 R18 R9 R8
ltac:(rewrite R25; f_equal; clear; lia) ltac:(rewrite R24; f_equal; clear; lia) ltac:(rewrite R27; f_equal; clear; lia) ltac:(rewrite R20; f_equal; clear; lia)
R23 R10 R11 W88). }
cbv beta. intros c2 (regs3 & m3 & pc3 & -> & HJ3 & K3 & F3 & Hpc3 & HK3).
assert (P2 : getr regs3 2 = Z_to_bv 64 spv) by (rewrite (HK3 2%bv ltac:(cbv; auto 20)); exact R2).
assert (P8 : getr regs3 8 = Z_to_bv 64 (fr_img b)) by (rewrite (HK3 8%bv ltac:(cbv; auto 20)); exact R8).
assert (P9 : getr regs3 9 = Z_to_bv 64 (fr_img f)) by (rewrite (HK3 9%bv ltac:(cbv; auto 20)); exact R9).
assert (P18 : getr regs3 18 = Z_to_bv 64 (fr_ptr b)) by (rewrite (HK3 18%bv ltac:(cbv; auto 20)); exact R18).
assert (P3 : getr regs3 3 = getr regs0 3) by (rewrite (HK3 3%bv ltac:(cbv; auto 20)); exact R3).
assert (P4 : getr regs3 4 = getr regs0 4) by (rewrite (HK3 4%bv ltac:(cbv; auto 20)); exact R4).
assert (W48a : word_mem ubs2segs m3 (spv + 48) np).
{ intros k Hk. rewrite (F3 (spv + 48 + Z.of_nat k)) by (clear - Hk Hsp0 Hsp1 Hac; lia). exact (W48 k Hk). }
destruct Hpc3 as [[-> (top & c0 & Htop & Hc0 & Hne & Q26 & Q12 & Q13 & W96)] | [-> Q10]].
2: exact (fl_sid L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE regs3 m3 HJ3 K3 W48a P2 P9 P18 Q10 P3 P4).
eapply SR_bind.
{ exact (fl_s2 API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
FLUSH_STK sp0 FP L A mem md Lc Ac mdc regs3 m3 top HJ3 K3 Hfi Hbi eq_refl ltac:(clear - HFSv; lia) Htop W96 P2 P18 P9 P8 Q26 Q12 Q13). }
cbv beta. intros c4 (regs4 & m4 & -> & HJ4 & K4 & F4 & (hrow & Hhr & Q26b) & Q12b & Q13b & Q21 & Q23 & W96b & HK4).
assert (Y2 : getr regs4 2 = Z_to_bv 64 spv) by (rewrite (HK4 2%bv ltac:(cbv; auto 20)); exact P2).
assert (Y8 : getr regs4 8 = Z_to_bv 64 (fr_img b)) by (rewrite (HK4 8%bv ltac:(cbv; auto 20)); exact P8).
assert (Y9 : getr regs4 9 = Z_to_bv 64 (fr_img f)) by (rewrite (HK4 9%bv ltac:(cbv; auto 20)); exact P9).
assert (Y18 : getr regs4 18 = Z_to_bv 64 (fr_ptr b)) by (rewrite (HK4 18%bv ltac:(cbv; auto 20)); exact P18).
assert (Y3 : getr regs4 3 = getr regs0 3) by (rewrite (HK4 3%bv ltac:(cbv; auto 20)); exact P3).
assert (Y4 : getr regs4 4 = getr regs0 4) by (rewrite (HK4 4%bv ltac:(cbv; auto 20)); exact P4).
assert (W48b : word_mem ubs2segs m4 (spv + 48) np).
{ intros k Hk. rewrite (F4 (spv + 48 + Z.of_nat k)) by (clear - Hk Hsp0 Hsp1 Hac; lia). exact (W48a k Hk). }
eapply SR_bind.
{ exact (fl_s3 API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
FLUSH_STK sp0 FP L A mem md Lc Ac mdc regs4 m4 top hrow c0 HJ4 K4 Hfi Hbi eq_refl ltac:(clear - HFSv; lia)
ltac:(clear - Htop Hhr; lia) ltac:(clear - Hhr; lia) Hc0 Hne W96b Y2 Y8 Y9 Y18 Q21 Q23 Q12b Q13b Q26b). }
cbv beta. intros c5 (regs5 & m5 & lft & -> & HJ5 & K5 & W64 & F5 & W96c & Hlft & Q26c & Q25 & Q20 & Q19 & Q24 & Q10c & HK5).
assert (D2 : getr regs5 2 = Z_to_bv 64 spv) by (rewrite (HK5 2%bv ltac:(cbv; auto 20)); exact Y2).
assert (D8 : getr regs5 8 = Z_to_bv 64 (fr_img b)) by (rewrite (HK5 8%bv ltac:(cbv; auto 20)); exact Y8).
assert (D9 : getr regs5 9 = Z_to_bv 64 (fr_img f)) by (rewrite (HK5 9%bv ltac:(cbv; auto 20)); exact Y9).
assert (D18 : getr regs5 18 = Z_to_bv 64 (fr_ptr b)) by (rewrite (HK5 18%bv ltac:(cbv; auto 20)); exact Y18).
assert (D3 : getr regs5 3 = getr regs0 3) by (rewrite (HK5 3%bv ltac:(cbv; auto 20)); exact Y3).
assert (D4 : getr regs5 4 = getr regs0 4) by (rewrite (HK5 4%bv ltac:(cbv; auto 20)); exact Y4).
assert (D21 : getr regs5 21 = Z_to_bv 64 (2 ^ 64 - 1 - fr_img f)) by (rewrite (HK5 21%bv ltac:(cbv; auto 20)); exact Q21).
assert (D23 : getr regs5 23 = Z_to_bv 64 (2 ^ 64 - 1 - fr_img b)) by (rewrite (HK5 23%bv ltac:(cbv; auto 20)); exact Q23).
assert (W48c : word_mem ubs2segs m5 (spv + 48) np).
{ intros k Hk. rewrite (F5 (spv + 48 + Z.of_nat k)) by (clear - Hk Hsp0 Hsp1 Hac; lia). exact (W48b k Hk). }
set (h := hrow + 1 - top).
assert (Hh : 1 <= h /\ top + h <= cg_H s) by (subst h; clear - Hhr Htop; lia).
eapply SR_bind.
{ exact (fl_s4l API IMG memc g (fr_ptr f) (fr_ptr b) (fr_img f) (fr_img b) (cg_W s) (cg_H s) N spv _ _ _ _ _ _ _ _ _ _ _ _ _ ctcur ctbef HC
(Datatypes.S (Z.to_nat ((cg_W s - 1 - c0) * h + h))) top (cg_W s - 1) FLUSH_STK sp0 FP L A mem md Lc Ac mdc regs5 m5 top h c0
HJ5 K5 Hfi Hbi ltac:(clear - Htop; lia) ltac:(clear - Hh; lia) ltac:(clear - Hh; lia) Hc0 Hne
ltac:(clear - Hh; lia) ltac:(clear; lia) ltac:(clear - Hc0; lia) ltac:(clear - Hc0 Hh; nia)
W96c D2 D8 D9 D18 D21 D23 Q20 Q25 Q10c Q19 ltac:(rewrite Q24; f_equal; subst h; clear; lia)). }
cbv beta. intros c6 (regs6 & m6 & xr & -> & HJ6 & E6 & Hxr & Q25d & HK6).
assert (WE : forall a v, word_mem ubs2segs m5 a v -> word_mem ubs2segs m6 a v).
{ intros a v Hw k Hk. rewrite (mbyte_of_eq _ _ _ _ E6). exact (Hw k Hk). }
assert (T2 : getr regs6 2 = Z_to_bv 64 spv) by (rewrite (HK6 2%bv ltac:(cbv; auto 20)); exact D2).
assert (T9 : getr regs6 9 = Z_to_bv 64 (fr_img f)) by (rewrite (HK6 9%bv ltac:(cbv; auto 20)); exact D9).
assert (T18 : getr regs6 18 = Z_to_bv 64 (fr_ptr b)) by (rewrite (HK6 18%bv ltac:(cbv; auto 20)); exact D18).
assert (T26 : getr regs6 26 = Z_to_bv 64 lft) by (rewrite (HK6 26%bv ltac:(cbv; auto 20)); exact Q26c).
assert (T3 : getr regs6 3 = getr regs0 3) by (rewrite (HK6 3%bv ltac:(cbv; auto 20)); exact D3).
assert (T4 : getr regs6 4 = getr regs0 4) by (rewrite (HK6 4%bv ltac:(cbv; auto 20)); exact D4).
exact (fl_s4fd L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE regs6 m6 top h lft xr
HJ6 (KD_eq _ _ _ _ K5 E6) (WE _ _ W48c) (WE _ _ W64) (WE _ _ W96c)
ltac:(clear - Hlft Hxr; lia) ltac:(clear - Hxr; lia) ltac:(clear - Htop; lia) ltac:(clear - Hh; lia) ltac:(clear - Hh; lia)
T2 T9 T18 Q25d T26 T3 T4).
Qed.
End S.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
