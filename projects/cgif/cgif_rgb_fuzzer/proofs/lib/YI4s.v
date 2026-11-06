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
YI1e YI1i YI57 YI1h YI0x YI07 YP14 YI08 YI0c YI0g
YI3h YI3d YI4v YI4r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Lemma optfp_fp : forall p n, optfp p n = blocks_fp (optb p n).
Proof. intros p n. unfold optfp, optb, blocks_fp. destruct (p =? 0); reflexivity. Qed.

Lemma optb_nz : forall p n, p <> 0 -> optb p n = [(p, n)].
Proof. intros p n Hp. unfold optb. rewrite (proj2 (Z.eqb_neq p 0) Hp). reflexivity. Qed.
Definition LAY_XC : layout_t := [(48, 8%N)].
Definition LAY_XD : layout_t := [(56, 8%N)].
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Hypothesis FCHT : forall fx', free_cht_spec (fx:=fx') API.
Hypothesis FTREE : forall fx', free_tree_spec (fx:=fx') API.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation keep2 pnew fimg := (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)]).
Lemma heap_sep_app' : forall Lc Ac memc mdc (l1 l2 : list (Z * Z)) x y,
heap_ok MR Lc Ac memc mdc -> Permutation (blocks Lc Ac) (l1 ++ l2) -> In x l1 -> In y l2 ->
fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
intros Lc Ac memc mdc l1 l2 x y HH HP Hx Hy. destruct (in_split _ _ Hx) as (a & b & ->).
apply (heap_sep_perm _ _ LAWS Lc Ac memc mdc x (a ++ b ++ l2) y HH).
- eapply Permutation_trans; [exact HP|]. rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle.
- apply in_app_iff. right. apply in_app_iff. right. exact Hy.
Qed.
Lemma tmp_of_station : forall Lc Ac memc mdc (keep tmp : list (Z * Z)) b n,
heap_ok MR Lc Ac memc mdc ->
Permutation (blocks Lc Ac) (keep ++ tmp) ->
Permutation (blocks L A) (BASE r g N img fmt rest s bef beffmt) ->
(forall x, In x (BASE r g N img fmt rest s bef beffmt) -> In x keep) ->
In (b, n) tmp -> 0 < n ->
In (b, n) (blocks Lc Ac) /\ ~ In (b, n) (blocks L A).
Proof.
intros Lc Ac memc mdc keep tmp b n HH HP HBe Hsub Hin Hn.
split; [eapply Permutation_in; [apply Permutation_sym; exact HP | apply in_app_iff; right; exact Hin]|].
apply in_split in Hin as (T1 & T2 & ->).
eapply (tmp_not_entry API L A Lc Ac memc mdc b n (keep ++ T1 ++ T2)); [exact HH | | | exact Hn].
- eapply Permutation_trans; [exact HP|]. rewrite app_assoc. apply Permutation_sym.
replace (keep ++ T1 ++ T2) with ((keep ++ T1) ++ T2) by (rewrite app_assoc; reflexivity). apply Permutation_middle.
- intros x Hx. apply in_app_iff. left. apply Hsub. eapply Permutation_in; [exact HBe | exact Hx].
Qed.
Lemma kept_across_call : forall STK1 sp1 Lc Ac memc mdc L2 A2 mem2 md2 (keep tmp : list (Z * Z)),
heap_ok MR Lc Ac memc mdc ->
Permutation (blocks Lc Ac) (keep ++ tmp) ->
journal src2_msyms MR STK1 sp1 (blocks_fp tmp) Lc Ac memc mdc L2 A2 mem2 md2 ->
Permutation (blocks L2 A2) keep ->
forall b m i, In (b, m) keep -> 0 <= i < m -> mbyte src2segs mem2 (b + i) = mbyte src2segs memc (b + i).
Proof.
intros STK1 sp1 Lc Ac memc mdc L2 A2 mem2 md2 keep tmp HH HP HJc HB2 b m i Hbm Hi.
pose proof HJc as (_ & _ & _ & Hblk & _).
apply (Hblk b m i).
- eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact Hbm.
- eapply Permutation_in; [apply Permutation_sym; exact HB2|]. exact Hbm.
- exact Hi.
- intros HF1. apply inFP_blocks_fp in HF1 as (b' & m' & Hbm' & Hab').
pose proof (heap_sep_app' Lc Ac memc mdc keep tmp (b, m) (b', m') HH HP Hbm Hbm') as Hsep. cbn [fst snd] in Hsep. lia.
Qed.
Lemma init_of_live_r : forall L2 A2 mem2 md2 l,
heap_ok MR L2 A2 mem2 md2 -> Permutation (blocks L2 A2) (BASE r g N img fmt rest s bef beffmt ++ l) -> st_init_done A2 = true.
Proof.
intros L2 A2 mem2 md2 l HH HB.
assert (Hin : In (r, RGB_SIZE) (blocks L2 A2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left. left. reflexivity. }
apply blocks_In in Hin as (q & _ & Hq). exact (init_done_of_block A2 (q, RGB_SIZE) (proj1 (proj2 HH)) Hq).
Qed.
Definition ss_X38 : sstate := mkSS PC_X38 sr_atoms [] None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Lemma src2_rgbadd_X38 : seg_X38 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof.
intros KXB regs1 Lc Ac memc mdc pnew fimg c f h u p x cnt0 ts0 HAT.
destruct HAT as (HINV & HREGS & Hfmt & G20 & G9 & G25 & G21 & G8 & Hobj & Hcg & Hpnew & Hfimg & Hcht & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HCSv : CHT_SIZE = 48) by reflexivity. assert (HFSv : FREECHT_STK = 8208) by reflexivity.
assert (HN1 : 1 <= N).
{ destruct Hwf as (_ & HW1 & HH1 & HNdef & _). rewrite HNdef. clear - HW1 HH1. nia. }
set (tmp := (c, CHT_SIZE) :: optb f (4 * TS0) ++ optb h (3 * TS0) ++ optb u TS0 ++ optb p (3 * TS0) ++ optb x (4 * TS0)).
assert (HB' : Permutation (blocks Lc Ac) (keep2 pnew fimg ++ tmp)).
{ eapply Permutation_trans; [exact HB|]. subst tmp. rewrite <- !app_assoc. apply Permutation_refl. }
assert (HBc : Permutation (blocks Lc Ac) ((c, CHT_SIZE) :: optb f (4 * TS0) ++ optb h (3 * TS0) ++ optb u TS0 ++ optb p (3 * TS0) ++ optb x (4 * TS0) ++ keep2 pnew fimg)).
{ eapply Permutation_trans; [exact HB'|]. eapply Permutation_trans; [apply Permutation_app_comm|]. subst tmp. cbn [app]. rewrite <- !app_assoc. apply Permutation_refl. }
assert (Hsub : forall x0, In x0 (BASE r g N img fmt rest s bef beffmt) -> In x0 (keep2 pnew fimg)) by (intros x0 Hx0; apply in_app_iff; left; exact Hx0).
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = sp regs0) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : sp regs0 mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok src2segs E ss_X38 (mkst regs1 (Z_to_bv 64 PC_X38) memc (seg_rom src2segs))).
{ unfold ss_X38. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_X38) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_free_col_hash_table. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Hmm : ms_mem ms = memc) by (apply functional_extensionality; intros x0; apply (frame_of_nil _ _ _ _ HF)).
jreg HS (10%bv:reg) as Hr10. rewrite (HE 20%nat 20%bv eq_refl), G20 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
assert (Hspms : spZ (ms_regs ms) = sp regs0) by (unfold spZ; rewrite Hr2; apply unsigned_lit_small; unfold sp, sp0, RGBA_FRAME in *; lia).
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := FREECHT_STK)
(FP1 := (c, c + CHT_SIZE) :: optfp f (4 * TS0) ++ optfp h (3 * TS0) ++ optfp u TS0 ++ optfp p (3 * TS0) ++ optfp x (4 * TS0))
(K := fun L5 A5 (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) => Permutation (blocks L5 A5) (keep2 pnew fimg));
[ exact HS | reflexivity | exact HJ | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspms; exact Hsp16 | lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia | exact Hr4 | ].
- intros HPRE1. rewrite Hmm in HPRE1 |- *. eapply SR_mono.
{ eapply (FCHT fx Lc Ac (ms_regs ms) memc mdc c f h u p x cnt0 ts0 (4 * TS0) (3 * TS0) TS0 (3 * TS0) (4 * TS0) (keep2 pnew fimg) HPRE1 Hr10 Hcht HBc). }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & HB5).
exists L5, A5, regs5, mem5, md5. split; [rewrite Hr1; reflexivity|]. split; [exact HJc5|]. split; [exact HP5 | exact HB5].
- intros a Ha. right.
assert (Ha' : inFP (blocks_fp tmp) a).
{ subst tmp. cbn [blocks_fp map fst snd]. rewrite !map_app. change (map ?F (optb ?q ?n)) with (blocks_fp (optb q n)). rewrite <- !optfp_fp. exact Ha. }
apply inFP_blocks_fp in Ha' as (b & n & Hbn & Hab). exists b, n.
destruct (tmp_of_station Lc Ac memc mdc (keep2 pnew fimg) tmp b n HHc HB' HBent Hsub Hbn ltac:(lia)) as [H1 H2].
split; [exact H1|]. split; [exact H2 | lia]. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HB5). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc5, HP5, HJ5.
pose proof HJc5 as (HH5 & _ & Hhi5 & _).
assert (HI : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte src2segs mem5 x0 = mbyte src2segs memc x0).
{ intros x0 Hx Hsx. rewrite <- Hmm. apply (proj1 (Hhi5 x0 Hx ltac:(rewrite Hspms; lia))). }
assert (Hkeep' : forall b m i, In (b, m) (keep2 pnew fimg) -> 0 <= i < m -> mbyte src2segs mem5 (b + i) = mbyte src2segs memc (b + i)).
{ rewrite <- Hmm. eapply (kept_across_call FREECHT_STK (spZ (ms_regs ms)) Lc Ac (ms_mem ms) mdc L5 A5 mem5 md5 (keep2 pnew fimg) tmp);
[rewrite Hmm; exact HHc | exact HB' | | exact HB5].
subst tmp. cbn [blocks_fp map fst snd]. rewrite !map_app. change (map ?F (optb ?q ?n)) with (blocks_fp (optb q n)). rewrite <- !optfp_fp. exact HJc5. }
change (Z_to_bv 64 82592) with (Z_to_bv 64 PC_XB).
apply (KXB regs5 L5 A5 mem5 md5 pnew fimg).
split.
{
split; [exact HJ5|]. split; [exact (init_of_live_r L5 A5 mem5 md5 _ (proj1 HJ5) HB5)|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc mem5 (sp regs0)); [exact HRA | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp0 in *; lia | unfold sp0 in *; lia | exact HI]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply HI; unfold sp, sp0, RGBA_FRAME in *; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [rewrite (regs_preserved_frame _ _ HP5 2%bv ltac:(vm_compute; reflexivity)); exact Hr2|].
split; [rewrite (regs_preserved_frame _ _ HP5 3%bv ltac:(vm_compute; reflexivity)); jreg HS (3%bv:reg) as Hq3; rewrite (HE 3%nat 3%bv eq_refl), G3 in Hq3; exact Hq3|].
rewrite (regs_preserved_frame _ _ HP5 4%bv ltac:(vm_compute; reflexivity)), Hr4, Htp0. reflexivity. }
split; [exact Hfmt|].
split. { rewrite (regs_preserved_frame _ _ HP5 9%bv ltac:(vm_compute; reflexivity)). jreg HS (9%bv:reg) as Hq. rewrite (HE 9%nat 9%bv eq_refl), G9 in Hq. exact Hq. }
split. { rewrite (regs_preserved_frame _ _ HP5 25%bv ltac:(vm_compute; reflexivity)). jreg HS (25%bv:reg) as Hq. rewrite (HE 25%nat 25%bv eq_refl), G25 in Hq. exact Hq. }
split. { rewrite (regs_preserved_frame _ _ HP5 21%bv ltac:(vm_compute; reflexivity)). jreg HS (21%bv:reg) as Hq. rewrite (HE 21%nat 21%bv eq_refl), G21 in Hq. exact Hq. }
split. { rewrite (regs_preserved_frame _ _ HP5 8%bv ltac:(vm_compute; reflexivity)). jreg HS (8%bv:reg) as Hq. rewrite (HE 8%nat 8%bv eq_refl), G8 in Hq. exact Hq. }
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |].
intros i Hi. apply (Hkeep' r RGB_SIZE i); [apply in_app_iff; left; left; reflexivity | exact Hi]. }
split. { eapply (cgif_at_kept _ _ g s N (keep2 pnew fimg)); [| exact Hcg | exact Hkeep'].
unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
split; [exact Hpnew|]. split; [exact Hfimg|]. exact HB5.
Qed.
Lemma slot_kept : forall (m m' : word -> option byte) off v,
slot regs0 m off v -> 0 <= off -> alloc_ceiling <= sp regs0 -> sp regs0 + off + 8 <= 2 ^ 64 ->
(forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte src2segs m' x0 = mbyte src2segs m x0) ->
slot regs0 m' off v.
Proof. intros m m' off v Hs Hoff Hlo Hhi HI k Hk. rewrite HI; [apply Hs; exact Hk | lia | lia]. Qed.
Lemma slots_mid_kept : forall (m m' : word -> option byte) pnew fimg,
slots_mid regs0 cfp N fattr m pnew fimg -> alloc_ceiling <= sp regs0 -> sp regs0 + RGBA_FRAME <= 2 ^ 64 ->
(forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte src2segs m' x0 = mbyte src2segs m x0) ->
slots_mid regs0 cfp N fattr m' pnew fimg.
Proof.
intros m m' pnew fimg (S1 & S2 & S3 & S4 & S5) Hlo Hhi HI. unfold RGBA_FRAME in Hhi.
unfold slots_mid, SL_N, SL_cfp, SL_new, SL_fimg, SL_fa1 in *.
repeat split; (eapply slot_kept; [eassumption | lia | exact Hlo | lia | exact HI]).
Qed.
Lemma chtq_ok_kept : forall (m m' : word -> option byte) C cnt pal,
chtq_ok m C cnt pal ->
(forall i, 0 <= i < CHT_SIZE -> mbyte src2segs m' (ch_c C + i) = mbyte src2segs m (ch_c C + i)) ->
(forall i, 0 <= i < 3 * ch_T C -> mbyte src2segs m' (ch_p C + i) = mbyte src2segs m (ch_p C + i)) ->
chtq_ok m' C cnt pal.
Proof.
intros m m' C cnt pal (Ho & Ha & Hl & Hin & Hlow) Kc Kp.
split; [|split; [|split; [exact Hl | split; [exact Hin | exact Hlow]]]].
- eapply (obj_at_transport_range src2segs _ _ _ _ _ CHT_SIZE); [exact Ho | reflexivity | exact Kc].
- eapply arr8_frame; [exact Ha|]. intros a Ha'. replace a with (ch_p C + (a - ch_p C)) by lia. apply Kp. lia.
Qed.
Section j.
Context {fxi : YK11.FPState}.
Definition ss_XD : sstate :=
mkSS PC_XD sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 (obj_chunks_from LAY_XD 32) ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Lemma XD_at : forall regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn,
K_XC (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
frm_zero (@fp_csr fxi) ->
at_XD (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn ->
SR src2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XD) memc (seg_rom src2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn KXC HFRM HAT.
destruct HAT as (HINV & HREGS & Hfmt & G24 & G20 & G21 & G8 & Hsl & Hobj & Hcg & Hchq & Hpnew & Hfimg & Hfdp & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HCSv : CHT_SIZE = 48) by reflexivity.
assert (HN1 : 1 <= N).
{ destruct Hwf as (_ & HW1 & HH1 & HNdef & _). rewrite HNdef. clear - HW1 HH1. nia. }
pose proof Hsl as (S32 & S40 & S48 & S56 & S24).
set (keep := keep2 pnew fimg ++ cht_blks C).
assert (HB' : Permutation (blocks Lc Ac) ((fdp, fdn) :: keep)).
{ eapply Permutation_trans; [exact HB|].
replace (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ [(fdp, fdn)]) with (keep ++ [(fdp, fdn)])
by (subst keep; rewrite <- !app_assoc; reflexivity).
apply Permutation_sym, Permutation_cons_append. }
assert (Hsub : forall x0, In x0 (BASE r g N img fmt rest s bef beffmt) -> In x0 keep)
by (intros x0 Hx0; subst keep; apply in_app_iff; left; apply in_app_iff; left; exact Hx0).
assert (Hfin : In (fdp, fdn) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB' | left; reflexivity]).
assert (Hfiin : In (fimg, N) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB' | right; subst keep; apply in_app_iff; left; apply in_app_iff; right; right; left; reflexivity]. }
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac memc mdc fimg N HHc Hfiin ltac:(lia)) as (Hfi0 & Hfi1 & _).
assert (HoXD : obj_at src2segs memc (sp regs0) LAY_XD [fimg]).
{ cbn [obj_at LAY_XD].
split; [split; [cbn [fst snd]; apply val_mem_word_mem; exact S56 | cbn [fst snd]; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia]|]. exact I. }
set (E := Ereg regs1 (map (Z_to_bv 64) [fimg] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; apply (Ereg_vals regs1 _ [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp regs0) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : sp regs0 mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok (fx:=fxi) src2segs E ss_XD (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XD) memc (seg_rom src2segs))).
{ unfold ss_XD. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj src2segs _ memc 2 (sp regs0)); [exact HU2 | unfold sp, sp0 in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | exact HoXD | reflexivity | | intros i Hi; lia].
intros jj v Hjj. apply (Ereg_vals regs1 _ [] jj v Hjj).
- cbn [pairwise_disjoint all_disjoint]. repeat split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change memc with (ms_mem (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XD) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_free. { apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (Hmm : ms_mem ms = memc) by (apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF x0); reflexivity).
clear HF HG.
jreg HS (10%bv:reg) as Hq10. rewrite (HE 24%nat 24%bv eq_refl), G24 in Hq10.
jreg HS (2%bv:reg) as Hq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hq2.
jreg HS (4%bv:reg) as Hq4. rewrite (HE 4%nat 4%bv eq_refl), G4 in Hq4.
jreg HS (1%bv:reg) as Hq1.
eapply SR_bind.
{ eapply (jfree_at _ _ LAWS src2_errno_low IMG (aa_free API)) with (a := fdp) (n := fdn) (spc := sp regs0);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hfin | exact Hq10 | exact Hq2
| unfold sp, sp0, RGBA_FRAME in *; lia | exact Hsp16 | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia
| rewrite Hq4; exact Htp0 | exact Hq1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hin0 i Hi. exfalso.
refine (proj2 (tmp_of_station Lc Ac memc mdc keep [(fdp, fdn)] fdp fdn HHc _ HBent Hsub ltac:(left; reflexivity) ltac:(lia)) Hin0).
eapply Permutation_trans; [exact HB' | apply Permutation_cons_append]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hinit2).
pose proof (perm_after_rm1 _ _ _ _ HB' Hrm) as HB2.
rewrite Hmm in Hkeep, Hhi2.
assert (HI : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte src2segs mem2 x0 = mbyte src2segs memc x0).
{ intros x0 Hx Hsx. apply (proj1 (Hhi2 x0 Hx ltac:(lia))). }
assert (Hkeep' : forall b m i, In (b, m) keep -> 0 <= i < m -> mbyte src2segs mem2 (b + i) = mbyte src2segs memc (b + i)).
{ intros b m i Hbm Hi. apply (Hkeep b m i); [| exact Hi]. eapply Permutation_in; [apply Permutation_sym; exact HB2 | exact Hbm]. }
jafter_call_keep HS 33%nat regs2 mem2 HP2 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack src2segs _ _ _ 2); [exact HU2 | rewrite Hmm; exact Hhi2 | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | lia | cbn; lia | cbn; lia]. }
clear HS Hq10 Hq2 Hq4 Hq1. rename HS2 into HS.
jrun_to LAWS src2tbl_ok HS HJ2 PC_XC. { apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_regs ms_mem mkst] in HF, HJ2.
assert (Hmm2 : ms_mem ms0 = mem2) by (apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF x0); reflexivity).
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 83184) with (Z_to_bv 64 PC_XC). rewrite Hmm2. rewrite Hmm2 in HJ2.
apply (KXC fxi (ms_regs ms0) L2 A2 mem2 md2 ha pnew fimg C cnt pal HFRM).
split.
{
split; [exact HJ2|]. split; [exact Hinit2|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc mem2 (sp regs0)); [exact HRA | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp0 in *; lia | unfold sp0 in *; lia | exact HI]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply HI; unfold sp, sp0, RGBA_FRAME in *; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [jreg HS (2%bv:reg) as Hq; rewrite Hq, (HE 2%nat 2%bv eq_refl); exact G2|].
split; [jreg HS (3%bv:reg) as Hq; rewrite Hq, (HE 3%nat 3%bv eq_refl); exact G3|].
jreg HS (4%bv:reg) as Hq; rewrite Hq, (HE 4%nat 4%bv eq_refl); exact G4. }
split; [exact Hfmt|].
split; [jreg HS (20%bv:reg) as Hq; rewrite Hq, (HE 20%nat 20%bv eq_refl); exact G20|].
split; [jreg HS (25%bv:reg) as Hq; rewrite Hq; exact HE32|].
split; [jreg HS (21%bv:reg) as Hq; rewrite Hq, (HE 21%nat 21%bv eq_refl); exact G21|].
split; [jreg HS (8%bv:reg) as Hq; rewrite Hq, (HE 8%nat 8%bv eq_refl); exact G8|].
split. { eapply slots_mid_kept; [exact Hsl | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | exact HI]. }
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |].
intros i Hi. apply (Hkeep' r RGB_SIZE i); [subst keep; apply in_app_iff; left; apply in_app_iff; left; left; reflexivity | exact Hi]. }
split. { eapply (cgif_at_kept _ _ g s N keep); [| exact Hcg | exact Hkeep'].
subst keep. unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
split. { eapply chtq_ok_kept; [exact Hchq | |].
- intros i Hi. apply (Hkeep' (ch_c C) CHT_SIZE i); [subst keep; apply in_app_iff; right; left; reflexivity | exact Hi].
- intros i Hi. apply (Hkeep' (ch_p C) (3 * ch_T C) i); [subst keep; apply in_app_iff; right; right; right; right; right; left; reflexivity | exact Hi]. }
split; [exact Hpnew|]. split; [exact Hfimg|]. subst keep. rewrite <- app_assoc in HB2. exact HB2.
Qed.
Definition ss_XT : sstate := mkSS PC_XT sr_atoms [] None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Lemma XT_at : forall regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn t,
K_XD (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
frm_zero (@fp_csr fxi) ->
at_XT (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn t ->
SR src2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XT) memc (seg_rom src2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn t KXD HFRM HAT.
destruct HAT as (HINV & HREGS & Hfmt & G9 & G24 & G20 & G21 & G8 & Hsl & Hobj & Hcg & Hchq & Htree & Hth & Hpnew & Hfimg & Hfdp & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HCSv : CHT_SIZE = 48) by reflexivity.
assert (HFTv : FREETREE_STK = 12304) by reflexivity.
set (keep := (keep2 pnew fimg ++ cht_blks C) ++ [(fdp, fdn)]).
assert (HB' : Permutation (blocks Lc Ac) (keep ++ tree_blocks t)).
{ eapply Permutation_trans; [exact HB|]. subst keep. rewrite <- !app_assoc. apply Permutation_refl. }
assert (HBt : Permutation (blocks Lc Ac) (tree_blocks t ++ keep)) by (eapply Permutation_trans; [exact HB' | apply Permutation_app_comm]).
assert (Hsub : forall x0, In x0 (BASE r g N img fmt rest s bef beffmt) -> In x0 keep)
by (intros x0 Hx0; subst keep; apply in_app_iff; left; apply in_app_iff; left; apply in_app_iff; left; exact Hx0).
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = sp regs0) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : sp regs0 mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok (fx:=fxi) src2segs E ss_XT (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XT) memc (seg_rom src2segs))).
{ unfold ss_XT. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change memc with (ms_mem (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XT) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_free_decision_tree. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Hmm : ms_mem ms = memc) by (apply functional_extensionality; intros x0; apply (frame_of_nil _ _ _ _ HF)).
jreg HS (10%bv:reg) as Hr10. rewrite (HE 9%nat 9%bv eq_refl), G9 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
assert (Hspms : spZ (ms_regs ms) = sp regs0) by (unfold spZ; rewrite Hr2; apply unsigned_lit_small; unfold sp, sp0, RGBA_FRAME in *; lia).
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := FREETREE_STK) (FP1 := blocks_fp (tree_blocks t))
(K := fun L5 A5 (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) => Permutation (blocks L5 A5) keep);
[ exact HS | reflexivity | exact HJ | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspms; exact Hsp16 | lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia | exact Hr4 | ].
- intros HPRE1. rewrite Hmm in HPRE1 |- *. eapply SR_mono.
{ eapply (FTREE fxi Lc Ac (ms_regs ms) memc mdc t keep HPRE1 Hr10 Htree Hth HBt). }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & HB5).
exists L5, A5, regs5, mem5, md5. split; [rewrite Hr1; reflexivity|]. split; [exact HJc5|]. split; [exact HP5 | exact HB5].
- intros a Ha. right. apply inFP_blocks_fp in Ha as (b & n & Hbn & Hab). exists b, n.
destruct (tmp_of_station Lc Ac memc mdc keep (tree_blocks t) b n HHc HB' HBent Hsub Hbn ltac:(lia)) as [H1 H2].
split; [exact H1|]. split; [exact H2 | lia]. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HB5). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc5, HP5, HJ5.
pose proof HJc5 as (HH5 & _ & Hhi5 & _).
assert (HI : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte src2segs mem5 x0 = mbyte src2segs memc x0).
{ intros x0 Hx Hsx. rewrite <- Hmm. apply (proj1 (Hhi5 x0 Hx ltac:(rewrite Hspms; lia))). }
assert (Hkeep' : forall b m i, In (b, m) keep -> 0 <= i < m -> mbyte src2segs mem5 (b + i) = mbyte src2segs memc (b + i)).
{ rewrite <- Hmm. eapply (kept_across_call FREETREE_STK (spZ (ms_regs ms)) Lc Ac (ms_mem ms) mdc L5 A5 mem5 md5 keep (tree_blocks t));
[rewrite Hmm; exact HHc | exact HB' | exact HJc5 | exact HB5]. }
assert (HB5' : Permutation (blocks L5 A5) (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ [(fdp, fdn)])).
{ eapply Permutation_trans; [exact HB5|]. subst keep. rewrite <- !app_assoc. apply Permutation_refl. }
change (Z_to_bv 64 83172) with (Z_to_bv 64 PC_XD).
apply (KXD fxi regs5 L5 A5 mem5 md5 ha pnew fimg C cnt pal fdp fdn HFRM).
split.
{
split; [exact HJ5|].
split; [exact (init_of_live_r L5 A5 mem5 md5 _ (proj1 HJ5) HB5')|].
split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc mem5 (sp regs0)); [exact HRA | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp0 in *; lia | unfold sp0 in *; lia | exact HI]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply HI; unfold sp, sp0, RGBA_FRAME in *; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [rewrite (regs_preserved_frame _ _ HP5 2%bv ltac:(vm_compute; reflexivity)); exact Hr2|].
split; [rewrite (regs_preserved_frame _ _ HP5 3%bv ltac:(vm_compute; reflexivity)); jreg HS (3%bv:reg) as Hq3; rewrite (HE 3%nat 3%bv eq_refl), G3 in Hq3; exact Hq3|].
rewrite (regs_preserved_frame _ _ HP5 4%bv ltac:(vm_compute; reflexivity)), Hr4, Htp0. reflexivity. }
split; [exact Hfmt|].
split. { rewrite (regs_preserved_frame _ _ HP5 24%bv ltac:(vm_compute; reflexivity)). jreg HS (24%bv:reg) as Hq. rewrite (HE 24%nat 24%bv eq_refl), G24 in Hq. exact Hq. }
split. { rewrite (regs_preserved_frame _ _ HP5 20%bv ltac:(vm_compute; reflexivity)). jreg HS (20%bv:reg) as Hq. rewrite (HE 20%nat 20%bv eq_refl), G20 in Hq. exact Hq. }
split. { rewrite (regs_preserved_frame _ _ HP5 21%bv ltac:(vm_compute; reflexivity)). jreg HS (21%bv:reg) as Hq. rewrite (HE 21%nat 21%bv eq_refl), G21 in Hq. exact Hq. }
split. { rewrite (regs_preserved_frame _ _ HP5 8%bv ltac:(vm_compute; reflexivity)). jreg HS (8%bv:reg) as Hq. rewrite (HE 8%nat 8%bv eq_refl), G8 in Hq. exact Hq. }
split. { eapply slots_mid_kept; [exact Hsl | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | exact HI]. }
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |].
intros i Hi. apply (Hkeep' r RGB_SIZE i); [apply Hsub; left; reflexivity | exact Hi]. }
split. { eapply (cgif_at_kept _ _ g s N keep); [| exact Hcg | exact Hkeep'].
subst keep. unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
split. { eapply chtq_ok_kept; [exact Hchq | |].
- intros i Hi. apply (Hkeep' (ch_c C) CHT_SIZE i); [subst keep; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity | exact Hi].
- intros i Hi. apply (Hkeep' (ch_p C) (3 * ch_T C) i); [subst keep; apply in_app_iff; left; apply in_app_iff; right; right; right; right; right; left; reflexivity | exact Hi]. }
split; [exact Hpnew|]. split; [exact Hfimg|]. split; [exact Hfdp|]. exact HB5'.
Qed.
Definition ss_XT2 : sstate := mkSS PC_XT2 sr_atoms [] None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Lemma XT2_at : forall regs1 Lc Ac memc mdc ha pnew fimg C cnt pal t,
K_XC (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
frm_zero (@fp_csr fxi) ->
at_XT2 (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc ha pnew fimg C cnt pal t ->
SR src2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XT2) memc (seg_rom src2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc ha pnew fimg C cnt pal t KXC HFRM HAT.
destruct HAT as (HINV & HREGS & Hfmt & G23 & G25 & G20 & G21 & G8 & Hsl & Hobj & Hcg & Hchq & Htree & Hth & Hpnew & Hfimg & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HCSv : CHT_SIZE = 48) by reflexivity.
assert (HFTv : FREETREE_STK = 12304) by reflexivity.
set (keep := keep2 pnew fimg ++ cht_blks C).
assert (HB' : Permutation (blocks Lc Ac) (keep ++ tree_blocks t)).
{ eapply Permutation_trans; [exact HB|]. subst keep. rewrite <- !app_assoc. apply Permutation_refl. }
assert (HBt : Permutation (blocks Lc Ac) (tree_blocks t ++ keep)) by (eapply Permutation_trans; [exact HB' | apply Permutation_app_comm]).
assert (Hsub : forall x0, In x0 (BASE r g N img fmt rest s bef beffmt) -> In x0 keep)
by (intros x0 Hx0; subst keep; apply in_app_iff; left; apply in_app_iff; left; exact Hx0).
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = sp regs0) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : sp regs0 mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok (fx:=fxi) src2segs E ss_XT2 (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XT2) memc (seg_rom src2segs))).
{ unfold ss_XT2. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change memc with (ms_mem (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XT2) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_free_decision_tree. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Hmm : ms_mem ms = memc) by (apply functional_extensionality; intros x0; apply (frame_of_nil _ _ _ _ HF)).
jreg HS (10%bv:reg) as Hr10. rewrite (HE 23%nat 23%bv eq_refl), G23 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
assert (Hspms : spZ (ms_regs ms) = sp regs0) by (unfold spZ; rewrite Hr2; apply unsigned_lit_small; unfold sp, sp0, RGBA_FRAME in *; lia).
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := FREETREE_STK) (FP1 := blocks_fp (tree_blocks t))
(K := fun L5 A5 (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) => Permutation (blocks L5 A5) keep);
[ exact HS | reflexivity | exact HJ | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspms; exact Hsp16 | lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia | exact Hr4 | ].
- intros HPRE1. rewrite Hmm in HPRE1 |- *. eapply SR_mono.
{ eapply (FTREE fxi Lc Ac (ms_regs ms) memc mdc t keep HPRE1 Hr10 Htree Hth HBt). }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & HB5).
exists L5, A5, regs5, mem5, md5. split; [rewrite Hr1; reflexivity|]. split; [exact HJc5|]. split; [exact HP5 | exact HB5].
- intros a Ha. right. apply inFP_blocks_fp in Ha as (b & n & Hbn & Hab). exists b, n.
destruct (tmp_of_station Lc Ac memc mdc keep (tree_blocks t) b n HHc HB' HBent Hsub Hbn ltac:(lia)) as [H1 H2].
split; [exact H1|]. split; [exact H2 | lia]. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HB5). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc5, HP5, HJ5.
pose proof HJc5 as (HH5 & _ & Hhi5 & _).
assert (HI : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte src2segs mem5 x0 = mbyte src2segs memc x0).
{ intros x0 Hx Hsx. rewrite <- Hmm. apply (proj1 (Hhi5 x0 Hx ltac:(rewrite Hspms; lia))). }
assert (Hkeep' : forall b m i, In (b, m) keep -> 0 <= i < m -> mbyte src2segs mem5 (b + i) = mbyte src2segs memc (b + i)).
{ rewrite <- Hmm. eapply (kept_across_call FREETREE_STK (spZ (ms_regs ms)) Lc Ac (ms_mem ms) mdc L5 A5 mem5 md5 keep (tree_blocks t));
[rewrite Hmm; exact HHc | exact HB' | exact HJc5 | exact HB5]. }
assert (HB5' : Permutation (blocks L5 A5) (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C)).
{ eapply Permutation_trans; [exact HB5|]. subst keep. rewrite <- !app_assoc. apply Permutation_refl. }
jafter_call HS 32%nat regs5 mem5 HP5 HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [constructor | specialize (HS2 HK); clear HK] end.
clear HS. rename HS2 into HS.
jrun_to LAWS src2tbl_ok HS HJ5 PC_XC. { apply wr_ok_nil. }
cbn [ms_regs ms_mem mkst] in HF0, HJ5.
assert (Hmm2 : ms_mem ms0 = mem5) by (apply functional_extensionality; intros x0; apply (frame_of_nil _ _ _ _ HF0)).
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 83184) with (Z_to_bv 64 PC_XC). rewrite Hmm2. rewrite Hmm2 in HJ5.
apply (KXC fxi (ms_regs ms0) L5 A5 mem5 md5 ha pnew fimg C cnt pal HFRM).
split.
{
split; [exact HJ5|].
split; [exact (init_of_live_r L5 A5 mem5 md5 _ (proj1 HJ5) HB5')|].
split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc mem5 (sp regs0)); [exact HRA | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp0 in *; lia | unfold sp0 in *; lia | exact HI]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply HI; unfold sp, sp0, RGBA_FRAME in *; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [jreg HS (2%bv:reg) as Hq; rewrite Hq, (HE 2%nat 2%bv eq_refl); exact G2|].
split; [jreg HS (3%bv:reg) as Hq; rewrite Hq, (HE 3%nat 3%bv eq_refl); exact G3|].
jreg HS (4%bv:reg) as Hq; rewrite Hq, (HE 4%nat 4%bv eq_refl); exact G4. }
split; [exact Hfmt|].
split; [jreg HS (20%bv:reg) as Hq; rewrite Hq, (HE 20%nat 20%bv eq_refl); exact G20|].
split; [jreg HS (25%bv:reg) as Hq; rewrite Hq, (HE 25%nat 25%bv eq_refl); exact G25|].
split; [jreg HS (21%bv:reg) as Hq; rewrite Hq, (HE 21%nat 21%bv eq_refl); exact G21|].
split; [jreg HS (8%bv:reg) as Hq; rewrite Hq, (HE 8%nat 8%bv eq_refl); exact G8|].
split. { eapply slots_mid_kept; [exact Hsl | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | exact HI]. }
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |].
intros i Hi. apply (Hkeep' r RGB_SIZE i); [apply Hsub; left; reflexivity | exact Hi]. }
split. { eapply (cgif_at_kept _ _ g s N keep); [| exact Hcg | exact Hkeep'].
subst keep. unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
split. { eapply chtq_ok_kept; [exact Hchq | |].
- intros i Hi. apply (Hkeep' (ch_c C) CHT_SIZE i); [subst keep; apply in_app_iff; right; left; reflexivity | exact Hi].
- intros i Hi. apply (Hkeep' (ch_p C) (3 * ch_T C) i); [subst keep; apply in_app_iff; right; right; right; right; right; left; reflexivity | exact Hi]. }
split; [exact Hpnew|]. split; [exact Hfimg|]. exact HB5'.
Qed.
Definition ss_XC : sstate :=
mkSS PC_XC sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 (obj_chunks_from LAY_XC 32) ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Lemma XC_at : forall regs1 Lc Ac memc mdc ha pnew fimg C cnt pal,
K_XF (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt s N img fmt fattr fgen delay rest ->
frm_zero (@fp_csr fxi) ->
at_XC (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc ha pnew fimg C cnt pal ->
SR src2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XC) memc (seg_rom src2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc ha pnew fimg C cnt pal KXF HFRM HAT.
destruct HAT as (HINV & HREGS & Hfmt & G20 & G25 & G21 & G8 & Hsl & Hobj & Hcg & Hchq & Hpnew & Hfimg & HB).
destruct C as [c f h u p x T hS uS TS Ht ent]. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T ch_hS ch_uS ch_TS ch_H ch_ent] in *.
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HCSv : CHT_SIZE = 48) by reflexivity. assert (HFSv : FREECHT_STK = 8208) by reflexivity.
assert (HN1 : 1 <= N).
{ destruct Hwf as (_ & HW1 & HH1 & HNdef & _). rewrite HNdef. clear - HW1 HH1. nia. }
destruct Hchq as (Hcht & Hpal & Hpl & HTin & Hlow).
pose proof Hsl as (S32 & S40 & S48 & S56 & S24).
set (tmp := cht_blks (mkCHT c f h u p x T hS uS TS Ht ent)) in *.
assert (HL : forall q n, In (q, n) tmp -> q <> 0) by (intros q n Hq; pose proof (Hlow _ Hq) as Hq'; cbn [fst] in Hq'; lia).
pose proof (HL f (4 * T) ltac:(right; left; reflexivity)) as Hf0.
pose proof (HL h (3 * T) ltac:(right; right; left; reflexivity)) as Hh0.
pose proof (HL u T ltac:(right; right; right; left; reflexivity)) as Hu0.
pose proof (HL p (3 * T) ltac:(right; right; right; right; left; reflexivity)) as Hp0.
pose proof (HL x (4 * T) ltac:(right; right; right; right; right; left; reflexivity)) as Hx0.
assert (HB' : Permutation (blocks Lc Ac) (keep2 pnew fimg ++ tmp)).
{ eapply Permutation_trans; [exact HB|]. rewrite app_assoc. apply Permutation_refl. }
assert (HBc : Permutation (blocks Lc Ac) ((c, CHT_SIZE) :: optb f (4 * T) ++ optb h (3 * T) ++ optb u T ++ optb p (3 * T) ++ optb x (4 * T) ++ keep2 pnew fimg)).
{ rewrite (optb_nz f _ Hf0), (optb_nz h _ Hh0), (optb_nz u _ Hu0), (optb_nz p _ Hp0), (optb_nz x _ Hx0).
eapply Permutation_trans; [exact HB'|]. apply Permutation_app_comm. }
assert (Hsub : forall x0, In x0 (BASE r g N img fmt rest s bef beffmt) -> In x0 (keep2 pnew fimg)) by (intros x0 Hx'; apply in_app_iff; left; exact Hx').
assert (Hpin : In (pnew, fmt * N) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB' | apply in_app_iff; left; apply in_app_iff; right; left; reflexivity]).
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac memc mdc pnew (fmt * N) HHc Hpin ltac:(clear - Hfmt HN1; nia)) as (Hp0' & Hp1' & _).
assert (Hrin : In (r, RGB_SIZE) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB' | apply in_app_iff; left; apply in_app_iff; left; left; reflexivity]).
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac memc mdc r RGB_SIZE HHc Hrin ltac:(lia)) as (Rr0 & Rr1 & _).
assert (Hcin : In (c, CHT_SIZE) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB' | apply in_app_iff; right; left; reflexivity]).
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac memc mdc c CHT_SIZE HHc Hcin ltac:(lia)) as (Hc0 & Hc1 & _).
assert (HoXC : obj_at src2segs memc (sp regs0) LAY_XC [pnew]).
{ cbn [obj_at LAY_XC].
split; [split; [cbn [fst snd]; apply val_mem_word_mem; exact S48 | cbn [fst snd]; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia]|]. exact I. }
set (E := Ereg regs1 (map (Z_to_bv 64) [pnew] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 pnew) by (subst E; apply (Ereg_vals regs1 _ [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp regs0) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : sp regs0 mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok (fx:=fxi) src2segs E ss_XC (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XC) memc (seg_rom src2segs))).
{ unfold ss_XC. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj src2segs _ memc 2 (sp regs0)); [exact HU2 | unfold sp, sp0 in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | exact HoXC | reflexivity | | intros i Hi; lia].
intros jj v Hjj. apply (Ereg_vals regs1 _ [] jj v Hjj).
- cbn [pairwise_disjoint all_disjoint]. repeat split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change memc with (ms_mem (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XC) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_free_col_hash_table. { apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (Hmm : ms_mem ms = memc) by (apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF x0); reflexivity).
clear HF HG.
jreg HS (10%bv:reg) as Hr10. rewrite (HE 20%nat 20%bv eq_refl), G20 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
assert (Hspms : spZ (ms_regs ms) = sp regs0) by (unfold spZ; rewrite Hr2; apply unsigned_lit_small; unfold sp, sp0, RGBA_FRAME in *; lia).
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := FREECHT_STK)
(FP1 := (c, c + CHT_SIZE) :: optfp f (4 * T) ++ optfp h (3 * T) ++ optfp u T ++ optfp p (3 * T) ++ optfp x (4 * T))
(K := fun L5 A5 (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) => Permutation (blocks L5 A5) (keep2 pnew fimg));
[ exact HS | reflexivity | exact HJ | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspms; exact Hsp16 | lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia | exact Hr4 | ].
- intros HPRE1. rewrite Hmm in HPRE1 |- *. eapply SR_mono.
{ eapply (FCHT fxi Lc Ac (ms_regs ms) memc mdc c f h u p x cnt T (4 * T) (3 * T) T (3 * T) (4 * T) (keep2 pnew fimg) HPRE1 Hr10 Hcht HBc). }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & HB5).
exists L5, A5, regs5, mem5, md5. split; [rewrite Hr1; reflexivity|]. split; [exact HJc5|]. split; [exact HP5 | exact HB5].
- intros a Ha. right.
assert (Ha' : inFP (blocks_fp tmp) a).
{ subst tmp. cbn [cht_blks cht_blocks ch_c ch_f ch_h ch_u ch_p ch_x ch_T blocks_fp map fst snd].
unfold optfp in Ha. rewrite (proj2 (Z.eqb_neq f 0) Hf0), (proj2 (Z.eqb_neq h 0) Hh0), (proj2 (Z.eqb_neq u 0) Hu0), (proj2 (Z.eqb_neq p 0) Hp0), (proj2 (Z.eqb_neq x 0) Hx0) in Ha.
cbn [app] in Ha. exact Ha. }
apply inFP_blocks_fp in Ha' as (b & n & Hbn & Hab). exists b, n.
destruct (tmp_of_station Lc Ac memc mdc (keep2 pnew fimg) tmp b n HHc HB' HBent Hsub Hbn ltac:(lia)) as [H1 H2].
split; [exact H1|]. split; [exact H2 | lia]. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HB5). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc5, HP5, HJ5.
pose proof HJc5 as (HH5 & _ & Hhi5 & _).
assert (HI5 : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte src2segs mem5 x0 = mbyte src2segs memc x0).
{ intros x0 Hx Hsx. rewrite <- Hmm. apply (proj1 (Hhi5 x0 Hx ltac:(rewrite Hspms; lia))). }
assert (Hkeep5 : forall b m i, In (b, m) (keep2 pnew fimg) -> 0 <= i < m -> mbyte src2segs mem5 (b + i) = mbyte src2segs memc (b + i)).
{ rewrite <- Hmm. eapply (kept_across_call FREECHT_STK (spZ (ms_regs ms)) Lc Ac (ms_mem ms) mdc L5 A5 mem5 md5 (keep2 pnew fimg) tmp);
[rewrite Hmm; exact HHc | exact HB' | | exact HB5].
subst tmp. cbn [cht_blks cht_blocks ch_c ch_f ch_h ch_u ch_p ch_x ch_T blocks_fp map fst snd].
unfold optfp in HJc5. rewrite (proj2 (Z.eqb_neq f 0) Hf0), (proj2 (Z.eqb_neq h 0) Hh0), (proj2 (Z.eqb_neq u 0) Hu0), (proj2 (Z.eqb_neq p 0) Hp0), (proj2 (Z.eqb_neq x 0) Hx0) in HJc5.
cbn [app] in HJc5. exact HJc5. }
jafter_call_keep HS 33%nat regs5 mem5 HP5 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack src2segs _ _ _ 2); [exact HU2 | exact Hhi5 | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | rewrite Hspms; lia | cbn; lia | cbn; lia]. }
clear HS Hr10 Hr2 Hr4 Hr1. rename HS2 into HS.
jrun_to LAWS src2tbl_ok HS HJ5 src2_A_free. { apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_regs ms_mem mkst] in HF, HJ5.
assert (Hmm1 : ms_mem ms0 = mem5) by (apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF x0); reflexivity).
clear HF HG.
jreg HS (10%bv:reg) as Hq10. rewrite HE32 in Hq10.
jreg HS (2%bv:reg) as Hq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hq2.
jreg HS (4%bv:reg) as Hq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hq4.
jreg HS (1%bv:reg) as Hq1.
assert (HB5c : Permutation (blocks L5 A5) ((pnew, fmt * N) :: BASE r g N img fmt rest s bef beffmt ++ [(fimg, N)])).
{ eapply Permutation_trans; [exact HB5|]. apply Permutation_sym. apply Permutation_middle. }
assert (Hpin5 : In (pnew, fmt * N) (blocks L5 A5)) by (eapply blocks_perm_in; [exact HB5c | left; reflexivity]).
eapply SR_bind.
{ eapply (jfree_at _ _ LAWS src2_errno_low IMG (aa_free API)) with (a := pnew) (n := fmt * N) (spc := sp regs0);
[ exact HS | reflexivity | reflexivity | exact HJ5 | exact Hpin5 | exact Hq10 | exact Hq2
| unfold sp, sp0, RGBA_FRAME in *; lia | exact Hsp16 | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia
| exact Hq4 | exact Hq1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hin0 i Hi. exfalso.
exact (proj2 (tmp_of_station L5 A5 (ms_mem ms0) md5 (BASE r g N img fmt rest s bef beffmt) [(pnew, fmt * N); (fimg, N)] pnew (fmt * N)
(proj1 HJ5) HB5 HBent ltac:(intros x1 Hx1; exact Hx1) ltac:(left; reflexivity) ltac:(lia)) Hin0). }
cbv beta. intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Hrm6 & Hkeep6 & Hhi6 & Hinit6).
pose proof (perm_after_rm1 _ _ _ _ HB5c Hrm6) as HB6.
rewrite Hmm1 in Hkeep6, Hhi6.
change (Z_to_bv 64 82600) with (Z_to_bv 64 PC_XF).
assert (HI : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte src2segs mem6 x0 = mbyte src2segs memc x0).
{ intros x0 Hx Hsx. rewrite <- (HI5 x0 Hx Hsx). apply (proj1 (Hhi6 x0 Hx ltac:(lia))). }
assert (KB : forall b m i, In (b, m) (BASE r g N img fmt rest s bef beffmt ++ [(fimg, N)]) -> 0 <= i < m ->
mbyte src2segs mem6 (b + i) = mbyte src2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- (Hkeep5 b m i); [| | exact Hi].
- apply (Hkeep6 b m i); [| exact Hi]. eapply Permutation_in; [apply Permutation_sym; exact HB6 | exact Hbm].
- apply in_app_iff in Hbm as [Hbm|Hbm]; apply in_app_iff; [left; exact Hbm | right]. right. exact Hbm. }
apply (KXF fxi regs6 L6 A6 mem6 md6 2 fimg N s bef beffmt cur HFRM).
split.
{
split; [exact HJ6|]. split; [exact Hinit6|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc mem6 (sp regs0)); [exact HRA | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp0 in *; lia | unfold sp0 in *; lia | exact HI]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply HI; unfold sp, sp0, RGBA_FRAME in *; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [rewrite (regs_preserved_frame _ _ HP6 2%bv ltac:(vm_compute; reflexivity)); exact Hq2|].
split; [rewrite (regs_preserved_frame _ _ HP6 3%bv ltac:(vm_compute; reflexivity)); jreg HS (3%bv:reg) as Hq3; rewrite (HE 3%nat 3%bv eq_refl), G3 in Hq3; exact Hq3|].
rewrite (regs_preserved_frame _ _ HP6 4%bv ltac:(vm_compute; reflexivity)), Hq4, Htp0. reflexivity. }
split; [lia|].
split. { rewrite (regs_preserved_frame _ _ HP6 25%bv ltac:(vm_compute; reflexivity)). jreg HS (25%bv:reg) as Hq. rewrite (HE 25%nat 25%bv eq_refl), G25 in Hq. exact Hq. }
split. { rewrite (regs_preserved_frame _ _ HP6 21%bv ltac:(vm_compute; reflexivity)). jreg HS (21%bv:reg) as Hq. rewrite (HE 21%nat 21%bv eq_refl), G21 in Hq. exact Hq. }
split. { rewrite (regs_preserved_frame _ _ HP6 8%bv ltac:(vm_compute; reflexivity)). jreg HS (8%bv:reg) as Hq. rewrite (HE 8%nat 8%bv eq_refl), G8 in Hq. exact Hq. }
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |].
intros i Hi. apply (KB r RGB_SIZE i); [apply in_app_iff; left; left; reflexivity | exact Hi]. }
split. { eapply (cgif_at_kept _ _ g s N (BASE r g N img fmt rest s bef beffmt ++ [(fimg, N)])); [| exact Hcg | exact KB].
unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hbef|].
split; [exact Hfimg|].
split. { exact (proj2 (tmp_of_station L6 A6 mem6 md6 (BASE r g N img fmt rest s bef beffmt) [(fimg, N)] fimg N
(proj1 HJ6) HB6 HBent ltac:(intros x1 Hx1; exact Hx1) ltac:(left; reflexivity) ltac:(lia))). }
exact HB6.
Qed.
End j.
Lemma src2_rgbadd_XD : seg_XD API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof. intros KXC fx1 regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn HFRM HAT. exact (XD_at regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn KXC HFRM HAT). Qed.
Lemma src2_rgbadd_XT : seg_XT API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof. intros KXD fx1 regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn t HFRM HAT. exact (XT_at regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn t KXD HFRM HAT). Qed.
Lemma src2_rgbadd_XT2 : seg_XT2 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof. intros KXC fx1 regs1 Lc Ac memc mdc ha pnew fimg C cnt pal t HFRM HAT. exact (XT2_at regs1 Lc Ac memc mdc ha pnew fimg C cnt pal t KXC HFRM HAT). Qed.
Lemma src2_rgbadd_XC : seg_XC API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof. intros KXF fx1 regs1 Lc Ac memc mdc ha pnew fimg C cnt pal HFRM HAT. exact (XC_at regs1 Lc Ac memc mdc ha pnew fimg C cnt pal KXF HFRM HAT). Qed.
End e.
End d.
