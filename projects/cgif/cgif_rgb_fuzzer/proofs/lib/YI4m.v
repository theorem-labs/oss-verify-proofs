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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YK1j.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03
YI1e YI1i YI57 YI1h YI0x YI16 YI07 YP14 YI08 YI0c YI0g
YI3h YI3d YI4v YI4r YI4s YI0f.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition segs_below (segs : list Segment) (B : Z) : bool :=
forallb (fun sg => Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? B) segs.
Lemma writable_present_high : forall segs B m a,
segs_below segs B = true -> B <= a < 2 ^ 64 -> writable_at segs m a -> exists b, mbyte segs m a = Some b.
Proof.
intros segs B m a Hb Ha Hw. unfold writable_at, wview in Hw. unfold mbyte.
destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|]. exfalso.
destruct (find_segment segs (bv_unsigned (Z_to_bv 64 a)) 1) as [sg|] eqn:Hf; [| apply Hw; reflexivity].
pose proof (find_segment_range _ _ _ _ Hf) as [H1 H2]. pose proof (find_segment_in _ _ _ _ Hf) as Hin.
unfold segs_below in Hb. pose proof (proj1 (forallb_forall _ _) Hb sg Hin) as Hle. cbn beta in Hle. apply Z.leb_le in Hle.
rewrite unsigned_lit_small in H2 by lia. lia.
Qed.
Lemma src2_segs_below : segs_below src2segs 140735332483072 = true.
Proof. vm_compute. reflexivity. Qed.
Definition LAY_QE : layout_t := [(88, 8%N); (112, 8%N)].
Definition hold (P : Prop) : Prop := P.
Lemma keep_subq : forall (l L : list reg) (f g : reg -> word),
forallb (fun r => existsb (bv_eqb r) L) l = true ->
(forall r, In r L -> f r = g r) -> forall r, In r l -> f r = g r.
Proof.
intros l L f g Hs H r Hr. apply H. pose proof (proj1 (forallb_forall _ _) Hs r Hr) as Hx. cbn beta in Hx.
apply existsb_exists in Hx as (r' & Hin & Heq). apply bv_eqb_eq in Heq. subst r'. exact Hin.
Qed.
Lemma in_subq : forall (l L : list reg), forallb (fun r => existsb (bv_eqb r) L) l = true -> forall r, In r l -> In r L.
Proof.
intros l L Hs r Hr. pose proof (proj1 (forallb_forall _ _) Hs r Hr) as Hx. cbn beta in Hx.
apply existsb_exists in Hx as (r' & Hin & Heq). apply bv_eqb_eq in Heq. subst r'. exact Hin.
Qed.
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


Section w.
Context {fxi : YK11.FPState}.
Definition ss_QE0 : sstate := mkSS PC_QE sr_atoms [] None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Definition ss_QE1 : sstate := mkSS 0x14468 sr_atoms [] None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Definition ss_QE2 : sstate :=
mkSS 0x14470 sr_atoms
[ YQ0b.mkRegion (Some 20%nat) 40 44 40 44 [] ]
None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (20%nat, mkAF 4096 (2^48) 3) ] [] []).
Lemma QE_at : forall regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt,
K_FIN (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
frm_zero (@fp_csr fxi) ->
at_QE (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt ->
SR src2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_QE) memc (seg_rom src2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt KFIN HFRM HAT.
destruct HAT as (HINV & HREGS & Hfmt & HN1 & Hha & G10 & G27 & G20 & G8 & G24 & Hsl & Hsq & Hfc & Hobj & Hcg & Him & Hchq & Htok & Hpnew & Hfimg & Hflt & HB).
destruct C as [c f h u p x T hS uS TS Ht ent]. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T ch_hS ch_uS ch_TS ch_H ch_ent] in *.
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HCSv : CHT_SIZE = 48) by reflexivity. assert (HFSv : FREECHT_STK = 8208) by reflexivity. assert (HFTv : FREETREE_STK = 12304) by reflexivity.
destruct Hchq as (Hcht & Hpal & Hpl & HTin & Hlow).
destruct Htok as (Htree & Hfull & Hth & Hwft & Hnrng).
pose proof Hsq as ((Q88 & Q96 & Q112) & Q72 & Q80 & Q104).
set (tmp := cht_blks (mkCHT c f h u p x T hS uS TS Ht ent)) in *.
assert (HL : forall q n, In (q, n) tmp -> q <> 0) by (intros q n Hq; pose proof (Hlow _ Hq) as Hq'; cbn [fst] in Hq'; lia).
pose proof (HL f (4 * T) ltac:(right; left; reflexivity)) as Hf0.
pose proof (HL h (3 * T) ltac:(right; right; left; reflexivity)) as Hh0.
pose proof (HL u T ltac:(right; right; right; left; reflexivity)) as Hu0.
pose proof (HL p (3 * T) ltac:(right; right; right; right; left; reflexivity)) as Hp0.
pose proof (HL x (4 * T) ltac:(right; right; right; right; right; left; reflexivity)) as Hx0.
change (hold (fmt = 3 \/ fmt = 4)) in Hfmt. change (hold (ha = 0 \/ (ha = 1 /\ fmt = 4))) in Hha. change (hold (bef = 0 \/ beffmt = 3 \/ beffmt = 4)) in Hbef.
change (hold (pnew <> 0)) in Hpnew. change (hold (fimg <> 0)) in Hfimg. change (hold (flt <> 0)) in Hflt.
change (hold (f <> 0)) in Hf0. change (hold (h <> 0)) in Hh0. change (hold (u <> 0)) in Hu0. change (hold (p <> 0)) in Hp0. change (hold (x <> 0)) in Hx0.
clear HL Hlow. assert (Hha2 : 0 <= ha <= 1) by (pose proof Hha as X; unfold hold in X; lia).
assert (Hsub : forall x0, In x0 (BASE r g N img fmt rest s bef beffmt) -> In x0 (keep2 pnew fimg)) by (intros x0 Hx0'; apply in_app_iff; left; exact Hx0').
assert (Hsp16 : sp regs0 mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HN1' : 1 <= fmt * N) by (clear -Hfmt HN1; unfold hold in Hfmt; nia).
set (keepA := keep2 pnew fimg ++ tmp ++ tree_blocks t).
assert (HBA : Permutation (blocks Lc Ac) ((flt, 4 * (fmt * N)) :: keepA)).
{ eapply Permutation_trans; [exact HB|]. subst keepA. rewrite <- !app_assoc. apply Permutation_sym.
replace (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ tmp ++ tree_blocks t ++ [(flt, 4 * (fmt * N))])
with ((BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ tmp ++ tree_blocks t) ++ [(flt, 4 * (fmt * N))]) by (rewrite <- !app_assoc; reflexivity).
apply Permutation_cons_append. }
assert (HsubA : forall x0, In x0 (BASE r g N img fmt rest s bef beffmt) -> In x0 keepA) by (intros x0 Hx0'; subst keepA; apply in_app_iff; left; apply Hsub; exact Hx0').
assert (Hflt_in : In (flt, 4 * (fmt * N)) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HBA | left; reflexivity]).
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = sp regs0) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HS : st_ok (fx:=fxi) src2segs E ss_QE0 (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_QE) memc (seg_rom src2segs))).
{ unfold ss_QE0. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change memc with (ms_mem (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_QE) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_free. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Hmm : ms_mem ms = memc) by (apply functional_extensionality; intros x0; apply (frame_of_nil _ _ _ _ HF)).
jreg HS (10%bv:reg) as Hq10. rewrite (HE 10%nat 10%bv eq_refl), G10 in Hq10.
jreg HS (2%bv:reg) as Hq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hq2.
jreg HS (4%bv:reg) as Hq4. rewrite (HE 4%nat 4%bv eq_refl), G4 in Hq4.
jreg HS (1%bv:reg) as Hq1.
eapply SR_bind.
{ eapply (jfree_at _ _ LAWS src2_errno_low IMG (aa_free API)) with (a := flt) (n := 4 * (fmt * N)) (spc := sp regs0);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hflt_in | exact Hq10 | exact Hq2
| unfold sp, sp0, RGBA_FRAME in *; lia | exact Hsp16 | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia
| rewrite Hq4; exact Htp0 | exact Hq1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hin0 i Hi. exfalso.
refine (proj2 (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac memc mdc keepA [(flt, 4 * (fmt * N))] flt (4 * (fmt * N)) HHc _ HBent HsubA ltac:(left; reflexivity) ltac:(lia)) Hin0).
eapply Permutation_trans; [exact HBA | apply Permutation_cons_append]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hinit2).
pose proof (perm_after_rm1 _ _ _ _ HBA Hrm) as HB2.
assert (HI2 : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte src2segs mem2 x0 = mbyte src2segs memc x0).
{ intros x0 Hx Hsx. rewrite <- Hmm. apply (proj1 (Hhi2 x0 Hx ltac:(lia))). }
assert (HkeepA : forall b m i, In (b, m) keepA -> 0 <= i < m -> mbyte src2segs mem2 (b + i) = mbyte src2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- Hmm. apply (Hkeep b m i); [| exact Hi]. eapply Permutation_in; [apply Permutation_sym; exact HB2 | exact Hbm]. }
assert (R2 : forall rr : reg, In rr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs2 rr = getr regs1 rr).
{ intros rr Hrr. rewrite (regs_preserved_in _ _ rr HP2) by (exact (in_subq [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv CALLEE_SAVED ltac:(vm_compute; reflexivity) rr Hrr)).
exact (regs_kept_of_st_ok _ _ _ _ regs1 _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity) rr Hrr). }
clear HS HF HG Hq10 Hq2 Hq4 Hq1 Hhi2 Hkeep Hmm HJ HP2 Hrm ms.
set (keepB := keep2 pnew fimg ++ tmp).
assert (HB2' : Permutation (blocks L2 A2) (keepB ++ tree_blocks t)) by (eapply Permutation_trans; [exact HB2|]; subst keepA keepB; rewrite <- !app_assoc; apply Permutation_refl).
assert (HBt : Permutation (blocks L2 A2) (tree_blocks t ++ keepB)) by (eapply Permutation_trans; [exact HB2' | apply Permutation_app_comm]).
assert (HsubB : forall x0, In x0 (BASE r g N img fmt rest s bef beffmt) -> In x0 keepB) by (intros x0 Hx0'; subst keepB; apply in_app_iff; left; apply Hsub; exact Hx0').
pose proof (proj1 HJ2) as HH2.
set (E1 := Ereg regs2 []).
assert (HE1 : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E1 n = getr regs2 rr) by (intros; subst E1; apply ew_Ereg_nat; assumption).
assert (HU2' : bv_unsigned (ew E1 2) = sp regs0) by (rewrite (HE1 2%nat 2%bv eq_refl), (R2 2%bv ltac:(cbv; tauto)), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HS : st_ok (fx:=fxi) src2segs E1 ss_QE1 (mkst (fx:=fxi) regs2 (Z_to_bv 64 0x14468) mem2 (seg_rom src2segs))).
{ unfold ss_QE1. subst E1. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2'.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change mem2 with (ms_mem (mkst (fx:=fxi) regs2 (Z_to_bv 64 0x14468) mem2 (seg_rom src2segs))) in HJ2.
jrun_to LAWS src2tbl_ok HS HJ2 src2_A_free_decision_tree. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Hmm1 : ms_mem ms = mem2) by (apply functional_extensionality; intros x0; apply (frame_of_nil _ _ _ _ HF)).
jreg HS (10%bv:reg) as Hr10. rewrite (HE1 27%nat 27%bv eq_refl), (R2 27%bv ltac:(cbv; tauto)), G27 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE1 2%nat 2%bv eq_refl), (R2 2%bv ltac:(cbv; tauto)), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE1 4%nat 4%bv eq_refl), (R2 4%bv ltac:(cbv; tauto)), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
assert (Hspms : spZ (ms_regs ms) = sp regs0) by (unfold spZ; rewrite Hr2; apply unsigned_lit_small; unfold sp, sp0, RGBA_FRAME in *; lia).
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := FREETREE_STK) (FP1 := blocks_fp (tree_blocks t))
(K := fun L5 A5 (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) => Permutation (blocks L5 A5) keepB);
[ exact HS | reflexivity | exact HJ2 | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspms; exact Hsp16 | lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia | exact Hr4 | ].
- intros HPRE1. rewrite Hmm1 in HPRE1 |- *. eapply SR_mono.
{ eapply (FTREE fxi L2 A2 (ms_regs ms) mem2 md2 t keepB HPRE1 Hr10); [| exact Hth | exact HBt].
eapply tree_at_frame; [exact Htree|]. intros n0 a Hn0 Ha. replace a with (tn_addr n0 + (a - tn_addr n0)) by lia. apply (HkeepA (tn_addr n0) NODE_SIZE (a - tn_addr n0)); [| lia].
subst keepA. apply in_app_iff. right. apply in_app_iff. right. rewrite tree_blocks_nodes. apply in_map_iff. exists n0. split; [reflexivity | exact Hn0]. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & HB5).
exists L5, A5, regs5, mem5, md5. split; [rewrite Hr1; reflexivity|]. split; [exact HJc5|]. split; [exact HP5 | exact HB5].
- intros a Ha. right. apply inFP_blocks_fp in Ha as (b & n & Hbn & Hab). exists b, n.
destruct (tmp_of_station API L A r g bef beffmt s N img fmt rest L2 A2 mem2 md2 keepB (tree_blocks t) b n HH2 HB2' HBent HsubB Hbn ltac:(lia)) as [H1 H2].
split; [exact H1|]. split; [exact H2 | lia]. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HB5). clear HJ2.
cbn [ms_regs ms_mem mkst] in HJc5, HP5, HJ5.
pose proof HJc5 as (HH5 & _ & Hhi5 & _).
assert (HI5 : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte src2segs mem5 x0 = mbyte src2segs mem2 x0).
{ intros x0 Hx Hsx. rewrite <- Hmm1. apply (proj1 (Hhi5 x0 Hx ltac:(rewrite Hspms; lia))). }
assert (HkeepB : forall b m i, In (b, m) keepB -> 0 <= i < m -> mbyte src2segs mem5 (b + i) = mbyte src2segs mem2 (b + i)).
{ rewrite <- Hmm1. eapply (kept_across_call API FREETREE_STK (spZ (ms_regs ms)) L2 A2 (ms_mem ms) md2 L5 A5 mem5 md5 keepB (tree_blocks t));
[rewrite Hmm1; exact HH2 | exact HB2' | exact HJc5 | exact HB5]. }
assert (R5 : forall rr : reg, In rr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs5 rr = getr regs1 rr).
{ intros rr Hrr. rewrite (regs_preserved_in _ _ rr HP5) by (exact (in_subq [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv CALLEE_SAVED ltac:(vm_compute; reflexivity) rr Hrr)).
rewrite (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity) rr Hrr).
apply R2. exact Hrr. }
clear HS HF HG Hr10 Hr2 Hr4 Hr1 Hspms Hhi5 HJc5 HP5 Hmm1 ms.
assert (HI25 : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte src2segs mem5 x0 = mbyte src2segs memc x0).
{ intros x0 Hx Hsx. rewrite (HI5 x0 Hx Hsx). apply HI2; [exact Hx | exact Hsx]. }
assert (HkeepAB : forall b m i, In (b, m) keepB -> 0 <= i < m -> mbyte src2segs mem5 (b + i) = mbyte src2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite (HkeepB b m i Hbm Hi). apply (HkeepA b m i); [| exact Hi]. subst keepA keepB. apply in_app_iff in Hbm as [Hbm|Hbm]; apply in_app_iff; [left; exact Hbm | right; apply in_app_iff; left; exact Hbm]. }
pose proof HJ5 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw5) & _).
assert (Hcin5 : In (c, CHT_SIZE) (blocks L5 A5)) by (eapply Permutation_in; [apply Permutation_sym; exact HB5 | subst keepB; apply in_app_iff; right; left; reflexivity]).
destruct (heap_blocks_range src2_msyms MR LAWS L5 A5 mem5 md5 c CHT_SIZE HH5 Hcin5 ltac:(lia)) as (Hc0 & Hc1 & Hc16).
assert (Hcht5 : obj_at src2segs mem5 c LAY_Cht [f; h; u; p; x; cnt; T]).
{ eapply (obj_at_transport_range src2segs _ _ _ _ _ CHT_SIZE); [exact Hcht | reflexivity |]. intros i Hi. apply (HkeepAB c CHT_SIZE i); [subst keepB; apply in_app_iff; right; left; reflexivity | exact Hi]. }
set (E2 := Ereg regs5 []).
assert (HE2 : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E2 n = getr regs5 rr) by (intros; subst E2; apply ew_Ereg_nat; assumption).
assert (HU2c : bv_unsigned (ew E2 2) = sp regs0) by (rewrite (HE2 2%nat 2%bv eq_refl), (R5 2%bv ltac:(cbv; tauto)), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HU33 : bv_unsigned (ew E2 20) = c) by (rewrite (HE2 20%nat 20%bv eq_refl), (R5 20%bv ltac:(cbv; tauto)), G20; apply unsigned_lit_small; lia).
assert (HS : st_ok (fx:=fxi) src2segs E2 ss_QE2 (mkst (fx:=fxi) regs5 (Z_to_bv 64 0x14470) mem5 (seg_rom src2segs))).
{ unfold ss_QE2. subst E2. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU33.
split; [lia|]. split; [lia|]. split; [| apply Forall_nil].
intros o Ho. apply (present_writable src2_msyms). apply (proj1 (heap_blocks src2_msyms MR LAWS L5 A5 mem5 md5 c CHT_SIZE o HH5 Hcin5 ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint]. repeat split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2c, HU33.
change (2 ^ 4) with 16. change (2 ^ 3) with 8.
assert (c mod 8 = 0) by (pose proof (Z.div_mod c 16 ltac:(lia)) as Hdm; rewrite Hc16 in Hdm; rewrite Hdm; replace (16 * (c / 16) + 0) with ((2 * (c / 16)) * 8) by lia; apply Z.mod_mul; lia).
unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change mem5 with (ms_mem (mkst (fx:=fxi) regs5 (Z_to_bv 64 0x14470) mem5 (seg_rom src2segs))) in HJ5.
assert (Hctmp : ~ In (c, CHT_SIZE) (blocks L A)).
{ exact (proj2 (tmp_of_station API L A r g bef beffmt s N img fmt rest L5 A5 mem5 md5 (keep2 pnew fimg) tmp c CHT_SIZE HH5 ltac:(subst keepB; exact HB5) HBent Hsub ltac:(left; reflexivity) ltac:(lia))). }
jrun_to LAWS src2tbl_ok HS HJ5 src2_A_free_col_hash_table.
{ apply wr_ok_eval || idtac.
lazymatch goal with |- wr_ok ?Ee ?rs ?stk ?spp ?fp ?b0 ?bc => let rs' := eval vm_compute in rs in change (wr_ok Ee rs' stk spp fp b0 bc) end.
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 20); [reflexivity | exact HU33 | cbn [r_wlo r_whi]; intros x1 Hx1; right; right; exists c, CHT_SIZE; split; [exact Hcin5 | split; [exact Hctmp | lia]] | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ5.
lazymatch type of HS with st_ok _ _ ?ssf _ =>
pose proof (st_chunk_val src2segs E2 ssf ms 0%nat _ 20%nat 40 4%N (SLit 255) c 255 HS eq_refl eq_refl ltac:(cbn; tauto) HU33 eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Mcnt
end.
change (N.to_nat 4) with 4%nat in Mcnt.
assert (FR3 : forall x0, 0 <= x0 < 2 ^ 64 -> ~ (c + 40 <= x0 < c + 44) -> mbyte src2segs (ms_mem ms) x0 = mbyte src2segs mem5 x0).
{ intros x0 Hx0q Hn. mb_frame_g HF ltac:(exact Hx0q) ltac:(rewrite ?HU2c, ?HU33; lia). reflexivity. }
assert (Hcht6 : obj_at src2segs (ms_mem ms) c LAY_Cht [f; h; u; p; x; 255; T]).
{ eapply (obj_at_upd src2segs mem5 (ms_mem ms) c LAY_Cht CHT_SIZE _ _ [5%nat] [(40, 44)] Hcht5 lay_inside_Cht eq_refl); [reflexivity | | |].
- intros i0 Hi0 Hw. apply in_wins_cons_false in Hw as [Hw _]. apply FR3; lia.
- intros j fd v' Hj Hf Hv'. destruct Hj as [<-|[]]. cbn in Hf, Hv'. injection Hf as <-. injection Hv' as <-. split; [exact Mcnt | cbn; lia].
- intros j Hj. do 5 (destruct j as [|j]; [reflexivity|]). destruct j as [|j]; [exfalso; apply Hj; left; reflexivity | reflexivity]. }
jreg HS (10%bv:reg) as Hr10. rewrite (HE2 20%nat 20%bv eq_refl), (R5 20%bv ltac:(cbv; tauto)), G20 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE2 2%nat 2%bv eq_refl), (R5 2%bv ltac:(cbv; tauto)), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE2 4%nat 4%bv eq_refl), (R5 4%bv ltac:(cbv; tauto)), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
assert (Hspms : spZ (ms_regs ms) = sp regs0) by (unfold spZ; rewrite Hr2; apply unsigned_lit_small; unfold sp, sp0, RGBA_FRAME in *; lia).
pose proof (proj1 HJ5) as HH6.
assert (HB6t : Permutation (blocks L5 A5) (keep2 pnew fimg ++ tmp)) by (subst keepB; exact HB5).
assert (HBc : Permutation (blocks L5 A5) ((c, CHT_SIZE) :: optb f (4 * T) ++ optb h (3 * T) ++ optb u T ++ optb p (3 * T) ++ optb x (4 * T) ++ keep2 pnew fimg)).
{ rewrite (optb_nz f _ Hf0), (optb_nz h _ Hh0), (optb_nz u _ Hu0), (optb_nz p _ Hp0), (optb_nz x _ Hx0).
eapply Permutation_trans; [exact HB6t|]. apply Permutation_app_comm. }
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := FREECHT_STK)
(FP1 := (c, c + CHT_SIZE) :: optfp f (4 * T) ++ optfp h (3 * T) ++ optfp u T ++ optfp p (3 * T) ++ optfp x (4 * T))
(K := fun L7 A7 (regs7 : bvmap 5 word) (mem7 : word -> option byte) (md7 : Model) => Permutation (blocks L7 A7) (keep2 pnew fimg));
[ exact HS | reflexivity | exact HJ5 | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspms; exact Hsp16 | lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia | exact Hr4 | ].
- intros HPRE1. eapply SR_mono.
{ eapply (FCHT fxi L5 A5 (ms_regs ms) (ms_mem ms) md5 c f h u p x 255 T (4 * T) (3 * T) T (3 * T) (4 * T) (keep2 pnew fimg) HPRE1 Hr10 Hcht6 HBc). }
cbv beta. intros c' (L7 & A7 & regs7 & mem7 & md7 & -> & HJc7 & HP7 & HB7).
exists L7, A7, regs7, mem7, md7. split; [rewrite Hr1; reflexivity|]. split; [exact HJc7|]. split; [exact HP7 | exact HB7].
- intros a Ha. right.
assert (Ha' : inFP (blocks_fp tmp) a).
{ subst tmp. cbn [cht_blks cht_blocks ch_c ch_f ch_h ch_u ch_p ch_x ch_T blocks_fp map fst snd].
unfold optfp in Ha. rewrite (proj2 (Z.eqb_neq f 0) Hf0), (proj2 (Z.eqb_neq h 0) Hh0), (proj2 (Z.eqb_neq u 0) Hu0), (proj2 (Z.eqb_neq p 0) Hp0), (proj2 (Z.eqb_neq x 0) Hx0) in Ha.
cbn [app] in Ha. exact Ha. }
apply inFP_blocks_fp in Ha' as (b & n & Hbn & Hab). exists b, n.
destruct (tmp_of_station API L A r g bef beffmt s N img fmt rest L5 A5 (ms_mem ms) md5 (keep2 pnew fimg) tmp b n HH6 HB6t HBent Hsub Hbn ltac:(lia)) as [H1 H2].
split; [exact H1|]. split; [exact H2 | lia]. }
cbv beta. intros c' (L7 & A7 & regs7 & mem7 & md7 & -> & HJ7 & HJc7 & HP7 & HB7). clear HJ5.
cbn [ms_regs ms_mem mkst] in HJc7, HP7, HJ7.
pose proof HJc7 as (HH7 & _ & Hhi7 & _).
assert (HI7 : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte src2segs mem7 x0 = mbyte src2segs memc x0).
{ intros x0 Hx Hsx. rewrite <- (HI25 x0 Hx Hsx), <- (FR3 x0 ltac:(lia) ltac:(lia)). apply (proj1 (Hhi7 x0 Hx ltac:(rewrite Hspms; lia))). }
assert (Hkeep7 : forall b m i, In (b, m) (keep2 pnew fimg) -> 0 <= i < m -> mbyte src2segs mem7 (b + i) = mbyte src2segs memc (b + i)).
{ assert (HJc7' : journal src2_msyms MR FREECHT_STK (spZ (ms_regs ms)) (blocks_fp tmp) L5 A5 (ms_mem ms) md5 L7 A7 mem7 md7).
{ subst tmp. cbn [cht_blks cht_blocks ch_c ch_f ch_h ch_u ch_p ch_x ch_T blocks_fp map fst snd].
pose proof HJc7 as HJc7'. unfold optfp in HJc7'. rewrite (proj2 (Z.eqb_neq f 0) Hf0), (proj2 (Z.eqb_neq h 0) Hh0), (proj2 (Z.eqb_neq u 0) Hu0), (proj2 (Z.eqb_neq p 0) Hp0), (proj2 (Z.eqb_neq x 0) Hx0) in HJc7'.
cbn [app] in HJc7'. exact HJc7'. }
intros b m i Hbm Hi. destruct (heap_blocks src2_msyms MR LAWS L5 A5 mem5 md5 b m i HH5 ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB6t | apply in_app_iff; left; exact Hbm]) Hi) as (_ & B0 & B1 & _).
transitivity (mbyte src2segs (ms_mem ms) (b + i)).
- exact (kept_across_call API FREECHT_STK (spZ (ms_regs ms)) L5 A5 (ms_mem ms) md5 L7 A7 mem7 md7 (keep2 pnew fimg) tmp HH6 HB6t HJc7' HB7 b m i Hbm Hi).
- rewrite (FR3 (b + i) ltac:(lia)).
+ apply (HkeepAB b m i); [subst keepB; apply in_app_iff; left; exact Hbm | exact Hi].
+ pose proof (heap_sep_app' API L5 A5 mem5 md5 (keep2 pnew fimg) tmp (b, m) (c, CHT_SIZE) HH5 HB6t Hbm ltac:(subst tmp; left; reflexivity)) as Hsep. cbn [fst snd] in Hsep. lia. }
assert (R7 : forall rr : reg, In rr [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs7 rr = getr regs1 rr).
{ intros rr Hrr. rewrite (regs_preserved_in _ _ rr HP7) by (exact (in_subq [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv CALLEE_SAVED ltac:(vm_compute; reflexivity) rr Hrr)).
rewrite (regs_kept_of_st_ok _ _ _ _ regs5 _ [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity) rr Hrr).
apply (keep_subq [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv _ _ ltac:(vm_compute; reflexivity) R5 rr Hrr). }
assert (G9' : getr regs7 9 = Z_to_bv 64 255).
{ rewrite (regs_preserved_in _ _ 9%bv HP7 ltac:(cbv; tauto)). jreg HS (9%bv:reg) as Hq9. exact Hq9. }
clear HS HF HG Hr10 Hr2 Hr4 Hr1.
pose proof HJ7 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw7) & _).
assert (HB7' : Permutation (blocks L7 A7) (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)])) by exact HB7.
change (Z_to_bv 64 83072) with (Z_to_bv 64 PC_FIN).
apply (KFIN fxi regs7 L7 A7 mem7 md7 ha pnew fimg 255 HFRM).
unfold at_FIN. unfold hold in Hfmt, Hha, Hbef, Hpnew, Hfimg.
split.
{ split; [exact HJ7|]. split; [exact (init_of_live_r API r g bef beffmt s N img fmt rest L7 A7 mem7 md7 _ (proj1 HJ7) HB7')|].
split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc mem7 (sp regs0)); [exact HRA | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp0 in *; lia | unfold sp0 in *; lia | exact HI7]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply HI7; unfold sp, sp0, RGBA_FRAME in *; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split; [split; [rewrite (R7 2%bv ltac:(cbv; tauto)); exact G2 | split; [rewrite (R7 3%bv ltac:(cbv; tauto)); exact G3 | rewrite (R7 4%bv ltac:(cbv; tauto)); exact G4]]|].
split; [exact Hfmt|]. split; [exact HN1|]. split; [exact Hha|]. split; [lia|].
split; [exact G9'|]. split; [rewrite (R7 8%bv ltac:(cbv; tauto)); exact G8|]. split; [rewrite (R7 24%bv ltac:(cbv; tauto)); exact G24|].
split. { eapply slots_mid_kept; [exact Hsl | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | exact HI7]. }
split. { eapply slot_kept; [exact Q88 | unfold SL_88; lia | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, SL_88, RGBA_FRAME in *; lia | exact HI7]. }
split. { unfold fcfg_at in *. eapply (obj_at_transport_range src2segs _ _ _ _ _ 32); [exact Hfc | reflexivity |]. intros i Hi. unfold OFF_fcfg in *. apply HI7; unfold sp, sp0, RGBA_FRAME in *; lia. }
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |].
intros i Hi. apply (Hkeep7 r RGB_SIZE i); [apply Hsub; left; reflexivity | exact Hi]. }
split. { eapply (cgif_at_kept _ _ g s N (keep2 pnew fimg)); [| exact Hcg | exact Hkeep7].
unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
split. { intros i Hi. unfold OFF_apal. apply (writable_present_high src2segs 140735332483072 mem7 _ src2_segs_below); [pose proof (proj1 YN05.alloc_ceiling_val); unfold sp, sp0, RGBA_FRAME in *; lia|].
apply Hstw7. unfold sp, sp0, RGBA_FRAME in *. lia. }
split; [exact Hpnew|]. split; [exact Hfimg|]. exact HB7'.
Qed.
End w.
Lemma src2_rgbadd_QE : seg_QE API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof. intros KFIN fx1 regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt HFRM HAT. exact (QE_at regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt KFIN HFRM HAT). Qed.
End e.
End d.
