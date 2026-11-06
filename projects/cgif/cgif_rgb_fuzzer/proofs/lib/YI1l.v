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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YO3l YI00 YI02 YI01 YI03
YI1e YI1c YI39 YI1i YI59 YI56 YI0x YI57
YI1h YI16 YI1z YI1k YI22 YI1j.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma list_neq_nth : forall (l r : list byte), length l = length r -> l <> r -> exists k, (k < length l)%nat /\ nth_error l k <> nth_error r k.
Proof.
induction l as [|a l IH]; intros [|b r] Hlen Hne; cbn in Hlen; try discriminate.
- exfalso. apply Hne. reflexivity.
- destruct (base.decide (a = b)) as [->|Hab].
+ destruct (IH r ltac:(lia) ltac:(intros ->; apply Hne; reflexivity)) as (k & Hk & Hnk). exists (S k). cbn. split; [lia | exact Hnk].
+ exists 0%nat. cbn. split; [lia|]. intros Heq. injection Heq as ->. apply Hab. reflexivity.
Qed.
Definition DIFb (mem0 : word -> option byte) (fimg bimg p : Z) : Prop := byte_at mem0 (fimg + p) <> byte_at mem0 (bimg + p).
Definition ss_f1l : sstate :=
mkSS FL_F1L sr_atoms [ YQ0b.mkRegion (Some 2%nat) 96 104 96 96 [mkChunk 96 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (27%nat, mkAF 1 65535 0); (32%nat, mkAF 1 65535 0); (26%nat, mkAF 0 65534 0);
(20%nat, mkAF 4096 CEIL_MAX 0); (21%nat, mkAF 4096 CEIL_MAX 0) ] [] []).
Definition F1_KEPT : list reg := [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25]%bv.
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Section d.
Variables (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis HC : dctx mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef.
Lemma memcmp_callD : forall STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (m : word -> option byte) (p retpc : Z),
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac m mdc -> KD mem0 spv m ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) -> 0 <= p -> p + W <= N ->
getr regs 10 = Z_to_bv 64 (fimg + p) -> getr regs 11 = Z_to_bv 64 (bimg + p) -> getr regs 12 = Z_to_bv 64 W ->
v_jalr (getr regs 1) 0 = Z_to_bv 64 retpc ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 src2_A_memcmp) m (seg_rom src2segs)) mdc)
(fun c' => exists regs2 r, c' = mkCfg (mkst regs2 (Z_to_bv 64 retpc) m (seg_rom src2segs)) mdc /\
getr regs2 10 = Z_to_bv 64 r /\ -256 < r < 256 /\
(r <> 0 -> exists k, 0 <= k < W /\ DIFb mem0 fimg bimg (p + k)) /\
(forall x : reg, reg_in x BCMP_CLOB = false -> getr regs2 x = getr regs x)).
Proof.
intros STK sp0 FP L A mem md Lc Ac mdc regs m p retpc HJ K Hfi Hbi Hp HpW G10 G11 G12 Hret.
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
destruct (rdn_of_present src2_msyms m (Z.to_nat W) (fimg + p) ltac:(intros k Hk; replace (fimg + p + k) with (fimg + (p + k)) by lia; apply (proj1 (heap_blocks _ _ LAWS Lc Ac m mdc fimg N (p + k) HHc Hfi ltac:(lia)))) ltac:(lia) ltac:(lia)) as (bl & Rbl & Lbl).
destruct (rdn_of_present src2_msyms m (Z.to_nat W) (bimg + p) ltac:(intros k Hk; replace (bimg + p + k) with (bimg + (p + k)) by lia; apply (proj1 (heap_blocks _ _ LAWS Lc Ac m mdc bimg N (p + k) HHc Hbi ltac:(lia)))) ltac:(lia) ltac:(lia)) as (br & Rbr & Lbr).
destruct (src2_memcmp bl br _ _ _ m (seg_rom src2segs) regs G10 G11 G12) as (regs2 & Hms & Hres & Hfr2);
[ rewrite unsigned_lit_small by lia; rewrite Lbl; lia | rewrite Lbr, Lbl; reflexivity
| rewrite Lbl; exact Rbl | rewrite Lbl; exact Rbr
| rewrite unsigned_lit_small, Lbl by lia; lia | rewrite unsigned_lit_small, Lbl by lia; lia | ].
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |]. rewrite Hret.
apply SR_ret. exists regs2, (memcmp_spec bl br). split; [reflexivity|]. split; [exact Hres|]. split; [apply memcmp_spec_range|]. split.
- intros Hne. assert (Hlr : bl <> br) by (intros Heq; apply Hne; apply (proj2 (memcmp_spec_zero_iff bl br ltac:(lia))); exact Heq).
destruct (list_neq_nth bl br ltac:(lia) Hlr) as (k & Hk & Hnk). exists (Z.of_nat k). split; [lia|].
pose proof (proj1 (rdn_mbytes src2segs m (Z.to_nat W) (fimg + p) bl) Rbl) as [_ Ml].
pose proof (proj1 (rdn_mbytes src2segs m (Z.to_nat W) (bimg + p) br) Rbr) as [_ Mr].
specialize (Ml k ltac:(lia)). specialize (Mr k ltac:(lia)).
unfold DIFb. rewrite <- (byte_at_KD mem0 spv m (fimg + (p + Z.of_nat k)) K) by lia. rewrite <- (byte_at_KD mem0 spv m (bimg + (p + Z.of_nat k)) K) by lia.
unfold byte_at. replace (fimg + (p + Z.of_nat k)) with (fimg + p + Z.of_nat k) by lia. replace (bimg + (p + Z.of_nat k)) with (bimg + p + Z.of_nat k) by lia.
rewrite Ml, Mr. destruct (nth_error bl k) as [x|] eqn:Hx; destruct (nth_error br k) as [y|] eqn:Hy.
+ intros Heq. apply Hnk. f_equal. apply bv_eq. exact Heq.
+ exfalso. pose proof (proj1 (nth_error_None br k) Hy). lia.
+ exfalso. pose proof (proj1 (nth_error_None bl k) Hx). lia.
+ exfalso. pose proof (proj1 (nth_error_None bl k) Hx). lia.
- intros x Hx. apply Hfr2; intros ->; vm_compute in Hx; discriminate Hx.
Qed.
Definition f1_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (c' : config) : Prop :=
exists regs' mem' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom src2segs)) mdc /\
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall z, mem' z = memc z) /\
((pc' = FL_F2 /\ exists top c0, 0 <= top < H /\ 0 <= c0 < W /\ DIFb mem0 fimg bimg (top * W + c0) /\
getr regs' 26 = Z_to_bv 64 top /\ getr regs' 27 = Z_to_bv 64 W)
\/ (pc' = FL_IDENT /\ getr regs' 27 = Z_to_bv 64 W)) /\
(forall r : reg, In r F1_KEPT -> getr regs' r = getr regs r).
Lemma fl_f1l : forall (n : nat) (i : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc,
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= i -> i + Z.of_nat n = H -> (1 <= n)%nat ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 20 = Z_to_bv 64 (fimg + i * W) -> getr regs 21 = Z_to_bv 64 (bimg + i * W) ->
getr regs 26 = Z_to_bv 64 i -> getr regs 27 = Z_to_bv 64 W ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 FL_F1L) memc (seg_rom src2segs)) mdc) (f1_post STK sp0 FP L A mem md Lc Ac mdc regs memc).
Proof.
intros n. induction n as [|n IH]; intros i STK sp0 FP L A mem md Lc Ac mdc regs memc HJ K0 Hfi Hbi Hi0 Hin Hn G2 G20 G21 G26 G27; [lia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HiW : 0 <= i * W /\ i * W + W <= N) by (rewrite HN; clear - Hi0 Hin Hn HW; nia).
destruct (dctx_objs mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC memc K0) as (_ & _ & _ & _ & _ & WHm).
set (E := Ereg regs (map (Z_to_bv 64) [H] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 H) by (subst E; apply (Ereg_vals regs [H] [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HU20 : bv_unsigned (ew E 20) = fimg + i * W) by (rewrite (HE 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; clear - HiW Hfimg0 Hfimg1 HW Hac; lia).
assert (HU21 : bv_unsigned (ew E 21) = bimg + i * W) by (rewrite (HE 21%nat 21%bv eq_refl), G21; apply unsigned_lit_small; clear - HiW Hbimg0 Hbimg1 HW Hac; lia).
assert (HR : region_ok src2segs E memc (YQ0b.mkRegion (Some 2%nat) 96 104 96 96 [mkChunk 96 (CVal 8 (SOff 32 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. eapply (chunk_ok_val _ _ _ _ _ _ _ H); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact WHm]. }
assert (HFA : atoms_ok E [ (2%nat, mkAF CEIL_MIN (2^63) 4); (27%nat, mkAF 1 65535 0); (32%nat, mkAF 1 65535 0); (26%nat, mkAF 0 65534 0);
(20%nat, mkAF 4096 CEIL_MAX 0); (21%nat, mkAF 4096 CEIL_MAX 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU20, HU21, HE32, (HE 27%nat 27%bv eq_refl), (HE 26%nat 26%bv eq_refl), G27, G26.
rewrite !unsigned_lit_small by lia. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
clear - Hsp0 Hsp1 Hsp16 HW HH Hi0 Hin Hn HiW Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hac. repeat split; lia. }
assert (HS : st_ok src2segs E ss_f1l (mkst regs (Z_to_bv 64 FL_F1L) memc (seg_rom src2segs))).
{ unfold ss_f1l. subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HR | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | exact HFA]. }
clear HR HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_F1L) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_memcmp. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ha0. rewrite (HE 20%nat 20%bv eq_refl), G20 in Ha0.
jreg HS (11%bv:reg) as Ha1. rewrite (HE 21%nat 21%bv eq_refl), G21 in Ha1.
jreg HS (12%bv:reg) as Ha2. rewrite (HE 27%nat 27%bv eq_refl), G27 in Ha2.
jreg HS (1%bv:reg) as Hra.
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc ss_f1l].
eapply SR_bind.
{ apply (memcmp_callD STK sp0 FP L A mem md Lc Ac mdc (ms_regs ms) (ms_mem ms) (i * W) FL_F1R HJ (KD_eq _ _ _ _ K0 K1) Hfi Hbi ltac:(clear - HiW; lia) ltac:(clear - HiW; lia) Ha0 Ha1 Ha2).
rewrite Hra. apply (ret_ok_even (Z_to_bv 64 FL_F1R)). vm_compute. reflexivity. }
cbv beta. intros c' (regs2 & r & -> & Hr10 & Rr & Hwit & Hfr2).
jafter_stretch_keep HS 33%nat regs2 (ms_mem ms) BCMP_CLOB FL_F1R [0%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor].
eapply (region_kept_out src2segs _ _ _ _ 0 0); [intros z _; reflexivity | apply mem_grows_of_eq; intros z; reflexivity
| cbn [r_base r_lo base_val]; ew_havocA; rewrite HU2; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite HU2; lia
| intros a Ha; clear; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
change (ms_mem ms) with (ms_mem (mkst regs2 (Z_to_bv 64 FL_F1R) (ms_mem ms) (seg_rom src2segs))) in HJ.
set (E2 := havoc E 33 (map (getr regs2) BCMP_CLOB)) in HS.
assert (EA1 : env_agree 32 E E2) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (HE2_33 : ew E2 33 = Z_to_bv 64 r).
{ subst E2. pose proof (ew_havoc_new E 33 (map (getr regs2) BCMP_CLOB) 0 (Z_to_bv 64 0) ltac:(cbn; lia)) as X.
replace (33 + 0)%nat with 33%nat in X by reflexivity. rewrite X. cbn [nth map BCMP_CLOB]. exact Hr10. }
assert (EXIT : forall ss ms' pc', st_ok src2segs E2 ss ms' -> ss_pc ss = pc' -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) F1_KEPT = true ->
((pc' = FL_F2 /\ exists top c0, 0 <= top < H /\ 0 <= c0 < W /\ DIFb mem0 fimg bimg (top * W + c0) /\
getr (ms_regs ms') 26 = Z_to_bv 64 top /\ getr (ms_regs ms') 27 = Z_to_bv 64 W)
\/ (pc' = FL_IDENT /\ getr (ms_regs ms') 27 = Z_to_bv 64 W)) ->
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall z, ms_mem ms' z = memc z) ->
f1_post STK sp0 FP L A mem md Lc Ac mdc regs memc (mkCfg ms' mdc)).
{ intros ss ms' pc' HS' Hpc Hrv Hkl Hpc' HJ' K'. exists (ms_regs ms'), (ms_mem ms'), pc'.
split; [rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact K'|]. split; [exact Hpc'|].
intros rr Hrr. subst E E2. exact (regs_kept_of_st_ok src2segs _ ss ms' regs _ F1_KEPT HS' EA1 Hkl rr Hrr). }
jbranch src2tbl HS.
-
assert (Hne : r <> 0).
{ intros Hz. rewrite branch_ne_U, U_lit, (U_atom E2 33 0) in Hc; [discriminate Hc | rewrite HE2_33, Hz; reflexivity | clear; lia | clear; lia]. }
clear Hc. destruct (Hwit Hne) as (c0 & Hc0 & Hdif).
jrun_to LAWS src2tbl_ok HS HJ FL_F2. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ FL_F2 HS eq_refl eq_refl ltac:(vm_compute; reflexivity)); [| exact HJ |].
+ left. split; [reflexivity|]. exists i, c0. split; [clear - Hi0 Hin Hn; lia|]. split; [exact Hc0|]. split; [exact Hdif|].
split; [reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 26%nat 26%bv eq_refl), G26, Z_to_bv_bv_unsigned; reflexivity)|].
reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 27%nat 27%bv eq_refl), G27, Z_to_bv_bv_unsigned; reflexivity).
+ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1.
-
clear Hc. jrun LAWS src2tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K2 : forall z, ms_mem ms0 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1. }
clear HF HG.
jbranch src2tbl HS.
+
rewrite branch_ltu_U, (U_atom_off E2 26 i 1), (U_atom E2 32 H) in Hc
by first [subst E2; ew_havocA; first [rewrite (HE 26%nat 26%bv eq_refl); exact G26 | exact HE32] | clear - Hi0 Hin Hn HH; lia].
assert (Hn1 : (1 <= n)%nat) by (destruct (Z.ltb_spec (i + 1) H) as [Hl|Hl]; [clear - Hl Hin; lia | discriminate Hc]). clear Hc.
jrun_to LAWS src2tbl_ok HS HJ FL_F1L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall z, ms_mem ms1 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs Ef ssf msf regs _ F1_KEPT HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ HJ (KD_eq _ _ _ _ K0 K3) Hfi Hbi ltac:(clear - Hi0; lia) ltac:(clear - Hin; lia) Hn1).
- rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg src2segs Ec ssc msc 20%bv HS) end. eval_sr_get. apply denot_of_U'. replace (fimg + (i + 1) * W) with (fimg + i * W + W) by (clear; lia).
apply (U_add_small E2 _ _ (fimg + i * W) W); [apply U_atom; [subst E2; ew_havocA; rewrite (HE 20%nat 20%bv eq_refl); exact G20 | clear - HiW Hfimg0 Hfimg1 HW Hac; lia]
| apply U_atom; [subst E2; ew_havocA; rewrite (HE 27%nat 27%bv eq_refl); exact G27 | clear - HW; lia] | clear - HiW Hfimg0; lia | clear - HW; lia | clear - HiW Hfimg0 Hfimg1 HW Hac; nia].
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg src2segs Ec ssc msc 21%bv HS) end. eval_sr_get. apply denot_of_U'. replace (bimg + (i + 1) * W) with (bimg + i * W + W) by (clear; lia).
apply (U_add_small E2 _ _ (bimg + i * W) W); [apply U_atom; [subst E2; ew_havocA; rewrite (HE 21%nat 21%bv eq_refl); exact G21 | clear - HiW Hbimg0 Hbimg1 HW Hac; lia]
| apply U_atom; [subst E2; ew_havocA; rewrite (HE 27%nat 27%bv eq_refl); exact G27 | clear - HW; lia] | clear - HiW Hbimg0; lia | clear - HW; lia | clear - HiW Hbimg0 Hbimg1 HW Hac; nia].
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 26%nat 26%bv eq_refl), G26, unsigned_lit_small by (clear - Hi0 Hin Hn HH; lia); reflexivity).
- rewrite (HKR 27%bv ltac:(cbv; auto 20)) || reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 27%nat 27%bv eq_refl), G27, Z_to_bv_bv_unsigned; reflexivity). all: try exact G27. }
cbv beta. intros c' (regs' & mem' & pc' & -> & HJ' & K' & Hpc' & HK'). exists regs', mem', pc'.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K3|]. split; [exact Hpc'|].
intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
+
clear Hc. jrun_to LAWS src2tbl_ok HS HJ FL_IDENT. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ FL_IDENT HS eq_refl eq_refl ltac:(vm_compute; reflexivity)); [| exact HJ |].
* right. split; [reflexivity|]. reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 27%nat 27%bv eq_refl), G27, Z_to_bv_bv_unsigned; reflexivity).
* intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2.
Qed.
End d.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
