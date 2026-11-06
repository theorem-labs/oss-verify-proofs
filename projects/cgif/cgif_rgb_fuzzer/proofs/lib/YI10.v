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
YI1e YI1d YI39 YI1i YI20 YI59 YI56 YI0x YI57
YI1h YI1g YI16 YI19 YI17 YI18 YI11
YI12 YI15 YI13 YI14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition AF_A : Z := Eval vm_compute in (src2_A_cgif_addframe + 0x48).
Definition af_entry_chunks : list YQ0b.chunk :=
[ mkChunk (-8) (CVal 8 (SOff 1 0)); mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-24) (CVal 8 (SOff 9 0)); mkChunk (-32) (CVal 8 (SOff 18 0));
mkChunk (-40) (CVal 8 (SOff 19 0)); mkChunk (-48) (CVal 8 (SOff 20 0)); mkChunk (-56) (CVal 8 (SOff 21 0)); mkChunk (-64) (CVal 8 (SOff 22 0));
mkChunk (-72) (CVal 8 (SOff 23 0)); mkChunk (-80) (CVal 8 (SOff 24 0)); mkChunk (-88) (CVal 8 (SOff 25 0)) ].
Lemma saved_word : forall E mem sp0 off n (regs : bvmap 5 word) (rr : reg),
chunk_ok src2segs E mem sp0 (mkChunk off (CVal 8 (SOff n 0))) -> ew E n = getr regs rr ->
forall a, a = sp0 + off -> word_mem src2segs mem a (bv_unsigned (getr regs rr)).
Proof.
intros E mem sp0 off n regs rr Hc He a ->. apply val_mem_word_mem.
eapply (val_of_chunk_ok src2segs E mem sp0 off 8%N (SOff n 0)); [exact Hc | | cbn; apply u64_range_getr | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, He, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma af_saved_of_chunks : forall E (regs : bvmap 5 word) mem sp0 cs,
Forall (chunk_ok src2segs E mem sp0) cs ->
(forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) ->
incl af_entry_chunks cs ->
af_saved_ok mem sp0 regs.
Proof.
intros E regs mem sp0 cs Hcs HE Hincl j r Hr.
assert (Hj : (j < 11)%nat) by (apply (proj1 (nth_error_Some AF_SAVED j)); rewrite Hr; discriminate).
assert (Hc : chunk_ok src2segs E mem sp0 (nth j af_entry_chunks (mkChunk 0 (CVal 8 (SLit 0))))).
{ apply (proj1 (Forall_forall _ _) Hcs). apply Hincl. apply nth_In. cbn. exact Hj. }
do 11 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; cbn [nth af_entry_chunks] in Hc;
eapply (saved_word E mem sp0 _ _ regs _ Hc); [apply HE; reflexivity | cbn; lia] |]).
cbn in Hj. lia.
Qed.
Lemma denot_of_U : forall E v z, U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z <-. unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Definition ss_A : sstate :=
mkSS AF_A sr_atoms [ af_Rg None None None None ; af_Rcf ] None
(mkFacts ((af_facts ++ cf_facts) ++ [(56%nat, mkAF 0 4294967295 0)]) [] []).
Definition ss_af0 : sstate :=
mkSS src2_A_cgif_addframe sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-96) 0 (-96) 0 [] ;
YQ0b.mkRegion (Some 10%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF 51 (litsG None None None None)) ] None
(mkFacts [(2%nat, mkAF (CEIL_MIN + 9728) (2 ^ 63 - 1) 4); (10%nat, mkAF 4096 (CEIL_MAX - 96) 4)] [] []).
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Hypothesis FLUSH : flush_spec API.
Ltac interp_Hc HX56 HC46 :=
match goal with Hc : branch_taken _ _ _ = _ |- _ =>
first [ rewrite branch_eq_U, U_and_lit, U_lit, (U_atom _ 56 _ HX56) in Hc by lia
| rewrite branch_ne_U, U_and_lit, U_lit, (U_atom _ 56 _ HX56) in Hc by lia
| rewrite branch_eq_U, U_and_lit, U_lit, (U_atom _ 46 _ HC46) in Hc by lia
| rewrite branch_ne_U, U_and_lit, U_lit, (U_atom _ 46 _ HC46) in Hc by lia
| idtac ];
first [ apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc
| apply Bool.negb_true_iff in Hc; apply Z.eqb_neq in Hc
| apply Bool.negb_false_iff in Hc; apply Z.eqb_eq in Hc
| clear Hc ];
try (let H := fresh "HC" in rename Hc into H)
end.
Ltac get_HS := match goal with H : st_ok _ _ _ _ |- _ => H end.
Ltac get_HJ := match goal with H : journal _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => H end.
Ltac get_HF := match goal with H : frame_of _ _ _ _ |- _ => H end.
Ltac clear_HG := repeat match goal with H : mem_grows _ _ |- _ => clear H end.
Ltac runA stop RO :=
let HS := get_HS in let HJ := get_HJ in
jrun_to LAWS src2tbl_ok HS HJ stop; [apply RO |];
let HF := get_HF in
cbn [ms_mem mkst] in HF; clear_HG;
lazymatch goal with K : forall a, mbyte src2segs ?m a = mbyte src2segs ?mc a |- _ =>
lazymatch type of HF with frame_of ?E1 ?rs m ?m2 =>
let K2 := fresh "K" in
assert (K2 : forall a, mbyte src2segs m2 a = mbyte src2segs mc a)
by (intros a; try rewrite <- (K a); unfold mbyte; rewrite (frame_of_ro E1 rs m m2 ltac:(vm_compute; reflexivity) HF); reflexivity);
clear HF K
end
end.
Ltac af_tree RUN LEAF INTERP n :=
lazymatch n with
| O => fail "af_tree: out of depth"
| Datatypes.S ?m => RUN; first [ LEAF | let HS := get_HS in jbranch src2tbl HS; [ INTERP; af_tree RUN LEAF INTERP m | INTERP; af_tree RUN LEAF INTERP m ] ]
end.
Lemma af_A :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (rest FP : list (Z * Z))
(cfp lpal lpa img fattr fgen delay nlp tidx : Z),
let sp0 := spZ regs0 in
let CB := [(img, N)] in
journal src2_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 -> getr regs0 4 = Z_to_bv 64 (ms_tp src2_msyms) ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
obj_at src2segs memc cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
cfp mod 8 = 0 -> sp0 <= cfp -> cfp + 32 <= 2 ^ 63 ->
pal_ok mem sp0 fattr lpal nlp ->
(forall b n a, In (b, n) (cgif_blocks g s N) -> b <= a < b + n -> inFP FP a) ->
Permutation (blocks Lc Ac) (cgif_blocks g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 96) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 cfp ->
af_untouched regs0 regs1 ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_A) memc (seg_rom src2segs)) mdc) (af_post API regs0 g N s0 CB rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP cfp lpal lpa img fattr fgen delay nlp tidx sp0 CB
HJ Hid Hra0 Hal16 Htp0 Hat Hwf Hgeom Hcf Hcf8 Hcflo Hcfhi Hlpa HFP HB HSV G2 G8 G9 HUT.
pose proof HUT as (G3 & G4 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
destruct (af_cgif_geom API Lc Ac memc mdc g s N _ HH0 HB) as (_ & _ & (Hg0 & Hg1 & Hg16)).
pose proof Hat as (Hobj & Hraw & Hfrs).
pose proof (obj_at_range _ _ _ _ _ Hcf) as Rcf. pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
pose proof (Rcf 2%nat fattr eq_refl) as Rfattr. cbn [nth snd LAY_FrameConfig Z.of_N] in Rfattr.
pose proof (Rg 5%nat (cg_attr s) eq_refl) as Rattr. cbn [nth snd LAY_CGIF Z.of_N] in Rattr.
set (E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s []).
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HK regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (af_HC regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HC.
pose proof (af_HX regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HX.
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 96) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = cfp) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
pose proof (HX 56%nat 5%nat (cg_attr s) eq_refl eq_refl) as HX56.
pose proof (HC 46%nat 2%nat fattr eq_refl eq_refl) as HC46.
assert (GO_B : forall ss ms', st_ok src2segs E ss ms' -> ss_pc ss = AF_B -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 -> sr_get (ss_regs ss) 10%bv = SOff 46 0 ->
sr_get (ss_regs ss) 20%bv = SAlu ALU_AND (SOff 46 0) (SLit 4) -> sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
journal src2_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, mbyte src2segs (ms_mem ms') a = mbyte src2segs memc a) ->
(Z.land fattr 1 = 0 -> Z.land (cg_attr s) 4 = 0) ->
SR src2segs (mkCfg ms' mdc) (af_post API regs0 g N s0 CB rest FP L A mem md)).
{ intros ss ms' HS' Hpc Hrv Q2 Q3 Q4 Q8 Q9 Q10 Q23 Q26 Q27 HJ' K HnoCT. rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hw. rewrite (st_ok_reg src2segs E ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hw. }
eapply (af_B API IMG FLUSH L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s0 s rest FP cfp lpal lpa img fattr fgen delay nlp tidx);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hgeom | exact HnoCT
| eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply K] | exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact HFP | exact HB
| apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply K]
| apply (RG _ _ _ Q2); rewrite (HE 2%nat 2%bv eq_refl); exact G2
| apply (RG _ _ _ Q8); rewrite (HE 8%nat 8%bv eq_refl); exact G8
| apply (RG _ _ _ Q9); rewrite (HE 9%nat 9%bv eq_refl); exact G9
| apply (RG _ _ _ Q10); exact HC46
| rewrite (st_ok_reg src2segs E ss ms' 20%bv HS'), Q23; apply denot_of_U; rewrite U_and_lit, (U_atom _ 46 fattr HC46) by lia; reflexivity
| split; [|split; [|split]]; [ apply (RG _ _ _ Q3); rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG _ _ _ Q4); rewrite (HE 4%nat 4%bv eq_refl); exact G4
| apply (RG _ _ _ Q26); rewrite (HE 26%nat 26%bv eq_refl); exact G26
| apply (RG _ _ _ Q27); rewrite (HE 27%nat 27%bv eq_refl); exact G27 ] ].
eapply (cgif_at_kept memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply K]. }
assert (GO_RC : forall ss ms', st_ok src2segs E ss ms' -> ss_pc ss = AF_RETC -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
journal src2_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, mbyte src2segs (ms_mem ms') a = mbyte src2segs memc a) ->
SR src2segs (mkCfg ms' mdc) (af_post API regs0 g N s0 CB rest FP L A mem md)).
{ intros ss ms' HS' Hpc Hrv Q2 Q3 Q4 Q8 Q26 Q27 HJ' K. rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hw. rewrite (st_ok_reg src2segs E ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hw. }
eapply (af_ret_cur API IMG L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s0 s CB rest FP);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16
| intros a Ha; apply (HFP g CGIF_SIZE a); [left; reflexivity | exact Ha]
| | exact Hwf | exact Hgeom | exact HB
| apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply K]
| apply (RG _ _ _ Q2); rewrite (HE 2%nat 2%bv eq_refl); exact G2
| apply (RG _ _ _ Q8); rewrite (HE 8%nat 8%bv eq_refl); exact G8
| split; [|split; [|split]]; [ apply (RG _ _ _ Q3); rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG _ _ _ Q4); rewrite (HE 4%nat 4%bv eq_refl); exact G4
| apply (RG _ _ _ Q26); rewrite (HE 26%nat 26%bv eq_refl); exact G26
| apply (RG _ _ _ Q27); rewrite (HE 27%nat 27%bv eq_refl); exact G27 ] ].
eapply (cgif_at_kept memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply K]. }
assert (HR1 : region_ok src2segs E memc (af_Rg None None None None)).
{ apply (af_Rg_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s [] memc g); [exact HU8 | lia | lia | exact Hobj | exact I | exact I | exact I | exact I]. }
pose proof (af_Rcf_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s [] memc cfp HU9 ltac:(lia) ltac:(lia) Hcf) as HR2.
assert (HPD : pairwise_disjoint E (ss_mem ss_A)).
{ cbn [ss_mem ss_A]. unfold af_Rg, af_Rcf. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU8, HU9. clear - Hg1 Hceil Hcflo HASv HGSv Hac. repeat split; lia. }
assert (HFA : atoms_ok E ((af_facts ++ cf_facts) ++ [(56%nat, mkAF 0 4294967295 0)])).
{ apply atoms_ok_app; [apply atoms_ok_app; [| exact (cf_facts_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s [] memc cfp Hcf)]|].
- cbn [atoms_ok af_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, HU9.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia.
replace (sp0 - 96) with (sp0 + (-6) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HX56, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
assert (HS : st_ok src2segs E ss_A (mkst regs1 (Z_to_bv 64 AF_A) memc (seg_rom src2segs))).
{ unfold ss_A. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | exact HPD | split; [exact HFA | split; exact I]].
constructor; [exact HR1|]. constructor; [exact HR2|]. constructor. }
clear HR1 HR2 HPD HFA.
assert (RO : wr_ok E [af_Rg None None None None; af_Rcf] ADDFRAME_STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (K0 : forall a, mbyte src2segs memc a = mbyte src2segs memc a) by (intros a; reflexivity).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_A) memc (seg_rom src2segs))) in HJ.
clear Rcf Rg.
af_tree ltac:(idtac; runA AF_B RO)
ltac:(idtac; lazymatch goal with K : forall a, mbyte src2segs _ a = mbyte src2segs memc a |- _ =>
first [ apply (GO_B _ _ HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ K);
first [ intros _; assumption
| intros HF1; exfalso; match goal with H : Z.land fattr 1 <> 0 |- _ => exact (H HF1) end ]
| exact (GO_RC _ _ HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ K) ]
end)
ltac:(idtac; interp_Hc HX56 HC46)
constr:(8%nat).
Qed.
Ltac runE stop WR HU2 sp0 :=
let HS := get_HS in let HJ := get_HJ in
jrun_to LAWS src2tbl_ok HS HJ stop; [apply WR; [exact HU2 | cbn; lia] |];
let HF := get_HF in
cbn [ms_mem mkst] in HF; clear_HG;
lazymatch goal with K : forall a, _ -> _ -> mbyte src2segs ?m a = mbyte src2segs ?m0 a |- _ =>
lazymatch type of HF with frame_of ?E1 ?rs m ?m2 =>
let K2 := fresh "K" in
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 96 <= a < sp0) -> mbyte src2segs m2 a = mbyte src2segs m0 a);
[ intros a Ha Hna; try rewrite <- (K a Ha Hna);
apply (mbyte_of_frame E1 rs m m2 a HF Ha);
intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; rewrite ?HU2; lia |]); destruct Hr
| clear HF K ]
end
end.
Theorem src2_cgif_addframeG : addframe_specG API.
Proof.
intros L A regs mem md g cfp s N lpal img fattr fgen delay nlp tidx rest HPRE Hid G10 G11 Hcf8 Hcflo Hcfhi Hcf Hat Hwf Hlpa HB. pose (lpa := lpal).
pose proof HPRE as (HH & Hra0 & Hst & Htp0 & Herr). destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
set (sp0 := spZ regs) in *.
change ((img, N) :: rest) with ([(img, N)] ++ rest) in HB |- *. set (CB := [(img, N)]) in *.
set (FP := blocks_fp (cgif_blocks g s N)).
assert (HFPin : forall b n a, In (b, n) (cgif_blocks g s N) -> b <= a < b + n -> inFP FP a) by (intros b n a Hbn Ha; apply (cgif_fp_in g s N b n a Hbn Ha)).
destruct (af_cgif_geom API L A mem md g s N (CB ++ rest) HH HB) as (_ & _ & (Hg0 & Hg1 & Hg16)).
pose proof Hat as (Hobj & Hraw & Hfrs).
set (E := af_E regs regs [lpal; img; fattr; fgen; delay; nlp; tidx] s []).
pose proof (af_HE regs regs lpal img fattr fgen delay nlp tidx s [] : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HX regs regs lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HX.
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = g) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (GO : forall ss ms' rg0, st_ok src2segs E ss ms' -> (ss_pc ss = AF_A \/ ss_pc ss = AF_RET) -> ss_resv ss = None ->
nth_error (ss_mem ss) 0 = Some rg0 -> r_base rg0 = Some 2%nat -> incl_chunks af_entry_chunks (r_chunks rg0) = true ->
sr_get (ss_regs ss) 2%bv = SOff 2 (-96) -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 10 0 -> sr_get (ss_regs ss) 9%bv = SOff 11 0 -> sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
journal src2_msyms MR ADDFRAME_STK sp0 FP L A mem md L A (ms_mem ms') md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 96 <= a < sp0) -> mbyte src2segs (ms_mem ms') a = mbyte src2segs mem a) ->
SR src2segs (mkCfg ms' md) (af_post API regs g N s CB rest FP L A mem md)).
{ intros ss ms' rg0 HS' Hpc Hrv Hrg0 Hb0 Hincl Q2 Q3 Q4 Q8 Q9 Q26 Q27 HJ' K. rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv).
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hw. rewrite (st_ok_reg src2segs E ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hw. }
assert (Q2' : getr (ms_regs ms') 2 = Z_to_bv 64 (sp0 - 96)).
{ rewrite (st_ok_reg src2segs E ss ms' 2%bv HS'), Q2. cbn [sv_denot]. rewrite HU2. f_equal; lia. }
assert (HUT : af_untouched regs (ms_regs ms')).
{ split; [|split; [|split]]; [ apply (RG _ _ _ Q3); apply (HE 3%nat 3%bv eq_refl) | apply (RG _ _ _ Q4); apply (HE 4%nat 4%bv eq_refl)
| apply (RG _ _ _ Q26); apply (HE 26%nat 26%bv eq_refl) | apply (RG _ _ _ Q27); apply (HE 27%nat 27%bv eq_refl) ]. }
assert (HSV : af_saved_ok (ms_mem ms') sp0 regs).
{ eapply (af_saved_of_chunks E regs (ms_mem ms') sp0 (r_chunks rg0)); [| exact HE | apply incl_chunks_sound; exact Hincl].
eapply (st_region_chunks src2segs E ss ms' 0 rg0 2%nat sp0 HS' Hrg0 Hb0 HU2). }
assert (KB : forall b n i, In (b, n) (blocks L A) -> 0 <= i < n -> mbyte src2segs (ms_mem ms') (b + i) = mbyte src2segs mem (b + i)).
{ intros b n i Hbn Hi. destruct (blocks_range _ _ LAWS L A mem md b n HH Hbn) as [B0 B1]. apply K; lia. }
assert (Hat' : cgif_at (ms_mem ms') g s) by (eapply (cgif_at_kept mem _ g s N (blocks L A)); [exact HB | exact Hat | exact KB]).
destruct Hpc as [Hpc | Hpc]; rewrite Hpc.
- eapply (af_A L A mem md regs (ms_regs ms') L A (ms_mem ms') md g N s s rest FP cfp lpal lpa img fattr fgen delay nlp tidx);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | exact Hat' | exact Hwf | apply same_geom_refl
| eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply K; lia]
| exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact HFPin | exact HB | exact HSV | exact Q2'
| apply (RG _ _ _ Q8); rewrite (HE 10%nat 10%bv eq_refl); exact G10
| apply (RG _ _ _ Q9); rewrite (HE 11%nat 11%bv eq_refl); exact G11
| exact HUT ].
- eapply (af_ret API IMG L A mem md regs (ms_regs ms') L A (ms_mem ms') md g N s s CB rest FP);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Hat' | exact Hwf | apply same_geom_refl | exact HB | exact HSV | exact Q2' | exact HUT ]. }
assert (HR0 : region_ok src2segs E mem (YQ0b.mkRegion (Some 2%nat) (-96) 0 (-96) 0 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia | apply Forall_nil]. }
assert (HR1 : region_ok src2segs E mem (YQ0b.mkRegion (Some 10%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF 51 (litsG None None None None)))).
{ eapply (region_ok_obj_gen src2segs E mem 10 g 96 0 0 LAY_CGIF (cgif_vals s) 51 (litsG None None None None));
[exact HU10 | lia | lia | exact Hobj | reflexivity | | apply (litsG_ok s); exact I | intros i Hi; lia].
intros j v Hj. apply (HX (51 + j)%nat j v eq_refl Hj). }
assert (HPD : pairwise_disjoint E (ss_mem ss_af0)).
{ cbn [ss_mem ss_af0 pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU10. repeat split; lia. }
assert (HFA : atoms_ok E [(2%nat, mkAF (CEIL_MIN + 9728) (2 ^ 63 - 1) 4); (10%nat, mkAF 4096 (CEIL_MAX - 96) 4)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU10. change (2 ^ 4) with 16. repeat split; lia. }
assert (HS : st_ok src2segs E ss_af0 (mkst regs (Z_to_bv 64 src2_A_cgif_addframe) mem (seg_rom src2segs))).
{ unfold ss_af0. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | exact HPD | split; [exact HFA | split; exact I]].
constructor; [exact HR0 | constructor; [exact HR1 | constructor]]. }
clear HR0 HR1 HPD HFA.
pose proof (journal_init src2_msyms MR ADDFRAME_STK FP L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 src2_A_cgif_addframe) mem (seg_rom src2segs))) in HJ. fold sp0 in HJ.
assert (WR : forall E0 cs rg, bv_unsigned (ew E0 2) = sp0 -> r_whi rg <= r_wlo rg ->
wr_ok E0 [YQ0b.mkRegion (Some 2%nat) (-96) 0 (-96) 0 cs; rg] ADDFRAME_STK sp0 FP (blocks L A) (blocks L A)).
{ intros E0 cs rg H2 Hrg. eapply wr_ok_cons_stack; [reflexivity | exact H2 | cbn; lia | cbn; lia |]. apply wr_ok_cons_ro; [exact Hrg|]. apply wr_ok_nil. }
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 96 <= a < sp0) ->
mbyte src2segs (ms_mem (mkst regs (Z_to_bv 64 src2_A_cgif_addframe) mem (seg_rom src2segs))) a = mbyte src2segs mem a) by (intros; reflexivity).
cbn [ms_mem mkst] in K0.
runE AF_A WR HU2 sp0.
jbranch src2tbl HS; clear Hc.
- runE AF_A WR HU2 sp0.
lazymatch goal with K : forall a, _ -> _ -> mbyte src2segs _ a = mbyte src2segs mem a |- _ =>
eapply (GO _ _ _ HS); [left; reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact HJ | exact K] end.
- runE AF_A WR HU2 sp0.
jbranch src2tbl HS; clear Hc.
+ runE AF_RET WR HU2 sp0.
lazymatch goal with K : forall a, _ -> _ -> mbyte src2segs _ a = mbyte src2segs mem a |- _ =>
eapply (GO _ _ _ HS); [right; reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact HJ | exact K] end.
+ runE AF_A WR HU2 sp0.
lazymatch goal with K : forall a, _ -> _ -> mbyte src2segs _ a = mbyte src2segs mem a |- _ =>
eapply (GO _ _ _ HS); [left; reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact HJ | exact K] end.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
