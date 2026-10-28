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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3a YI06 UI5b YI09 YI08 YI0r UI1w UI1v UI4l UI21 UI2m UI5o UI5l YI6b UI5n UI20 UI1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI1n UI1e UI1f UI1c UI1g UI1l UI1h UI1k UI1i UI1j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI01 UI3u UI22 UI23 YI5a UI5d YI0f YI2w UI2v YI0o UI2s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25 UI2n UI1x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0b UI1o YI1m UI1p UI1q UIZo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Notation inFP_nil := YI04.inFP_nil (only parsing).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition AF_A : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0x48).
Definition af_entry_chunks : list YP09.chunk :=
[ mkChunk (-8) (CVal 8 (SOff 1 0)); mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-24) (CVal 8 (SOff 9 0)); mkChunk (-32) (CVal 8 (SOff 18 0));
mkChunk (-40) (CVal 8 (SOff 19 0)); mkChunk (-48) (CVal 8 (SOff 20 0)); mkChunk (-56) (CVal 8 (SOff 21 0)); mkChunk (-64) (CVal 8 (SOff 22 0)) ].
Lemma saved_word : forall E mem sp0 off n (regs : bvmap 5 word) (rr : reg),
chunk_ok ubs0segs E mem sp0 (mkChunk off (CVal 8 (SOff n 0))) -> ew E n = getr regs rr ->
forall a, a = sp0 + off -> word_mem ubs0segs mem a (bv_unsigned (getr regs rr)).
Proof using.
intros E mem sp0 off n regs rr Hc He a ->. apply val_mem_word_mem.
eapply (val_of_chunk_ok ubs0segs E mem sp0 off 8%N (SOff n 0)); [exact Hc | | cbn; apply u64_range_getr | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, He, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma af_saved_of_chunks : forall E (regs : bvmap 5 word) mem sp0 cs,
Forall (chunk_ok ubs0segs E mem sp0) cs ->
(forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) ->
incl af_entry_chunks cs ->
af_saved_ok mem sp0 regs.
Proof using.
intros E regs mem sp0 cs Hcs HE Hincl j r Hr.
assert (Hj : (j < 8)%nat) by (apply (proj1 (nth_error_Some AF_SAVED j)); rewrite Hr; discriminate).
assert (Hc : chunk_ok ubs0segs E mem sp0 (nth j af_entry_chunks (mkChunk 0 (CVal 8 (SLit 0))))).
{ apply (proj1 (Forall_forall _ _) Hcs). apply Hincl. apply nth_In. cbn. exact Hj. }
do 8 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; cbn [nth af_entry_chunks] in Hc;
eapply (saved_word E mem sp0 _ _ regs _ Hc); [apply HE; reflexivity | cbn; lia] |]).
cbn in Hj. lia.
Qed.
Lemma denot_of_U : forall E v z, U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof using. intros E v z <-. unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Definition ss_A : sstate :=
mkSS AF_A sr_atoms [ af_Rg None None None None ; af_Rcf ] None
(mkFacts ((af_facts ++ cf_facts) ++ [(56%nat, mkAF 0 4294967295 0)]) [] []).
Definition ss_af0 : sstate :=
mkSS ubs0_A_cgif_addframe sr_atoms
[ YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 [] ;
YP09.mkRegion (Some 10%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF 51 (litsG None None None None)) ] None
(mkFacts [(2%nat, mkAF (CEIL_MIN + 9728) (2 ^ 63 - 1) 4); (10%nat, mkAF 4096 (CEIL_MAX - 96) 4)] [] []).
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis FLUSHX : flushX_spec API.
Ltac iff_ofU E a HX56 HC46 Rf Rg :=
lazymatch a with
| SAlu ALU_AND (SOff 56 0) (SLit ?k) => constr:(afz_iff_atom E 56 _ k HX56 Rg ltac:(lia))
| SAlu ALU_AND (SAlu ALU_SRL (SAlu ALU_AND (SExt true 32 (SOff 46 0)) (SLit 4)) (SLit 2)) (SLit 1) => constr:(afz_iff_x1 E 46 _ HC46 Rf)
| SAlu ALU_AND (SAlu ALU_SRL (SAlu ALU_SLL (SExt true 32 (SOff 46 0)) (SLit 32)) (SLit 32)) (SLit ?k) => constr:(afz_iff_zext E 46 _ HC46 Rf k ltac:(lia))
| SAlu ALU_AND (SExt true 32 (SOff 46 0)) (SLit ?k) => constr:(afz_iff_sext E 46 _ HC46 Rf k ltac:(lia))
| SAlu ALU_AND (SAlu ALU_SRL (SAlu ALU_SLL (SExt false 8 (SOff 46 0)) (SLit 62)) (SLit 63)) _ => constr:(afz_iff_b2 E 46 _ HC46 Rf)
end.
Ltac interpU HX56 HC46 Rf Rg :=
match goal with Hc : branch_taken _ _ _ = _ |- _ =>
rewrite ?branch_eq_U, ?branch_ne_U, YI04.U_lit in Hc by lia;
first [ apply (proj1 (Bool.negb_true_iff _)) in Hc; apply (proj1 (Z.eqb_neq _ _)) in Hc
| apply (proj1 (Bool.negb_false_iff _)) in Hc; apply (proj1 (Z.eqb_eq _ _)) in Hc
| apply (proj1 (Z.eqb_eq _ _)) in Hc
| apply (proj1 (Z.eqb_neq _ _)) in Hc ];
lazymatch type of Hc with
| U ?E ?a = 0 => let Lm := iff_ofU E a HX56 HC46 Rf Rg in apply (proj1 Lm) in Hc
| U ?E ?a <> 0 => let Lm := iff_ofU E a HX56 HC46 Rf Rg in
let T := fresh "HC" in assert (T : ~ _) by (intros X; apply Hc; apply (proj2 Lm); exact X); clear Hc
end;
repeat match goal with H : ~ (_ \/ _) |- _ => apply afz_not_or in H; destruct H end;
repeat match goal with H : Z.land _ _ = 0 \/ Z.land _ _ = 0 |- _ => destruct H end
end.
Ltac errtac :=
unfold af_err, af_hasAlpha, af_hasSet, YO07.flag; cbn [YO07.g_attr gcfg_of];
repeat match goal with H : Z.land ?x ?k = 0 |- context [Z.land ?x ?k =? 0] => rewrite (proj2 (Z.eqb_eq (Z.land x k) 0) H) end;
cbn;
repeat match goal with |- context [Z.land ?x ?k =? 0] => destruct (Z.land x k =? 0) eqn:? end;
first [ reflexivity
| exfalso;
match goal with
| H : Z.lor _ _ <> 0 |- _ => apply H; apply (proj2 (Z.lor_eq_0_iff _ _)); split; first [assumption | apply (proj1 (Z.eqb_eq _ _)); assumption]
| H : Z.land _ _ <> 0 |- _ => apply H; first [assumption | apply (proj1 (Z.eqb_eq _ _)); assumption]
end ].
Ltac get_HS := match goal with H : st_ok _ _ _ _ |- _ => H end.
Ltac get_HJ := match goal with H : journal _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => H end.
Ltac get_HF := match goal with H : frame_of _ _ _ _ |- _ => H end.
Ltac clear_HG := repeat match goal with H : mem_grows _ _ |- _ => clear H end.
Ltac runA stop RO :=
let HS := get_HS in let HJ := get_HJ in
jrun_to LAWS ubs0tbl_ok HS HJ stop; [apply RO |];
let HF := get_HF in
cbn [ms_mem mkst] in HF; clear_HG;
lazymatch goal with K : forall a, mbyte ubs0segs ?m a = mbyte ubs0segs ?mc a |- _ =>
lazymatch type of HF with frame_of ?E1 ?rs m ?m2 =>
let K2 := fresh "K" in
assert (K2 : forall a, mbyte ubs0segs m2 a = mbyte ubs0segs mc a)
by (intros a; try rewrite <- (K a); unfold mbyte; rewrite (frame_of_ro E1 rs m m2 ltac:(vm_compute; reflexivity) HF); reflexivity);
clear HF K
end
end.
Ltac af_tree RUN LEAF INTERP n :=
lazymatch n with
| O => fail "af_tree: out of depth"
| Datatypes.S ?m => RUN; first [ LEAF | let HS := get_HS in jbranch ubs0tbl HS; [ INTERP; af_tree RUN LEAF INTERP m | INTERP; af_tree RUN LEAF INTERP m ] ]
end.
Lemma af_A :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (rest FP : list (Z * Z))
(cfp lpal lpa img fattr fgen delay nlp tidx : Z)
(GPAL IMGv LPALv : list Z) (gs : YO07.gif_st) (brb : rbound),
let sp0 := spZ regs0 in
let CB := (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) in
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
obj_at ubs0segs memc cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
cfp mod 8 = 0 -> sp0 <= cfp -> cfp + 32 <= 2 ^ 63 ->
Z_to_bv 64 lpa = Z_to_bv 64 lpal ->
(forall b n a, In (b, n) (cgif_blocks0 g s N) -> b <= a < b + n -> inFP FP a) ->
Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 64) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 cfp ->
af_untouched regs0 regs1 ->
cg_gen s = cg_gen s0 -> cg_file s = cg_file s0 ->
af_sink g s0 s N rest FP (concat (YO07.s_out gs)) L A mem md -> (forall a, inFP (cgif_fp g s0 N) a -> a < alloc_ceiling) ->
Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N <= SINK_MAX -> spZ regs0 <= 2 ^ 47 ->
cgif_live gs -> rc_int (cg_cur s) = YO07.s_cur gs -> af_live memc s N GPAL gs ->
garr8 ubs0segs memc img IMGv -> Z.of_nat (length IMGv) = N ->
(Z.land fattr 1 <> 0 -> garr8 ubs0segs memc lpa LPALv /\ Z.of_nat (length LPALv) = 3 * nlp) ->
res_ok Ac brb -> af_room brb N ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_A) memc (seg_rom ubs0segs)) mdc)
(af_postX API regs0 g N s0 CB rest GPAL gs (if af_err (gcfg_of s GPAL) fattr then YO07.with_cur gs YO07.C_ERROR else af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) (af_rb brb N (qcount gs) (qcount (if af_err (gcfg_of s GPAL) fattr then YO07.with_cur gs YO07.C_ERROR else af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs))) L A mem md).
Proof using FLUSHX IMG.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP cfp lpal lpa img fattr fgen delay nlp tidx GPAL IMGv LPALv gs brb sp0 CB
HJ Hid Hra0 Hal16 Htp0 Hat Hwf Hgeom Hcf Hcf8 Hcflo Hcfhi Hlpa HFP HB HSV G2 G8 G9 HUT
Xgen Xfile XSK XLOW XMAX Xsp47 XLV XCUR XLIVE XIMG0 XIL XLPA XRq XROOM.
pose proof XSK as (XSK1 & XSK2 & XFIN & XSK4 & XSK5 & HFPX).
pose proof (proj1 (af_live_iff _ _ _ _ _) XLIVE) as ((XHrc & XHra & XHih & XHgp) & XSL).
pose proof (proj1 (af_live_iff _ _ _ _ _) XLIVE) as (XH & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & _).
pose proof HUT as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N _ HH0 HB) as (_ & _ & (Hg0 & Hg1 & Hg16)).
pose proof Hat as (Hobj & Hraw & Hfrs).
pose proof (obj_at_range _ _ _ _ _ Hcf) as Rcf. pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
pose proof (Rcf 2%nat fattr eq_refl) as Rfattr. cbn [nth snd LAY_FrameConfig Z.of_N] in Rfattr.
pose proof (Rg 5%nat (cg_attr s) eq_refl) as Rattr. cbn [nth snd LAY_CGIF Z.of_N] in Rattr.
set (E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s []).
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HK regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (af_HC regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HC.
pose proof (af_HX regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HX.
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = cfp) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
pose proof (HX 56%nat 5%nat (cg_attr s) eq_refl eq_refl) as HX56.
pose proof (HC 46%nat 2%nat fattr eq_refl eq_refl) as HC46.
assert (Rf : 0 <= fattr < 2 ^ 32) by (clear - Rfattr; lia).
assert (Rga : 0 <= cg_attr s < 2 ^ 64) by (clear - Rattr; lia).
assert (GO_B : forall ss ms', st_ok ubs0segs E ss ms' -> ss_pc ss = AF_B -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 ->
sr_get (ss_regs ss) 23%bv = SOff 23 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 -> sr_get (ss_regs ss) 25%bv = SOff 25 0 ->
sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs memc a) ->
getr (ms_regs ms') 11 = Z_to_bv 64 fattr -> getr (ms_regs ms') 19 = Z_to_bv 64 (Z.land fattr 4) ->
(Z.land fattr 1 = 0 -> Z.land (cg_attr s) 4 = 0) ->
(af_err (gcfg_of s GPAL) fattr) = false ->
SR ubs0segs (mkCfg ms' mdc) (af_postX API regs0 g N s0 CB rest GPAL gs (if af_err (gcfg_of s GPAL) fattr then YO07.with_cur gs YO07.C_ERROR else af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) (af_rb brb N (qcount gs) (qcount (if af_err (gcfg_of s GPAL) fattr then YO07.with_cur gs YO07.C_ERROR else af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs))) L A mem md)).
{ intros ss ms' HS' Hpc Hrv Q2 Q3 Q4 Q8 Q9 Q23 Q24 Q25 Q26 Q27 HJ' K X11 X19 HnoCT ERRF. rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc. rewrite ERRF.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hw. rewrite (st_ok_reg ubs0segs E ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hw. }
eapply (af_B API IMG FLUSHX L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s0 s rest FP cfp lpal lpa img fattr fgen delay nlp tidx GPAL IMGv LPALv gs brb);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hgeom | exact HnoCT
| eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply K] | exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact HFP | exact HB
| apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply K]
| apply (RG _ _ _ Q2); rewrite (HE 2%nat 2%bv eq_refl); exact G2
| apply (RG _ _ _ Q8); rewrite (HE 8%nat 8%bv eq_refl); exact G8
| apply (RG _ _ _ Q9); rewrite (HE 9%nat 9%bv eq_refl); exact G9
| exact X11
| exact X19
| split; [|split; [|split; [|split; [|split; [|split]]]]]; [ apply (RG _ _ _ Q3); rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG _ _ _ Q4); rewrite (HE 4%nat 4%bv eq_refl); exact G4
| apply (RG _ _ _ Q23); rewrite (HE 23%nat 23%bv eq_refl); exact G23
| apply (RG _ _ _ Q24); rewrite (HE 24%nat 24%bv eq_refl); exact G24
| apply (RG _ _ _ Q25); rewrite (HE 25%nat 25%bv eq_refl); exact G25
| apply (RG _ _ _ Q26); rewrite (HE 26%nat 26%bv eq_refl); exact G26
| apply (RG _ _ _ Q27); rewrite (HE 27%nat 27%bv eq_refl); exact G27 ]
| exact Xgen | exact Xfile | exact XSK | exact XLOW | exact XMAX | exact Xsp47 | exact XLV | exact XCUR
| apply (proj2 (af_live_iff _ _ _ _ _)); split; [apply (af_hdr_kept memc); [intros _ k _; apply K | exact XH] | apply (af_slots_kept memc); [intros; apply K | exact XSL]]
| eapply garr8_frame; [exact XIMG0 | intros a _; apply K]
| exact XIL
| intros H1; destruct (XLPA H1) as [Hg Hgl]; split; [| exact Hgl]; eapply garr8_frame; [exact Hg | intros a _; apply K]
| exact XRq | exact XROOM ].
eapply (cgif_at_kept0 memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply K]. }
assert (GO_RC : forall ss ms' (v18 : Z), st_ok ubs0segs E ss ms' -> ss_pc ss = AF_RETC -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 8 0 ->
sr_get (ss_regs ss) 23%bv = SOff 23 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 -> sr_get (ss_regs ss) 25%bv = SOff 25 0 ->
sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
sr_get (ss_regs ss) 18%bv = SLit v18 -> v18 mod 2 ^ 32 = 2 ^ 32 - 1 -> (af_err (gcfg_of s GPAL) fattr) = true ->
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs memc a) ->
SR ubs0segs (mkCfg ms' mdc) (af_postX API regs0 g N s0 CB rest GPAL gs (if af_err (gcfg_of s GPAL) fattr then YO07.with_cur gs YO07.C_ERROR else af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) (af_rb brb N (qcount gs) (qcount (if af_err (gcfg_of s GPAL) fattr then YO07.with_cur gs YO07.C_ERROR else af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs))) L A mem md)).
{ intros ss ms' v18 HS' Hpc Hrv Q2 Q3 Q4 Q8 Q23 Q24 Q25 Q26 Q27 Q18 V18 ERRT HJ' K. rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc. rewrite ERRT.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hw. rewrite (st_ok_reg ubs0segs E ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hw. }
eapply (af_ret_cur API IMG L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s0 s CB rest FP GPAL gs (YO07.with_cur gs YO07.C_ERROR)
(af_rb brb N (qcount gs) (qcount (YO07.with_cur gs YO07.C_ERROR))));
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16
| intros a Ha; apply (HFP g CGIF_SIZE a); [left; reflexivity | exact Ha]
| | exact Hwf | exact Hgeom | exact HB
| apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply K]
| apply (RG _ _ _ Q2); rewrite (HE 2%nat 2%bv eq_refl); exact G2
| apply (RG _ _ _ Q8); rewrite (HE 8%nat 8%bv eq_refl); exact G8
| split; [|split; [|split; [|split; [|split; [|split]]]]]; [ apply (RG _ _ _ Q3); rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG _ _ _ Q4); rewrite (HE 4%nat 4%bv eq_refl); exact G4
| apply (RG _ _ _ Q23); rewrite (HE 23%nat 23%bv eq_refl); exact G23
| apply (RG _ _ _ Q24); rewrite (HE 24%nat 24%bv eq_refl); exact G24
| apply (RG _ _ _ Q25); rewrite (HE 25%nat 25%bv eq_refl); exact G25
| apply (RG _ _ _ Q26); rewrite (HE 26%nat 26%bv eq_refl); exact G26
| apply (RG _ _ _ Q27); rewrite (HE 27%nat 27%bv eq_refl); exact G27 ]
| exact Xgen | exact Xfile | exact HFPX
|   rewrite (st_ok_reg ubs0segs E ss ms' 18%bv HS'), Q18; cbn [sv_denot]; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
rewrite (Z.mod_mod_divide v18 (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity); rewrite V18; reflexivity
|   pose proof (af_slots_occ _ _ _ _ XSL) as OC; unfold cgif_occ, YO07.with_cur in OC |- *; cbn [YO07.s_q0 YO07.s_q1 YO07.s_q2]; exact OC
|   unfold YO07.with_cur; cbn [YO07.s_out]; exact (proj1 (af_sink_at API ADDFRAME_STK sp0 g s0 s N rest FP _ L A mem md Lc Ac (ms_mem ms') mdc HJ' XSK))
| exact XFIN
|   intros HL; exfalso; unfold cgif_live, YO07.with_cur in HL; cbn [YO07.s_cur] in HL; cbv in HL; destruct HL as [HL|HL]; discriminate HL
|   unfold YO07.with_cur; cbn [YO07.s_out]; unfold FRAME_OUT; clear - HN HW1 HH1; nia
|   replace (qcount (YO07.with_cur gs YO07.C_ERROR)) with (qcount gs) by reflexivity; exact (res_ok_mono _ _ _ (af_rb_same brb N (qcount gs) ltac:(clear - HN HW1 HH1; nia)) XRq) ].
eapply (cgif_at_kept0 memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply K]. }
assert (HR1 : region_ok ubs0segs E memc (af_Rg None None None None)).
{ apply (af_Rg_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s [] memc g); [exact HU8 | lia | lia | exact Hobj | exact I | exact I | exact I | exact I]. }
pose proof (af_Rcf_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s [] memc cfp HU9 ltac:(lia) ltac:(lia) Hcf) as HR2.
assert (HPD : pairwise_disjoint E (ss_mem ss_A)).
{ cbn [ss_mem ss_A]. unfold af_Rg, af_Rcf. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU8, HU9. clear - Hg1 Hceil Hcflo HASv HGSv Hac. repeat split; lia. }
assert (HFA : atoms_ok E ((af_facts ++ cf_facts) ++ [(56%nat, mkAF 0 4294967295 0)])).
{ apply atoms_ok_app; [apply atoms_ok_app; [| exact (cf_facts_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s [] memc cfp Hcf)]|].
- cbn [atoms_ok af_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, HU9.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia.
replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HX56, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
assert (HS : st_ok ubs0segs E ss_A (mkst regs1 (Z_to_bv 64 AF_A) memc (seg_rom ubs0segs))).
{ unfold ss_A. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | exact HPD | split; [exact HFA | split; exact I]].
constructor; [exact HR1|]. constructor; [exact HR2|]. constructor. }
clear HR1 HR2 HPD HFA.
assert (RO : wr_ok E [af_Rg None None None None; af_Rcf] ADDFRAME_STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (K0 : forall a, mbyte ubs0segs memc a = mbyte ubs0segs memc a) by (intros a; reflexivity).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_A) memc (seg_rom ubs0segs))) in HJ.
clear Rcf Rg.
af_tree ltac:(idtac; runA AF_B RO)
ltac:(idtac; lazymatch goal with K : forall a, mbyte ubs0segs _ a = mbyte ubs0segs memc a |- _ =>
first [ apply (GO_B _ _ HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ K);
[ rewrite (st_ok_reg ubs0segs _ _ _ 11%bv HS); eval_sr_get; apply denot_of_U; exact (afz_zext_sext _ 46 fattr HC46 Rf)
| rewrite (st_ok_reg ubs0segs _ _ _ 19%bv HS); eval_sr_get; apply denot_of_U; apply (afz_sext_land _ 46 fattr HC46 Rf 4); lia
| first [ intros _; assumption
| intros HF1; exfalso; match goal with H : Z.land fattr 1 <> 0 |- _ => exact (H HF1) end ]
| errtac ]
| exact (GO_RC _ _ _ HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(errtac) HJ K) ]
end)
ltac:(idtac; interpU HX56 HC46 Rf Rga)
constr:(8%nat).
Qed.
Ltac runE stop WR HU2 sp0 :=
let HS := get_HS in let HJ := get_HJ in
jrun_to LAWS ubs0tbl_ok HS HJ stop; [apply WR; [exact HU2 | cbn; lia] |];
let HF := get_HF in
cbn [ms_mem mkst] in HF; clear_HG;
lazymatch goal with K : forall a, _ -> _ -> mbyte ubs0segs ?m a = mbyte ubs0segs ?m0 a |- _ =>
lazymatch type of HF with frame_of ?E1 ?rs m ?m2 =>
let K2 := fresh "K" in
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 64 <= a < sp0) -> mbyte ubs0segs m2 a = mbyte ubs0segs m0 a);
[ intros a Ha Hna; try rewrite <- (K a Ha Hna);
apply (mbyte_of_frame E1 rs m m2 a HF Ha);
intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; rewrite ?HU2; lia |]); destruct Hr
| clear HF K ]
end
end.
Theorem ubs0_cgif_addframe_x : addframe_specX API.
Proof using FLUSHX IMG.
intros L A regs mem md g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMGv LPALv gs brb HPRE Hid XMAX Xsp47 G10 G11 Hcf8 Hcflo Hcfhi Hcf Hat Hwf Hlpa HB00 HREL XIMG0 XIL XLPA XRq XROOM.
pose proof HPRE as (HH & Hra0 & Hst & Htp0 & Herr). destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
set (sp0 := spZ regs) in *.
set (CB := (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)])) in *.
set (rest' := (cg_file s, FILE_BLOCK) :: rest).
assert (HB : Permutation (blocks L A) (cgif_blocks0 g s N ++ CB ++ rest')).
{ eapply Permutation_trans; [exact HB00|]. eapply Permutation_trans; [apply cgif_blocks0_perm|]. apply Permutation_app_head. subst rest'. apply (Permutation_middle CB rest (cg_file s, FILE_BLOCK)). }
set (FP := blocks_fp (cgif_blocks0 g s N)).
assert (HFPin : forall b n a, In (b, n) (cgif_blocks0 g s N) -> b <= a < b + n -> inFP FP a) by (intros b n a Hbn Ha; apply (cgif_fp_in g s N b n a Hbn Ha)).
destruct (af_cgif_geom0 API L A mem md g s N (CB ++ rest') HH HB) as (_ & _ & (Hg0 & Hg1 & Hg16)).
pose proof (proj1 (cgif_rel_split _ _ _ _ _ _) HREL) as ((Hcurq & Hocc) & HSK0 & Hlive).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & _).
assert (Hfin : In (cg_file s, FILE_BLOCK) (blocks L A)) by (eapply Permutation_in; [apply Permutation_sym; exact HB|]; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
assert (HFPX : forall a, inFP FP a -> inFP (cgif_fp g s N) a).
{ intros a Ha. subst FP. apply (proj1 (inFP_blocks_fp _ _)) in Ha as (bb & nn & Hbn & Hab). unfold cgif_fp. apply (proj2 (inFP_cons _ _ _ _)). right.
apply (proj2 (inFP_blocks_fp _ _)). exists bb, nn. split; [apply cgif_blocks0_in; exact Hbn | exact Hab]. }
assert (XLOW : forall a, inFP (cgif_fp g s N) a -> a < alloc_ceiling).
{ intros a Ha. unfold cgif_fp in Ha. apply inFP_cons in Ha. destruct Ha as [Ha|Ha]; [unfold sink_token in Ha; cbn [fst snd] in Ha; lia|].
apply inFP_blocks_fp in Ha as (b' & n & Hbn & Hba).
destruct (blocks_range _ _ LAWS L A mem md b' n HH ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB00|]; apply in_app_iff; left; exact Hbn)). lia. }
assert (Hnot : ~ sink_open_fp FP).
{ unfold sink_open_fp, in_fp. intros (r & Hr & Hrz). subst FP. unfold blocks_fp in Hr. apply in_map_iff in Hr as ([bb nn] & <- & Hbn). cbn [fst snd] in Hrz.
assert (Hl : In (bb, nn) (blocks L A)) by (eapply Permutation_in; [apply Permutation_sym; exact HB|]; apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS L A mem md bb nn HH Hl) as [R0 R1]. unfold sink_token in Hrz. cbn in Hrz. lia. }
assert (Havoid : fp_avoids FP (cg_file s) (cg_file s + FILE_BLOCK)).
{ intros a Ha Hin. subst FP. apply (proj1 (inFP_blocks_fp _ _)) in Hin as (bb & nn & Hbn & Hab).
pose proof (fl_file_sep API L A mem md g s N [] (CB ++ rest') bb nn HH HB ltac:(apply in_app_iff; right; left; reflexivity) Hbn) as Y. clear - Y Ha Hab. lia. }
assert (XSK : af_sink g s s N rest' FP (concat (YO07.s_out gs)) L A mem md).
{ split; [exact HSK0|]. split; [exact Hfin|]. split; [subst rest'; left; reflexivity|]. split; [exact Hnot|]. split; [exact Havoid | exact HFPX]. }
pose proof (obj_at_range _ _ _ _ _ (proj1 Hat) 15%nat (cg_cur s) eq_refl) as Rcur. cbn [nth snd LAY_CGIF Z.of_N] in Rcur.
pose proof Hat as (Hobj & Hraw & Hfrs).
set (E := af_E regs regs [lpal; img; fattr; fgen; delay; nlp; tidx] s []).
pose proof (af_HE regs regs lpal img fattr fgen delay nlp tidx s [] : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HX regs regs lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HX.
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = g) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (GO : forall ss ms' rg0 (dead : bool), st_ok ubs0segs E ss ms' -> ss_pc ss = (if dead then AF_RET else AF_A) -> ss_resv ss = None ->
nth_error (ss_mem ss) 0 = Some rg0 -> r_base rg0 = Some 2%nat -> incl_chunks af_entry_chunks (r_chunks rg0) = true ->
sr_get (ss_regs ss) 2%bv = SOff 2 (-64) -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 10 0 -> sr_get (ss_regs ss) 9%bv = SOff 11 0 ->
sr_get (ss_regs ss) 23%bv = SOff 23 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 -> sr_get (ss_regs ss) 25%bv = SOff 25 0 ->
sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
negb (YO07.s_cur gs =? YO07.C_OK) && negb (YO07.s_cur gs =? YO07.C_PENDING) = dead ->
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md L A (ms_mem ms') md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 64 <= a < sp0) -> mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs mem a) ->
SR ubs0segs (mkCfg ms' md) (fun c' => exists L' A' regs' mem' md' (s' : cgif_st),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR ADDFRAME_STK (spZ regs) (cgif_fp g s N) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
cgif_at mem' g s' /\ cgif_wf s' N /\
cg_W s' = cg_W s /\ cg_H s' = cg_H s /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\ cg_file s' = cg_file s /\
Permutation (blocks L' A')
(cgif_blocks g s' N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) /\
cg_gen s' = cg_gen s /\ cg_ngp s' = cg_ngp s /\ cg_pal s' = cg_pal s /\
cgif_rel mem' md' s' N GPAL (YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPALv IMGv) /\
Z.of_nat (length (concat (YO07.s_out (YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPALv IMGv))))
<= Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N /\
res_ok A' (af_rb brb N (qcount gs) (qcount (YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPALv IMGv))))).
{ intros ss ms' rg0 dead HS' Hpc Hrv Hrg0 Hb0 Hincl Q2 Q3 Q4 Q8 Q9 Q23 Q24 Q25 Q26 Q27 XDEAD HJ' K. rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv).
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hw. rewrite (st_ok_reg ubs0segs E ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hw. }
assert (Q2' : getr (ms_regs ms') 2 = Z_to_bv 64 (sp0 - 64)).
{ rewrite (st_ok_reg ubs0segs E ss ms' 2%bv HS'), Q2. cbn [sv_denot]. rewrite HU2. f_equal; lia. }
assert (HUT : af_untouched regs (ms_regs ms')).
{ split; [|split; [|split; [|split; [|split; [|split]]]]]; [ apply (RG _ _ _ Q3); apply (HE 3%nat 3%bv eq_refl) | apply (RG _ _ _ Q4); apply (HE 4%nat 4%bv eq_refl)
| apply (RG _ _ _ Q23); apply (HE 23%nat 23%bv eq_refl) | apply (RG _ _ _ Q24); apply (HE 24%nat 24%bv eq_refl) | apply (RG _ _ _ Q25); apply (HE 25%nat 25%bv eq_refl)
| apply (RG _ _ _ Q26); apply (HE 26%nat 26%bv eq_refl) | apply (RG _ _ _ Q27); apply (HE 27%nat 27%bv eq_refl) ]. }
assert (HSV : af_saved_ok (ms_mem ms') sp0 regs).
{ eapply (af_saved_of_chunks E regs (ms_mem ms') sp0 (r_chunks rg0)); [| exact HE | apply incl_chunks_sound; exact Hincl].
eapply (st_region_chunks ubs0segs E ss ms' 0 rg0 2%nat sp0 HS' Hrg0 Hb0 HU2). }
assert (KB : forall b n i, In (b, n) (blocks L A) -> 0 <= i < n -> mbyte ubs0segs (ms_mem ms') (b + i) = mbyte ubs0segs mem (b + i)).
{ intros b n i Hbn Hi. destruct (blocks_range _ _ LAWS L A mem md b n HH Hbn) as [B0 B1]. apply K; lia. }
assert (Hat' : cgif_at (ms_mem ms') g s) by (eapply (cgif_at_kept0 mem _ g s N (blocks L A)); [exact HB | exact Hat | exact KB]).
assert (KL : forall a, 0 <= a < alloc_ceiling -> mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs mem a) by (intros a Ha; apply K; clear - Ha Hceil Hac HASv; lia).
assert (XLIVE' : cgif_live gs -> af_live (ms_mem ms') s N GPAL gs).
{ intros Hl. apply (af_live_kept mem (ms_mem ms') s N GPAL gs Hwf); [| exact (Hlive Hl)]. intros a n k Hin Hk. apply (KB a n k); [| exact Hk].
eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left. unfold cgif_blocks0. right. right. exact (af_vblocks_sub0 s N _ Hin). }
assert (XREL' : cgif_rel (ms_mem ms') md s N GPAL gs).
{ apply (proj2 (cgif_rel_split _ _ _ _ _ _)). split; [exact (conj Hcurq Hocc)|]. split; [| exact XLIVE'].
apply (sink_at_frame ubs0_msyms mem); [| exact HSK0]. intros a [Ha|Ha].
- destruct (blocks_range _ _ LAWS L A mem md _ _ HH Hfin) as [R0 R1]. apply KL. clear - Ha R0 R1; lia.
- pose proof (ubs0_env_addr_range a Ha). apply KL. clear - H Hac; lia. }
assert (XIMG' : garr8 ubs0segs (ms_mem ms') img IMGv).
{ eapply garr8_frame; [exact XIMG0|]. intros a Ha. rewrite <- (Zplus_minus img a). apply (KB img N); [| clear - Ha XIL; lia].
eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. apply in_app_iff. left. subst CB. left. reflexivity. }
assert (XLPA' : Z.land fattr 1 <> 0 -> garr8 ubs0segs (ms_mem ms') lpa LPALv /\ Z.of_nat (length LPALv) = 3 * nlp).
{ intros Hz. destruct (XLPA Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha. rewrite <- (Zplus_minus lpa a). apply (KB lpa (3 * nlp)); [| clear - Ha Hgl; lia].
eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. apply in_app_iff. left. subst CB. right.
destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]. }
rewrite Hpc, add_frame_split, XDEAD. destruct dead.
-
cbv iota. eapply SR_mono.
{ eapply (af_ret API IMG L A mem md regs (ms_regs ms') L A (ms_mem ms') md g N s s CB rest' FP GPAL gs gs (af_rb brb N (qcount gs) (qcount gs)));
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Hat' | exact Hwf | apply same_geom_refl | exact HB | exact HSV | exact Q2' | exact HUT
| reflexivity | reflexivity | exact HFPX | exact XREL' | unfold FRAME_OUT; clear - HN HW1 HH1; nia
| exact (res_ok_mono _ _ _ (af_rb_same brb N (qcount gs) ltac:(clear - HN HW1 HH1; nia)) XRq) ]. }
cbv beta. intros c' (L' & A' & regs' & mem' & md' & s' & -> & HJ2 & HP & Hid2 & Hat2 & Hwf2 & HW & HHt & Hattr & Hraw2 & Hfile & HB2 & Hgen & Hngp & Hpal & XREL2 & XLEN2 & XRQ2).
exists L', A', regs', mem', md', s'. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact Hid2|]. split; [exact Hat2|]. split; [exact Hwf2|].
split; [exact HW|]. split; [exact HHt|]. split; [exact Hattr|]. split; [exact Hraw2|]. split; [exact Hfile|].
split; [| split; [exact Hgen | split; [exact Hngp | split; [exact Hpal | split; [exact XREL2 | split; [exact XLEN2 | exact XRQ2]]]]]].
apply Permutation_sym. eapply Permutation_trans; [apply cgif_blocks0_perm|]. apply Permutation_sym. eapply Permutation_trans; [exact HB2|]. apply Permutation_app_head. subst rest'. rewrite Hfile. apply Permutation_sym. apply (Permutation_middle CB rest (cg_file s, FILE_BLOCK)).
-
cbv iota.
assert (XLV : cgif_live gs).
{ unfold cgif_live. destruct (Z.eqb_spec (YO07.s_cur gs) YO07.C_OK) as [E0|E0]; [left; exact E0|]. destruct (Z.eqb_spec (YO07.s_cur gs) YO07.C_PENDING) as [E6|E6]; [right; exact E6|]. cbn in XDEAD. discriminate XDEAD. }
eapply SR_mono.
{ eapply (af_A L A mem md regs (ms_regs ms') L A (ms_mem ms') md g N s s rest' FP cfp lpal lpa img fattr fgen delay nlp tidx GPAL IMGv LPALv gs brb);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | exact Hat' | exact Hwf | apply same_geom_refl
| eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply K; lia]
| exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact HFPin | exact HB | exact HSV | exact Q2'
| apply (RG _ _ _ Q8); rewrite (HE 10%nat 10%bv eq_refl); exact G10
| apply (RG _ _ _ Q9); rewrite (HE 11%nat 11%bv eq_refl); exact G11
| exact HUT
| reflexivity | reflexivity | exact XSK | exact XLOW | exact XMAX | exact Xsp47 | exact XLV | exact Hcurq | exact (XLIVE' XLV) | exact XIMG' | exact XIL | exact XLPA' | exact XRq | exact XROOM ]. }
cbv beta. intros c' (L' & A' & regs' & mem' & md' & s' & -> & HJ2 & HP & Hid2 & Hat2 & Hwf2 & HW & HHt & Hattr & Hraw2 & Hfile & HB2 & Hgen & Hngp & Hpal & XREL2 & XLEN2 & XRQ2).
exists L', A', regs', mem', md', s'. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact Hid2|]. split; [exact Hat2|]. split; [exact Hwf2|].
split; [exact HW|]. split; [exact HHt|]. split; [exact Hattr|]. split; [exact Hraw2|]. split; [exact Hfile|].
split; [| split; [exact Hgen | split; [exact Hngp | split; [exact Hpal | split; [exact XREL2 | split; [exact XLEN2 | exact XRQ2]]]]]].
apply Permutation_sym. eapply Permutation_trans; [apply cgif_blocks0_perm|]. apply Permutation_sym. eapply Permutation_trans; [exact HB2|]. apply Permutation_app_head. subst rest'. rewrite Hfile. apply Permutation_sym. apply (Permutation_middle CB rest (cg_file s, FILE_BLOCK)). }
assert (HR0 : region_ok ubs0segs E mem (YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia | apply Forall_nil]. }
assert (HR1 : region_ok ubs0segs E mem (YP09.mkRegion (Some 10%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF 51 (litsG None None None None)))).
{ eapply (region_ok_obj_gen ubs0segs E mem 10 g 96 0 0 LAY_CGIF (cgif_vals s) 51 (litsG None None None None));
[exact HU10 | lia | lia | exact Hobj | reflexivity | | apply (litsG_ok s); exact I | intros i Hi; lia].
intros j v Hj. apply (HX (51 + j)%nat j v eq_refl Hj). }
assert (HPD : pairwise_disjoint E (ss_mem ss_af0)).
{ cbn [ss_mem ss_af0 pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU10. repeat split; lia. }
assert (HFA : atoms_ok E [(2%nat, mkAF (CEIL_MIN + 9728) (2 ^ 63 - 1) 4); (10%nat, mkAF 4096 (CEIL_MAX - 96) 4)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU10. change (2 ^ 4) with 16. repeat split; lia. }
assert (HS : st_ok ubs0segs E ss_af0 (mkst regs (Z_to_bv 64 ubs0_A_cgif_addframe) mem (seg_rom ubs0segs))).
{ unfold ss_af0. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | exact HPD | split; [exact HFA | split; exact I]].
constructor; [exact HR0 | constructor; [exact HR1 | constructor]]. }
clear HR0 HR1 HPD HFA.
pose proof (journal_init ubs0_msyms MR ADDFRAME_STK FP L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs0_A_cgif_addframe) mem (seg_rom ubs0segs))) in HJ. fold sp0 in HJ.
assert (WR : forall E0 cs rg, bv_unsigned (ew E0 2) = sp0 -> r_whi rg <= r_wlo rg ->
wr_ok E0 [YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 cs; rg] ADDFRAME_STK sp0 FP (blocks L A) (blocks L A)).
{ intros E0 cs rg H2 Hrg. eapply wr_ok_cons_stack; [reflexivity | exact H2 | cbn; lia | cbn; lia |]. apply wr_ok_cons_ro; [exact Hrg|]. apply wr_ok_nil. }
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 64 <= a < sp0) ->
mbyte ubs0segs (ms_mem (mkst regs (Z_to_bv 64 ubs0_A_cgif_addframe) mem (seg_rom ubs0segs))) a = mbyte ubs0segs mem a) by (intros; reflexivity).
cbn [ms_mem mkst] in K0.
pose proof (HX 66%nat 15%nat (cg_cur s) eq_refl eq_refl) as HX66.
runE AF_A WR HU2 sp0.
jbranch ubs0tbl HS.
- assert (XDEAD : negb (YO07.s_cur gs =? YO07.C_OK) && negb (YO07.s_cur gs =? YO07.C_PENDING) = false).
{ rewrite branch_eq_U, U_lit in Hc by lia. apply (proj1 (Z.eqb_eq _ _)) in Hc.
assert (C6 : cg_cur s = 6) by (rewrite <- (U_sext32_low E 66 (cg_cur s) HX66 ltac:(clear - Rcur; lia)); rewrite Hc; reflexivity).
rewrite <- Hcurq, C6. reflexivity. }
clear Hc. runE AF_A WR HU2 sp0.
lazymatch goal with K : forall a, _ -> _ -> mbyte ubs0segs _ a = mbyte ubs0segs mem a |- _ =>
eapply (GO _ _ _ false HS); [reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact XDEAD | exact HJ | exact K] end.
- assert (XNP : YO07.s_cur gs <> YO07.C_PENDING).
{ rewrite branch_eq_U, U_lit in Hc by lia. apply (proj1 (Z.eqb_neq _ _)) in Hc. rewrite <- Hcurq. intros E6.
pose proof (proj1 (rc_int_eq_small (cg_cur s) 6 ltac:(clear - Rcur; lia) ltac:(clear; lia)) E6) as C6.
apply Hc. rewrite (U_sext32_small E 66%nat (cg_cur s) HX66) by (rewrite C6; clear; lia). exact C6. }
clear Hc. runE AF_A WR HU2 sp0.
jbranch ubs0tbl HS.
+ assert (XDEAD : negb (YO07.s_cur gs =? YO07.C_OK) && negb (YO07.s_cur gs =? YO07.C_PENDING) = true).
{ rewrite ?branch_ne_U, ?branch_eq_U, U_lit in Hc by lia.
assert (C0 : cg_cur s <> 0). { intros E0. rewrite (U_sext32_small E 66%nat (cg_cur s) HX66) in Hc by (rewrite E0; clear; lia). rewrite E0 in Hc. cbn in Hc. discriminate Hc. }
rewrite <- Hcurq. destruct (Z.eqb_spec (rc_int (cg_cur s)) YO07.C_OK) as [E0|E0]; [exfalso; apply C0; exact (proj1 (rc_int_eq_small (cg_cur s) 0 ltac:(clear - Rcur; lia) ltac:(clear; lia)) E0)|].
destruct (Z.eqb_spec (rc_int (cg_cur s)) YO07.C_PENDING) as [E6|E6]; [exfalso; rewrite Hcurq in E6; exact (XNP E6)|]. reflexivity. }
clear Hc. runE AF_RET WR HU2 sp0.
lazymatch goal with K : forall a, _ -> _ -> mbyte ubs0segs _ a = mbyte ubs0segs mem a |- _ =>
eapply (GO _ _ _ true HS); [reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact XDEAD | exact HJ | exact K] end.
+ assert (XDEAD : negb (YO07.s_cur gs =? YO07.C_OK) && negb (YO07.s_cur gs =? YO07.C_PENDING) = false).
{ rewrite ?branch_ne_U, ?branch_eq_U, U_lit in Hc by lia.
pose proof (U_sext32_low E 66 (cg_cur s) HX66 ltac:(clear - Rcur; lia)) as UL.
first [apply (proj1 (Z.eqb_eq _ _)) in Hc | apply (proj1 (Bool.negb_false_iff _)) in Hc; apply (proj1 (Z.eqb_eq _ _)) in Hc].
rewrite Hc in UL. cbn in UL. rewrite <- Hcurq, <- UL. reflexivity. }
clear Hc. runE AF_A WR HU2 sp0.
lazymatch goal with K : forall a, _ -> _ -> mbyte ubs0segs _ a = mbyte ubs0segs mem a |- _ =>
eapply (GO _ _ _ false HS); [reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact XDEAD | exact HJ | exact K] end.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
