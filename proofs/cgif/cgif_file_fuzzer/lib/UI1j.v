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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI1n UI1e UI1f UI1c UI1g UI1l UI1h UI1k UI1i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI01 UI3u UI22 YI5a UI5d YI0f YI2w UI2v YI0o UI2s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25 UI2n UI1x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0b UI1o YI1m UI1p UI1q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Notation inFP_nil := YI04.inFP_nil (only parsing).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis FLUSHX : flushX_spec API.
Ltac roK HF Kprev K memc :=
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
assert (K : forall a, mbyte ubs0segs m2 a = mbyte ubs0segs memc a)
by (intros a; rewrite <- (Kprev a); unfold mbyte; rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF); reflexivity);
clear HF
end.
Definition ss_Bn (ih : Z) : sstate :=
mkSS AF_B sr_atoms
[ YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) ;
(if ih =? 1 then af_Rg None (Some 0) None (Some ih) else af_Rg None None (Some 0) (Some ih)) ; af_Rcf ]
None (mkFacts (af_facts ++ cf_facts) [] []).
Definition ss_Bs (ih : Z) (z1 : bool) : sstate :=
mkSS AF_B sr_atoms
[ YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) ; af_Rg None None None (Some ih) ; af_Rcf ;
af_Rfr_part (Z.to_nat (51 + ih)) 68 0 40 0 0 ]
None (mkFacts ((af_facts ++ cf_facts) ++ [(58%nat, mkAF 1 65535 0); (59%nat, mkAF 1 65535 0); (Z.to_nat (51 + ih), mkAF 4096 (CEIL_MAX - 40) 4);
(11%nat, mkAF 0 4294967295 0); (69%nat, mkAF 4096 CEIL_MAX 0); (70%nat, mkAF 0 4294967295 0); (72%nat, mkAF 0 65535 0)])
[mkAC (if z1 then BC_EQ else BC_NE) (SAlu ALU_AND (SOff 11 0) (SLit 1)) (SLit 0)] []).
Lemma af_B :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (rest FP : list (Z * Z))
(cfp lpal lpa img fattr fgen delay nlp tidx : Z)
(GPAL IMGv LPALv : list Z) (gs : YO07.gif_st) (brb : rbound),
let sp0 := spZ regs0 in
let CB := (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) in
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
(Z.land fattr 1 = 0 -> Z.land (cg_attr s) 4 = 0) ->
obj_at ubs0segs memc cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
cfp mod 8 = 0 -> sp0 <= cfp -> cfp + 32 <= 2 ^ 63 ->
Z_to_bv 64 lpa = Z_to_bv 64 lpal ->
(forall b n a, In (b, n) (cgif_blocks0 g s N) -> b <= a < b + n -> inFP FP a) ->
Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 64) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 cfp ->
getr regs1 11 = Z_to_bv 64 fattr -> getr regs1 19 = Z_to_bv 64 (Z.land fattr 4) ->
af_untouched regs0 regs1 ->
cg_gen s = cg_gen s0 -> cg_file s = cg_file s0 ->
af_sink g s0 s N rest FP (concat (YO07.s_out gs)) L A mem md -> (forall a, inFP (cgif_fp g s0 N) a -> a < alloc_ceiling) ->
Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N <= SINK_MAX -> spZ regs0 <= 2 ^ 47 ->
cgif_live gs -> rc_int (cg_cur s) = YO07.s_cur gs -> af_live memc s N GPAL gs ->
garr8 ubs0segs memc img IMGv -> Z.of_nat (length IMGv) = N ->
(Z.land fattr 1 <> 0 -> garr8 ubs0segs memc lpa LPALv /\ Z.of_nat (length LPALv) = 3 * nlp) ->
res_ok Ac brb -> af_room brb N ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_B) memc (seg_rom ubs0segs)) mdc)
(af_postX API regs0 g N s0 CB rest GPAL gs (af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) (af_rb brb N (qcount gs) (qcount (af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs))) L A mem md).
Proof using FLUSHX IMG.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP cfp lpal lpa img fattr fgen delay nlp tidx GPAL IMGv LPALv gs brb sp0 CB
HJ Hid Hra0 Hal16 Htp0 Hat Hwf Hgeom HnoCT Hcf Hcf8 Hcflo Hcfhi Hlpa HFP HB HSV G2 G8 G9 G11 G19 HUT
Xgen Xfile XSK XLOW XMAX Xsp47 XLV XCUR XLIVE XIMG0 XIL XLPA XRq XROOM.
pose proof (proj1 (af_live_iff _ _ _ _ _) XLIVE) as ((XHrc & XHra & XHih & XHgp) & XSL).
pose proof (proj1 (af_live_iff _ _ _ _ _) XLIVE) as (XH & _).
pose proof HUT as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & Hih & Hfwf).
assert (Hih3 : (Z.to_nat (cg_ihead s) < 3)%nat) by (clear - Hih; lia).
assert (XihN : YO07.s_ihead gs = Z.of_nat (Z.to_nat (cg_ihead s))) by (rewrite <- XHih; clear - Hih; lia).
destruct (frames3 s N Hwf) as (o0 & o1 & o2 & Hfr).
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N _ HH0 HB) as (_ & Hfgeom & (Hg0 & Hg1 & Hg16)).
pose proof Hat as (Hobj & Hraw & Hfrs).
pose proof (obj_at_range _ _ _ _ _ Hcf) as Rcf. pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
pose proof (Rcf 2%nat fattr eq_refl) as Rfattr. cbn [nth snd LAY_FrameConfig Z.of_N] in Rfattr.
pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. cbn [nth snd LAY_CGIF Z.of_N] in RW, RH.
assert (GO_C : forall (more : list Z) E' ss ms',
let E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s more in
st_ok ubs0segs E' ss ms' -> env_agree 32 E E' -> ss_pc ss = AF_C -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 ->
sr_get (ss_regs ss) 19%bv = SOff 19 0 -> sr_get (ss_regs ss) 20%bv = SLit (cg_ihead s) ->
sr_get (ss_regs ss) 23%bv = SOff 23 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 -> sr_get (ss_regs ss) 25%bv = SOff 25 0 ->
sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
af_merged (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs = None ->
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs memc a) ->
SR ubs0segs (mkCfg ms' mdc) (af_postX API regs0 g N s0 CB rest GPAL gs (af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) (af_rb brb N (qcount gs) (qcount (af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs))) L A mem md)).
{ intros more E' ss ms' E HS' HA Hpc Hrv Q2 Q3 Q4 Q8 Q9 Q19 Q20 Q23 Q24 Q25 Q26 Q27 XMN HJ' K. rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc.
rewrite (af_from_merge_none (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs XMN).
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s more : forall n rr, _ -> ew E n = _) as HE.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> (n < 32)%nat -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hn Hw. rewrite (st_ok_reg ubs0segs E' ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, <- Hw. apply (proj1 HA). exact Hn. }
eapply (af_C API IMG FLUSHX L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s0 s rest FP cfp lpal lpa img fattr fgen delay nlp tidx (Z.land fattr 4) GPAL IMGv LPALv gs brb);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hgeom | exact HnoCT
| eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply K] | exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact HFP | exact HB
| apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply K]
| apply (RG _ _ _ Q2 ltac:(lia)); rewrite (HE 2%nat 2%bv eq_refl); exact G2
| apply (RG _ _ _ Q8 ltac:(lia)); rewrite (HE 8%nat 8%bv eq_refl); exact G8
| apply (RG _ _ _ Q9 ltac:(lia)); rewrite (HE 9%nat 9%bv eq_refl); exact G9
| apply (RG _ _ _ Q19 ltac:(lia)); rewrite (HE 19%nat 19%bv eq_refl); exact G19
| pose proof (land_le fattr 4 ltac:(lia)); lia
| rewrite (st_ok_reg ubs0segs E' ss ms' 20%bv HS'), Q20; reflexivity
| split; [|split; [|split; [|split; [|split; [|split]]]]]; [ apply (RG _ _ _ Q3 ltac:(lia)); rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG _ _ _ Q4 ltac:(lia)); rewrite (HE 4%nat 4%bv eq_refl); exact G4
| apply (RG _ _ _ Q23 ltac:(lia)); rewrite (HE 23%nat 23%bv eq_refl); exact G23
| apply (RG _ _ _ Q24 ltac:(lia)); rewrite (HE 24%nat 24%bv eq_refl); exact G24
| apply (RG _ _ _ Q25 ltac:(lia)); rewrite (HE 25%nat 25%bv eq_refl); exact G25
| apply (RG _ _ _ Q26 ltac:(lia)); rewrite (HE 26%nat 26%bv eq_refl); exact G26
| apply (RG _ _ _ Q27 ltac:(lia)); rewrite (HE 27%nat 27%bv eq_refl); exact G27 ]
| exact Xgen | exact Xfile | reflexivity | exact XSK | exact XLOW | exact XMAX | exact Xsp47 | exact XLV | exact XCUR
| apply (proj2 (af_live_iff _ _ _ _ _)); split; [apply (af_hdr_kept memc); [intros _ k _; apply K | exact XH] | apply (af_slots_kept memc); [intros; apply K | exact XSL]]
| eapply garr8_frame; [exact XIMG0 | intros a _; apply K]
| exact XIL
| intros H1; destruct (XLPA H1) as [Hg Hgl]; split; [| exact Hgl]; eapply garr8_frame; [exact Hg | intros a _; apply K]
| exact XRq | exact XROOM ].
eapply (cgif_at_kept0 memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply K]. }
assert (GO_SF : forall fh E' ss ms' pc (HD : YO07.frame) (fdx : sv),
let E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s (frame_vals fh) in
st_ok ubs0segs E' ss ms' -> env_agree 32 E E' -> ss_pc ss = pc -> ss_resv ss = None -> (pc = AF_SLOW \/ pc = AF_FAST) ->
qslot gs (Z.to_nat (cg_ihead s)) = Some HD -> delay + YO07.f_delay HD <= 65535 -> Z.land (cg_gen s) 1 = 0 ->
sr_get (ss_regs ss) 21%bv = fdx -> U E' fdx mod 2 ^ 16 = delay + YO07.f_delay HD ->
pc = (if negb (YO07.flag fattr 1) && negb (YO07.flag (YO07.f_attr HD) 1) && negb (YO07.flag fattr 4) && negb (YO07.flag (YO07.f_attr HD) 4) then AF_FAST else AF_SLOW) ->
nth_error (cg_frames s) (Z.to_nat (cg_ihead s)) = Some (Some fh) ->
ew E' (Z.to_nat (51 + cg_ihead s)) = Z_to_bv 64 (fr_ptr fh) ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 -> sr_get (ss_regs ss) 12%bv = SOff (Z.to_nat (51 + cg_ihead s)) 0 ->
sr_get (ss_regs ss) 19%bv = SOff 19 0 -> sr_get (ss_regs ss) 20%bv = SLit (cg_ihead s) ->
sr_get (ss_regs ss) 23%bv = SOff 23 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 -> sr_get (ss_regs ss) 25%bv = SOff 25 0 ->
sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs memc a) ->
SR ubs0segs (mkCfg ms' mdc) (af_postX API regs0 g N s0 CB rest GPAL gs (af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) (af_rb brb N (qcount gs) (qcount (af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs))) L A mem md)).
{ intros fh E' ss ms' pc HD fdx E HS' HA Hpc Hrv Hpc2 XHD XFD XKEEP Q21 Ufd Hpcx Hfh Hfhp Q2 Q3 Q4 Q8 Q9 Q12 Q19 Q20 Q23 Q24 Q25 Q26 Q27 HJ' K. rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc.
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HX regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n j v, _ -> _ -> ew E n = _) as HX.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> (n < 32)%nat -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hn Hw. rewrite (st_ok_reg ubs0segs E' ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, <- Hw. apply (proj1 HA). exact Hn. }
assert (PRE : B_pre API L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s0 s rest FP fh cfp lpal lpa img fattr fgen delay nlp tidx).
{ split; [exact HJ'|]. split; [exact Hid|]. split; [exact Hra0|]. split; [exact Hal16|]. split; [exact Htp0|].
split; [eapply (cgif_at_kept0 memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply K]|].
split; [exact Hwf|]. split; [exact Hgeom|]. split; [exact Hfh|]. split; [exact HnoCT|].
split; [eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply K]|].
split; [exact Hcf8|]. split; [exact Hcflo|]. split; [exact Hcfhi|]. split; [exact Hlpa|]. split; [exact HFP|]. split; [exact HB|].
split; [apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply K]|].
split; [apply (RG _ _ _ Q2 ltac:(lia)); rewrite (HE 2%nat 2%bv eq_refl); exact G2|].
split; [apply (RG _ _ _ Q8 ltac:(lia)); rewrite (HE 8%nat 8%bv eq_refl); exact G8|].
split; [apply (RG _ _ _ Q9 ltac:(lia)); rewrite (HE 9%nat 9%bv eq_refl); exact G9|].
split. { rewrite (st_ok_reg ubs0segs E' ss ms' 12%bv HS'), Q12. cbn [sv_denot]. rewrite Z.add_0_r, Hfhp. apply Z_to_bv_bv_unsigned. }
split; [apply (RG _ _ _ Q19 ltac:(lia)); rewrite (HE 19%nat 19%bv eq_refl); exact G19|].
split; [rewrite (st_ok_reg ubs0segs E' ss ms' 20%bv HS'), Q20; reflexivity|].
split; [|split; [|split; [|split; [|split; [|split]]]]]; [ apply (RG _ _ _ Q3 ltac:(lia)); rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG _ _ _ Q4 ltac:(lia)); rewrite (HE 4%nat 4%bv eq_refl); exact G4
| apply (RG _ _ _ Q23 ltac:(lia)); rewrite (HE 23%nat 23%bv eq_refl); exact G23
| apply (RG _ _ _ Q24 ltac:(lia)); rewrite (HE 24%nat 24%bv eq_refl); exact G24
| apply (RG _ _ _ Q25 ltac:(lia)); rewrite (HE 25%nat 25%bv eq_refl); exact G25
| apply (RG _ _ _ Q26 ltac:(lia)); rewrite (HE 26%nat 26%bv eq_refl); exact G26
| apply (RG _ _ _ Q27 ltac:(lia)); rewrite (HE 27%nat 27%bv eq_refl); exact G27 ]. }
assert (PREX : B_preX L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s0 s rest FP fh cfp lpal lpa img fattr fgen delay nlp tidx GPAL IMGv LPALv gs brb HD).
{ split; [exact Xgen|]. split; [exact Xfile|]. split; [exact XSK|]. split; [exact XLOW|]. split; [exact XMAX|]. split; [exact Xsp47|].
split; [exact XLV|]. split; [exact XCUR|].
split; [apply (proj2 (af_live_iff _ _ _ _ _)); split; [apply (af_hdr_kept memc); [intros _ k _; apply K | exact XH] | apply (af_slots_kept memc); [intros; apply K | exact XSL]]|].
split; [eapply garr8_frame; [exact XIMG0 | intros a _; apply K]|]. split; [exact XIL|].
split; [intros H1; destruct (XLPA H1) as [Hg Hgl]; split; [| exact Hgl]; eapply garr8_frame; [exact Hg | intros a _; apply K]|].
split; [exact XRq|]. split; [exact XROOM|]. split; [exact XHD|]. split; [exact XFD|]. split; [exact XKEEP|].
rewrite (st_ok_reg ubs0segs E' ss ms' 21%bv HS'), Q21. unfold U in Ufd. exact Ufd. }
clear Hpc2. destruct (negb (YO07.flag fattr 1) && negb (YO07.flag (YO07.f_attr HD) 1) && negb (YO07.flag fattr 4) && negb (YO07.flag (YO07.f_attr HD) 4)) eqn:XCOND; rewrite Hpcx;
[apply (af_fast API IMG FLUSHX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE PREX XCOND) | apply (af_slow API IMG FLUSHX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE PREX XCOND)]. }
assert (Hspf : forall more, let E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s more in
bv_unsigned (ew E 2) = sp0 - 64 /\ bv_unsigned (ew E 8) = g /\ bv_unsigned (ew E 9) = cfp /\
region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32)) /\
region_ok ubs0segs E memc af_Rcf /\ atoms_ok E (af_facts ++ cf_facts) /\
(forall p0 p1 p2, pin_ok p0 (frame_ptr o0) -> pin_ok p1 (frame_ptr o1) -> pin_ok p2 (frame_ptr o2) ->
region_ok ubs0segs E memc (af_Rg p0 p1 p2 (Some (cg_ihead s))))).
{ intros more. cbn zeta.
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s more : forall n rr, _ -> ew _ n = _) as HE.
pose proof (af_HK regs1 regs0 lpal img fattr fgen delay nlp tidx s more : forall n j v, _ -> _ -> ew _ n = _) as HK.
assert (HU2 : bv_unsigned (ew (af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s more) 2) = sp0 - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew (af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s more) 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew (af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s more) 9) = cfp) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
split; [exact HU2|]. split; [exact HU8|]. split; [exact HU9|]. split.
{ pose proof (af_Rstk_ok _ memc sp0 regs0 32 HU2 ltac:(lia) ltac:(lia) HSV (fun j v Hj => HK _ j v eq_refl Hj) (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4]. }
split; [exact (af_Rcf_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s more memc cfp HU9 ltac:(lia) ltac:(lia) Hcf)|].
split.
{ apply atoms_ok_app; [| exact (cf_facts_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s more memc cfp Hcf)].
cbn [atoms_ok af_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, HU9.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia.
replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
intros p0 p1 p2 P0 P1 P2. apply (af_Rg_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s more memc g); [exact HU8 | lia | lia | exact Hobj | | | | exact eq_refl];
rewrite Hfr; cbn [nth]; assumption. }
assert (RO3 : forall E rg, r_whi rg <= r_wlo rg -> wr_ok E [YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32); rg; af_Rcf] ADDFRAME_STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E rg Hrg. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [exact Hrg|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (RO4 : forall E rg rg', r_whi rg <= r_wlo rg -> r_whi rg' <= r_wlo rg' ->
wr_ok E [YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32); rg; af_Rcf; rg'] ADDFRAME_STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E rg rg' Hrg Hrg'. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [exact Hrg|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [exact Hrg'|]. apply wr_ok_nil. }
destruct (nth (Z.to_nat (cg_ihead s)) (cg_frames s) None) as [fh|] eqn:Hslot.
-
assert (Hfh : nth_error (cg_frames s) (Z.to_nat (cg_ihead s)) = Some (Some fh)).
{ rewrite (nth_error_nth' _ None) by (rewrite Hlen; destruct Hih as [H1|[H2 _]]; rewrite ?H1, ?H2; cbn; lia). rewrite Hslot. reflexivity. }
assert (Hfin : In (Some fh) (cg_frames s)) by (eapply nth_error_In; exact Hfh).
destruct (Hfgeom fh Hfin) as (Hf0 & Hf1 & Hfg).
destruct (af_frame_geom0 API Lc Ac memc mdc g s N _ fh HH0 HB Hfin) as (Hfblk & Hfimgblk & _).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr fh) FRAME_SIZE HH0 Hfblk ltac:(lia)) as (_ & _ & Hf16).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc (fr_img fh) N HH0 Hfimgblk) as [Hfi0 Hfi1].
pose proof (Hfrs fh Hfin) as Hfobj. pose proof (obj_at_range _ _ _ _ _ Hfobj) as Rf.
pose proof (Rf 2%nat (fr_attr fh) eq_refl) as Rfa. pose proof (Rf 4%nat (fr_delay fh) eq_refl) as Rfd. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfa, Rfd.
pose proof (XSL (Z.to_nat (cg_ihead s)) Hih3 I) as FR. rewrite Hslot in FR.
assert (XX : exists HD, qslot gs (Z.to_nat (cg_ihead s)) = Some HD) by (destruct (qslot gs (Z.to_nat (cg_ihead s))) as [HD'|]; [exists HD'; reflexivity | exfalso; exact FR]).
destruct XX as [HD XHD]. rewrite XHD in FR. cbn [oframe_relb] in FR.
pose proof FR as (FRa & FRg & FRd & FRn & FRc & FRdisp & FRt & FRimg & FRil & FRlp). pose proof XHD as XHDk.
pose proof (Rcf 4%nat delay eq_refl) as Rdelay. cbn [nth snd LAY_FrameConfig Z.of_N] in Rdelay.
pose proof (Rg 6%nat (cg_gen s) eq_refl) as Rgen. cbn [nth snd LAY_CGIF Z.of_N] in Rgen.
set (E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s (frame_vals fh)).
pose proof (af_HC regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n j v, _ -> _ -> ew E n = _) as HC.
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HX regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n j v, _ -> _ -> ew E n = _) as HX.
pose proof (af_HM regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n j v, _ -> _ -> ew E n = _) as HM.
destruct (Hspf (frame_vals fh)) as (HU2 & HU8 & HU9 & HR0 & HR2 & HFA & HR1). fold E in HU2, HU8, HU9, HR0, HR2, HFA, HR1.
assert (HXfh : ew E (Z.to_nat (51 + cg_ihead s)) = Z_to_bv 64 (fr_ptr fh)).
{ destruct Hih as [H1|[H2 _]].
- rewrite H1 in Hslot |- *. change (Z.to_nat (51 + 1)) with 52%nat. change (Z.to_nat 1) with 1%nat in Hslot.
apply (HX 52%nat 1%nat (fr_ptr fh) eq_refl). unfold cgif_vals. cbn [nth_error]. rewrite Hslot. reflexivity.
- rewrite H2 in Hslot |- *. change (Z.to_nat (51 + 2)) with 53%nat. change (Z.to_nat 2) with 2%nat in Hslot.
apply (HX 53%nat 2%nat (fr_ptr fh) eq_refl). unfold cgif_vals. cbn [nth_error]. rewrite Hslot. reflexivity. }
assert (HUfh : bv_unsigned (ew E (Z.to_nat (51 + cg_ihead s))) = fr_ptr fh) by (rewrite HXfh; apply unsigned_lit_small; lia).
assert (HR3 : region_ok ubs0segs E memc (af_Rfr_part (Z.to_nat (51 + cg_ihead s)) 68 0 40 0 0)).
{ eapply (af_Rfr_part_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) memc _ (fr_ptr fh) fh 68);
[exact HUfh | reflexivity | lia | lia | exact Hfobj | lia | intros j v Hj; rewrite Nat.sub_diag; exact Hj | lia | lia | intros k Hk; lia]. }
assert (HPD : forall z1, pairwise_disjoint E (ss_mem (ss_Bs (cg_ihead s) z1))).
{ intros z1. cbn [ss_mem ss_Bs]. unfold af_Rg, af_Rcf, af_Rfr_part. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU8, HU9, HUfh. clear - Hg1 Hf1 Hfg Hceil Hcflo HASv HGSv HFSv Hac. repeat split; lia. }
assert (HFA2 : atoms_ok E [(58%nat, mkAF 1 65535 0); (59%nat, mkAF 1 65535 0); (Z.to_nat (51 + cg_ihead s), mkAF 4096 (CEIL_MAX - 40) 4);
(11%nat, mkAF 0 4294967295 0); (69%nat, mkAF 4096 CEIL_MAX 0); (70%nat, mkAF 0 4294967295 0); (72%nat, mkAF 0 65535 0)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (HX 58%nat 7%nat _ eq_refl eq_refl), (HX 59%nat 8%nat _ eq_refl eq_refl), HUfh, (HE 11%nat 11%bv eq_refl), G11,
(HM 69%nat 1%nat (fr_img fh) eq_refl eq_refl), (HM 70%nat 2%nat (fr_attr fh) eq_refl eq_refl), (HM 72%nat 4%nat (fr_delay fh) eq_refl eq_refl).
rewrite !unsigned_lit_small by lia. change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
clear - RW RH HW1 HH1 Hf0 Hf1 Hf16 Hfi0 Hfi1 Rfa Rfd Rfattr HFSv HN HNle Hac. repeat split; try lia; nia. }
assert (HCF : forall z1 : bool, (if z1 then Z.land fattr 1 = 0 else Z.land fattr 1 <> 0) ->
conds_ok E [mkAC (if z1 then BC_EQ else BC_NE) (SAlu ALU_AND (SOff 11 0) (SLit 1)) (SLit 0)]).
{ intros z1 Hz1. cbn [conds_ok]. split; [|exact I]. unfold acond_ok.
destruct z1; cbn [ac_c ac_a ac_b]; rewrite ?branch_eq_U, ?branch_ne_U, U_and_lit, U_lit, (U_atom _ 11 fattr ltac:(rewrite (HE 11%nat 11%bv eq_refl); exact G11)) by lia;
[rewrite Hz1; reflexivity | destruct (Z.eqb_spec (Z.land fattr 1) 0); [lia | reflexivity]]. }
assert (MK : forall z1 : bool, (if z1 then Z.land fattr 1 = 0 else Z.land fattr 1 <> 0) ->
st_ok ubs0segs E (ss_Bs (cg_ihead s) z1) (mkst regs1 (Z_to_bv 64 AF_B) memc (seg_rom ubs0segs))).
{ intros z1 Hz1. unfold ss_Bs. apply entry_st_ok_full; [apply regs_ok_Ereg | destruct Hih as [H1|[H2 _]]; rewrite ?H1, ?H2; vm_compute; reflexivity | | exact (HPD z1) |].
- constructor; [exact HR0|]. constructor; [apply HR1; exact I|]. constructor; [exact HR2|]. constructor; [exact HR3|]. constructor.
- split; [apply atoms_ok_app; [exact HFA | exact HFA2]|]. split; [exact (HCF z1 Hz1) | exact I]. }
clear HR0 HR1 HR2 HR3 HPD HFA HFA2 HCF.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_B) memc (seg_rom ubs0segs))) in HJ.
assert (MEMRO : forall (E0 : env) rs (m m' : word -> option byte), all_ro rs = true -> frame_of E0 rs m m' -> forall a, mbyte ubs0segs m' a = mbyte ubs0segs m a).
{ intros E0 rs m m' Hro HFx a. unfold mbyte. rewrite (frame_of_ro E0 rs m m' Hro HFx). reflexivity. }
destruct (Z.eq_dec (Z.land fattr 1) 0) as [Hz1|Hz1].
+ pose proof (MK true Hz1) as HS. clear MK.
destruct Hih as [Hih1 | [Hih2 _]]; [rewrite Hih1 in HS, GO_C, GO_SF, HXfh, Hfh, XHDk | rewrite Hih2 in HS, GO_C, GO_SF, HXfh, Hfh, XHDk].
all: cbn [Z.to_nat Z.add Pos.add Pos.succ Pos.to_nat Pos.iter_op Nat.add Z.mul Pos.mul] in HS, GO_C, GO_SF, HXfh, Hfh, XHDk.
all: jrun_to LAWS ubs0tbl_ok HS HJ AF_C; [apply RO4; cbn; lia|]; cbn [ms_mem mkst] in HF; clear HG.
all: assert (K0 : forall a, mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs memc a) by
(intros a; unfold mbyte; lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end; reflexivity).
all: clear HF.
all: pose proof (HC 48%nat 4%nat delay eq_refl eq_refl) as HC48; pose proof (HM 72%nat 4%nat (fr_delay fh) eq_refl eq_refl) as HM72.
all: assert (Ufd : U E (SAlu ALU_ADD (SOff 48 0) (SOff 72 0)) = delay + YO07.f_delay HD)
by (rewrite <- FRd; apply (U_add_smallAF E _ _ delay (fr_delay fh) (U_atom _ 48 delay HC48 ltac:(clear - Rdelay; lia)) (U_atom _ 72 (fr_delay fh) HM72 ltac:(clear - Rfd; lia))); clear - Rdelay Rfd; lia).
all: jbranch ubs0tbl HS; rewrite branch_ne_U, U_lit, (U_srl_litAF E _ 16), Ufd in Hc by lia; change (2 ^ 16) with 65536 in Hc.
all: first
[ assert (FDGT : 65535 < delay + YO07.f_delay HD) by (destruct (Z_lt_le_dec (delay + YO07.f_delay HD) 65536) as [l|l]; [rewrite (Z.div_small (delay + YO07.f_delay HD) 65536 ltac:(clear - l Rdelay Rfd FRd; lia)) in Hc; discriminate Hc | clear - l; lia]); clear Hc;
jrun_to LAWS ubs0tbl_ok HS HJ AF_C; [apply RO4; cbn; lia|]; cbn [ms_mem mkst] in HF; clear HG; roK HF K0 K1 memc; exact (GO_C (frame_vals fh) _ _ _ HS (env_agree_refl _ _) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (af_merged_none_fd (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs (Z.to_nat (cg_ihead s)) HD XihN Hih3 XHD FDGT) HJ K1)
| assert (XFD : delay + YO07.f_delay HD <= 65535) by (destruct (Z_lt_le_dec (delay + YO07.f_delay HD) 65536) as [l|l]; [clear - l; lia | exfalso; pose proof (Z.div_le_lower_bound (delay + YO07.f_delay HD) 65536 1 ltac:(clear; lia) ltac:(clear - l; lia)) as D1; destruct (Z.eqb_spec ((delay + YO07.f_delay HD) / 65536) 0) as [Q0|Q0]; [clear - D1 Q0; lia | discriminate Hc]]); clear Hc ].
all: jrun_to LAWS ubs0tbl_ok HS HJ AF_SLOW; [apply RO4; cbn; lia|]; cbn [ms_mem mkst] in HF; clear HG; roK HF K0 K1 memc.
all: pose proof (HX 57%nat 6%nat (cg_gen s) eq_refl eq_refl) as HX57.
all: jbranch ubs0tbl HS; rewrite branch_ne_U, U_and_lit, U_lit, U_zext, (U_atom _ 57 (cg_gen s) HX57) in Hc by (clear - Rgen; lia); change (2 ^ Z.of_N 8) with (2 ^ 8) in Hc;
replace (Z.land (cg_gen s mod 2 ^ 8) 1) with (Z.land (cg_gen s) 1) in Hc by (rewrite <- (Z.land_ones (cg_gen s) 8) by (clear; lia); rewrite <- Z.land_assoc; change (Z.land (Z.ones 8) 1) with 1; reflexivity).
all: first
[ assert (GEN1 : Z.land (cg_gen s) 1 <> 0) by (intros Z0; rewrite Z0 in Hc; discriminate Hc); clear Hc;
jrun_to LAWS ubs0tbl_ok HS HJ AF_C; [apply RO4; cbn; lia|]; cbn [ms_mem mkst] in HF; clear HG; roK HF K1 K2 memc; exact (GO_C (frame_vals fh) _ _ _ HS (env_agree_refl _ _) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (af_merged_none_keep (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs ltac:(apply (proj2 (flag1_true_iff _)); exact GEN1)) HJ K2)
| assert (XKEEP : Z.land (cg_gen s) 1 = 0) by (destruct (Z.eqb_spec (Z.land (cg_gen s) 1) 0) as [Z0|Z0]; [exact Z0 | discriminate Hc]); clear Hc ].
all: jrun_to LAWS ubs0tbl_ok HS HJ AF_SLOW; [apply RO4; cbn; lia|]; cbn [ms_mem mkst] in HF; clear HG; roK HF K1 K2 memc.
all: pose proof (HM 70%nat 2%nat (fr_attr fh) eq_refl eq_refl) as HM70.
all: assert (U19 : U E (SOff 19 0) = Z.land fattr 4) by (apply U_atom; [rewrite (HE 19%nat 19%bv eq_refl); exact G19 | pose proof (land_le fattr 4 ltac:(clear - Rfattr; lia)); split; [apply Z.land_nonneg; clear - Rfattr; lia | clear - H Rfattr; lia]]).
all: assert (U70 : U E (SAlu ALU_AND (SOff 70 0) (SLit 5)) = Z.land (fr_attr fh) 5) by (rewrite U_and_lit, (U_atom _ 70 (fr_attr fh) HM70) by (clear - Rfa; lia); reflexivity).
all: pose proof (land_le fattr 4 ltac:(clear - Rfattr; lia)) as L4; pose proof (land_le (fr_attr fh) 5 ltac:(clear - Rfa; lia)) as L5.
all: assert (N4 : 0 <= Z.land fattr 4) by (apply Z.land_nonneg; clear - Rfattr; lia); assert (N5 : 0 <= Z.land (fr_attr fh) 5) by (apply Z.land_nonneg; clear - Rfa; lia).
all: jbranch ubs0tbl HS; rewrite branch_eq_U, U_lit, (U_or_smallAF E _ _ _ _ U19 U70 N4 N5 ltac:(clear - L4 L5; lia)) in Hc by (clear; lia).
all: first
[ pose proof (proj1 (Z.lor_eq_0_iff _ _) (proj1 (Z.eqb_eq _ _) Hc)) as [F4 F5]; pose proof (proj1 (land5_eq0_iff _) F5) as [F1' F4']; clear Hc;
jrun_to LAWS ubs0tbl_ok HS HJ AF_FAST; [apply RO4; cbn; lia|]; cbn [ms_mem mkst] in HF; clear HG; roK HF K2 K3 memc;
exact (GO_SF fh _ _ _ AF_FAST HD (SAlu ALU_ADD (SOff 48 0) (SOff 72 0)) HS (env_agree_refl _ _) eq_refl eq_refl (or_intror eq_refl) XHDk XFD XKEEP eq_refl ltac:(rewrite Ufd; apply Z.mod_small; clear - XFD Rdelay Rfd FRd; lia)
ltac:(unfold YO07.flag; rewrite <- FRa, (proj2 (Z.eqb_eq _ _) Hz1), (proj2 (Z.eqb_eq _ _) F4), (proj2 (Z.eqb_eq _ _) F1'), (proj2 (Z.eqb_eq _ _) F4'); reflexivity)
Hfh HXfh eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ K3)
| assert (LNZ : Z.lor (Z.land fattr 4) (Z.land (fr_attr fh) 5) <> 0) by (intros Z0; rewrite Z0 in Hc; discriminate Hc); clear Hc;
jrun_to LAWS ubs0tbl_ok HS HJ AF_SLOW; [apply RO4; cbn; lia|]; cbn [ms_mem mkst] in HF; clear HG; roK HF K2 K3 memc;
exact (GO_SF fh _ _ _ AF_SLOW HD (SAlu ALU_ADD (SOff 48 0) (SOff 72 0)) HS (env_agree_refl _ _) eq_refl eq_refl (or_introl eq_refl) XHDk XFD XKEEP eq_refl ltac:(rewrite Ufd; apply Z.mod_small; clear - XFD Rdelay Rfd FRd; lia)
ltac:(unfold YO07.flag; rewrite <- FRa, (proj2 (Z.eqb_eq _ _) Hz1); cbn [negb];
destruct (Z.eqb_spec (Z.land fattr 4) 0) as [F4|F4]; destruct (Z.eqb_spec (Z.land (fr_attr fh) 1) 0) as [F1'|F1']; destruct (Z.eqb_spec (Z.land (fr_attr fh) 4) 0) as [F4'|F4']; cbn [negb andb]; try reflexivity;
exfalso; apply LNZ; apply (proj2 (Z.lor_eq_0_iff _ _)); split; [exact F4 | apply (proj2 (land5_eq0_iff _)); split; assumption])
Hfh HXfh eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ K3) ].
+ pose proof (MK false Hz1) as HS. clear MK.
destruct Hih as [Hih1 | [Hih2 _]]; [rewrite Hih1 in HS, GO_C, GO_SF, HXfh, Hfh, XHDk | rewrite Hih2 in HS, GO_C, GO_SF, HXfh, Hfh, XHDk].
all: cbn [Z.to_nat Z.add Pos.add Pos.succ Pos.to_nat Pos.iter_op Nat.add Z.mul Pos.mul] in HS, GO_C, GO_SF, HXfh, Hfh, XHDk.
all: jrun_to LAWS ubs0tbl_ok HS HJ AF_C; [apply RO4; cbn; lia|]; cbn [ms_mem mkst] in HF; clear HG.
all: assert (K0 : forall a, mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs memc a) by
(intros a; unfold mbyte; lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end; reflexivity).
all: clear HF.
all: pose proof (HC 48%nat 4%nat delay eq_refl eq_refl) as HC48; pose proof (HM 72%nat 4%nat (fr_delay fh) eq_refl eq_refl) as HM72.
all: assert (Ufd : U E (SAlu ALU_ADD (SOff 48 0) (SOff 72 0)) = delay + YO07.f_delay HD)
by (rewrite <- FRd; apply (U_add_smallAF E _ _ delay (fr_delay fh) (U_atom _ 48 delay HC48 ltac:(clear - Rdelay; lia)) (U_atom _ 72 (fr_delay fh) HM72 ltac:(clear - Rfd; lia))); clear - Rdelay Rfd; lia).
all: jbranch ubs0tbl HS; rewrite branch_ne_U, U_lit, (U_srl_litAF E _ 16), Ufd in Hc by lia; change (2 ^ 16) with 65536 in Hc.
all: first
[ assert (FDGT : 65535 < delay + YO07.f_delay HD) by (destruct (Z_lt_le_dec (delay + YO07.f_delay HD) 65536) as [l|l]; [rewrite (Z.div_small (delay + YO07.f_delay HD) 65536 ltac:(clear - l Rdelay Rfd FRd; lia)) in Hc; discriminate Hc | clear - l; lia]); clear Hc;
jrun_to LAWS ubs0tbl_ok HS HJ AF_C; [apply RO4; cbn; lia|]; cbn [ms_mem mkst] in HF; clear HG; roK HF K0 K1 memc; exact (GO_C (frame_vals fh) _ _ _ HS (env_agree_refl _ _) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (af_merged_none_fd (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs (Z.to_nat (cg_ihead s)) HD XihN Hih3 XHD FDGT) HJ K1)
| assert (XFD : delay + YO07.f_delay HD <= 65535) by (destruct (Z_lt_le_dec (delay + YO07.f_delay HD) 65536) as [l|l]; [clear - l; lia | exfalso; pose proof (Z.div_le_lower_bound (delay + YO07.f_delay HD) 65536 1 ltac:(clear; lia) ltac:(clear - l; lia)) as D1; destruct (Z.eqb_spec ((delay + YO07.f_delay HD) / 65536) 0) as [Q0|Q0]; [clear - D1 Q0; lia | discriminate Hc]]); clear Hc ].
all: jrun_to LAWS ubs0tbl_ok HS HJ AF_SLOW; [apply RO4; cbn; lia|]; cbn [ms_mem mkst] in HF; clear HG; roK HF K0 K1 memc.
all: pose proof (HX 57%nat 6%nat (cg_gen s) eq_refl eq_refl) as HX57.
all: jbranch ubs0tbl HS; rewrite branch_ne_U, U_and_lit, U_lit, U_zext, (U_atom _ 57 (cg_gen s) HX57) in Hc by (clear - Rgen; lia); change (2 ^ Z.of_N 8) with (2 ^ 8) in Hc;
replace (Z.land (cg_gen s mod 2 ^ 8) 1) with (Z.land (cg_gen s) 1) in Hc by (rewrite <- (Z.land_ones (cg_gen s) 8) by (clear; lia); rewrite <- Z.land_assoc; change (Z.land (Z.ones 8) 1) with 1; reflexivity).
all: first
[ assert (GEN1 : Z.land (cg_gen s) 1 <> 0) by (intros Z0; rewrite Z0 in Hc; discriminate Hc); clear Hc;
jrun_to LAWS ubs0tbl_ok HS HJ AF_C; [apply RO4; cbn; lia|]; cbn [ms_mem mkst] in HF; clear HG; roK HF K1 K2 memc; exact (GO_C (frame_vals fh) _ _ _ HS (env_agree_refl _ _) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (af_merged_none_keep (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs ltac:(apply (proj2 (flag1_true_iff _)); exact GEN1)) HJ K2)
| assert (XKEEP : Z.land (cg_gen s) 1 = 0) by (destruct (Z.eqb_spec (Z.land (cg_gen s) 1) 0) as [Z0|Z0]; [exact Z0 | discriminate Hc]); clear Hc ].
all: jrun_to LAWS ubs0tbl_ok HS HJ AF_SLOW; [apply RO4; cbn; lia|]; cbn [ms_mem mkst] in HF; clear HG; roK HF K1 K2 memc;
exact (GO_SF fh _ _ _ AF_SLOW HD (SAlu ALU_ADD (SOff 48 0) (SOff 72 0)) HS (env_agree_refl _ _) eq_refl eq_refl (or_introl eq_refl) XHDk XFD XKEEP eq_refl ltac:(rewrite Ufd; apply Z.mod_small; clear - XFD Rdelay Rfd FRd; lia)
ltac:(unfold YO07.flag; replace (Z.land fattr 1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hz1); reflexivity)
Hfh HXfh eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ K2).
-
assert (XMN : af_merged (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs = None).
{ apply (af_merged_none_empty (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs (Z.to_nat (cg_ihead s)) XihN Hih3).
apply (proj1 (oframe_relb_occ _ _ _ _ _ (XSL (Z.to_nat (cg_ihead s)) Hih3 I))). exact Hslot. }
set (E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s []).
destruct (Hspf []) as (HU2 & HU8 & HU9 & HR0 & HR2 & HFA & HR1). fold E in HU2, HU8, HU9, HR0, HR2, HFA, HR1.
assert (HPD : pairwise_disjoint E (ss_mem (ss_Bn (cg_ihead s)))).
{ cbn [ss_mem ss_Bn]. destruct Hih as [H1|[H2 _]]; rewrite ?H1, ?H2; cbn [Z.eqb Pos.eqb]; unfold af_Rg, af_Rcf; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val];
rewrite HU2, HU8, HU9; clear - Hg1 Hceil Hcflo HASv HGSv Hac; repeat split; lia. }
assert (HS : st_ok ubs0segs E (ss_Bn (cg_ihead s)) (mkst regs1 (Z_to_bv 64 AF_B) memc (seg_rom ubs0segs))).
{ unfold ss_Bn. apply entry_st_ok_full; [apply regs_ok_Ereg | destruct Hih as [H1|[H2 _]]; rewrite ?H1, ?H2; vm_compute; reflexivity | | exact HPD | split; [exact HFA | split; exact I]].
constructor; [exact HR0|]. constructor; [| constructor; [exact HR2 | constructor]].
destruct Hih as [H1|[H2 Hn1]]; rewrite ?H1, ?H2 in Hslot, HR1 |- *; cbn [Z.eqb Pos.eqb]; apply HR1; try exact I; rewrite Hfr in Hslot; try change (Z.to_nat 1) with 1%nat in Hslot; try change (Z.to_nat 2) with 2%nat in Hslot; cbn [nth] in Hslot; rewrite Hslot; reflexivity. }
clear HR0 HR1 HR2 HPD HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_B) memc (seg_rom ubs0segs))) in HJ.
destruct Hih as [Hih1 | [Hih2 _]]; [rewrite Hih1 in HS, GO_C | rewrite Hih2 in HS, GO_C]; cbn [Z.eqb Pos.eqb] in HS.
* jrun_to LAWS ubs0tbl_ok HS HJ AF_C. { apply RO3. cbn. lia. }
apply (GO_C [] _ _ _ HS (env_agree_refl _ _) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl XMN HJ).
intros a. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity.
* jrun_to LAWS ubs0tbl_ok HS HJ AF_C. { apply RO3. cbn. lia. }
apply (GO_C [] _ _ _ HS (env_agree_refl _ _) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl XMN HJ).
intros a. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
