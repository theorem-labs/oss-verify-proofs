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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b YI06 UI5b YI09 YI08 YI0r UI1w UI4l UI21 UI2m UI5o UI5l YI6b UI5n UI20 UI1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI1n UI1e UI1f UI1c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI01 UI3u UI22 YI5a UI5d YI0f YI2w UI2v YI0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25 UI2n UI1x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0b UI1o YI1m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Notation inFP_nil := YI04.inFP_nil (only parsing).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition AF_CF : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0x2a8).
Definition AF_FREED : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0x2d0).
Definition ss_CF : sstate :=
mkSS AF_CF sr_atoms [ YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) ; af_Rg None None None None ] None (mkFacts af_facts [] []).
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis FLUSHX : flushX_spec API.
Lemma af_CF :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (rest FP : list (Z * Z))
(o0 : option frame_st) (f1 f2 : frame_st) (cfp lpal lpa img fattr fgen delay nlp tidx t4 : Z)
(GPAL IMGv LPALv : list Z) (gs : YO07.gif_st) (brb : rbound),
let sp0 := spZ regs0 in
let CB := (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) in
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
cg_frames s = [o0; Some f1; Some f2] ->
(Z.land fattr 1 = 0 -> Z.land (cg_attr s) 4 = 0) ->
obj_at ubs0segs memc cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
cfp mod 8 = 0 -> sp0 <= cfp -> cfp + 32 <= 2 ^ 63 ->
Z_to_bv 64 lpa = Z_to_bv 64 lpal ->
(forall b n a, In (b, n) (cgif_blocks0 g s N) -> b <= a < b + n -> inFP FP a) ->
Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 64) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 cfp ->
getr regs1 19 = Z_to_bv 64 t4 -> 0 <= t4 < 2 ^ 64 ->
af_untouched regs0 regs1 ->
cg_gen s = cg_gen s0 -> cg_file s = cg_file s0 -> t4 = Z.land fattr 4 ->
af_sink g s0 s N rest FP (concat (YO07.s_out gs)) L A mem md -> (forall a, inFP (cgif_fp g s0 N) a -> a < alloc_ceiling) ->
Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N <= SINK_MAX -> spZ regs0 <= 2 ^ 47 ->
cgif_live gs -> rc_int (cg_cur s) = YO07.s_cur gs -> af_live memc s N GPAL gs ->
garr8 ubs0segs memc img IMGv -> Z.of_nat (length IMGv) = N ->
(Z.land fattr 1 <> 0 -> garr8 ubs0segs memc lpa LPALv /\ Z.of_nat (length LPALv) = 3 * nlp) ->
res_ok Ac brb -> af_room brb N ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_CF) memc (seg_rom ubs0segs)) mdc)
(af_postX API regs0 g N s0 CB rest GPAL gs (af_rest (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) (af_rb brb N (qcount gs) (qcount (af_rest (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs))) L A mem md).
Proof using FLUSHX IMG.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP o0 f1 f2 cfp lpal lpa img fattr fgen delay nlp tidx t4 GPAL IMGv LPALv gs brb sp0 CB
HJ Hid Hra0 Hal16 Htp0 Hat Hwf Hgeom Hfr HnoCT Hcf Hcf8 Hcflo Hcfhi Hlpa HFP HB HSV G2 G8 G9 G23 Rt4 HUT
Xgen Xfile Xt4 XSK XLOW XMAX Xsp47 XLV XCUR XLIVE XIMG0 XIL XLPA XRq XROOM.
pose proof XSK as (XSK1 & XSK2 & XFIN & XSK4 & XSK5 & HFPX).
pose proof (proj1 (af_live_iff _ _ _ _ _) XLIVE) as ((XHrc & XHra & XHih & XHgp) & XSL).
pose proof (XSL 0%nat ltac:(lia) I) as XS0. pose proof (XSL 1%nat ltac:(lia) I) as XS1. pose proof (XSL 2%nat ltac:(lia) I) as XS2.
rewrite Hfr in XS0, XS1, XS2. cbn [nth wgk qslot] in XS0, XS1, XS2.
destruct (YO07.s_q1 gs) as [F1|] eqn:Hq1; [| destruct XS1]. destruct (YO07.s_q2 gs) as [F2|] eqn:Hq2; [| destruct XS2]. cbn [oframe_relb] in XS1, XS2.
assert (Hih12 : cg_ihead s = 1 \/ cg_ihead s = 2) by (pose proof Hwf as (_ & _ & _ & _ & _ & _ & Hih & _); clear - Hih; lia).
assert (Xi0 : af_i0 gs = 3).
{ unfold af_i0, YO07.q_get. rewrite <- XHih, Hq2. destruct Hih12 as [E1|E2]; rewrite E1 || rewrite E2; cbn; rewrite ?Hq1, ?Hq2; reflexivity. }
pose proof (af_rest_full (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs F1 Xi0 Hq1) as XREST.
set (FPw := FP ++ sink_fp (cg_file s)).
assert (HFPw : forall a, inFP (cgif_fp g s N) a -> inFP FPw a /\ a < alloc_ceiling).
{ intros a Ha. subst FPw. unfold cgif_fp in Ha. apply inFP_cons in Ha. destruct Ha as [Ha|Ha].
- split; [apply (proj2 (inFP_app _ _ _)); right; unfold sink_fp; apply (proj2 (inFP_cons _ _ _ _)); left; exact Ha | unfold sink_token in Ha; cbn [fst snd] in Ha; pose proof (proj1 alloc_ceiling_val); lia].
- apply inFP_blocks_fp in Ha as (bb & nn & Hbn & Hab). unfold cgif_blocks in Hbn. cbn [app] in Hbn.
assert (Hbn' : In (bb, nn) (cgif_blocks0 g s N) \/ (bb, nn) = (cg_file s, FILE_BLOCK)).
{ unfold cgif_blocks0. cbn [app]. destruct Hbn as [H0|[H0|[H0|H0]]]; [left; left | left; right; left | right; symmetry | left; right; right]; exact H0. }
destruct Hbn' as [Hbn'|Hbn'].
+ split; [apply (proj2 (inFP_app _ _ _)); left; exact (HFP bb nn a Hbn' Hab)|].
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) ltac:(apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hbn')). lia.
+ injection Hbn' as -> ->. split; [apply (proj2 (inFP_app _ _ _)); right; unfold sink_fp; apply (proj2 (inFP_cons _ _ _ _)); right; apply (proj2 (inFP_cons _ _ _ _)); left; cbn [fst snd]; exact Hab|].
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) ltac:(apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; right; apply in_app_iff; right; exact XFIN)). lia. }
assert (HFPwsub : forall a, inFP FPw a -> inFP (cgif_fp g s0 N) a).
{ intros a Ha. subst FPw. apply (proj1 (inFP_app _ _ _)) in Ha. destruct Ha as [Ha|Ha]; [exact (HFPX a Ha)|].
unfold sink_fp in Ha. apply inFP_cons in Ha. unfold cgif_fp. apply (proj2 (inFP_cons _ _ _ _)). destruct Ha as [Ha|Ha]; [left; exact Ha | right].
apply inFP_cons in Ha. destruct Ha as [Ha|Ha]; [| exfalso; exact (inFP_nil _ Ha)]. apply (proj2 (inFP_blocks_fp _ _)). exists (cg_file s0), FILE_BLOCK.
split; [unfold cgif_blocks; right; right; left; reflexivity | rewrite <- Xfile; cbn [fst snd] in Ha; exact Ha]. }
pose proof HUT as (G3 & G4 & U23 & U24 & U25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
assert (HFLv : FLUSH_STK = 9216) by reflexivity. assert (HFFv : FREEFRAME_STK = 8208) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & _).
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N _ HH0 HB) as (_ & _ & (Hg0 & Hg1 & Hg16)).
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (HFPg : forall a, g <= a < g + CGIF_SIZE -> inFP FP a) by (intros a Ha; apply (HFP g CGIF_SIZE a); [left; reflexivity | exact Ha]).
assert (HFPlow : forall a, inFP (blocks_fp (cgif_blocks0 g s N)) a -> inFP FP a /\ a < alloc_ceiling).
{ intros a Ha. apply inFP_blocks_fp in Ha as (b & n & Hbn & Hab). split; [exact (HFP b n a Hbn Hab)|].
destruct (blocks_range _ _ LAWS Lc Ac memc mdc b n HH0 ltac:(apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hbn)) as [_ R1]. lia. }
pose proof Hat as (Hobj & Hraw & Hfrs).
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
assert (Ho1 : nth_error (cg_frames s) 1 = Some (Some f1)) by (rewrite Hfr; reflexivity).
assert (Ho2 : nth_error (cg_frames s) 2 = Some (Some f2)) by (rewrite Hfr; reflexivity).
set (E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s []).
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HK regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (af_HX regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HX.
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HR0 : region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32))).
{ pose proof (af_Rstk_ok _ memc sp0 regs0 32 HU2 ltac:(lia) ltac:(lia) HSV (fun j v Hj => HK _ j v eq_refl Hj) (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4]. }
pose proof (af_Rg_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s [] memc g None None None None HU8 ltac:(lia) ltac:(lia) Hobj I I I I) as HR1.
assert (HPD : pairwise_disjoint E (ss_mem ss_CF)).
{ cbn [ss_mem ss_CF]. unfold af_Rg. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU8. clear - Hg1 Hceil HASv HGSv Hac. repeat split; lia. }
assert (HFA : atoms_ok E af_facts).
{ cbn [atoms_ok af_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, (HE 9%nat 9%bv eq_refl), G9, unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia.
replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HS : st_ok ubs0segs E ss_CF (mkst regs1 (Z_to_bv 64 AF_CF) memc (seg_rom ubs0segs))).
{ unfold ss_CF. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | exact HPD | split; [exact HFA | split; exact I]].
constructor; [exact HR0|]. constructor; [exact HR1|]. constructor. }
clear HR0 HR1 HPD HFA.
assert (Hspm : (sp0 - 64) mod 16 = 0) by (replace (sp0 - 64) with (sp0 + (-4) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_CF) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_flushFrame. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hm10. jreg HS (11%bv:reg) as Hm11. jreg HS (12%bv:reg) as Hm12.
jreg HS (2%bv:reg) as Hm2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hm2.
jreg HS (4%bv:reg) as Hm4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hm4. jreg HS (1%bv:reg) as Hm1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 64) by (unfold spZ; rewrite Hm2; apply unsigned_lit_small; lia) end.
cbn [ms_mem mkst] in HF.
assert (K1 : forall a, mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs memc a).
{ intros a. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF.
assert (HSKc : sink_at ubs0_msyms (ms_mem ms) mdc (cg_file s) (concat (YO07.s_out gs)))
by exact (proj1 (af_sink_at API ADDFRAME_STK sp0 g s0 s N rest FP _ L A mem md Lc Ac (ms_mem ms) mdc HJ XSK)).
destruct (in_split _ _ XFIN) as (rl1 & rl2 & Hrest).
assert (HBf1 : Permutation (blocks Lc Ac) (cgif_blocks g s N ++ (CB ++ rl1 ++ rl2))).
{ eapply Permutation_trans; [exact HB|]. rewrite Hrest. eapply Permutation_trans; [| apply Permutation_sym; apply cgif_blocks0_perm].
apply Permutation_app_head. rewrite !app_assoc. apply Permutation_sym.
change ((cg_file s, FILE_BLOCK) :: (CB ++ rl1) ++ rl2) with ((cg_file s, FILE_BLOCK) :: ((CB ++ rl1) ++ rl2)). apply Permutation_middle. }
assert (Rrw : 0 <= rw_cur s < 2 ^ 32) by (pose proof (obj_at_range _ _ _ _ _ (proj1 (proj2 Hat)) 8%nat (rw_cur s) eq_refl) as X; exact X).
apply (journal_fp_weaken API _ _ FP FPw) in HJ; [| intros a Ha; subst FPw; apply (proj2 (inFP_app _ _ _)); left; exact Ha].
eapply SR_bind with (R := fun c' => exists L2 A2 regs2 mem2 md2 (r rwcur' code : Z) (bytes : list Z),
c' = mkCfg (mkst regs2 (Z_to_bv 64 (ubs0_A_cgif_addframe + 0x2c0)) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR ADDFRAME_STK sp0 FPw L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\ st_init_done A2 = true /\ getr regs2 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
cgif_at mem2 g (flush_upd s 1 (fl_gen3 (gcfg_of s GPAL) F1 (YO07.s_q0 gs)) rwcur') /\ cgif_wf (flush_upd s 1 (fl_gen3 (gcfg_of s GPAL) F1 (YO07.s_q0 gs)) rwcur') N /\
Permutation (blocks L2 A2) (cgif_blocks0 g s N ++ CB ++ rest) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 64 - FLUSH_STK <= x < sp0 - 64) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem ms) x /\ (writable_at ubs0segs (ms_mem ms) x <-> writable_at ubs0segs mem2 x)) /\
YO07.flush_frame (gcfg_of s GPAL) (rc_int (rw_cur s)) F1 (YO07.s_q0 gs) = (code, bytes) /\ Z_to_bv 64 r = Z_to_bv 64 code /\ rwcur' = code mod 2 ^ 32 /\
sink_at ubs0_msyms mem2 md2 (cg_file s) (concat (YO07.s_out gs) ++ bytes) /\ Z.of_nat (length bytes) <= FRAME_OUT N /\ res_ok A2 (flush_rb brb) /\
(forall a n k, In (a, n) (blocks Lc Ac) -> (a, n) <> (cg_file s, FILE_BLOCK) -> 0 <= k < n ->
~ (a = cg_raw s /\ 40 <= k < 44) -> ~ (a = fr_ptr f1 /\ 20 <= k < 24) ->
mbyte ubs0segs mem2 (a + k) = mbyte ubs0segs (ms_mem ms) (a + k))).
{ eapply SR_mono.
{ eapply (jcall ubs0_msyms MR) with (STK1 := FLUSH_STK) (FP1 := cgif_fp g s N)
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => exists (r rwcur' code : Z) (bytes : list Z),
st_init_done A2 = true /\ getr regs2 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
cgif_at mem2 g (flush_upd s 1 (fl_gen3 (gcfg_of s GPAL) F1 (YO07.s_q0 gs)) rwcur') /\ cgif_wf (flush_upd s 1 (fl_gen3 (gcfg_of s GPAL) F1 (YO07.s_q0 gs)) rwcur') N /\
Permutation (blocks L2 A2) (cgif_blocks0 g s N ++ CB ++ rest) /\
YO07.flush_frame (gcfg_of s GPAL) (rc_int (rw_cur s)) F1 (YO07.s_q0 gs) = (code, bytes) /\ Z_to_bv 64 r = Z_to_bv 64 code /\ rwcur' = code mod 2 ^ 32 /\
sink_at ubs0_msyms mem2 md2 (cg_file s) (concat (YO07.s_out gs) ++ bytes) /\ Z.of_nat (length bytes) <= FRAME_OUT N /\ res_ok A2 (flush_rb brb) /\
(forall a n k, In (a, n) (blocks Lc Ac) -> (a, n) <> (cg_file s, FILE_BLOCK) -> 0 <= k < n ->
~ (a = cg_raw s /\ 40 <= k < 44) -> ~ (a = fr_ptr f1 /\ 20 <= k < 24) ->
mbyte ubs0segs mem2 (a + k) = mbyte ubs0segs (ms_mem ms) (a + k)));
[ exact HS | reflexivity | exact HJ | exact Hm1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FLUSH_STK; lia | rewrite Hsp; unfold FLUSH_STK; lia | rewrite Hsp; lia | exact Hm4 | exact HFPw ].
intros HPRE1. eapply SR_mono.
{ eapply (FLUSHX Lc Ac _ _ mdc g s N 1%nat f1 (CB ++ rl1 ++ rl2) (concat (YO07.s_out gs)) GPAL F1 (YO07.s_q0 gs) brb HPRE1 Hid);
[ exact HSKc | exact XMAX | rewrite Hsp; clear - Xsp47; lia | | | exact Hwf | left; reflexivity | exact Ho1 | | | exact HBf1 | | | | exact XHra | exact XRq
| apply af_room_flush; [clear - HN HW1 HH1; nia | exact XROOM] ].
- rewrite Hm10, (HE 8%nat 8%bv eq_refl). exact G8.
- eapply (cgif_at_kept0 memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros bb n k Hb Hk; apply K1].
- rewrite Hm11, (HX 52%nat 1%nat _ eq_refl eq_refl), Hfr. reflexivity.
- rewrite Hm12, (HX 51%nat 0%nat _ eq_refl eq_refl). reflexivity.
- intros Hz. destruct (XHgp Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg | intros a _; apply K1].
- apply (frame_relb_kept true memc); [intros; apply K1 | intros; apply K1 | exact XS1].
- rewrite Hfr. cbn [nth]. destruct o0 as [f0|]; destruct (YO07.s_q0 gs) as [F0|]; cbn [oframe_relb oframe_rel0] in XS0 |- *;
[ apply (frame_relb_kept false memc); [intros; apply K1 | intros; apply K1 | exact XS0] | destruct XS0 | destruct XS0 | exact I ]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & r & rwcur' & -> & HJc & HP & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2 & (code & bytes & Hff & Hrc & Hrw & HSK2 & Hlenb) & HR2 & Hkeepv).
exists L2, A2, regs2, mem2, md2. split; [rewrite Hm1; reflexivity|]. split; [exact HJc|]. split; [exact HP|].
exists r, rwcur', code, bytes. repeat (split; [assumption|]).
split; [| repeat (split; [assumption|]); exact Hkeepv].
eapply Permutation_trans; [exact HB2|]. eapply Permutation_trans; [apply cgif_blocks0_perm|]. apply Permutation_app_head. rewrite Hrest, !app_assoc.
change ((cg_file s, FILE_BLOCK) :: (CB ++ rl1) ++ rl2) with ((cg_file s, FILE_BLOCK) :: ((CB ++ rl1) ++ rl2)). apply Permutation_middle. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (r & rwcur' & code & bytes & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2 & Hrestc)).
exists L2, A2, regs2, mem2, md2, r, rwcur', code, bytes. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
repeat (split; [assumption|]). split; [| exact Hrestc].
pose proof HJc2 as (_ & _ & Hhi2 & _). rewrite Hsp in Hhi2. exact Hhi2. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & r & rwcur' & code & bytes & -> & HJ2 & HP2 & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2 & Hhi2 & Hff & Hrc & Hrw & HSK2 & Hlenb & HR2 & Hkeepv). clear HJ.
set (gen' := fl_gen3 (gcfg_of s GPAL) F1 (YO07.s_q0 gs)) in *.
cbn [ms_regs ms_mem mkst] in HP2, Hhi2, HJ2, Hr10, Hat2, Hkeepv.
rename HJ2 into HJw. pose proof (journal_restart API ADDFRAME_STK sp0 FPw FP _ _ _ _ _ _ _ _ HJw) as HJ2.
rewrite XHrc in Hff. rewrite Hff in XREST. cbv beta iota zeta in XREST.
assert (Hrc' : (if negb (YO07.s_rcur gs =? YO07.R_OK) && negb (YO07.s_rcur gs =? YO07.R_PENDING) then YO07.s_rcur gs else code) = code).
{ destruct (negb (YO07.s_rcur gs =? YO07.R_OK) && negb (YO07.s_rcur gs =? YO07.R_PENDING)) eqn:ED; [| reflexivity].
pose proof (flush_frame_dead (gcfg_of s GPAL) (YO07.s_rcur gs) F1 (YO07.s_q0 gs) ED) as D. rewrite Hff in D. injection D as D1 D2. symmetry. exact D1. }
rewrite Hrc' in XREST. clear Hrc'.
assert (Hcode : - 2 ^ 31 <= code < 2 ^ 31 /\ (code <> YO07.C_OK -> code <> YO07.C_PENDING)).
{ pose proof (rc_int_range (rw_cur s) Rrw) as Rrc. rewrite XHrc in Rrc.
destruct (negb (YO07.s_rcur gs =? YO07.R_OK) && negb (YO07.s_rcur gs =? YO07.R_PENDING)) eqn:ED.
- pose proof (flush_frame_dead (gcfg_of s GPAL) (YO07.s_rcur gs) F1 (YO07.s_q0 gs) ED) as D. rewrite Hff in D. injection D as Ec Eb.
apply andb_prop in ED as [E1 E2]. unfold YO07.R_OK, YO07.R_PENDING, YO07.C_OK, YO07.C_PENDING in *.
destruct (Z.eqb_spec (YO07.s_rcur gs) 0); [discriminate E1|]. destruct (Z.eqb_spec (YO07.s_rcur gs) 6); [discriminate E2|]. clear - Rrc Ec n n0. lia.
- destruct (flush_frame_code_live (gcfg_of s GPAL) _ _ _ _ _ Hff ED) as [Ec|[Ec|Ec]]; rewrite Ec; unfold YO07.R_ERROR, YO07.R_EINDEX, YO07.R_OK, YO07.C_OK, YO07.C_PENDING; lia. }
assert (Hr64 : r = code mod 2 ^ 64).
{ rewrite <- (unsigned_lit_small r) by lia. rewrite Hrc, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity. }
assert (Hr0iff : r = 0 <-> code = 0).
{ rewrite Hr64. split; intros E0.
- destruct (Z_lt_le_dec code 0); [| rewrite Z.mod_small in E0 by (clear - Hcode l; lia); exact E0].
replace (code mod 2 ^ 64) with (code + 2 ^ 64) in E0 by (symmetry; rewrite <- (Z.mod_add code 1 (2 ^ 64)) by lia; apply Z.mod_small; clear - Hcode l; lia). clear - E0 Hcode l. lia.
- rewrite E0. reflexivity. }
assert (Hfin2 : In (cg_file s, FILE_BLOCK) (blocks L2 A2)) by (apply (Permutation_in _ (Permutation_sym HB2)); apply in_app_iff; right; apply in_app_iff; right; exact XFIN).
set (s1 := flush_upd s 1 gen' rwcur') in *.
set (f1' := set_fr_gen f1 gen').
assert (Hvals1 : cgif_vals s1 = cgif_vals s) by (subst s1; apply cgif_vals_flush_upd).
assert (Hblk1 : cgif_blocks0 g s1 N = cgif_blocks0 g s N) by (subst s1; apply flush_upd_blocks0; rewrite Hlen; lia).
assert (Hfr1 : cg_frames s1 = [o0; Some f1'; Some f2]) by (subst s1 f1'; apply frames_flush_upd1; exact Hfr).
assert (Hgeom1 : same_geom s1 s0) by (subst s1; exact Hgeom).
assert (HB2' : Permutation (blocks L2 A2) (cgif_blocks0 g s1 N ++ CB ++ rest)) by (rewrite Hblk1; exact HB2).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
assert (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
pose proof Hat2 as (Hobj2 & Hraw2 & Hfrs2). rewrite Hvals1 in Hobj2.
jafter_call_keep HS 68%nat regs2 mem2 HP2 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor]. eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi2 | lia | lia | unfold FLUSH_STK; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq72. cbn [ms_regs mkst] in Hq72. rewrite Hr10 in Hq72. symmetry in Hq72.
af_add_region HS (af_Rg None None None None).
2:{ apply (af_Rg_okE _ mem2 g s None None None None); try exact I; [ew_havocA; exact HU8 | lia | lia | exact Hobj2 | apply (HX_havoc _ s); [exact HX | lia]]. }
2:{ cbn [ss_mem all_disjoint]. unfold af_Rg, extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, HU8. clear - Hg1 Hceil HASv HGSv Hac. repeat split; lia. }
jrun_to LAWS ubs0tbl_ok HS HJ2 ubs0_A_freeFrame. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hf10. rewrite (HX 51%nat 0%nat _ eq_refl eq_refl), Hfr in Hf10. cbn [nth] in Hf10.
jreg HS (2%bv:reg) as Hf2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hf2.
jreg HS (4%bv:reg) as Hf4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hf4. jreg HS (1%bv:reg) as Hf1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp2 : spZ (ms_regs msx) = sp0 - 64) by (unfold spZ; rewrite Hf2; apply unsigned_lit_small; lia) end.
cbn [ms_mem mkst] in HF.
assert (K2 : forall a, mbyte ubs0segs (ms_mem ms0) a = mbyte ubs0segs mem2 a).
{ intros a. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF.
set (s2 := set_frames s1 [None; Some f1'; Some f2]).
assert (HB2s : Permutation (blocks L2 A2) (match o0 with Some f0 => frame_blocks N f0 | None => [] end ++ cgif_blocks0 g s2 N ++ CB ++ rest)).
{ subst s2. destruct o0 as [f0|].
- eapply Permutation_trans; [exact HB2'|]. apply (perm_frame0_front0 g s1 N f0 (Some f1') (Some f2) (CB ++ rest) Hfr1).
- cbn [app]. eapply Permutation_trans; [exact HB2'|]. unfold cgif_blocks0. rewrite Hfr1. cbn [cg_raw cg_frames set_frames]. rewrite pal_blocks_set_frames. apply Permutation_refl. }
assert (Hcg2 : forall b n, In (b, n) (cgif_blocks0 g s2 N ++ CB ++ rest) -> In (b, n) (blocks L2 A2)).
{ intros b n Hbn. apply (Permutation_in _ (Permutation_sym HB2s)). apply in_app_iff. right. exact Hbn. }
assert (Hcgr2 : forall b n, In (b, n) (cgif_blocks0 g s2 N ++ CB ++ rest) -> 4096 <= b /\ b + n <= alloc_ceiling).
{ intros b n Hbn. exact (blocks_range _ _ LAWS L2 A2 mem2 md2 b n HH2 (Hcg2 b n Hbn)). }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
eapply SR_bind with (R := fun c' => exists L3 A3 regs3 mem3 md3,
c' = mkCfg (mkst regs3 (Z_to_bv 64 AF_FREED) mem3 (seg_rom ubs0segs)) md3 /\
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L2 A2 mem2 md2 L3 A3 mem3 md3 /\
regs_preserved (ms_regs msx) regs3 /\ st_init_done A3 = true /\
res_ok A3 (match o0 with Some _ => rb_free (flush_rb brb) N | None => flush_rb brb end) /\
Permutation (blocks L3 A3) (cgif_blocks0 g s2 N ++ CB ++ rest) /\
(forall b n i, In (b, n) (cgif_blocks0 g s2 N ++ CB ++ rest) -> 0 <= i < n -> mbyte ubs0segs mem3 (b + i) = mbyte ubs0segs (ms_mem msx) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 64 - FREEFRAME_STK <= x < sp0 - 64) ->
mbyte ubs0segs mem3 x = mbyte ubs0segs (ms_mem msx) x /\ (writable_at ubs0segs (ms_mem msx) x <-> writable_at ubs0segs mem3 x)))
end.
{ destruct o0 as [f0|].
-
assert (Hf0in : In (Some f0) (cg_frames s1)) by (rewrite Hfr1; left; reflexivity).
assert (Hf0in0 : In (Some f0) (cg_frames s)) by (rewrite Hfr; left; reflexivity).
eapply SR_mono.
{ eapply (jcall ubs0_msyms MR) with (STK1 := FREEFRAME_STK) (FP1 := fp_freeFrame (fr_ptr f0) (fr_img f0) N (fr_attr f0) (fr_lpal f0) (3 * fr_nlp f0))
(K := fun L3 A3 (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) => Permutation (blocks L3 A3) (cgif_blocks0 g s2 N ++ CB ++ rest) /\ st_init_done A3 = true /\ res_ok A3 (rb_free (flush_rb brb) N));
[ exact HS | reflexivity | exact HJ2 | exact Hf1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp2; exact Hspm | unfold FREEFRAME_STK; lia | rewrite Hsp2; unfold FREEFRAME_STK; lia | rewrite Hsp2; lia | exact Hf4 | ].
+ intros HPRE1. eapply SR_mono.
{ eapply (ubs0_freeFrame_resc API IMG _ _ _ _ _ (fr_ptr f0) (frame_vals f0) (fr_img f0) N (fr_attr f0) (fr_lpal f0) (3 * fr_nlp f0) (cgif_blocks0 g s2 N ++ CB ++ rest) (flush_rb brb) HPRE1);
[ exact Hf10 | | reflexivity | reflexivity | reflexivity | | exact HR2 ].
- eapply obj_at_transport_range; [exact (Hfrs2 f0 Hf0in) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply K2].
- eapply Permutation_trans; [exact HB2s|]. unfold frame_blocks, pals_of. cbn [app]. apply Permutation_refl. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJc & HP & HB3 & Hid3x & HR3).
exists L3, A3, regs3, mem3, md3. split; [rewrite Hf1; reflexivity|]. split; [exact HJc|]. split; [exact HP | split; [exact HB3 | split; [exact Hid3x | exact HR3]]].
+ intros a Ha. split; [| apply HFPlow; apply inFP_blocks_fp].
all: unfold fp_freeFrame in Ha; apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[first [ apply (HFP (fr_ptr f0) FRAME_SIZE a); [apply (frame_blocks_in_cgif0 g s N f0); [exact Hf0in0 | left; reflexivity] | unfold FRAME_SIZE; lia]
| exists (fr_ptr f0), FRAME_SIZE; split; [apply (frame_blocks_in_cgif0 g s N f0); [exact Hf0in0 | left; reflexivity] | unfold FRAME_SIZE; lia] ] |];
apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[first [ apply (HFP (fr_img f0) N a); [apply (frame_blocks_in_cgif0 g s N f0); [exact Hf0in0 | right; left; reflexivity] | lia]
| exists (fr_img f0), N; split; [apply (frame_blocks_in_cgif0 g s N f0); [exact Hf0in0 | right; left; reflexivity] | lia] ] |];
(destruct (Z.land (fr_attr f0) 1 =? 0) eqn:Hz; [exfalso; exact (inFP_nil a Ha)|]);
apply inFP_cons in Ha; (destruct Ha as [Ha|Ha]; [|exfalso; exact (inFP_nil a Ha)]);
first [ apply (HFP (fr_lpal f0) (3 * fr_nlp f0) a); [apply (frame_blocks_in_cgif0 g s N f0); [exact Hf0in0|]; unfold frame_blocks; rewrite Hz; right; right; left; reflexivity | lia]
| exists (fr_lpal f0), (3 * fr_nlp f0); split; [apply (frame_blocks_in_cgif0 g s N f0); [exact Hf0in0|]; unfold frame_blocks; rewrite Hz; right; right; left; reflexivity | lia] ]. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HB3 & Hid3x & HR3).
exists L3, A3, regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact HP3|].
split; [exact Hid3x|]. split; [exact HR3|]. split; [exact HB3|].
pose proof HJc3 as (_ & _ & Hhi3 & Hkeep3 & _). rewrite Hsp2 in Hhi3. split; [| exact Hhi3].
intros b n i Hbn Hi.
assert (HsepR : forall x, In x (frame_blocks N f0) -> fst x + snd x <= b \/ b + n <= fst x).
{ intros x Hx. pose proof (heap_sep_app API L2 A2 mem2 md2 (frame_blocks N f0) (cgif_blocks0 g s2 N ++ CB ++ rest) x (b, n) HH2 HB2s Hx Hbn) as Hs. cbn [fst snd] in Hs. exact Hs. }
apply (Hkeep3 b n i); [exact (Hcg2 b n Hbn) | eapply blocks_perm_in; [exact HB3 |]; destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right; exact Hbn] | exact Hi |].
intros Hin. unfold fp_freeFrame in Hin. apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [pose proof (HsepR _ ltac:(left; reflexivity)) as HS1; cbn [fst snd] in HS1, Hin; first [clear - Hin Hi HS1; lia | cbn [fst snd] in *; lia]|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [pose proof (HsepR _ ltac:(right; left; reflexivity)) as HS2; cbn [fst snd] in HS2, Hin; first [clear - Hin Hi HS2; lia | cbn [fst snd] in *; lia]|].
destruct (Z.land (fr_attr f0) 1 =? 0) eqn:Hz; [exact (inFP_nil _ Hin)|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [| exact (inFP_nil _ Hin)].
pose proof (HsepR (fr_lpal f0, 3 * fr_nlp f0) ltac:(unfold frame_blocks; rewrite Hz; right; right; left; reflexivity)) as HS3. cbn [fst snd] in HS3, Hin. first [clear - Hin Hi HS3; lia | cbn [fst snd] in *; lia].
-
eapply SR_mono.
{ eapply (jcall ubs0_msyms MR) with (STK1 := FREEFRAME_STK) (FP1 := @nil (Z * Z))
(K := fun L3 A3 (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) => A3 = A2 /\ Permutation (blocks L3 A3) (cgif_blocks0 g s2 N ++ CB ++ rest));
[ exact HS | reflexivity | exact HJ2 | exact Hf1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp2; exact Hspm | unfold FREEFRAME_STK; lia | rewrite Hsp2; unfold FREEFRAME_STK; lia | rewrite Hsp2; lia | exact Hf4
| intros a Ha; exfalso; exact (inFP_nil a Ha) ].
intros HPRE1. eapply SR_mono.
{ eapply (ubs0_freeFrame_null API IMG _ _ _ _ _ HPRE1). exact Hf10. }
cbv beta. intros c' (regs3 & mem3 & -> & HJc & HP).
exists L2, A2, regs3, mem3, md2. split; [rewrite Hf1; reflexivity|]. split; [exact HJc|]. split; [exact HP|]. split; [reflexivity|]. cbn [app] in HB2s. exact HB2s. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & -> & HB3).
exists L3, A2, regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact HP3|]. split; [exact Hid2|]. split; [exact HR2|]. split; [exact HB3|].
pose proof HJc3 as (_ & _ & Hhi3 & Hkeep3 & _). rewrite Hsp2 in Hhi3. split; [| exact Hhi3].
intros b n i Hbn Hi. apply (Hkeep3 b n i); [exact (Hcg2 b n Hbn) | eapply blocks_perm_in; [exact HB3 |]; destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right; exact Hbn] | exact Hi | intros Hin; exact (inFP_nil _ Hin)]. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hid3 & HR3 & HB3 & Hkeep3 & Hhi3). clear HJ2.
cbn [ms_regs ms_mem mkst] in HP3, Hkeep3, Hhi3, HJ3.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HH3.
assert (Hgin3 : In (g, CGIF_SIZE) (blocks L3 A3)) by (eapply blocks_perm_in; [exact HB3 | left; reflexivity]).
jafter_call_keep HS 84%nat regs3 mem3 HP3 [1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor]. eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi3 | lia | lia | unfold FREEFRAME_STK; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ((exists b m, In (b, m) (cgif_blocks0 g s2 N ++ CB ++ rest) /\ b <= a < b + m) \/ sp0 - 64 <= a) ->
mbyte ubs0segs mem3 a = mbyte ubs0segs mem2 a).
{ intros a Ha Hw. rewrite <- (K2 a). destruct Hw as [(b & m & Hbm & Hab) | Hw].
- replace a with (b + (a - b)) by lia. apply (Hkeep3 b m (a - b) Hbm). lia.
- apply (proj1 (Hhi3 a ltac:(clear - Ha Hw Hceil HASv Hac; lia) ltac:(clear - Hw; lia))). }
assert (Hobj3 : obj_at ubs0segs mem3 g LAY_CGIF (cgif_vals s)).
{ eapply obj_at_transport_range; [exact Hobj2 | exact (proj1 LAY_CGIF_ok) |]. intros k Hk. apply K3; [clear - Hk Hg0 Hg1 HGSv Hac; lia | left; exists g, CGIF_SIZE; split; [left; reflexivity | lia]]. }
af_add_region HS (af_Rg_part 24 96 0 0 None None None None).
2:{ apply (af_Rg_part_okE _ mem3 g s None None None None); try exact I; [ew_havocA; exact HU8 | lia | lia | exact Hobj3 | apply (HX_havoc _ s); [apply (HX_havoc _ s); [exact HX | lia] | lia] | lia | lia | intros k Hk; lia]. }
2:{ cbn [ss_mem all_disjoint]. unfold af_Rg_part, extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, HU8. clear - Hg1 Hceil HASv HGSv Hac. repeat split; lia. }
af_add_region HS (af_Rg_part 0 24 0 24 None None None None).
2:{ apply (af_Rg_part_okE _ mem3 g s None None None None); try exact I; [ew_havocA; exact HU8 | lia | lia | exact Hobj3 | apply (HX_havoc _ s); [apply (HX_havoc _ s); [exact HX | lia] | lia] | lia | lia |].
intros k Hk. apply (present_writable ubs0_msyms). apply (proj1 (heap_blocks _ _ LAWS L3 A3 mem3 md3 g CGIF_SIZE k HH3 Hgin3 ltac:(lia))). }
2:{ cbn [ss_mem all_disjoint]. unfold af_Rg_part, extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, HU8. clear - Hg1 Hceil HASv HGSv Hac. repeat split; lia. }
jrun LAWS ubs0tbl_ok HS HJ3.
{ eapply wr_ok_cons_block with (m := CGIF_SIZE); [ reflexivity | ew_havocA; exact HU8 | exact Hgin3 | cbn; lia | cbn; lia | cbn [r_wlo r_whi]; intros a Ha; apply HFPg; lia | ].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
pose proof Hwf2 as (Hlen2 & _ & _ & _ & _ & _ & Hih2 & Hfwf2).
assert (Hrawin : In (cg_raw s, RAW_SIZE) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; right; left; reflexivity).
assert (HfinC : In (cg_file s, FILE_BLOCK) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; right; apply in_app_iff; right; exact XFIN).
assert (KVX : forall mX, (forall a, 0 <= a < 2 ^ 64 -> (a < g \/ g + 24 <= a) -> mbyte ubs0segs mX a = mbyte ubs0segs mem3 a) ->
forall a n k, In (a, n) (blocks Lc Ac) -> In (a, n) (cgif_blocks0 g s2 N ++ CB ++ rest) ->
(cg_raw s + RAW_SIZE <= a \/ a + n <= cg_raw s) -> (fr_ptr f1 + FRAME_SIZE <= a \/ a + n <= fr_ptr f1) ->
(cg_file s + FILE_BLOCK <= a \/ a + n <= cg_file s) -> (g + CGIF_SIZE <= a \/ a + n <= g) ->
0 <= k < n -> mbyte ubs0segs mX (a + k) = mbyte ubs0segs memc (a + k)).
{ intros mX K4 a n k Hin Hin2 Y1 Y2 Yf Y3 Hk. assert (HFBv : FILE_BLOCK = 1264) by reflexivity.
destruct (blocks_range _ _ LAWS Lc Ac memc mdc a n HH0 Hin) as [R0 R1].
rewrite (K4 (a + k)); [| clear - Hk R0 R1 Hac; lia | clear - Hk Y3 HGSv; lia].
rewrite (K3 (a + k)); [| clear - Hk R0 R1 Hac; lia | left; exists a, n; split; [exact Hin2 | clear - Hk; lia]].
rewrite <- (K1 (a + k)). apply (Hkeepv a n k Hin); [intros Heq; injection Heq as E1 E2; clear - E1 E2 Yf Hk HFBv; lia | exact Hk | clear - Y1 Hk HRSv; lia | clear - Y2 Hk HFSv; lia]. }
assert (VSEP : forall a n, In (a, n) (pal_blocks s ++ flat_map (af_fvb N) [Some f1; Some f2]) ->
In (a, n) (blocks Lc Ac) /\ In (a, n) (cgif_blocks0 g s2 N ++ CB ++ rest) /\
(cg_raw s + RAW_SIZE <= a \/ a + n <= cg_raw s) /\ (fr_ptr f1 + FRAME_SIZE <= a \/ a + n <= fr_ptr f1) /\
(cg_file s + FILE_BLOCK <= a \/ a + n <= cg_file s) /\ (g + CGIF_SIZE <= a \/ a + n <= g)).
{ intros a n Hin.
assert (Ivb : In (a, n) (af_vblocks s N)).
{ rewrite af_vblocks_eq, Hfr. apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left; exact Hin | right]. cbn [flat_map] in Hin |- *. apply in_app_iff. right. exact Hin. }
pose proof (af_vblocks_sub0 s N _ Ivb) as I0.
assert (Ic : In (a, n) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; unfold cgif_blocks0; right; right; exact I0).
split; [exact Ic|]. split.
{ apply in_app_iff. left. subst s2 s1. unfold cgif_blocks0. cbn [cg_raw cg_frames set_frames flush_upd]. rewrite pal_blocks_set_frames. right. right.
apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left; exact Hin | right].
apply (af_fvb_sub N [None; Some f1'; Some f2]). subst f1'. cbn [flat_map af_fvb fr_img fr_attr fr_lpal fr_nlp set_fr_gen app] in Hin |- *. exact Hin. }
split. { pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (cg_raw s, RAW_SIZE) ((g, CGIF_SIZE) :: (pal_blocks s ++ frames_blocks N (cg_frames s)) ++ CB ++ rest) (a, n) HH0
ltac:(eapply Permutation_trans; [exact HB | unfold cgif_blocks0; cbn [app]; apply perm_swap]) ltac:(right; apply in_app_iff; left; exact I0)) as Y. cbn [fst snd] in Y. exact Y. }
split. { exact (af_frame_vsep0 API Lc Ac memc mdc g s N (CB ++ rest) 1%nat f1 a n HH0 HB Ho1 Ivb). }
split. { exact (fl_file_sep API Lc Ac memc mdc g s N [] (CB ++ rest) a n HH0 HB ltac:(apply in_app_iff; right; exact XFIN) ltac:(unfold cgif_blocks0; right; right; exact I0)). }
pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (g, CGIF_SIZE) ((cg_raw s, RAW_SIZE) :: (pal_blocks s ++ frames_blocks N (cg_frames s)) ++ CB ++ rest) (a, n) HH0 HB ltac:(right; apply in_app_iff; left; exact I0)) as Y. cbn [fst snd] in Y. exact Y. }
assert (CSEP : forall a n, In (a, n) CB ->
In (a, n) (blocks Lc Ac) /\ In (a, n) (cgif_blocks0 g s2 N ++ CB ++ rest) /\
(cg_raw s + RAW_SIZE <= a \/ a + n <= cg_raw s) /\ (fr_ptr f1 + FRAME_SIZE <= a \/ a + n <= fr_ptr f1) /\
(cg_file s + FILE_BLOCK <= a \/ a + n <= cg_file s) /\ (g + CGIF_SIZE <= a \/ a + n <= g)).
{ intros a n Hin.
assert (Ic : In (a, n) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; right; apply in_app_iff; left; exact Hin).
split; [exact Ic|]. split; [apply in_app_iff; right; apply in_app_iff; left; exact Hin|].
assert (SEP : forall y, In y (cgif_blocks0 g s N) -> fst y + snd y <= a \/ a + n <= fst y).
{ intros y Hy. pose proof (heap_sep_app API Lc Ac memc mdc (cgif_blocks0 g s N) (CB ++ rest) y (a, n) HH0 HB Hy ltac:(apply in_app_iff; left; exact Hin)) as Y. cbn [fst snd] in Y. exact Y. }
split; [exact (SEP _ ltac:(right; left; reflexivity))|].
split; [exact (SEP _ ltac:(unfold cgif_blocks0; right; right; apply in_app_iff; right; apply af_frames_blocks_ptr_in; rewrite Hfr; right; left; reflexivity))|].
split; [| exact (SEP _ ltac:(left; reflexivity))].
pose proof (heap_sep_app API Lc Ac memc mdc (cgif_blocks0 g s N ++ CB) rest (a, n) (cg_file s, FILE_BLOCK) HH0 ltac:(rewrite <- app_assoc; exact HB) ltac:(apply in_app_iff; right; exact Hin) XFIN) as Y.
cbn [fst snd] in Y. clear - Y. lia. }
assert (Hf1'in : In (Some f1') (cg_frames s1)) by (rewrite Hfr1; right; left; reflexivity).
assert (Hf2in : In (Some f2) (cg_frames s1)) by (rewrite Hfr1; right; right; left; reflexivity).
assert (Hwf_s2 : cgif_wf s2 N).
{ subst s2. apply cgif_wf_set_frames; [exact Hwf2 | reflexivity | | intros f [Hf|[Hf|[Hf|[]]]]; try discriminate Hf; injection Hf as <-; apply Hfwf2; assumption].
destruct Hih2 as [H1|[H2 _]]; [left; exact H1 | right; split; [exact H2 | discriminate]]. }
assert (Hwf_s3 : cgif_wf (set_frames s1 [Some f1'; Some f2; None]) N).
{ apply cgif_wf_set_frames; [exact Hwf2 | reflexivity | | intros f [Hf|[Hf|[Hf|[]]]]; try discriminate Hf; injection Hf as <-; apply Hfwf2; assumption].
destruct Hih2 as [H1|[H2 _]]; [left; exact H1 | right; split; [exact H2 | discriminate]]. }
assert (Hrin2 : In (cg_raw s, RAW_SIZE) (cgif_blocks0 g s2 N ++ CB ++ rest)) by (right; left; subst s2 s1; reflexivity).
assert (Hf1blk : In (fr_ptr f1, FRAME_SIZE) (cgif_blocks0 g s2 N ++ CB ++ rest)).
{ apply in_app_iff. left. apply (frame_blocks_in_cgif0 g s2 N f1'); [subst s2; right; left; reflexivity | left; reflexivity]. }
assert (Hf2blk : In (fr_ptr f2, FRAME_SIZE) (cgif_blocks0 g s2 N ++ CB ++ rest)).
{ apply in_app_iff. left. apply (frame_blocks_in_cgif0 g s2 N f2); [subst s2; right; right; left; reflexivity | left; reflexivity]. }
destruct (af_cgif_geom0 API L2 A2 mem2 md2 g s1 N _ HH2 HB2') as ((Hr0 & Hr1 & Hrg1) & Hfgeom1 & _).
destruct (Hfgeom1 f1' Hf1'in) as (F10 & F11 & F1g). destruct (Hfgeom1 f2 Hf2in) as (F20 & F21 & F2g). cbn [f1' fr_ptr set_fr_gen] in F10, F11, F1g.
assert (OBJ : forall ssX msX (fr : list (option frame_st)) e0 e1 e2 rg,
st_ok ubs0segs (havoc (havoc E 68 (map (getr regs2) CLOB)) 84 (map (getr regs3) CLOB)) ssX msX ->
nth_error (ss_mem ssX) 0 = Some rg -> r_base rg = Some 8%nat ->
In (mkChunk 0 (CVal 8 e0)) (r_chunks rg) -> In (mkChunk 8 (CVal 8 e1)) (r_chunks rg) -> In (mkChunk 16 (CVal 8 e2)) (r_chunks rg) ->
(forall a, 0 <= a < 2 ^ 64 -> (a < g \/ g + 24 <= a) -> mbyte ubs0segs (ms_mem msX) a = mbyte ubs0segs mem3 a) ->
length fr = 3%nat ->
sv_denot (havoc (havoc E 68 (map (getr regs2) CLOB)) 84 (map (getr regs3) CLOB)) e0 = Z_to_bv 64 (frame_ptr (nth 0 fr None)) ->
sv_denot (havoc (havoc E 68 (map (getr regs2) CLOB)) 84 (map (getr regs3) CLOB)) e1 = Z_to_bv 64 (frame_ptr (nth 1 fr None)) ->
sv_denot (havoc (havoc E 68 (map (getr regs2) CLOB)) 84 (map (getr regs3) CLOB)) e2 = Z_to_bv 64 (frame_ptr (nth 2 fr None)) ->
(forall k, (k < 3)%nat -> 0 <= frame_ptr (nth k fr None) < 2 ^ 64) ->
(forall f, In (Some f) fr -> In (Some f) (cg_frames s2)) ->
cgif_at (ms_mem msX) g (set_frames s1 fr)).
{ intros ssX msX fr e0 e1 e2 rg HSX Hrg Hrb C0 C1 C2 KX Hlfr D0 D1 D2 Rfr Hsub.
assert (HU8X : bv_unsigned (ew (havoc (havoc E 68 (map (getr regs2) CLOB)) 84 (map (getr regs3) CLOB)) 8) = g) by (ew_havocA; exact HU8).
split; [|split].
- rewrite cgif_vals_set_frames, Hvals1.
eapply (obj_at_upd ubs0segs mem3 (ms_mem msX) g LAY_CGIF CGIF_SIZE (cgif_vals s) _ [0%nat; 1%nat; 2%nat] [(0, 24)] Hobj3 (proj1 LAY_CGIF_ok));
[vm_compute; reflexivity | reflexivity | | |].
+ intros k Hk Hw. apply in_wins_cons_false in Hw as [W1 _]. apply KX; clear - Hk W1 Hg0 Hg1 HGSv Hac; lia.
+ intros j f v [<-|[<-|[<-|[]]]] Hf Hv; cbn in Hf, Hv; injection Hf as <-; injection Hv as <-; rewrite <- HU8X.
* eapply (st_field ubs0segs _ _ _ 0%nat _ 8%nat _ 0 8%N e0 _ HSX Hrg Hrb C0); [reflexivity | exact D0 | apply (Rfr 0%nat); lia | cbn; lia].
* eapply (st_field ubs0segs _ _ _ 0%nat _ 8%nat _ 8 8%N e1 _ HSX Hrg Hrb C1); [reflexivity | exact D1 | apply (Rfr 1%nat); lia | cbn; lia].
* eapply (st_field ubs0segs _ _ _ 0%nat _ 8%nat _ 16 8%N e2 _ HSX Hrg Hrb C2); [reflexivity | exact D2 | apply (Rfr 2%nat); lia | cbn; lia].
+ intros j Hj. destruct j as [|[|[|j]]]; [exfalso; apply Hj; cbv; auto | exfalso; apply Hj; cbv; auto | exfalso; apply Hj; cbv; auto |]. reflexivity.
- rewrite raw_vals_set_frames, cg_raw_set_frames.
eapply obj_at_transport_range; [exact Hraw2 | exact (proj1 LAY_Raw_ok) |]. subst s1. cbn [cg_raw flush_upd] in *.
intros k Hk. rewrite (KX (cg_raw s + k)); [| clear - Hk Hr0 Hr1 HRSv Hac; lia | clear - Hk Hrg1 HRSv HGSv; lia].
apply K3; [clear - Hk Hr0 Hr1 HRSv Hac; lia | left; exists (cg_raw s), RAW_SIZE; split; [exact Hrin2 | lia]].
- rewrite cg_frames_set_frames. intros f Hf. pose proof (Hsub f Hf) as Hfs2. subst s2. rewrite cg_frames_set_frames in Hfs2.
destruct Hfs2 as [Hx|[Hx|[Hx|[]]]]; [discriminate Hx | injection Hx as <- | injection Hx as <-].
+ eapply obj_at_transport_range; [exact (Hfrs2 f1' Hf1'in) | exact (proj1 LAY_Frame_ok) |]. cbn [f1' fr_ptr set_fr_gen].
intros k Hk. rewrite (KX (fr_ptr f1 + k)); [| clear - Hk F10 F11 HFSv Hac; lia | clear - Hk F1g HFSv HGSv; lia].
apply K3; [clear - Hk F10 F11 HFSv Hac; lia | left; exists (fr_ptr f1), FRAME_SIZE; split; [exact Hf1blk | lia]].
+ eapply obj_at_transport_range; [exact (Hfrs2 f2 Hf2in) | exact (proj1 LAY_Frame_ok) |].
intros k Hk. rewrite (KX (fr_ptr f2 + k)); [| clear - Hk F20 F21 HFSv Hac; lia | clear - Hk F2g HFSv HGSv; lia].
apply K3; [clear - Hk F20 F21 HFSv Hac; lia | left; exists (fr_ptr f2), FRAME_SIZE; split; [exact Hf2blk | lia]]. }
pose proof (Rg 1%nat _ eq_refl) as R52. pose proof (Rg 2%nat _ eq_refl) as R53. rewrite Hfr in R52, R53. cbn [nth snd LAY_CGIF Z.of_N frame_ptr] in R52, R53.
assert (Hm32 : (code mod 2 ^ 64) mod 2 ^ 32 = code mod 2 ^ 32).
{ destruct (Z_lt_le_dec code 0); [| rewrite (Z.mod_small code (2 ^ 64)) by (clear - Hcode l; lia); reflexivity].
replace (code mod 2 ^ 64) with (code + 2 ^ 32 * 2 ^ 32) by (symmetry; rewrite <- (Z.mod_add code 1 (2 ^ 64)) by lia; apply Z.mod_small; clear - Hcode l; lia).
apply Z.mod_add. lia. }
jbranch ubs0tbl HS.
-
assert (Xcode : code <> YO07.C_OK).
{ intros Ec. exfalso. revert Hc. cbn [sv_denot]. ew_havocA. rewrite ?Z.add_0_r, ?Hq72, (unsigned_lit_small r) by (clear - Hr; lia).
replace r with 0 by (symmetry; apply (proj2 Hr0iff); exact Ec). cbn. rewrite (proj2 (bv_eqb_eq _ _) eq_refl). cbn. intros HH. first [discriminate HH | exact (HH eq_refl)]. }
clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ3 AF_RETC.
{ wr_norm. eapply wr_ok_cons_block with (m := CGIF_SIZE); [ reflexivity | ew_havocA; exact HU8 | exact Hgin3 | cbn; lia | cbn; lia | cbn [r_wlo r_whi]; intros a Ha; apply HFPg; lia | ].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HF0.
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> (a < g \/ g + 24 <= a) -> mbyte ubs0segs (ms_mem ms2) a = mbyte ubs0segs mem3 a).
{ intros a Ha W1. clear - HF HF0 Ha W1 HU2 HU8. mb_frame_with HF0 ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8; lia).
mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity. }
pose proof (OBJ _ _ [None; Some f1'; Some f2] (SLit 0) (SOff 52 0) (SOff 53 0) _ HS eq_refl eq_refl ltac:(cbv; auto 10) ltac:(cbv; auto 10) ltac:(cbv; auto 10) K4 eq_refl eq_refl) as Hat4.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
rewrite XREST. replace (code =? YO07.C_OK) with false by (symmetry; apply Z.eqb_neq; exact Xcode).
eapply SR_mono; [| cbv beta; intros c' Hc'; exact (af_postX_rebase API regs0 g N s0 CB rest GPAL gs _ _ L A mem md L2 A2 mem2 md2 FPw c' HJw HFPwsub XLOW Hc')].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ => assert (Hg18 : getr rg 18 = Z_to_bv 64 r) end.
{ reg_nowG HS ltac:(idtac). rewrite Hq72, (unsigned_lit_small r) by (clear - Hr; lia). reflexivity. }
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (af_ret_cur API IMG L2 A2 mem2 md2 regs0 rg L3 A3 mm md3 g N s0 s2 CB rest FP GPAL gs
(YO07.mkS None (YO07.s_q1 gs) (YO07.s_q2 gs) (YO07.s_ihead gs) code code (YO07.s_out gs))
(af_rb brb N (qcount gs) (qcount (YO07.mkS None (YO07.s_q1 gs) (YO07.s_q2 gs) (YO07.s_ihead gs) code code (YO07.s_out gs))))) end;
[ exact HJ3 | exact Hid3 | exact Hra0 | exact Hal16 | exact HFPg | | exact Hwf_s2 | subst s2; exact Hgeom1 | exact HB3 | | | |
| etransitivity; [| exact Xgen]; subst s2 s1; reflexivity | etransitivity; [| exact Xfile]; subst s2 s1; reflexivity | exact HFPX
|   rewrite Hg18, unsigned_lit_small by (clear - Hr; lia); cbn [YO07.s_cur]; rewrite Hr64, Hm32; apply rc_int_mod32; clear - Hcode; lia
|   unfold cgif_occ; subst s2; cbn [cg_frames set_frames nth YO07.s_q0 YO07.s_q1 YO07.s_q2]; rewrite Hq1, Hq2; repeat split; intros HH; first [reflexivity | discriminate HH]
|   cbn [YO07.s_out]; rewrite (flush_frame_fail_nil (gcfg_of s GPAL) _ _ _ _ _ Hff Xcode), app_nil_r in HSK2;
exact (proj1 (af_sink_at API ADDFRAME_STK sp0 g s0 s2 N rest FP _ L2 A2 mem2 md2 _ _ _ _ HJ3 (conj HSK2 (conj Hfin2 (conj XFIN (conj XSK4 (conj XSK5 HFPX)))))))
| exact XFIN
|   intros HL; exfalso; cbn [cgif_live YO07.s_cur] in HL; destruct HL as [HL|HL]; [exact (Xcode HL) | exact (proj2 Hcode Xcode HL)]
|   cbn [YO07.s_out]; unfold FRAME_OUT; clear - HN HW1 HH1; nia
|   rewrite !qcount_slots; cbn [qslot YO07.s_q0 YO07.s_q1 YO07.s_q2 ocnt]; rewrite Hq1, Hq2; cbn [ocnt];
destruct o0 as [f0|]; destruct (YO07.s_q0 gs) as [F0|]; cbn [oframe_relb] in XS0; try (exfalso; exact XS0); cbn [ocnt Z.add];
[ pose proof (af_rb_failed_evicted brb N 3 ltac:(clear - HN HW1 HH1; nia)) as Y; cbn [Z.sub Z.add Z.pos_sub] in Y; exact (res_ok_mono _ _ _ Y HR3)
| exact (res_ok_mono _ _ _ (af_rb_flushed_same brb N 2 ltac:(clear - HN HW1 HH1; nia)) HR3) ] ].
+ apply Hat4.
* cbn [nth frame_ptr f1' fr_ptr set_fr_gen sv_denot]. ew_havocA. rewrite Z.add_0_r, (HX 52%nat 1%nat _ eq_refl eq_refl), Hfr, Z_to_bv_bv_unsigned. reflexivity.
* cbn [nth frame_ptr sv_denot]. ew_havocA. rewrite Z.add_0_r, (HX 53%nat 2%nat _ eq_refl eq_refl), Hfr, Z_to_bv_bv_unsigned. reflexivity.
* intros k Hk. destruct k as [|[|[|k]]]; cbn [nth frame_ptr f1' fr_ptr set_fr_gen]; lia.
* intros f Hf. exact Hf.
+ apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha. rewrite K4; [| clear - Ha Hceil Hsp063 HASv Hac; lia | clear - Ha Hceil Hg1 HASv HGSv; lia].
rewrite K3; [| clear - Ha Hceil Hsp063 HASv Hac; lia | right; clear - Ha; lia].
rewrite (proj1 (Hhi2 a ltac:(clear - Ha Hceil Hsp063 HASv Hac; lia) ltac:(clear - Ha; lia))). apply K1.
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 2%nat 2%bv eq_refl); exact G2).
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 8%nat 8%bv eq_refl); exact G8).
+ split; [|split; [|split; [|split; [|split; [|split]]]]].
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact U23).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact U24).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact U25).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27).
-
assert (Xcode : code = YO07.C_OK).
{ apply (proj1 Hr0iff). revert Hc. cbn [sv_denot]. ew_havocA. rewrite ?Z.add_0_r, ?Hq72, (unsigned_lit_small r) by (clear - Hr; lia). cbn.
destruct (bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 0)) eqn:Eb; cbn; intros HH;
[ apply bv_eqb_eq in Eb; apply (f_equal bv_unsigned) in Eb; rewrite !unsigned_lit_small in Eb by (clear - Hr; lia); exact Eb
| exfalso; first [discriminate HH | exact (HH eq_refl)] ]. }
clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ3 AF_D.
{ wr_norm. eapply wr_ok_cons_block with (m := CGIF_SIZE); [ reflexivity | ew_havocA; exact HU8 | exact Hgin3 | cbn; lia | cbn; lia | cbn [r_wlo r_whi]; intros a Ha; apply HFPg; lia | ].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HF0.
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> (a < g \/ g + 24 <= a) -> mbyte ubs0segs (ms_mem ms2) a = mbyte ubs0segs mem3 a).
{ intros a Ha W1. clear - HF HF0 Ha W1 HU2 HU8. mb_frame_with HF0 ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8; lia).
mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity. }
pose proof (OBJ _ _ [Some f1'; Some f2; None] (SOff 52 0) (SOff 53 0) (SLit 0) _ HS eq_refl eq_refl ltac:(cbv; auto 10) ltac:(cbv; auto 10) ltac:(cbv; auto 10) K4 eq_refl) as Hat4.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
rewrite XREST. replace (code =? YO07.C_OK) with true by (symmetry; apply Z.eqb_eq; exact Xcode).
pose proof (af_tail_facts (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv (YO07.mkS (YO07.s_q1 gs) (YO07.s_q2 gs) None (YO07.s_ihead gs) (YO07.s_cur gs) code (YO07.s_out gs ++ [bytes])) 2%nat ltac:(right; reflexivity)) as TF.
cbv zeta in TF. destruct TF as (TF1 & TF2 & TF3 & TF4 & TF5 & TF6 & TF7). change (Z.of_nat 2%nat) with 2 in TF1, TF2, TF3, TF4, TF5, TF6, TF7.
assert (Rnlp : 0 <= nlp < 2 ^ 16) by (pose proof (obj_at_range _ _ _ _ _ Hcf 5%nat nlp eq_refl) as X; exact X).
eapply SR_mono; [| cbv beta; intros c' Hc'; exact (af_postX_rebase API regs0 g N s0 CB rest GPAL gs _ _ L A mem md L2 A2 mem2 md2 FPw c' HJw HFPwsub XLOW Hc')].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (af_D1 API IMG L2 A2 mem2 md2 regs0 rg L3 A3 mm md3 g N s0 (set_frames s1 [Some f1'; Some f2; None]) rest FP 2%nat (Some f2) cfp lpal lpa img fattr fgen delay nlp tidx t4
GPAL IMGv LPALv gs (YO07.mkS (YO07.s_q1 gs) (YO07.s_q2 gs) None (YO07.s_ihead gs) (YO07.s_cur gs) code (YO07.s_out gs ++ [bytes])) (af_tail (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv (YO07.mkS (YO07.s_q1 gs) (YO07.s_q2 gs) None (YO07.s_ihead gs) (YO07.s_cur gs) code (YO07.s_out gs ++ [bytes])) 2) (match o0 with Some _ => rb_free (flush_rb brb) N | None => flush_rb brb end) (af_rb brb N (qcount gs) (qcount (af_tail (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv (YO07.mkS (YO07.s_q1 gs) (YO07.s_q2 gs) None (YO07.s_ihead gs) (YO07.s_cur gs) code (YO07.s_out gs ++ [bytes])) 2)))) end;
[ exact HJ3 | exact Hid3 | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf_s3 | subst s1; exact Hgeom | right; reflexivity | reflexivity | reflexivity
| intros _; discriminate | subst s1; exact HnoCT | | exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact HFPg | | rewrite cgif_blocks_shift0; exact HB3 | | | | | | | |
| etransitivity; [| exact Xgen]; subst s1; reflexivity | etransitivity; [| exact Xfile]; subst s1; reflexivity | exact Xt4
|   split; [| exact (conj Hfin2 (conj XFIN (conj XSK4 (conj XSK5 HFPX))))]; rewrite TF3; cbn [YO07.s_out]; rewrite concat_app; cbn [concat]; rewrite app_nil_r; exact HSK2
|   split; [| split; [exact XHra | split; [exact XHih |]]];
[ subst s1; cbn [rw_cur set_frames flush_upd YO07.s_rcur]; rewrite Hrw; apply rc_int_mod32; clear - Hcode; lia
| intros Hz; subst s1; cbn [cg_attr cg_pal cg_ngp set_frames flush_upd] in Hz |- *; destruct (XHgp Hz) as [Hg Hgl]; split; [| exact Hgl]; eapply garr8_frame; [exact Hg|]; intros a Ha;
destruct (VSEP (cg_pal s) (3 * cg_ngp s) ltac:(apply in_app_iff; left; unfold pal_blocks; rewrite Hz; left; reflexivity)) as (V1 & V2 & V3 & V4 & V5 & V6);
rewrite <- (Zplus_minus (cg_pal s) a); apply (KVX _ K4 _ _ _ V1 V2 V3 V4 V5 V6); clear - Ha Hgl; lia ]
| exact TF2 | exact TF4
|
intros k Hk Hki; destruct k as [|[|[|k]]]; [ | | exfalso; exact (Hki eq_refl) | clear - Hk; lia];
cbn [nth cg_frames set_frames qslot YO07.s_q0 YO07.s_q1 wgk]; rewrite ?Hq1, ?Hq2; cbn [oframe_relb];
[ destruct XS1 as (FR1 & FR2 & FR3 & FR4 & FR5 & FR6 & FR7 & Hi & Hil & Hl); subst f1'; unfold frame_relb; cbn [set_fr_gen fr_attr fr_gen fr_delay fr_nlp fr_ctidx fr_disp fr_tidx fr_img fr_lpal];
split; [exact FR1|]; split; [exact I|]; split; [exact FR3|]; split; [exact FR4|]; split; [exact FR5|]; split; [exact FR6|]; split; [exact FR7|]; split; [| split; [exact Hil|]];
[ eapply garr8_frame; [exact Hi|]; intros a Ha; rewrite <- (Zplus_minus (fr_img f1) a);
destruct (VSEP (fr_img f1) N ltac:(apply in_app_iff; right; left; reflexivity)) as (V1 & V2 & V3 & V4 & V5 & V6); apply (KVX _ K4 _ _ _ V1 V2 V3 V4 V5 V6); clear - Ha Hil; lia
| intros H1; destruct (Hl H1) as [Hg Hgl]; split; [| exact Hgl]; eapply garr8_frame; [exact Hg|]; intros a Ha; rewrite <- (Zplus_minus (fr_lpal f1) a);
destruct (VSEP (fr_lpal f1) (3 * fr_nlp f1) ltac:(apply in_app_iff; right; cbn [flat_map af_fvb app]; right; destruct (Z.eqb_spec (Z.land (fr_attr f1) 1) 0); [exfalso; exact (H1 ltac:(assumption)) | left; reflexivity])) as (V1 & V2 & V3 & V4 & V5 & V6);
apply (KVX _ K4 _ _ _ V1 V2 V3 V4 V5 V6); clear - Ha Hgl; lia ]
| destruct XS2 as (FR1 & FR2 & FR3 & FR4 & FR5 & FR6 & FR7 & Hi & Hil & Hl); unfold frame_relb;
split; [exact FR1|]; split; [exact FR2|]; split; [exact FR3|]; split; [exact FR4|]; split; [exact FR5|]; split; [exact FR6|]; split; [exact FR7|]; split; [| split; [exact Hil|]];
[ eapply garr8_frame; [exact Hi|]; intros a Ha; rewrite <- (Zplus_minus (fr_img f2) a);
destruct (VSEP (fr_img f2) N ltac:(apply in_app_iff; right; cbn [flat_map af_fvb app]; right; apply in_app_iff; right; left; reflexivity)) as (V1 & V2 & V3 & V4 & V5 & V6); apply (KVX _ K4 _ _ _ V1 V2 V3 V4 V5 V6); clear - Ha Hil; lia
| intros H1; destruct (Hl H1) as [Hg Hgl]; split; [| exact Hgl]; eapply garr8_frame; [exact Hg|]; intros a Ha; rewrite <- (Zplus_minus (fr_lpal f2) a);
destruct (VSEP (fr_lpal f2) (3 * fr_nlp f2) ltac:(apply in_app_iff; right; cbn [flat_map af_fvb app]; right; apply in_app_iff; right; right; destruct (Z.eqb_spec (Z.land (fr_attr f2) 1) 0); [exfalso; exact (H1 ltac:(assumption)) | left; reflexivity])) as (V1 & V2 & V3 & V4 & V5 & V6);
apply (KVX _ K4 _ _ _ V1 V2 V3 V4 V5 V6); clear - Ha Hgl; lia ] ]
| exact TF7 | exact TF6 | exact TF1 | exact TF5
|   eapply garr8_frame; [exact XIMG0|]; intros a Ha; rewrite XIL in Ha; rewrite <- (Zplus_minus img a);
destruct (CSEP img N ltac:(left; reflexivity)) as (V1 & V2 & V3 & V4 & V5 & V6); apply (KVX _ K4 _ _ _ V1 V2 V3 V4 V5 V6); clear - Ha; lia
| exact XIL
|   intros H1; destruct (XLPA H1) as [Hg Hgl]; split; [| exact Hgl]; eapply garr8_frame; [exact Hg|]; intros a Ha; rewrite Hgl in Ha; rewrite <- (Zplus_minus lpa a);
destruct (CSEP lpa (3 * nlp) ltac:(subst CB; right; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (H1 ltac:(assumption)) | left; reflexivity])) as (V1 & V2 & V3 & V4 & V5 & V6);
apply (KVX _ K4 _ _ _ V1 V2 V3 V4 V5 V6); clear - Ha; lia
|   rewrite TF3; cbn [YO07.s_out]; rewrite concat_app; cbn [concat]; rewrite app_nil_r, length_app, Nat2Z.inj_add; clear - Hlenb; lia
|   exact HR3
|
destruct o0 as [f0|]; [ exact (proj1 (af_nums_evicted brb N nlp 3 ltac:(clear - HN HW1 HH1; nia) ltac:(clear - Rnlp; lia) ltac:(unfold PALMAX; clear - Rnlp; lia) XROOM))
| exact (proj1 (af_nums_flushed brb N nlp 2 ltac:(clear - HN HW1 HH1; nia) ltac:(clear - Rnlp; lia) ltac:(unfold PALMAX; clear - Rnlp; lia) XROOM)) ]
| destruct o0 as [f0|]; [ exact (proj1 (proj2 (af_nums_evicted brb N nlp 3 ltac:(clear - HN HW1 HH1; nia) ltac:(clear - Rnlp; lia) ltac:(unfold PALMAX; clear - Rnlp; lia) XROOM)))
| exact (proj1 (proj2 (af_nums_flushed brb N nlp 2 ltac:(clear - HN HW1 HH1; nia) ltac:(clear - Rnlp; lia) ltac:(unfold PALMAX; clear - Rnlp; lia) XROOM))) ]
| intros _; destruct o0 as [f0|]; [ exact (proj1 (proj2 (proj2 (af_nums_evicted brb N nlp 3 ltac:(clear - HN HW1 HH1; nia) ltac:(clear - Rnlp; lia) ltac:(unfold PALMAX; clear - Rnlp; lia) XROOM))))
| exact (proj1 (proj2 (proj2 (af_nums_flushed brb N nlp 2 ltac:(clear - HN HW1 HH1; nia) ltac:(clear - Rnlp; lia) ltac:(unfold PALMAX; clear - Rnlp; lia) XROOM)))) ]
|   replace (qcount (af_tail (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv (YO07.mkS (YO07.s_q1 gs) (YO07.s_q2 gs) None (YO07.s_ihead gs) (YO07.s_cur gs) code (YO07.s_out gs ++ [bytes])) 2)) with (qcount (YO07.mkS (YO07.s_q1 gs) (YO07.s_q2 gs) None (YO07.s_ihead gs) (YO07.s_cur gs) code (YO07.s_out gs ++ [bytes])) + 1) by (symmetry; exact (qcount_af_tail (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv (YO07.mkS (YO07.s_q1 gs) (YO07.s_q2 gs) None (YO07.s_ihead gs) (YO07.s_cur gs) code (YO07.s_out gs ++ [bytes])) 2%nat ltac:(right; reflexivity) eq_refl));
rewrite !qcount_slots; cbn [qslot YO07.s_q0 YO07.s_q1 YO07.s_q2]; rewrite Hq1, Hq2;
destruct o0 as [f0|]; destruct (YO07.s_q0 gs) as [F0|]; cbn [oframe_relb] in XS0; try (exfalso; exact XS0); cbn [ocnt Z.add];
[ pose proof (proj2 (proj2 (proj2 (af_nums_evicted brb N nlp 3 ltac:(clear - HN HW1 HH1; nia) ltac:(clear - Rnlp; lia) ltac:(unfold PALMAX; clear - Rnlp; lia) XROOM))) (negb (Z.land fattr 1 =? 0))) as Y;
destruct (Z.land fattr 1 =? 0); exact Y
| pose proof (proj2 (proj2 (proj2 (af_nums_flushed brb N nlp 2 ltac:(clear - HN HW1 HH1; nia) ltac:(clear - Rnlp; lia) ltac:(unfold PALMAX; clear - Rnlp; lia) XROOM))) (negb (Z.land fattr 1 =? 0))) as Y;
cbn [Z.add Z.pos_sub Pos.add] in Y; destruct (Z.land fattr 1 =? 0); exact Y ] ].
+ apply Hat4.
* cbn [nth frame_ptr f1' fr_ptr set_fr_gen sv_denot]. ew_havocA. rewrite Z.add_0_r, (HX 52%nat 1%nat _ eq_refl eq_refl), Hfr, Z_to_bv_bv_unsigned. reflexivity.
* cbn [nth frame_ptr sv_denot]. ew_havocA. rewrite Z.add_0_r, (HX 53%nat 2%nat _ eq_refl eq_refl), Hfr, Z_to_bv_bv_unsigned. reflexivity.
* reflexivity.
* intros k Hk. destruct k as [|[|[|k]]]; cbn [nth frame_ptr f1' fr_ptr set_fr_gen]; lia.
* intros f [Hf|[Hf|[Hf|[]]]]; [| | discriminate Hf]; injection Hf as <-; subst s2; rewrite cg_frames_set_frames; cbv; auto.
+ eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig |].
intros k Hk. rewrite K4; [| clear - Hk Hcflo Hcfhi Hceil HASv Hac; lia | clear - Hk Hcflo Hceil Hg1 HASv HGSv Hac; lia].
rewrite K3; [| clear - Hk Hcflo Hcfhi Hceil HASv Hac; lia | right; clear - Hk Hcflo; lia].
rewrite (proj1 (Hhi2 (cfp + k) ltac:(clear - Hk Hcflo Hcfhi Hceil HASv Hac; lia) ltac:(clear - Hk Hcflo; lia))). apply K1.
+ intros f a Hf Ha. rewrite cg_frames_set_frames in Hf. destruct Hf as [Hf|[Hf|[Hf|[]]]]; [injection Hf as <- | injection Hf as <- | discriminate Hf].
* apply (HFP (fr_ptr f1) FRAME_SIZE a); [apply (frame_blocks_in_cgif0 g s N f1); [rewrite Hfr; right; left; reflexivity | left; reflexivity] | exact Ha].
* apply (HFP (fr_ptr f2) FRAME_SIZE a); [apply (frame_blocks_in_cgif0 g s N f2); [rewrite Hfr; right; right; left; reflexivity | left; reflexivity] | exact Ha].
+ apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha. rewrite K4; [| clear - Ha Hceil Hsp063 HASv Hac; lia | clear - Ha Hceil Hg1 HASv HGSv; lia].
rewrite K3; [| clear - Ha Hceil Hsp063 HASv Hac; lia | right; clear - Ha; lia].
rewrite (proj1 (Hhi2 a ltac:(clear - Ha Hceil Hsp063 HASv Hac; lia) ltac:(clear - Ha; lia))). apply K1.
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 2%nat 2%bv eq_refl); exact G2).
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 8%nat 8%bv eq_refl); exact G8).
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 9%nat 9%bv eq_refl); exact G9).
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 19%nat 19%bv eq_refl); exact G23).
+ exact Rt4.
+ reg_nowG HS ltac:(reflexivity).
+ split; [|split; [|split; [|split; [|split; [|split]]]]].
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact U23).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact U24).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact U25).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27).
Qed.
Definition ss_C (ih : Z) (p0 p1 p2 : option Z) (fs : list (nat * afact)) : sstate :=
mkSS AF_C (sr_set sr_atoms 20%bv (SLit ih))
[ YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) ; af_Rg p0 p1 p2 (Some ih) ] None (mkFacts (af_facts ++ fs) [] []).
Lemma af_C :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (rest FP : list (Z * Z))
(cfp lpal lpa img fattr fgen delay nlp tidx t4 : Z)
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
getr regs1 19 = Z_to_bv 64 t4 -> 0 <= t4 < 2 ^ 64 -> getr regs1 20 = Z_to_bv 64 (cg_ihead s) ->
af_untouched regs0 regs1 ->
cg_gen s = cg_gen s0 -> cg_file s = cg_file s0 -> t4 = Z.land fattr 4 ->
af_sink g s0 s N rest FP (concat (YO07.s_out gs)) L A mem md -> (forall a, inFP (cgif_fp g s0 N) a -> a < alloc_ceiling) ->
Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N <= SINK_MAX -> spZ regs0 <= 2 ^ 47 ->
cgif_live gs -> rc_int (cg_cur s) = YO07.s_cur gs -> af_live memc s N GPAL gs ->
garr8 ubs0segs memc img IMGv -> Z.of_nat (length IMGv) = N ->
(Z.land fattr 1 <> 0 -> garr8 ubs0segs memc lpa LPALv /\ Z.of_nat (length LPALv) = 3 * nlp) ->
res_ok Ac brb -> af_room brb N ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_C) memc (seg_rom ubs0segs)) mdc)
(af_postX API regs0 g N s0 CB rest GPAL gs (af_rest (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) (af_rb brb N (qcount gs) (qcount (af_rest (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs))) L A mem md).
Proof using FLUSHX IMG.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP cfp lpal lpa img fattr fgen delay nlp tidx t4 GPAL IMGv LPALv gs brb sp0 CB
HJ Hid Hra0 Hal16 Htp0 Hat Hwf Hgeom HnoCT Hcf Hcf8 Hcflo Hcfhi Hlpa HFP HB HSV G2 G8 G9 G23 Rt4 G24 HUT
Xgen Xfile Xt4 XSK XLOW XMAX Xsp47 XLV XCUR XLIVE XIMG0 XIL XLPA XRq XROOM.
pose proof (proj1 (af_live_iff _ _ _ _ _) XLIVE) as ((XHrc & XHra & XHih & XHgp) & XSL).
pose proof (proj1 (af_live_iff _ _ _ _ _) XLIVE) as (XH & _).
pose proof (oframe_relb_occ _ _ _ _ _ (XSL 1%nat ltac:(lia) I)) as O1. pose proof (oframe_relb_occ _ _ _ _ _ (XSL 2%nat ltac:(lia) I)) as O2.
assert (Rnlp : 0 <= nlp < 2 ^ 16) by (pose proof (obj_at_range _ _ _ _ _ ltac:(exact Hcf) 5%nat nlp eq_refl) as X; exact X).
pose proof HUT as (G3 & G4 & U23 & U24 & U25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & _ & Hih & _).
destruct (frames3 s N Hwf) as (o0 & o1 & o2 & Hfr).
rewrite Hfr in O1, O2. cbn [nth qslot] in O1, O2.
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N _ HH0 HB) as (_ & Hfgeom & (Hg0 & Hg1 & Hg16)).
assert (HFPg : forall a, g <= a < g + CGIF_SIZE -> inFP FP a) by (intros a Ha; apply (HFP g CGIF_SIZE a); [left; reflexivity | exact Ha]).
assert (HFPfr : forall f a, In (Some f) (cg_frames s) -> fr_ptr f <= a < fr_ptr f + FRAME_SIZE -> inFP FP a).
{ intros f a Hf Ha. apply (HFP (fr_ptr f) FRAME_SIZE a); [apply (frame_blocks_in_cgif0 g s N f); [exact Hf | left; reflexivity] | exact Ha]. }
pose proof Hat as (Hobj & Hraw & Hfrs).
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
set (E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s []).
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HK regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (af_HX regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HX.
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HR0 : region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32))).
{ pose proof (af_Rstk_ok _ memc sp0 regs0 32 HU2 ltac:(lia) ltac:(lia) HSV (fun j v Hj => HK _ j v eq_refl Hj) (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4]. }
assert (HR1 : forall p0 p1 p2,
pin_ok p0 (frame_ptr o0) -> pin_ok p1 (frame_ptr o1) -> pin_ok p2 (frame_ptr o2) ->
region_ok ubs0segs E memc (af_Rg p0 p1 p2 (Some (cg_ihead s)))).
{ intros p0 p1 p2 P0 P1 P2. apply (af_Rg_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s [] memc g); [exact HU8 | lia | lia | exact Hobj | | | | exact eq_refl];
rewrite Hfr; cbn [nth]; assumption. }
assert (HPD : forall p0 p1 p2 fs, pairwise_disjoint E (ss_mem (ss_C (cg_ihead s) p0 p1 p2 fs))).
{ intros p0 p1 p2 fs. cbn [ss_mem ss_C]. unfold af_Rg. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU8. clear - Hg1 Hceil HASv HGSv Hac. repeat split; lia. }
assert (HFA : atoms_ok E af_facts).
{ cbn [atoms_ok af_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, (HE 9%nat 9%bv eq_refl), G9, unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia.
replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HFF : forall (k : nat) f, nth_error (cg_frames s) k = Some (Some f) -> atoms_ok E [((51 + k)%nat, mkAF 4096 (CEIL_MAX - 40) 4)]).
{ intros k f Hk. cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
assert (Hkl : (k < 3)%nat) by (rewrite <- Hlen; apply (proj1 (nth_error_Some _ _)); rewrite Hk; discriminate).
rewrite (HX (51 + k)%nat k (fr_ptr f) eq_refl).
2:{ unfold cgif_vals. destruct k as [|[|[|k]]]; try lia; cbn [nth_error]; rewrite (nth_error_nth _ _ _ Hk); reflexivity. }
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hk).
destruct (Hfgeom f Hfin) as (F0 & F1 & _).
pose proof (proj1 (af_frame_geom0 API Lc Ac memc mdc g s N _ f HH0 HB Hfin)) as Hfb.
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr f) FRAME_SIZE HH0 Hfb ltac:(lia)) as (_ & _ & F16).
rewrite unsigned_lit_small by lia. change (2 ^ 4) with 16. repeat split; lia. }
assert (HRG : regs_ok E (sr_set sr_atoms 20%bv (SLit (cg_ihead s))) regs1).
{ apply regs_ok_pin; [apply regs_ok_Ereg | intros H; discriminate H | cbn [sv_denot]; exact G24]. }
assert (MK : forall p0 p1 p2 fs,
pin_ok p0 (frame_ptr o0) -> pin_ok p1 (frame_ptr o1) -> pin_ok p2 (frame_ptr o2) -> atoms_ok E fs ->
st_ok ubs0segs E (ss_C (cg_ihead s) p0 p1 p2 fs) (mkst regs1 (Z_to_bv 64 AF_C) memc (seg_rom ubs0segs))).
{ intros p0 p1 p2 fs P0 P1 P2 Hfs. unfold ss_C. apply entry_st_ok_full; [exact HRG | | | exact (HPD p0 p1 p2 fs) | split; [apply atoms_ok_app; [exact HFA | exact Hfs] | split; exact I]].
- destruct Hih as [H1|[H2 _]]; rewrite ?H1, ?H2; vm_compute; reflexivity.
- constructor; [exact HR0|]. constructor; [exact (HR1 p0 p1 p2 P0 P1 P2)|]. constructor. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_C) memc (seg_rom ubs0segs))) in HJ.
assert (TOD : forall ss ms' (i : nat) op, st_ok ubs0segs E ss ms' -> ss_pc ss = AF_D -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 -> sr_get (ss_regs ss) 19%bv = SOff 19 0 ->
sr_get (ss_regs ss) 20%bv = SLit (Z.of_nat i) -> sr_get (ss_regs ss) 23%bv = SOff 23 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 ->
sr_get (ss_regs ss) 25%bv = SOff 25 0 -> sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs memc a) ->
(i = 1%nat \/ i = 2%nat) -> nth_error (cg_frames s) i = Some None -> nth_error (cg_frames s) (i - 1) = Some op -> (i = 2%nat -> op <> None) ->
af_i0 gs = Z.of_nat i ->
SR ubs0segs (mkCfg ms' mdc) (af_postX API regs0 g N s0 CB rest GPAL gs (af_rest (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) (af_rb brb N (qcount gs) (qcount (af_rest (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs))) L A mem md)).
{ intros ss ms' i op HS' Hpc Hrv Q2 Q3 Q4 Q8 Q9 Q19 Q20 Q23 Q24 Q25 Q26 Q27 HJ' K Hi Hinone Hiop Hi2 XI0.
rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hw. rewrite (st_ok_reg ubs0segs E ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hw. }
assert (XQN : qslot gs i = None) by (apply (proj1 (oframe_relb_occ _ _ _ _ _ (XSL i ltac:(clear - Hi; lia) I))); exact (@nth_error_nth _ (cg_frames s) i None None Hinone)).
rewrite (af_rest_free (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs ltac:(rewrite XI0; clear - Hi; lia)), XI0.
pose proof (af_tail_facts (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs i Hi) as TF. cbv zeta in TF. destruct TF as (TF1 & TF2 & TF3 & TF4 & TF5 & TF6 & TF7).
pose proof (af_nums_noflush brb N nlp (qcount gs) ltac:(clear - HN HW1 HH1; nia) ltac:(clear - Rnlp; lia) ltac:(unfold PALMAX; clear - Rnlp; lia) XROOM) as (NR1 & NR2 & NR3 & NR4).
eapply (af_D1 API IMG L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s0 s rest FP i op cfp lpal lpa img fattr fgen delay nlp tidx t4
GPAL IMGv LPALv gs gs (af_tail (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs (Z.of_nat i)) brb (af_rb brb N (qcount gs) (qcount (af_tail (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs (Z.of_nat i)))));
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hgeom | exact Hi | exact Hinone | exact Hiop | exact Hi2 | exact HnoCT
| | exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact HFPg | exact HFPfr | exact HB | | | | | | | |
| exact Xgen | exact Xfile | exact Xt4
|   rewrite TF3; exact XSK
|   apply (af_hdr_kept memc); [intros _ k _; apply K | exact XH]
| exact TF2 | exact TF4
|   apply (af_slots_kept memc); [intros; apply K | exact (af_slots_mono _ _ _ _ _ _ (fun k _ => I) XSL)]
| exact TF7 | exact TF6 | exact TF1 | exact TF5
|   eapply garr8_frame; [exact XIMG0 | intros a _; apply K]
| exact XIL
|   intros H1; destruct (XLPA H1) as [Hg Hgl]; split; [| exact Hgl]; eapply garr8_frame; [exact Hg | intros a _; apply K]
|   rewrite TF3; unfold FRAME_OUT; clear - HN HW1 HH1; nia
| exact XRq | exact NR1 | exact NR2 | intros _; exact NR3
|   replace (qcount (af_tail (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs (Z.of_nat i))) with (qcount gs + 1) by (symmetry; exact (qcount_af_tail (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs i Hi XQN));
destruct (Z.land fattr 1 =? 0); [exact (NR4 false) | exact (NR4 true)] ].
- eapply (cgif_at_kept0 memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply K].
- eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply K].
- apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply K].
- apply (RG _ _ _ Q2). rewrite (HE 2%nat 2%bv eq_refl). exact G2.
- apply (RG _ _ _ Q8). rewrite (HE 8%nat 8%bv eq_refl). exact G8.
- apply (RG _ _ _ Q9). rewrite (HE 9%nat 9%bv eq_refl). exact G9.
- apply (RG _ _ _ Q19). rewrite (HE 19%nat 19%bv eq_refl). exact G23.
- exact Rt4.
- rewrite (st_ok_reg ubs0segs E ss ms' 20%bv HS'), Q20. reflexivity.
- split; [|split; [|split; [|split; [|split; [|split]]]]]; [ apply (RG _ _ _ Q3); rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG _ _ _ Q4); rewrite (HE 4%nat 4%bv eq_refl); exact G4
| apply (RG _ _ _ Q23); rewrite (HE 23%nat 23%bv eq_refl); exact U23
| apply (RG _ _ _ Q24); rewrite (HE 24%nat 24%bv eq_refl); exact U24
| apply (RG _ _ _ Q25); rewrite (HE 25%nat 25%bv eq_refl); exact U25
| apply (RG _ _ _ Q26); rewrite (HE 26%nat 26%bv eq_refl); exact G26
| apply (RG _ _ _ Q27); rewrite (HE 27%nat 27%bv eq_refl); exact G27 ]. }
assert (TOCF : forall ss ms' f1 f2, st_ok ubs0segs E ss ms' -> ss_pc ss = AF_CF -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 -> sr_get (ss_regs ss) 19%bv = SOff 19 0 ->
sr_get (ss_regs ss) 23%bv = SOff 23 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 -> sr_get (ss_regs ss) 25%bv = SOff 25 0 ->
sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs memc a) ->
cg_frames s = [o0; Some f1; Some f2] ->
SR ubs0segs (mkCfg ms' mdc) (af_postX API regs0 g N s0 CB rest GPAL gs (af_rest (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) (af_rb brb N (qcount gs) (qcount (af_rest (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs))) L A mem md)).
{ intros ss ms' f1 f2 HS' Hpc Hrv Q2 Q3 Q4 Q8 Q9 Q19 Q23 Q24 Q25 Q26 Q27 HJ' K Hfr12.
rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hw. rewrite (st_ok_reg ubs0segs E ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hw. }
eapply (af_CF L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s0 s rest FP o0 f1 f2 cfp lpal lpa img fattr fgen delay nlp tidx t4 GPAL IMGv LPALv gs brb);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hgeom | exact Hfr12 | exact HnoCT
| | exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact HFP | exact HB | | | | | | |
| exact Xgen | exact Xfile | exact Xt4 | exact XSK | exact XLOW | exact XMAX | exact Xsp47 | exact XLV | exact XCUR
|   apply (proj2 (af_live_iff _ _ _ _ _)); split; [apply (af_hdr_kept memc); [intros _ k _; apply K | exact XH] | apply (af_slots_kept memc); [intros; apply K | exact XSL]]
|   eapply garr8_frame; [exact XIMG0 | intros a _; apply K]
| exact XIL
|   intros H1; destruct (XLPA H1) as [Hg Hgl]; split; [| exact Hgl]; eapply garr8_frame; [exact Hg | intros a _; apply K]
| exact XRq | exact XROOM ].
- eapply (cgif_at_kept0 memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply K].
- eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply K].
- apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply K].
- apply (RG _ _ _ Q2). rewrite (HE 2%nat 2%bv eq_refl). exact G2.
- apply (RG _ _ _ Q8). rewrite (HE 8%nat 8%bv eq_refl). exact G8.
- apply (RG _ _ _ Q9). rewrite (HE 9%nat 9%bv eq_refl). exact G9.
- apply (RG _ _ _ Q19). rewrite (HE 19%nat 19%bv eq_refl). exact G23.
- exact Rt4.
- split; [|split; [|split; [|split; [|split; [|split]]]]]; [ apply (RG _ _ _ Q3); rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG _ _ _ Q4); rewrite (HE 4%nat 4%bv eq_refl); exact G4
| apply (RG _ _ _ Q23); rewrite (HE 23%nat 23%bv eq_refl); exact U23
| apply (RG _ _ _ Q24); rewrite (HE 24%nat 24%bv eq_refl); exact U24
| apply (RG _ _ _ Q25); rewrite (HE 25%nat 25%bv eq_refl); exact U25
| apply (RG _ _ _ Q26); rewrite (HE 26%nat 26%bv eq_refl); exact G26
| apply (RG _ _ _ Q27); rewrite (HE 27%nat 27%bv eq_refl); exact G27 ]. }
assert (RO : forall p0 p1 p2 fs, wr_ok E (ss_mem (ss_C (cg_ihead s) p0 p1 p2 fs)) ADDFRAME_STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros. cbn [ss_mem ss_C]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (NT : forall k, 0 <= k <= 24 -> branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff 8 0) (SLit (-1)))) (sv_denot E (SLit k)) = false).
{ intros k Hk. rewrite YI04.branch_ltu_U, (YI08.U_not E 8 g) by first [rewrite (HE 8%nat 8%bv eq_refl); exact G8 | lia].
rewrite YP0e.U_SLit. unfold zcanon, M64. rewrite Z.mod_small by lia. apply Z.ltb_ge. lia. }
destruct Hih as [Hih1 | [Hih2 Hn1]].
-
rewrite Hih1 in MK, RO. destruct o1 as [f1|].
+ destruct o2 as [f2|].
*
pose proof (MK None None None _ I I I (atoms_ok_app _ _ _ (HFF 1%nat f1 ltac:(rewrite Hfr; reflexivity)) (HFF 2%nat f2 ltac:(rewrite Hfr; reflexivity)))) as HS.
jrun_to LAWS ubs0tbl_ok HS HJ AF_CF. { apply RO. }
jbranch ubs0tbl HS; [exfalso; rewrite NT in Hc by lia; discriminate Hc | clear Hc].
jrun_to LAWS ubs0tbl_ok HS HJ AF_CF. { wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jbranch ubs0tbl HS; [exfalso; rewrite NT in Hc by lia; discriminate Hc | clear Hc].
jrun_to LAWS ubs0tbl_ok HS HJ AF_CF. { wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (TOCF _ _ f1 f2 HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ); [| exact Hfr].
intros a. unfold mbyte. repeat match goal with H : frame_of ?E1 ?rs ?m1 ?m2 |- _ => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) H); clear H end. reflexivity.
*
pose proof (MK None None (Some 0) _ I I eq_refl (HFF 1%nat f1 ltac:(rewrite Hfr; reflexivity))) as HS.
jrun_to LAWS ubs0tbl_ok HS HJ AF_D. { apply RO. }
jbranch ubs0tbl HS; [exfalso; rewrite NT in Hc by lia; discriminate Hc | clear Hc].
jrun_to LAWS ubs0tbl_ok HS HJ AF_D. { wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jbranch ubs0tbl HS; [exfalso; rewrite NT in Hc by lia; discriminate Hc | clear Hc].
jrun_to LAWS ubs0tbl_ok HS HJ AF_D. { wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (TOD _ _ 2%nat (Some f1) HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ); [| right; reflexivity | rewrite Hfr; reflexivity | rewrite Hfr; reflexivity | intros _; discriminate
|   unfold af_i0, YO07.q_get; rewrite <- XHih, Hih1; cbn; destruct (YO07.s_q1 gs); [| discriminate (proj2 O1 eq_refl)]; rewrite (proj1 O2 eq_refl); reflexivity ].
intros a. unfold mbyte. repeat match goal with H : frame_of ?E1 ?rs ?m1 ?m2 |- _ => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) H); clear H end. reflexivity.
+
pose proof (MK None (Some 0) None [] I eq_refl I ltac:(exact I)) as HS.
jrun_to LAWS ubs0tbl_ok HS HJ AF_D. { apply RO. }
jbranch ubs0tbl HS; [exfalso; rewrite NT in Hc by lia; discriminate Hc | clear Hc].
jrun_to LAWS ubs0tbl_ok HS HJ AF_D. { wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (TOD _ _ 1%nat o0 HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ); [| left; reflexivity | rewrite Hfr; reflexivity | rewrite Hfr; reflexivity | intros H; discriminate H
|   unfold af_i0, YO07.q_get; rewrite <- XHih, Hih1; cbn; rewrite (proj1 O1 eq_refl); reflexivity ].
intros a. unfold mbyte. repeat match goal with H : frame_of ?E1 ?rs ?m1 ?m2 |- _ => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) H); clear H end. reflexivity.
-
rewrite Hfr in Hn1. cbn [nth] in Hn1. destruct o1 as [f1|]; [| exfalso; apply Hn1; reflexivity].
rewrite Hih2 in MK, RO. destruct o2 as [f2|].
+
pose proof (MK None None None _ I I I (HFF 2%nat f2 ltac:(rewrite Hfr; reflexivity))) as HS.
jrun_to LAWS ubs0tbl_ok HS HJ AF_CF. { apply RO. }
jbranch ubs0tbl HS; [exfalso; rewrite NT in Hc by lia; discriminate Hc | clear Hc].
jrun_to LAWS ubs0tbl_ok HS HJ AF_CF. { wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (TOCF _ _ f1 f2 HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ); [| exact Hfr].
intros a. unfold mbyte. repeat match goal with H : frame_of ?E1 ?rs ?m1 ?m2 |- _ => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) H); clear H end. reflexivity.
+
pose proof (MK None None (Some 0) [] I I eq_refl ltac:(exact I)) as HS.
jrun_to LAWS ubs0tbl_ok HS HJ AF_D. { apply RO. }
jbranch ubs0tbl HS; [exfalso; rewrite NT in Hc by lia; discriminate Hc | clear Hc].
jrun_to LAWS ubs0tbl_ok HS HJ AF_D. { wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (TOD _ _ 2%nat (Some f1) HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ); [| right; reflexivity | rewrite Hfr; reflexivity | rewrite Hfr; reflexivity | intros _; discriminate
|   unfold af_i0, YO07.q_get; rewrite <- XHih, Hih2; cbn; rewrite (proj1 O2 eq_refl); reflexivity ].
intros a. unfold mbyte. repeat match goal with H : frame_of ?E1 ?rs ?m1 ?m2 |- _ => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) H); clear H end. reflexivity.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
