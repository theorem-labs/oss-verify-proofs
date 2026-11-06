(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from cgif's lib/A/ACgq.v and lib/A/ACk8.v (file header, walk tactic forms) for reac_ctrl_parse of libreac's fuzz_grant, then ported to libreac/fuzz_scene from a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/Prog/CtrlParseMid.v at a working branch 7e98c198edd: module paths and the listing layer renamed (Grant* -> Scene*, GS___ -> SS___, grant_listing -> scene_listing, PL_grant -> PL_scene, KindOfLink1 -> P_kind_of_link1), and fuzz_scene.asan's objects put in place of fuzz_grant.asan's -- the shadow-base cell is object 16 and the side-stack flag object 17, where grant has 32 / 33, so the names Hob32 / Hob33 become Hob16 / Hob17. Every pc named in a comment is fuzz_scene.asan's (sha256 43654a025fd0...): reac_ctrl_parse = 0x83dd8, i.e. grant's pc + 0x1dd8; the cut pcs themselves are symbolic (AF_reac_ctrl_parse + an offset), and scene's reac_ctrl_parse has the same 616 instructions as grant's, so every instruction offset of the walk is the donor's. *)
(* reac_ctrl_parse, the walk from cut A (0x83e4c, the side-stack frame seated) to cut M (0x83f18): the
   frame's header and shadow, then the memset of the out struct. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaRun PaShadow PaJournal SceneSyms SceneList ScenePa ScenePaLib.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import SceneBase YC81 YC4b YC1g YC1h YC45 YC85 SceneFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import P_reac_ctrl_parse CtrlParseLib P_kind_of_link1 SceneRo ACj1 SceneACja.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import CtrlParseCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg scene_listing}.
Context {RO : ro_below_ofl (@pa_segs _ scene_listing PI) (@pa_relro_lo _ scene_listing PI) (@pa_relro_hi _ scene_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
(* The windows of a run lie in the stack below the entry sp, the out struct or the own frame. *)
Local Ltac mid_win :=
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Ha := fresh "Ha" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Ha;
lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (b, wlo, whi) l') in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha; revert Ha; pz_bases; intro Ha; cbv beta;
unfold pz_nf, SHADOW_OFF, SB in *; lia |]); destruct Hin.
(* The presence of a window byte at the memory of the journal HJx. *)
Local Ltac mid_pres HJx :=
first [ lia
| lazymatch goal with HFp : forall m md', AR _ _ _ _ _ m md' -> forall a, _ <= a < _ + 128 -> _ |- _ => apply (HFp _ _ (proj1 HJx)); lia end
| lazymatch goal with HFSp : forall m md', AR _ _ _ _ _ m md' -> forall a, _ <= a < _ + 16 -> _ |- _ => apply (HFSp _ _ (proj1 HJx)); lia end
| lazymatch goal with KP : acall_kept _ _ _ _ _ _ _ _ _ _ _ |- _ => apply (proj2 (proj2 (proj2 (proj2 (proj2 KP))))); lia end ].
(* lia over the walk's context: the disjunctive facts are boxed (lia would split on every one of them); a goal
   that needs one of them gets it destructed, one at a time. *)
Local Ltac mid_lia :=
first [ lia
| match goal with H : boxed (_ \/ _) |- _ => let X := fresh in pose proof H as X; unfold boxed in X; destruct X; lia end
| match goal with H : boxed (_ /\ (_ \/ _)) |- _ => let X := fresh in pose proof H as X; unfold boxed in X; destruct X as [? [?|?]]; lia end
| match goal with H : boxed (off_img _ _) |- _ => let X := fresh in pose proof H as X; unfold boxed, off_img in X; destruct X; lia end
| match goal with H : boxed (in_app _ _) |- _ => let X := fresh in pose proof H as X; unfold boxed, in_app in X; destruct X as [? [?|?]]; lia end
| unbox; lia ].
Lemma pz_segB : forall B G, pz_rt B G -> forall c, pz_ok B c -> pz_cutM_case B c True -> pz_cutA_spec B c.
Proof.
intros B G RT c Hok HM E ms md Hcur HS.
pz_open c Hok. pz_open_rt RT. pz_open_cur Hcur. pz_std.
pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
lazymatch type of AGX with forall n0, _ -> ew _ n0 = ew ?E0 n0 =>
assert (AG : forall n0, (n0 < 33)%nat -> ew E n0 = ew E0 n0) by (intros; apply AGX; lia) end.
assert (HFp : forall m md', AR SEGS B lyc S2 W m md' -> forall a, F <= a < F + 128 -> apresent (w_H W) m a).
{ intros m md' HA a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HA Hfin2) as (_ & _ & Hp & _).
rewrite <- EF in Hp. change (fs_frame_bytes 1) with 128 in Hp. exact (proj1 (Hp a Ha)). }
assert (HFSp : forall m md', AR SEGS B lyc S2 W m md' -> forall a, SB + F / 8 <= a < SB + F / 8 + 16 -> apresent (w_H W) m a).
{ intros m md' HA a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HA Hfin2) as (_ & _ & _ & Hp).
rewrite <- EF in Hp. unfold shadow_addr in Hp. change (fs_frame_bytes 1 / 8) with 16 in Hp.
replace a with (SHADOW_OFF + F / 8 + (a - (SB + F / 8))) by (unfold SHADOW_OFF, SB; lia).
assert (Hi : 0 <= a - (SB + F / 8) < 16).
{ unfold SB in *. idtac. lia. }
apply (proj1 (Hp (a - (SB + F / 8)) Hi)). }
assert (HOp : forall m md', AR SEGS B lyc S2 W m md' -> forall a, o <= a < o + 36 -> apresent (w_H W) m a).
{ intros m md' HA a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ co po HA (HfinS2 _ _ Hoin)) as (_ & _ & Hp & _).
apply (proj1 (Hp a ltac:(lia))). }
pose proof (in_app_sub _ _ f 50 Hfapp ltac:(lia) ltac:(lia) ltac:(lia)) as Hfa.
pose proof (in_app_sub _ _ o 36 Hoapp ltac:(lia) ltac:(lia) ltac:(lia)) as Hoa.
assert (Hsh_f : forall x, f <= x < f + 50 -> ~ (o <= shadow_addr x < o + 36))
by (intros x Hx; apply (pz_sh_app x o 36); [unfold ASAN_CEIL in *; lia | exact Hoa]).
assert (Hsh_o : forall x, o <= x < o + 36 -> ~ (o <= shadow_addr x < o + 36))
by (intros x Hx; apply (pz_sh_app x o 36); [unfold ASAN_CEIL in *; lia | exact Hoa]).
assert (Hfap : f + 50 <= kLowShadowBeg \/ kHighMemBeg <= f /\ f + 50 <= ASAN_CEIL) by (destruct Hfa as [_ H]; exact H).
assert (Hoap : o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o /\ o + 36 <= ASAN_CEIL) by (destruct Hoa as [_ H]; exact H).
repeat match goal with H : _ \/ _ |- _ => box H | H : off_img _ _ |- _ => box H | H : in_app _ _ |- _ => box H end.
(* 1. The frame's header (0x41b58ab3, its description, the function), its shadow (f1 f1 f1 f1, 00 x 4, 04,
   f3 f3 f3, f3 x 4), the frame address at sp1 + 24, to the memset of the out struct. *)
pose proof (SRr_run_pi_AJ_call B LAWS) as RUNC.
lazymatch type of RUNC with forall W n E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx) =>
let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
lazymatch r with (?ss', PRS_call ?sym) =>
assert (Hrun : sym_runN_pi tpi FUEL ssx = (ss', PRS_call sym)) by (vm_compute; reflexivity);
eapply (RUNC Wx FUEL Ex ssx ss' sym msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ2);
[ clear Hrun | clear Hrun HS HJ2; intros ms1 mat1 HS HJ2 HF HFr HG ] end end end.
{ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I. }
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) a) by mid_win;
pose proof (pz_kept_own B LAWS lyc Sc S2 W memc mdc _ _ mA mB (sp - TPARSE_STK) sp o fpos F FL
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) co po HAR HARc Hfrs2 Eab EF EFL FFL
ltac:(lia) ltac:(lia) Hoin Holo Hohi ltac:(intros a [Ha|[Ha|Ha]]; [left; lia | right; left; exact Ha | right; right; exact Ha]) KP
(kept_of_frame _ _ _ _ _ _ HFr Hw) (fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP' end.
clear KP Hw HF HFr HG; rename KP' into KP.
(* 2. memset(out, 0, 36). *)
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite AGX, E12 in Ra0 by lia. rewrite AGX, E33 in R2 by lia.
rewrite AGX, (EE 3%nat 3%bv eq_refl) in R3 by lia. rewrite AGX, (EE 4%nat 4%bv eq_refl) in R4 by lia.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA SS___asan_memset) AMEMSET W rT mT STK sp0 FP ly S W0 mem0 md0 _ lyc S2 dT k o 0 36 (sp1 - sp0) _ HJ2) end.
- rewrite Ra0. reflexivity.
- rewrite Ra1. reflexivity.
- rewrite Ra2. reflexivity.
- lia. - lia. - unfold ASAN_CEIL in *; lia.
- unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
- rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
- lia. - rewrite Hes; lia.
- rewrite R3. exact Hgp. - rewrite R4. exact Htp.
- exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split; [rewrite Eab; apply pz_awr_cons; apply HOW; lia | lia].
- unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hoap. mid_lia.
- exact (pz_kept_ra B LAWS lyc Sc W memc mdc _ _ _ _ co po o 36 HAR KP Hoin Holo Hohi Hsh_o HRo).
- intros _. exact (shadow_hull_vis_of_frame SEGS B LAWS _ _ _ _ _ co po o 36 (proj1 HJ2) (HfinS2 _ _ Hoin) Holo Hohi ltac:(lia)).
- exact I. }
cbv beta. clear R1 R2 R3 R4 Ra0 Ra1 Ra2.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hfr3 & Hpres3).
lazymatch type of KP with acall_kept _ _ _ _ _ _ _ ?mA _ _ _ =>
pose proof (pz_kept_own B LAWS lyc Sc S2 W memc mdc _ _ mA mem3 (sp - TPARSE_STK) sp o fpos F FL
(fun a => (sp1 - ESTACK <= a < sp1) \/ (o <= a < o + 36)) co po HAR HARc Hfrs2 Eab EF EFL FFL
ltac:(lia) ltac:(lia) Hoin Holo Hohi ltac:(intros a [Ha|Ha]; [left; rewrite Hes in Ha; lia | right; left; exact Ha]) KP
ltac:(intros a Ha Hna; apply Hfr3; [exact Ha | intros Hx; apply Hna; right; exact Hx | intros Hx; apply Hna; left; lia]) Hpres3) as KP' end.
clear KP; rename KP' into KP.
jafter_call_keep_hi HS 544%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat HS3.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [| specialize (HS3 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
(eapply pz_region_kept; [pz_bases; reflexivity
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr3; unfold ESTACK, off_img, SB, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; mid_lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; mid_pres HJ3 ]). }
rewrite <- restrict_mkst_fx in HS3. clear HS; rename HS3 into HS.
pz_rebase HS AGX.
(* 3. The out struct is zero (memset); the frame and its shadow become read-only for the shadow-checked part. *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
assert (ROK : region_ok SEGS Ev (ms_mem msx) (YP09.mkRegion (Some 12%nat) 0 36 0 36 [YP09.mkChunk 0 (CZero 36)]));
[| assert (RDJ : all_disjoint Ev (YP09.mkRegion (Some 12%nat) 0 36 0 36 [YP09.mkChunk 0 (CZero 36)]) (ss_mem ssx))] end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
pz_bases. split; [lia|]. split; [unfold ASAN_CEIL in *; lia|]. split.
- intros o0 Ho0. apply (apresent_writable SEGS). apply (HOp _ _ (proj1 HJ3)). lia.
- apply Forall_cons; [|apply Forall_nil]. apply pz_chunk_zero. intros i Hi.
replace (o + 0 + i) with (o + i) by lia. rewrite (Heff3 i Hi). reflexivity. }
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
pz_bases.
revert Hslo Hshi H47 Hceil Hwin Hstk0 WS C1 Hsp1r Hob0 Hob1 Hob16 Hob17 Hflo Hfhi Holo Hohi Hfceil Hoceil Hf4096 Ho4096 HF4096 HFceil HFapp HFimg HsepF HsepO Hfapp Hoapp Hsp0 HF8lo HF8hi Hdfo Hcoimg Hcfimg.
unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB. clear. intros. repeat split; mid_lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_region Ev ssx msx (YP09.mkRegion (Some 12%nat) 0 36 0 36 [YP09.mkChunk 0 (CZero 36)]) HS eq_refl ROK RDJ) as HS' end.
clear HS ROK RDJ; rename HS' into HS. pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o0 Ho0; lia))) as HS' end.
clear HS; rename HS' into HS. pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 516%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o0 Ho0; lia))) as HS' end.
clear HS; rename HS' into HS. pz_norm HS.
(* 4. Cut M. *)
ra_join HS ss_cutM 560%nat pz_deadM ltac:(idtac).
pz_rebase HS AGX.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
assert (SHOK : sh_ok SEGS PZx PZ_SH Ev (mrestrict (w_H W) (ms_mem msv)));
[ apply (pz_shok Ev _ _ f o); [rewrite AGX by lia; exact E10 | rewrite AGX by lia; exact E12 | rewrite AGX by lia; exact E32
| lia | exact Hfap | lia | exact Hoap
| exact (pz_kept_ra B LAWS lyc Sc W memc mdc _ _ _ _ cf pf f 50 HAR KP Hfin Hflo Hfhi Hsh_f HRf)
| exact (pz_kept_ra B LAWS lyc Sc W memc mdc _ _ _ _ co po o 36 HAR KP Hoin Holo Hohi Hsh_o HRo) ]
| apply (HM Ev msv md3); [ | exact HS | exact SHOK | exact I ] ] end.
cbn [pz_cur pz_E0 cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc
cx_mdc cx_k cx_regs cx_ch cx_f cx_n cx_o cx_fr cx_S2 cx_fpos cx_cf cx_pf cx_co cx_po ms_mem].
split; [assumption|]. split; [exact AGX|]. split; [exact RF|]. split; [exact E528|]. split; [exact E529|].
split; [exact HJ3 | exact KP].
Qed.
End d.
End b.
