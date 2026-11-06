(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfNil.v, sha256 759f43e471099c153ebd32d9f4e548ad397bd11c7c00db607a7fd3a0e289274f (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
*)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Taken by path from a working branch a0fed4266a1b, provisional. *)
(* Modified by Theorem Labs, 2026-10: module paths changed from fuzz_preset lib.Reusable to cgif_file_fuzzer lib; the text is otherwise unchanged. *)
(* Theorem Labs, 2026-10: the conversion point of the event-free second allocator instance (suffix cf).
   cgif's AR (YG0n.v:490-491) at a state implies ARcf (YG0ncf.v) at the same state with Hp = [], at an
   exposed world W' (wle W W') that adds class 1's shadow band; the driver switches once, at main. Two forms:
   - ARcf_nil_gen takes the hull premise with class 1's band added (sec_hulls + cls1_band_bytes_cf <= the
     credit not yet spent + the cf terms, with the unit's hull term cf_hull, YGcfNames.v).
   - ARcf_nil takes `sec_hulls S <= cf_hull S` (at init both are 0: cf_hull_init) and derives the hull premise
     from the event credit.
   No cgif file and no cf file is edited. No address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG08cf YGcfImgRows.
(* stdpp, through the LPS modules, shadows NoDup and Forall_forall; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section N.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------- *)
(* 3. The junk. ajunk_cf is cgif's ajunk with region_junk_cf = region_junk: the exhausted byte RI+68 is not junk     *)
(*    (ARmcf's amc_exh_cell pins it, field round 2). cfn_cell_vis: a cell that holds a value is visible.            *)
Lemma cfn_cell_vis : forall B ly rd a w e n, n = Z.of_nat w ->
cell_holds B ly rd (ACell a w (AV e)) -> range_vis B ly rd (a, n).
Proof.
intros B ly rd a w e n -> H i Hi. cbn [fst snd] in Hi |- *. unfold cell_holds in H. cbn [c_at c_w c_val] in H.
specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. rewrite H. discriminate.
Qed.

Lemma cfn_ajunk_split : forall B ly S x, In x (ajunk_cf B ly S) -> In x (ajunk B ly S).
Proof.
intros B ly S x H. unfold ajunk_cf in H. unfold ajunk.
destruct H as [H|[H|H]]; [left; exact H | right; left; exact H|].
right. right. exact H.
Qed.

Lemma cfn_ajunk_vis : forall B ly S rd,
Forall (range_vis B ly rd) (ajunk B ly S) -> Forall (range_vis B ly rd) (ajunk_cf B ly S).
Proof.
intros B ly S rd HJ. apply Forall_forall. intros x Hx.
exact (proj1 (Forall_forall _ _) HJ x (cfn_ajunk_split B ly S x Hx)).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. ARmcf from ARm at Hp = [], given the errbuf slot's placement, the two machine cells, Printf's two image cells
   (field round 3) and the unit's image rows (ARmcf's last fields; the conversion is a FRESH builder, so the rows are
   its premises). *)
Lemma cfn_ARmcf_nil : forall B ly S rd, ARm B ly S rd -> Compl0 S ->
Z.of_nat (length (st_sec_arr S)) <= cf_sec_live_max -> xs_placed_cf ly S ->
exh_cell_cf B ly S rd -> errb_cells_cf B ly S rd -> pf_cells_cf B ly rd ->
EXH_OFF_t /\ errb_obj_owned_t B /\ errb_ial_apart_t B -> pf_cells_owned_t B -> ARmcf B ly S [] rd.
Proof.
intros B ly S rd M HC HS HX HE HR HPF HO HPO. constructor;
try (exact (am_universe _ _ _ _ M)); try (exact (am_syms _ _ _ _ M)); try (exact (am_layout _ _ _ _ M));
try (exact (am_placed _ _ _ _ M)); try (exact (am_const _ _ _ _ M)); try (exact (am_const_owned _ _ _ _ M));
try (exact (am_fa _ _ _ _ M)); try (exact (am_flags _ _ _ _ M)); try (exact (am_depot _ _ _ _ M));
try (exact (am_zshadow _ _ _ _ M)); try (exact (am_areas _ _ _ _ M)); try (exact (am_client _ _ _ _ M));
try (exact (am_zero _ _ _ _ M)); try (exact (am_tsd _ _ _ _ M)); try (exact (am_static_img _ _ _ _ M)).
- unfold Wf_cf. apply WfP_cf_of_WfP; [exact (am_wf _ _ _ _ M) | exact HC | exact HS].
- apply Forall_forall. intros c Hc.
  exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ M) c (acells_cf_incl B ly S c Hc)).
- apply shadow_ok_cf_nil. exact (am_shadow _ _ _ _ M).
- exact (cfn_ajunk_vis B ly S rd (am_junk _ _ _ _ M)).
- constructor.
- exact HX.
- exact HE.
- exact HR.
- exact HO.
- exact HPF.
- exact HPO.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 5. The budget. abudget S = A_BASE + EV_A * st_nev S + sec_hulls S + sec_live_bytes S (YG0n.v:383);  *)
(*    A_BASE_CF = A_BASE + EV_A * EV_MAX absorbs the event term, the hull term is the premise. The      *)
(*    budget is checked at W', the entry world W with class 1's shadow band exposed (YGcfNilInit.v):   *)
(*    w_A grows by at most cls1_band_bytes_cf, which the premise fits beside the hulls, and the band   *)
(*    (abudget_ok_cf's third conjunct) is visible at W'.                                              *)
Lemma cfn_abudget_ok_cf : forall segs ly S (W W' : world segs),
abudget_ok segs ly S W -> errb_cap_cf S = 0 -> 0 <= prim_committed S -> 0 <= st_sec_reserved S ->
sec_hulls S + cls1_band_bytes_cf <= EV_A * (EV_MAX - st_nev S) + prim_committed S + 8 * st_sec_reserved S + cf_hull S ->
(forall i, In i (w_A W) -> In i (w_A W')) -> A_bytes (w_A W') <= A_bytes (w_A W) + cls1_band_bytes_cf ->
cls1_band_vis_cf ly (w_H W') ->
abudget_ok_cf segs ly S W'.
Proof.
intros segs ly S W W' [HA HS] HE HP HR HH HI HB HV.
split; [|split; [exact (asecA_transfer ly ly S S _ _ HS (fun e He => He) HI) | exact HV]].
(* abudget_cf's term beyond cgif's (prim_committed / 8) is nonnegative *)
pose proof (Z.div_pos (prim_committed S) 8 HP ltac:(lia)) as HP8.
unfold abudget in HA. unfold abudget_cf, A_BASE_CF. rewrite HE.
unfold A_BASE, EV_A, EV_MAX in *. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 6. The conversion. cgif's AR holds at the entry world W; ARcf holds at W', which is W with      *)
(*    class 1's shadow band exposed: wle W W', w_A W' contains w_A W and adds at most             *)
(*    cls1_band_bytes_cf, and the band is visible at W'. YGcfNilInit.v builds W' (wallow).         *)
Theorem ARcf_nil_gen : forall segs B ly S (W W' : world segs) mem md,
AR segs B ly S W mem md -> st_nev S < EV_MAX -> mtr_ok S (EV_A * EV_MAX) ->
Compl0 S -> Z.of_nat (length (st_sec_arr S)) <= cf_sec_live_max -> errb_cap_cf S = 0 ->
sec_hulls S + cls1_band_bytes_cf <= EV_A * (EV_MAX - st_nev S) + prim_committed S + 8 * st_sec_reserved S + cf_hull S ->
xs_placed_cf ly S -> xs_cf ly S = [] ->
wle W W' -> (forall i, In i (w_A W) -> In i (w_A W')) -> A_bytes (w_A W') <= A_bytes (w_A W) + cls1_band_bytes_cf ->
cls1_band_vis_cf ly (w_H W') ->
(forall x, YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x = true -> YK0g.covered (vm_maps (m_vmmaps md)) x = true) ->
exh_cell_cf B ly S (aview segs (w_H W') mem) -> errb_cells_cf B ly S (aview segs (w_H W') mem) ->
pf_cells_cf B ly (aview segs (w_H W') mem) ->
EXH_OFF_t /\ errb_obj_owned_t B /\ errb_ial_apart_t B -> pf_cells_owned_t B ->
ARcf segs B ly S [] W' mem md.
Proof.
intros segs B ly S W W' mem md (M & L & BU & MW & HS) Hev Hm HC HSL HE HH HX HXS Hs HI HB HV LM CE CR CP HO HPO.
assert (M' : ARm B ly S (aview segs (w_H W') mem)) by (eapply ARm_ext; [|exact M]; apply aview_ext; [apply w_Hoff | exact Hs]).
pose proof (cfn_ARmcf_nil B ly S _ M' HC HSL HX CE CR CP HO HPO) as MC.
assert (Wcf : WfP_cf (as_universe B) 0 0 0 S) by exact (amc_wf _ _ _ _ _ MC).
pose proof (prim_committed_bound_cf _ _ _ _ S Wcf) as [HP _].
pose proof (sec_reserved_bound_cf _ _ _ _ S Wcf) as [HR _].
split; [exact MC|]. split; [eapply ALedger_cf_of_ALedger; [exact L | exact HXS | exact LM]|].
split; [|split; [exact MW | exact (ahs_hsub B ly S _ _ mem Hs HS)]].
apply (cfn_abudget_ok_cf segs ly S W W' BU HE HP); [lia | exact HH | exact HI | exact HB | exact HV].
Qed.

(* The band fits in the event credit not yet spent: EV_A * st_nev S + cls1_band_bytes_cf <= EV_A * EV_MAX. *)
Theorem ARcf_nil : forall segs B ly S (W W' : world segs) mem md,
AR segs B ly S W mem md -> st_nev S < EV_MAX -> mtr_ok S (EV_A * EV_MAX) ->
Compl0 S -> Z.of_nat (length (st_sec_arr S)) <= cf_sec_live_max -> errb_cap_cf S = 0 ->
sec_hulls S <= cf_hull S -> xs_placed_cf ly S -> xs_cf ly S = [] ->
EV_A * st_nev S + cls1_band_bytes_cf <= EV_A * EV_MAX ->
wle W W' -> (forall i, In i (w_A W) -> In i (w_A W')) -> A_bytes (w_A W') <= A_bytes (w_A W) + cls1_band_bytes_cf ->
cls1_band_vis_cf ly (w_H W') ->
(forall x, YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x = true -> YK0g.covered (vm_maps (m_vmmaps md)) x = true) ->
exh_cell_cf B ly S (aview segs (w_H W') mem) -> errb_cells_cf B ly S (aview segs (w_H W') mem) ->
pf_cells_cf B ly (aview segs (w_H W') mem) ->
EXH_OFF_t /\ errb_obj_owned_t B /\ errb_ial_apart_t B -> pf_cells_owned_t B ->
ARcf segs B ly S [] W' mem md.
Proof.
intros segs B ly S W W' mem md A Hev Hm HC HSL HE HH HX HXS HF Hs HI HB HV LM CE CR CP HO HPO.
pose proof A as (M & _).
assert (M' : ARm B ly S (aview segs (w_H W') mem)) by (eapply ARm_ext; [|exact M]; apply aview_ext; [apply w_Hoff | exact Hs]).
pose proof (cfn_ARmcf_nil B ly S _ M' HC HSL HX CE CR CP HO HPO) as MC.
assert (Wcf : WfP_cf (as_universe B) 0 0 0 S) by exact (amc_wf _ _ _ _ _ MC).
pose proof (prim_committed_bound_cf _ _ _ _ S Wcf) as [HP _].
pose proof (sec_reserved_bound_cf _ _ _ _ S Wcf) as [HR _].
apply (ARcf_nil_gen segs B ly S W W' mem md A Hev Hm HC HSL HE);
[| exact HX | exact HXS | exact Hs | exact HI | exact HB | exact HV | exact LM | exact CE | exact CR | exact CP | exact HO
 | exact HPO].
unfold EV_A, EV_MAX in *. lia.
Qed.

End N.
