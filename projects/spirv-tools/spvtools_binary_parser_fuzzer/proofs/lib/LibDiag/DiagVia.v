(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim RefMemcpyLib LibIface LibEff.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Via.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.
Variable ST : StaticsIface SEGS L.
Hypothesis HLimg_lo : forall a, in_ranges (ly_img L) a -> a < alloc_ceiling.
Hypothesis HLrw_img : forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a.
Hypothesis HLrelro_img : forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a.
Hypothesis HLerr_img : forall a, errno_win L a -> in_ranges (ly_img L) a.
Hypothesis HLrw_relro : forall a, in_ranges (ly_rw L) a -> ~ in_ranges (ly_relro L) a.
Hypothesis HLerr_rw : forall a, errno_win L a -> in_ranges (ly_rw L) a.

Lemma hi_unowned : forall A M model a, ainv MI A M model -> alloc_ceiling <= a -> ~ owned MI A a.
Proof using AC SEGS L MI HLimg_lo HLrw_img.
  intros A M model a AI Ha Ho.
  destruct (ai_owned_not_img_ro MI A M model a AI Ho) as [Hrw|Hoff].
  - pose proof (HLimg_lo _ (HLrw_img _ Hrw)). lia.
  - pose proof (ai_owned_below_ceiling MI A M model a AI Ho Hoff). lia.
Qed.

Lemma hi_offimg : forall a, alloc_ceiling <= a -> ~ in_ranges (ly_img L) a.
Proof using AC L HLimg_lo. intros a Ha Hi. pose proof (HLimg_lo _ Hi). lia. Qed.

Lemma hi_not_errno : forall a, alloc_ceiling <= a -> ~ errno_win L a.
Proof using AC L HLimg_lo HLerr_img. intros a Ha He. exact (hi_offimg a Ha (HLerr_img _ He)). Qed.

Lemma img_ro_clear_of' : forall (s : SX ST) M, ro_clear L M -> sx_inv ST s M -> img_ro_clear L M.
Proof using SEGS L ST.
  intros s M RC SX. apply img_ro_clear_of; [exact RC|]. intros a Ha. exact (sx_relro ST s M a SX Ha).
Qed.

Lemma sx_inv_via_eff : forall (s0 : SX ST) (A A' : AS MI) M M' model (W : Z * Z) (F : Z -> Prop),
  sx_inv ST s0 M -> ainv MI A M model -> eff MI A A' M M' W F ->
  (forall a, owned MI A a -> ~ sx_region ST a) -> (forall a, errno_win L a -> ~ sx_region ST a) ->
  (forall a, F a -> ~ in_ranges (ly_img L) a) -> alloc_ceiling <= fst W ->
  sx_inv ST s0 M'.
Proof using AC SEGS L MI ST HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw.
  intros s0 A A' M M' model W F SX AI EF Hosx Hesx HF HW.
  apply (sx_frame ST s0 M M' SX). intros a Ha.
  assert (Himg : in_ranges (ly_img L) (bv_unsigned a)).
  { destruct Ha as [Hs | Hr]; [exact (HLrw_img _ (sx_region_rw ST _ Hs)) | exact (HLrelro_img _ Hr)]. }
  pose proof (HLimg_lo _ Himg) as Hlt.
  apply (ef_frame _ _ _ _ _ _ _ _ _ EF). intros [Ho | [Ho' | [Hnm | [Hf | [Hw | He]]]]].
  - destruct Ha as [Hs | Hr]; [exact (Hosx _ Ho Hs)|].
    destruct (ai_owned_not_img_ro MI A M model _ AI Ho) as [Hrw | Hni]; [exact (HLrw_relro _ Hrw Hr) | exact (Hni Himg)].
  - destruct (ef_own _ _ _ _ _ _ _ _ _ EF _ Ho') as [Ho | [[Hni _] | Hf]].
    + destruct Ha as [Hs | Hr]; [exact (Hosx _ Ho Hs)|].
      destruct (ai_owned_not_img_ro MI A M model _ AI Ho) as [Hrw | Hni]; [exact (HLrw_relro _ Hrw Hr) | exact (Hni Himg)].
    + exact (Hni Himg).
    + exact (HF _ Hf Himg).
  - destruct Hnm as (Hni & _). exact (Hni Himg).
  - exact (HF _ Hf Himg).
  - unfold W_of in Hw. lia.
  - destruct Ha as [Hs | Hr]; [exact (Hesx _ He Hs)|]. exact (HLrw_relro _ (HLerr_rw _ He) Hr).
Qed.

Lemma ro_clear_via_eff : forall (A A' : AS MI) M M' model (W : Z * Z) (F : Z -> Prop),
  ro_clear L M -> ainv MI A M model -> eff MI A A' M M' W F ->
  (forall a, F a -> ~ in_ranges (ly_img L) a) -> alloc_ceiling <= fst W ->
  ro_clear L M'.
Proof using AC SEGS L MI HLimg_lo HLerr_rw.
  intros A A' M M' model W F RC AI EF HF HW.
  eapply (ro_clear_frame L _ M M' RC (ef_frame _ _ _ _ _ _ _ _ _ EF)).
  intros a (Himg & Hnrw & Hnrel). pose proof (HLimg_lo _ Himg) as Hlt.
  intros [Ho | [Ho' | [Hnm | [Hf | [Hw | He]]]]].
  - destruct (ai_owned_not_img_ro MI A M model _ AI Ho) as [Hrw | Hni]; [exact (Hnrw Hrw) | exact (Hni Himg)].
  - destruct (ef_own _ _ _ _ _ _ _ _ _ EF _ Ho') as [Ho | [[Hni _] | Hf]].
    + destruct (ai_owned_not_img_ro MI A M model _ AI Ho) as [Hrw | Hni]; [exact (Hnrw Hrw) | exact (Hni Himg)].
    + exact (Hni Himg).
    + exact (HF _ Hf Himg).
  - destruct Hnm as (Hni & _). exact (Hni Himg).
  - exact (HF _ Hf Himg).
  - unfold W_of in Hw. lia.
  - exact (Hnrw (HLerr_rw _ He)).
Qed.

Lemma mdef_via_eff : forall (A A' : AS MI) M M' (W : Z * Z) (F : Z -> Prop) a n,
  eff MI A A' M M' W F -> alloc_ceiling <= a \/ (a + n <= alloc_ceiling /\ forall i, 0 <= i < n -> ~ in_ranges (ly_img L) (a + i)) ->
  0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> ~ owned MI A (a + i)) -> (forall i, 0 <= i < n -> ~ F (a + i)) ->
  mdef M a n -> mdef M' a n.
Proof using AC SEGS L MI HLimg_lo HLrw_img HLerr_rw.
  intros A A' M M' W F a n EF Ha Ha0 Han Hown HF Hdef i Hi. pose proof ac_bounds_lit as Hcv.
  destruct (ef_def _ _ _ _ _ _ _ _ _ EF (a + i) ltac:(lia) (Hdef i Hi)) as [H|[H|[H|H]]];
    [exact H | exfalso; exact (Hown i Hi H) | exfalso; exact (HF i Hi H) |].
  exfalso. pose proof (HLimg_lo _ (HLrw_img _ (HLerr_rw _ H))).
  destruct Ha as [Ha|[Ha Hni]]; [lia | exact (Hni i Hi (HLrw_img _ (HLerr_rw _ H)))].
Qed.

Lemma agree_via_eff : forall (A A' : AS MI) M M' (W : Z * Z) (F : Z -> Prop) (P : Z -> Prop),
  eff MI A A' M M' W F ->
  (forall a, P a -> 0 <= a < 2 ^ 64 /\ ~ owned MI A a /\ ~ owned MI A' a /\ M (Z_to_bv 64 a) <> None /\ ~ F a /\ ~ W_of W a /\ ~ errno_win L a) ->
  CRep.agree_on P M M'.
Proof using AC SEGS L MI.
  intros A A' M M' W F P EF HP a Ha. destruct (HP a Ha) as (Hr & Ho & Ho' & Hd & Hf & Hw & He).
  apply (ef_frame _ _ _ _ _ _ _ _ _ EF). rewrite u64_of_Z by lia.
  intros [H|[H|[H|[H|[H|H]]]]]; try tauto. destruct H as (_ & _ & Hn). exact (Hd Hn).
Qed.

Lemma agree_hi_via_eff : forall (A A' : AS MI) M M' model model' (W : Z * Z) (F : Z -> Prop) lo hi,
  eff MI A A' M M' W F -> ainv MI A M model -> ainv MI A' M' model' ->
  alloc_ceiling <= lo -> hi <= 2 ^ 64 -> mdef M lo (hi - lo) ->
  (forall a, lo <= a < hi -> ~ F a) -> (snd W <= lo \/ hi <= fst W) ->
  CRep.agree_on (zwin lo hi) M M'.
Proof using AC SEGS L MI HLimg_lo HLrw_img HLerr_img.
  intros A A' M M' model model' W F lo hi EF AI AI' Hlo Hhi HD HF HW.
  eapply agree_via_eff; [exact EF|]. intros a Ha. unfold zwin in Ha. pose proof ac_bounds_lit.
  split; [lia|]. split; [apply (hi_unowned A M model); [exact AI|lia]|]. split; [apply (hi_unowned A' M' model'); [exact AI'|lia]|].
  split; [replace a with (lo + (a - lo)) by lia; apply HD; lia|]. split; [apply HF; lia|].
  split; [unfold W_of; lia | apply hi_not_errno; lia].
Qed.

Lemma eff_widen : forall (A A' : AS MI) M M' (W W' : Z * Z) (F : Z -> Prop),
  eff MI A A' M M' W F -> fst W' <= fst W -> snd W <= snd W' -> eff MI A A' M M' W' F.
Proof using AC SEGS L MI.
  intros A A' M M' W W' F E H1 H2. destruct E as [C B O FR D OI]. constructor; try assumption.
  intros a Hn. apply FR. intros [H|[H|[H|[H|[H|H]]]]]; apply Hn; try tauto.
  right; right; right; right; left. unfold W_of in *. lia.
Qed.

Lemma eff_of_stores : forall (A : AS MI) M M' (W : Z * Z) (F G : Z -> Prop),
  stores_in G M M' -> (forall a, G a -> F a \/ W_of W a) -> eff MI A A M M' W F.
Proof using AC SEGS L MI.
  intros A M M' W F G [Ag D] HG. apply eff_store; [|exact D].
  intros a Hf Hw. apply Ag. intros Hg. destruct (HG _ Hg); tauto.
Qed.
End Via.
