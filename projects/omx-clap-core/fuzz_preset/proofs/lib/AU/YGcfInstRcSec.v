(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/YGcfInstRcSec.v (commit ce1a656b52b7, file sha256 cb8dee0851e5) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 2 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/YGcfInstRcSec.v (commit f02099425ace, round-3 cf layer, field round 3 (d0377850faa + 91bb9319bae); reply-rccf; file sha256 b249de0dd331) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfInstRcSec.v at commit 2c35faeeaec, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (1 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10: the generic cf instance layer, lane F2b (second hand of the lane): the SECONDARY arm of
   __asan::QuarantineCallback::Recycle's read fields over the drain's cut relation, the cf twin of
   YFf4.rs_fin_ARm (YFf4.v:1080).
   rule 24: no function proved (kind: relational transport of the RChunk post to the cf cut relation ARcfR).

   Lane B1's slice H4 states the secondary fields (commit a7bbacac3615, proofs/cgif/cgif_file_fuzzer/lib/
   DMrcSecReads.v: rc_sec_cut_t, rc_sec_mapr_t, rc_sec_step_t) over `world tfibsegs` and over its own machine
   predicates (DMrcSecGv.at_RET / WIN3, DMrcSecMun.LINKD / WPRE, DMrcSecFc.sec_cut, the literal TFIB_TSD), so that
   text cannot be stated at the cf instance, which is generic in ImgBase.AImg.  CfF2b (2026-10-30 02:4xZ) approved
   the F12 shape instead, which is what this file proves: the window and the memory premise are stated HERE, in the
   image-free form, and H4 writes the one bridge from at_RET / LINKD to these premises, as F12's walk does for
   CacheDealloc.
   The window is YFf4's (YFf4.v:78-87) with as_inst B for cgif's A_ALLOCATOR: the stack window below the entry sp
   [rsDS], four allocator word ranges [rsDI] (the mutex and the count carry written values), the two thread-stats
   pairs [rsDJ], the pointer-array slot
   of the dead entry [rsDQ], the last entry's index word [rsDL], the unmapped map's shadow [rsDH] and the unmapped
   map itself [rsDM].  The model step is YFf4.X2's text [rsX2]: the chunk deleted (YFf3.X1), the secmap marked dead
   and the pointer array swap-removed.  The world is refunded by the dead map's allowance ([W2] = YFfn.wrefund at
   (MAP, MAP + LEN), YFg8.v:77's text over im_segs); the model is the unmap of (MAP, LEN).
   PROVED here, in [rc_sec_step_sl_cf]: at (rsX2, W2) over the view after the call, the issuer row, ARmcfR (every
   cell, shadow, visible range and placement fact), ALedger_cf after the unmap ([ALedger_cf_munmap],
   YG0j.ALedger_munmap over the cf ledger), the budget loosened by cf_rec_drop (sm_len sm) with the allowance half
   (asecA, the band clause), amwf (YFfn.munmap_amwf), ahs, and
   the xs_mapped_cf keep (no xs extent is based at the dead map); plus the window in the owned set or the stack
   scratch, the owned set shrinks, and the window is apart from every primary user byte.
   Premises: the call's own frame (MEQ off rsD, presence off the dead map, the written words MUT' / NS' / QI' /
   LST', the constant cells CONST', the band bytes off rsD keep their memory, the dead map's shadow reads 0), the
   model after the unmap, two named image premises over ImgBase.AImg ([IMG_SAPART]: the four written allocator word
   ranges are apart from the depot, store and internal-allocator areas; [IMG_JUNK]: every byte of the image's junk
   ranges lies in a segment of im_segs, which the cut relation's ledger (alc_img) places in the image window), and
   the row ERRB_QAPART.  The post's budget is LOOSENED (YGcfRehideAR.ARcfR_sl, a prior worker's core): the world still holds
   the dead map's hull until the re-hide, while abudget_cf drops by LEN and at most the unit's per-recycle hull charge
   cf_rec_drop (sm_len sm) ([abudget_X2], YGcfAbudget.abudget_recycle_cf by CfParams's cf_hull_recycle) and
   YFfn.A_bytes_refund drops A_bytes by LEN; so the post holds at slack d := cf_rec_drop (sm_len sm).  The consumer
   lifts it to the re-hide's slack rh_hi MAP LEN - rh_lo MAP by YGcfRehideAR.ARcfR_sl_mono and the unit's law
   (reply_rec_drop_le_rh / preset_rec_drop_le_rh, YGcfRehideAR.v).
   Image-free (no image literal, no cgif segment list) and event-free (no event-count term, no event regime and no
   event-keyed budget appears). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08 YP03.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfTok YG03cf YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstDrainR YGcfInstDrainRL.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFeu YFf3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0v YK0g YA06 YG0h YG0j YFfn YGcfXsMapped YGcfLazyMaps.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstBase YGcfInstDrainX.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfImgRows.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfAbudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehideAR.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.
Ltac ceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg}.
Local Open Scope am_scope.

Lemma pairwise_nth_f : forall {A} (R : A -> A -> Prop) l i j x y, pairwise R l -> (i < j)%nat ->
nth_error l i = Some x -> nth_error l j = Some y -> R x y.
Proof.
intros A R l. induction l as [|h t IH]; intros i j x y HP Hij Hi Hj; [destruct i; discriminate|].
destruct HP as [HF HP]. destruct i as [|i]; destruct j as [|j]; try lia.
- cbn in Hi, Hj. injection Hi as <-. exact (proj1 (Forall_forall _ _) HF y (nth_error_In _ _ Hj)).
- cbn in Hi, Hj. exact (IH i j x y HP ltac:(lia) Hi Hj).
Qed.

Lemma Forall_flat_map_in : forall {A C} (Q : C -> Prop) (f : A -> list C) l x, Forall Q (flat_map f l) -> In x l -> Forall Q (f x).
Proof. intros A C Q f l x H Hx. apply Forall_forall. intros y Hy. apply (proj1 (Forall_forall _ _) H). apply in_flat_map. exists x. auto. Qed.

(* copy of YFex.v:71 *)
Lemma find_chunk_at_app_cf : forall B ly l1 l2 g,
find_chunk_at B ly (l1 ++ l2) g = match find_chunk_at B ly l1 g with Some x => Some x | None => find_chunk_at B ly l2 g end.
Proof. intros B ly l1 l2 g. induction l1 as [|x t IH]; cbn; [reflexivity|]. destruct (_ && _); [reflexivity | exact IH]. Qed.

(* copy of YFf4.v:826 *)
Lemma in_rangesb_remove : forall g A Bq lo len, ~ (lo <= g < lo + len) -> in_rangesb g (A ++ (lo, len) :: Bq) = in_rangesb g (A ++ Bq).
Proof.
intros g A Bq lo len Hn. induction A as [|[lo' len'] A IH]; cbn [app in_rangesb].
- replace ((lo <=? g) && (g <? lo + len)) with false; [reflexivity|]. symmetry. apply Bool.andb_false_iff.
  destruct (Z_lt_le_dec g lo); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
- rewrite IH. reflexivity.
Qed.

(* copies of YFf4.v:20-48 (that file is not required here: it fixes the zify euclidean-division flag globally) *)
Lemma nth_error_removelast_lt : forall {A} (l : list A) j, (S j < length l)%nat ->
nth_error (YG00.removelast l) j = nth_error l j.
Proof.
intros A l. induction l as [|x t IH]; intros j Hj; [cbn in Hj; lia|].
destruct t as [|y t']; [cbn in Hj; lia|]. cbn [YG00.removelast]. destruct j as [|j]; [reflexivity|]. cbn [nth_error].
apply IH. cbn [length] in Hj |- *. lia.
Qed.
Lemma last_nth_error : forall {A} (l : list A) (d : A), l <> [] -> nth_error l (length l - 1) = Some (last l d).
Proof.
intros A l d Hl. induction l as [|x t IH]; [congruence|]. destruct t as [|y t']; [reflexivity|].
specialize (IH ltac:(discriminate)). replace (length (x :: y :: t') - 1)%nat with (S (length (y :: t') - 1))%nat by (cbn [length]; lia).
cbn [nth_error]. rewrite IH. reflexivity.
Qed.
Lemma in_combine_seq_iff : forall {A} (l : list A) s j (x : A),
In (j, x) (combine (seq s (length l)) l) <-> exists j', j = (s + j')%nat /\ nth_error l j' = Some x.
Proof.
intros A l. induction l as [|y t IH]; intros s j x.
- cbn. split; [intros [] | intros (j' & _ & H); destruct j'; discriminate H].
- cbn [length seq combine In]. rewrite IH. split.
  + intros [E | (j' & -> & H)]; [injection E as <- <-; exists 0%nat; split; [lia | reflexivity] | exists (S j'); split; [lia | exact H]].
  + intros (j' & -> & H). destruct j' as [|j']; [left; injection H as ->; f_equal; lia | right; exists j'; split; [lia | exact H]].
Qed.
Lemma in_combine_seq0 : forall {A} (l : list A) j (x : A), In (j, x) (combine (seq 0 (length l)) l) <-> nth_error l j = Some x.
Proof.
intros A l j x. rewrite in_combine_seq_iff. split; [intros (j' & -> & H); exact H | intros H; exists j; split; [lia | exact H]].
Qed.
Lemma index_ofZ_nth : forall l j x, NoDup l -> nth_error l j = Some x -> index_ofZ l x = Z.of_nat j.
Proof.
intros l j x ND H. unfold index_ofZ. destruct (index_of_spec l x 0%nat (nth_error_In _ _ H)) as (j' & E & H').
rewrite Nat.add_0_l in E. rewrite E. f_equal.
apply (proj1 (NoDup_nth_error _) ND); [exact (nth_error_lt _ _ _ H') | rewrite H, H'; reflexivity].
Qed.

(* The image premise (named, over ImgBase.AImg's im_syms and the symbol table only; the pattern of
   YGcfInstDrainX.IMG_QAPART): the allocator words the secondary arm writes are apart from the depot, store and
   internal-allocator areas of the symbol table.  cgif: by its numerals (YFf4.v:727 / :736 / :774). *)
Definition sdeal_inst (B : asyms) (a : Z) : Prop :=
(as_inst B + 680 <= a < as_inst B + 684) \/ (as_inst B + 120 <= a < as_inst B + 129) \/
(as_inst B + 144 <= a < as_inst B + 160) \/ (as_inst B + 704 <= a < as_inst B + 720).
Definition IMG_SAPART : Prop :=
forall B, im_syms B -> forall a, sdeal_inst B a ->
~ (as_depot B <= a < as_depot B + 4 * 2 ^ 20 + 32) /\ ~ (as_store B <= a < as_store B + 32) /\
~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
(* Every byte of the image's own junk ranges lies in one of the image's segments (cgif: TfibSyms' ts_junk puts the
   junk in [0xa2000, 0x601000)).  The cut relation's ledger places every segment in the image window (ALedger_cf's
   alc_img), so no window-cover premise is needed. *)
Definition IMG_JUNK : Prop :=
forall B ly r0, im_syms B -> layout_ok ly -> In r0 (as_junk B ly) -> forall j, 0 <= j < snd r0 ->
exists sg, In sg im_segs /\ Z.of_N (seg_base sg) <= aeval B ly (fst r0) + j < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).

(* Marking a non-error-buffer entry dead keeps the error buffer's extent (is_errb_cap reads only sm_size). *)
Lemma filter_lupd_same : forall (l : list secmap) n v f, (forall sm, nth_error l n = Some sm -> f v = f sm) -> f v = false ->
filter f (lupd l n v) = filter f l.
Proof.
induction l as [|h t IH]; intros n v f Hn Hv; [destruct n; reflexivity|].
destruct n as [|n]; cbn [lupd filter].
- rewrite Hv. rewrite <- (Hn h eq_refl), Hv. reflexivity.
- destruct (f h); [f_equal|]; apply IH; auto.
Qed.
Lemma last_cap_idx_lupd : forall (l : list secmap) n v j acc, (forall sm, nth_error l n = Some sm -> is_errb_cap v = is_errb_cap sm) ->
last_cap_idx (lupd l n v) j acc = last_cap_idx l j acc.
Proof.
induction l as [|h t IH]; intros n v j acc Hn; [destruct n; reflexivity|].
destruct n as [|n]; cbn [lupd last_cap_idx].
- rewrite (Hn h eq_refl). reflexivity.
- apply IH. exact Hn.
Qed.



Ltac mproj' :=
repeat first [ rewrite YK0g.m_vmmaps_with_vm_backing | rewrite YK0g.m_vm_lazy_with_vm_backing
| rewrite YK0g.m_vmmaps_with_vmmaps | rewrite YK0g.m_vm_lazy_with_vmmaps ].

(* YG0j.ALedger_munmap (YG0j.v:438) over ALedger_cf: the unmap of one secondary extent e keeps the cf ledger at a
   state whose extents lose e and whose regions, committed bytes, reserved count and errbuf entry are unchanged.
   cgif's WfP premise is replaced by the size bound it was used for, and cgif's counter premise by the errbuf's. *)
Lemma ALedger_cf_munmap : forall ly S S' md (e : Z * Z) E1 E2,
layout_ok ly -> Forall (fun e => 4096 <= snd e < 2 ^ 64) (sec_extents ly S) -> sec_placed ly S -> xs_placed_cf ly S -> amwf md ->
ALedger_cf im_segs ly S md ->
sec_extents ly S = E1 ++ e :: E2 -> sec_extents ly S' = E1 ++ E2 ->
(forall c, 1 <= c <= 31 -> reg S' c = reg S c) -> prim_committed S' = prim_committed S ->
st_sec_reserved S' = st_sec_reserved S -> errb_zone ly S' = errb_zone ly S -> errb_cap_cf S' = errb_cap_cf S ->
let md' := YK0v.munmap_model (YG0n.w64 (fst e)) (YG0n.w64 (snd e)) md in
ALedger_cf im_segs ly S' md'.
Proof.
intros ly S S' md e E1 E2 LO SZ PL XP MW L ES ES' REG PC SR EZ EC md'.
destruct PL as [PF PD].
assert (He : In e (sec_extents ly S)) by (rewrite ES; apply in_app_iff; right; left; reflexivity).
pose proof (proj1 (Forall_forall _ _) PF e He) as (EA & [EH1 EH2] & EC'). pose proof (proj1 (Forall_forall _ _) SZ e He) as ESZ. cbn beta in ESZ.
pose proof alloc_ceiling_val as CV. pose proof (lo_high ly LO) as HI.
assert (UE1 : bv_unsigned (YG0n.w64 (fst e)) = fst e) by (unfold YG0n.w64; rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | ceil; unfold bv_modulus, kHighMemBeg, ASAN_CEIL in *; lia]).
assert (UE2 : bv_unsigned (YG0n.w64 (snd e)) = snd e) by (unfold YG0n.w64; rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | unfold bv_modulus in *; lia]).
assert (WINJ : forall z, 0 <= fst z < 2 ^ 64 -> 0 <= snd z < 2 ^ 64 -> wiv z = wiv e -> z = e).
{ intros z B1 B2 Heq. pose proof (f_equal (fun q => bv_unsigned (fst q)) Heq) as X1. pose proof (f_equal (fun q => bv_unsigned (snd q)) Heq) as X2.
  cbn [fst snd wiv] in X1, X2. rewrite UE1 in X1. rewrite UE2 in X2. unfold YG0n.w64 in X1, X2.
  rewrite Z_to_bv_unsigned, bv_wrap_small in X1 by (unfold bv_modulus; lia). rewrite Z_to_bv_unsigned, bv_wrap_small in X2 by (unfold bv_modulus; lia).
  destruct z; cbn [fst snd] in *; subst; destruct e; reflexivity. }
assert (APART : forall e', In e' (E1 ++ E2) -> zdisjoint e' e).
{ intros e' He'. rewrite ES, <- app_assoc in PD. cbn [app] in PD. destruct (YG0j.pairwise_app_mid zdisjoint E1 e (E2 ++ static_extents ly) PD) as [D1 D2].
  apply in_app_iff in He' as [He'|He']; [exact (D1 e' He')|]. pose proof (D2 e' ltac:(apply in_app_iff; left; exact He')) as D. unfold zdisjoint in *. lia. }
assert (STAT : forall y, In y (static_extents ly) -> zdisjoint e y).
{ intros y Hy. rewrite ES, <- app_assoc in PD. cbn [app] in PD. destruct (YG0j.pairwise_app_mid zdisjoint E1 e (E2 ++ static_extents ly) PD) as [_ D2].
  exact (D2 y ltac:(apply in_app_iff; right; exact Hy)). }
destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 L16 L17].
destruct (in_split _ _ (L7 e He)) as (M1 & M2 & EM).
destruct (YG0j.eager_used_munmap (wiv e) md M1 M2 MW EM) as [EG VM']. cbn [fst snd wiv] in EG, VM'. rewrite UE1, UE2 in EG.
replace (fst e, snd e) with e in EG by (destruct e; reflexivity). fold md' in EG, VM'.
pose proof MW as MW0. destruct MW as [(MW1 & MW2 & MW3 & PW & _) NE].
assert (MWF : YK0g.model_ivs_wf md).
{ split; [|split; [|split]]; [intros q Hq; exact (MW1 q Hq) | intros q Hq; exact (MW2 q Hq) | intros q Hq; exact (MW3 q Hq) | exact (ceil_top_init_sp_ok _ L13)]. }
assert (SURV : forall x, In x (vm_maps (m_vmmaps md)) -> x <> wiv e -> In x (M1 ++ M2)).
{ intros x Hx Hne. rewrite EM in Hx. apply in_app_iff in Hx as [Hx|[Hx|Hx]]; [apply in_app_iff; left; exact Hx | exfalso; exact (Hne (eq_sym Hx)) | apply in_app_iff; right; exact Hx]. }
assert (RES' : vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md)) by (subst md'; unfold YK0v.munmap_model, with_mmap_destroyed, vm_forget_range; mproj'; reflexivity).
assert (LIM' : vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md)) by (subst md'; unfold YK0v.munmap_model, with_mmap_destroyed, vm_forget_range; mproj'; reflexivity).
assert (MMB' : vm_mmap_base (m_vmmaps md') = vm_mmap_base (m_vmmaps md)) by (subst md'; unfold YK0v.munmap_model, with_mmap_destroyed, vm_forget_range; mproj'; reflexivity).
assert (ISP' : vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md)) by (subst md'; unfold YK0v.munmap_model, with_mmap_destroyed, vm_forget_range; mproj'; reflexivity).
assert (TOP' : alloc_top (m_vmmaps md') = alloc_top (m_vmmaps md)) by (unfold alloc_top; rewrite ISP'; reflexivity).
(* the eager list without the dead extent: the other secondary extents and the errbuf zone, all apart from e *)
assert (XSA : forall z, In z (errb_zone ly S) -> zdisjoint z e /\ 0 <= fst z /\ fst z + snd z <= alloc_ceiling /\ 0 <= snd z).
{ intros z Hz. unfold errb_zone in Hz. pose proof (proj1 (Forall_forall _ _) XP z Hz) as (P1 & [P2a P2b] & P3 & P4).
  assert (SZ0 : 0 <= snd z).
  { unfold xs_cf in Hz. destruct (last_cap_idx (st_secs S) 0 None); [|destruct Hz].
    destruct Hz as [<-|[]]. cbn [snd]. apply errb_cap_cf_nonneg. }
  split; [exact (proj1 (Forall_forall _ _) P4 e ltac:(apply in_app_iff; left; exact He))|]. lia. }
assert (ESX : esec (vm_noaccess (m_vmmaps md')) (m_vm_lazy md') ((E1 ++ E2) ++ errb_zone ly S) =
  esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) ((E1 ++ E2) ++ errb_zone ly S)).
{ apply esec_ext.
  - apply Forall_forall. intros e' He'. apply in_app_iff in He' as [He'|He'].
    + assert (In e' (sec_extents ly S)) as Hin by (rewrite ES; apply in_app_iff in He' as [?|?]; apply in_app_iff; [left|right;right]; assumption).
      pose proof (proj1 (Forall_forall _ _) PF e' Hin) as (_ & [H1 H2] & H3). pose proof (proj1 (Forall_forall _ _) SZ e' Hin) as H4. cbn beta in H4.
      ceil; unfold kHighMemBeg, ASAN_CEIL in *. lia.
    + destruct (XSA e' He') as (_ & Z1 & Z2 & Z3). pose proof alloc_ceiling_lt as ACL. change (2 ^ 47) with 140737488355328 in ACL. lia.
  - intros e' x He' Hx. subst md'. rewrite (YG0j.cov_munmap (YG0n.w64 (fst e)) (YG0n.w64 (snd e)) md x MWF); [reflexivity|]. rewrite UE1, UE2.
    apply in_app_iff in He' as [He'|He'].
    + pose proof (APART e' He') as D. unfold zdisjoint in D. lia.
    + destruct (XSA e' He') as (D & _). unfold zdisjoint in D. lia. }
assert (MONO1 : forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S c') <= rg_mapped_user (reg S' c') /\ rg_mapped_fa (reg S c') <= rg_mapped_fa (reg S' c'))
by (intros c' Hc'; rewrite (REG c' Hc'); lia).
assert (HOLES : forall c', 1 <= c' <= 31 -> rg_holes (reg S' c') = rg_holes (reg S c')) by (intros c' Hc'; rewrite (REG c' Hc'); reflexivity).
unfold eager_cf in *.
constructor; try unfold eager_cf; rewrite ?VM', ?RES', ?LIM', ?MMB', ?TOP', ?ES', ?PC, ?SR, ?EZ, ?ESX, ?EG, ?EC; try assumption;
try (destruct L15 as [N1 N2];
assert (NAS : vm_noaccess (m_vmmaps md') = maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned (YG0n.w64 (fst e))) (bv_unsigned (YG0n.w64 (fst e)) + bv_unsigned (YG0n.w64 (snd e))))
by (subst md'; destruct md as [fd0 [maps0 lz0 mt0] io0 fs0 proc0 lim0 tm0]; reflexivity);
rewrite NAS; split; apply YA06.region_free_subtract; first [exact MW2 | assumption]).
- destruct L4 as (pieces & (P1 & P2 & P3) & P4). exists pieces. split; [split; [|split; [exact P2|]]|].
  + eapply Forall_impl; [|exact P1]. intros p (A & B0 & C). split; [exact A|]. split; apply (YG0h.cut_ok_mono ly S S' MONO1); assumption.
  + intros x Hx. rewrite (P3 x Hx). rewrite (YG0h.prim_hole_at_same ly S S' HOLES x). tauto.
  + intros p. rewrite (P4 p). split.
    * intros (Hin & B1 & B2 & B3). split; [|auto]. apply SURV; [exact Hin|]. intros Heq.
      destruct HI as [HP1 HP2].
      pose proof (WINJ p ltac:(ceil; unfold kHighMemBeg, kPrimResvSize, ASAN_CEIL in *; lia) ltac:(ceil; unfold kHighMemBeg, kPrimResvSize, ASAN_CEIL in *; lia) Heq) as ->.
      pose proof (STAT (ly_prim ly, kPrimResvSize) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
    * intros (Hin & B1 & B2 & B3). split; [|auto]. rewrite EM. apply in_app_iff in Hin as [?|?]; apply in_app_iff; [left|right;right]; assumption.
- apply SURV; [exact L5|]. intros Heq.
  pose proof (proj1 (Forall_forall _ _) (lo_app ly LO) (ly_Q ly, kPtrArrayResv) ltac:(unfold owned_extents; cbn; tauto)) as [HQ1 HQ2]. cbn [fst snd] in HQ1, HQ2.
  pose proof (WINJ (ly_Q ly, kPtrArrayResv) ltac:(cbn; ceil; clear - HQ1 HQ2 CR; unfold kLowShadowBeg, kHighMemBeg, kPtrArrayResv, ASAN_CEIL in *; lia) ltac:(cbn; unfold kPtrArrayResv; lia) Heq) as X.
  pose proof (STAT (ly_Q ly, kPtrArrayResv) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D. rewrite <- X in D. unfold zdisjoint in D. cbn [fst snd] in D. unfold kPtrArrayResv in D. lia.
- apply SURV; [exact L6|]. intros Heq.
  pose proof (WINJ (kHighShadowBeg, kHighShadowEnd - kHighShadowBeg) ltac:(cbn; unfold kHighShadowBeg, kHighShadowEnd; lia) ltac:(cbn; unfold kHighShadowBeg, kHighShadowEnd; lia) Heq) as X.
  apply (f_equal fst) in X. cbn [fst] in X. clear - X EH1 EH2 ESZ. unfold kHighShadowBeg, kHighMemBeg, kLowShadowBeg in *. lia.
- intros e' He'. assert (Hin : In e' (sec_extents ly S)) by (rewrite ES; apply in_app_iff in He' as [?|?]; apply in_app_iff; [left|right;right]; assumption).
  apply SURV; [exact (L7 e' Hin)|]. intros Heq.
  pose proof (proj1 (Forall_forall _ _) PF e' Hin) as (_ & [H1 H2] & H3). pose proof (proj1 (Forall_forall _ _) SZ e' Hin) as H4. cbn beta in H4.
  pose proof (WINJ e' ltac:(ceil; unfold kHighMemBeg, ASAN_CEIL in *; lia) ltac:(lia) Heq) as ->. pose proof (APART e He') as D. unfold zdisjoint in D. lia.
- intros q Hq. assert (Hq0 : In q (vm_maps (m_vmmaps md))) by (rewrite EM; apply in_app_iff in Hq as [?|?]; apply in_app_iff; [left|right;right]; assumption).
  pose proof (L8 q Hq0) as Xq. apply Exists_exists in Xq as (z & Hz & Hqz). apply Exists_exists. exists z. split; [|exact Hqz].
  rewrite ES in Hz. rewrite !in_app_iff in Hz |- *.
  destruct Hz as [Hz|[[Hz|[<-|Hz]]|Hz]]; [left; exact Hz | right; left; left; exact Hz | exfalso | right; left; right; exact Hz | right; right; exact Hz].
  rewrite EM in PW. destruct (YG0j.pairwise_app_mid _ M1 (wiv e) M2 PW) as [D1 D2]. cbn [fst snd wiv] in D1, D2. rewrite UE1, UE2 in D1, D2.
  pose proof (NE q Hq0) as NZq. apply in_app_iff in Hq as [Hq|Hq]; [pose proof (D1 q Hq) | pose proof (D2 q Hq)]; lia.
- rewrite ES in L9. rewrite !esec_app, esec_cons in L9. rewrite !esec_app, esec_cons, esec_nil. rewrite !esec_app in ESX. lia.
- intros z Hz. apply SURV; [exact (L10 z Hz)|]. intros Heq. pose proof (YG0h.perm_facts ly 1 LO ltac:(lia) z Hz) as (Z1 & Z2 & Z3 & _).
  pose proof (WINJ z ltac:(lia) ltac:(lia) Heq) as ->. pose proof (L12 e e He Hz) as D. unfold zdisjoint in D. lia.
- intros z Hz. apply SURV; [exact (L11 z Hz)|]. intros Heq.
  unfold band_maps in Hz. cbn in Hz.
  destruct Hz as [<-|[<-|[<-|[]]]];
  (unshelve epose proof (WINJ _ _ _ Heq) as X;
   [cbn; unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd; lia | cbn; unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd; lia |];
   apply (f_equal fst) in X; cbn [fst] in X;
   clear - X EH1 EH2 ESZ; unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia).
- intros e' z He' Hz. apply L12; [|exact Hz]. rewrite ES. apply in_app_iff in He' as [?|?]; apply in_app_iff; [left|right;right]; assumption.
- (* alc_lazy_in_maps: the unmap keeps it, since the only map based at e's start is wiv e itself *)
  try rewrite <- VM'.
  assert (HB : forall q, In q (vm_maps (m_vmmaps md)) -> fst q = YG0n.w64 (fst e) ->
    bv_unsigned (snd q) <= bv_unsigned (YG0n.w64 (snd e))).
  2:{ subst md'. exact (YGcfLazyMaps.lazy_in_maps_munmap_cf (YG0n.w64 (fst e)) (YG0n.w64 (snd e)) md L16 MW2 MW3 HB). }
  intros q Hq Hb. pose proof (NE q Hq) as NZq. rewrite EM in Hq. rewrite EM in PW.
  destruct (YG0j.pairwise_app_mid _ M1 (wiv e) M2 PW) as [D1 D2]. cbn [fst snd wiv] in D1, D2. rewrite UE1, UE2 in D1, D2.
  assert (BQ : bv_unsigned (fst q) = fst e) by (rewrite Hb; exact UE1).
  apply in_app_iff in Hq as [Hq|[Hq|Hq]].
  + exfalso. pose proof (D1 q Hq). lia.
  + subst q. cbn [wiv snd]. lia.
  + exfalso. pose proof (D2 q Hq). lia.
- (* alc_xs: the errbuf extent is not the dead map, so it survives the unmap *)
  intros e0 He0. assert (He0' : In e0 (xs_cf ly S)) by (unfold errb_zone in EZ; rewrite <- EZ; exact He0).
  apply SURV; [exact (L17 e0 He0')|]. intros Heq.
  assert (Hz0 : In e0 (errb_zone ly S)) by (unfold errb_zone; exact He0').
  destruct (XSA e0 Hz0) as (D & Z1 & Z2 & Z3). pose proof alloc_ceiling_lt as ACL. change (2 ^ 47) with 140737488355328 in ACL.
  pose proof (WINJ e0 ltac:(lia) ltac:(lia) Heq) as ->. unfold zdisjoint in D. lia.
Qed.

Lemma existsb_lupd_same : forall (l : list secmap) n v f, (forall sm, nth_error l n = Some sm -> f v = f sm) ->
existsb f (lupd l n v) = existsb f l.
Proof.
induction l as [|h t IH]; intros n v f Hn; [destruct n; reflexivity|].
destruct n as [|n]; cbn [lupd existsb].
- rewrite (Hn h eq_refl). reflexivity.
- rewrite (IH n v f Hn). reflexivity.
Qed.
Lemma find_sz_lupd : forall (l : list secmap) n v i, (forall sm, nth_error l n = Some sm -> is_errb_sz v = is_errb_sz sm) ->
find_sz (lupd l n v) i = find_sz l i.
Proof.
induction l as [|h t IH]; intros n v i Hn; [destruct n; reflexivity|].
destruct n as [|n]; cbn [lupd find_sz].
- rewrite (Hn h eq_refl). destruct (is_errb_sz h); [reflexivity|]. reflexivity.
- destruct (is_errb_sz h); [reflexivity|]. exact (IH n v (S i) Hn).
Qed.
Lemma last_cap_none : forall l i acc, last_cap_idx l i acc = None -> acc = None /\ filter is_errb_cap l = [].
Proof.
induction l as [|h t IH]; intros i acc H; [split; [exact H | reflexivity]|].
cbn [last_cap_idx] in H. destruct (IH _ _ H) as [H1 H2]. cbn [filter].
destruct (is_errb_cap h); [discriminate H1 | split; [exact H1 | exact H2]].
Qed.

Section M.
Variable B : asyms.
Variable ly : alayout.
Variable X : astate.
Variable Hp : list Z.
Variables (k : chunk) (r : nat) (o : Z) (sm : secmap) (i : nat) (sp : Z).
Variables (W : world im_segs) (mem mem' : word -> option byte) (md : Model).
Local Notation rd := (aview im_segs (w_H W) mem).
Local Notation rd' := (aview im_segs (w_H W) mem').
Local Notation T := (ly_T ly).
Local Notation X1 := (YFf3.X1 X k).

Definition arr : list nat := st_sec_arr X.
Definition lastr : nat := last arr r.
Definition arr' : list nat := YG00.removelast (lupd arr i lastr).
(* YFf4.X2 (YFf4.v:66), verbatim. *)
Definition rsX2 : astate := set_sec_arr arr' (set_secs (lupd (st_secs X) r (mkSec (sm_len sm) (sm_size sm) false)) X1).
Definition MAP : Z := ly_sec ly r.
Definition LEN : Z := sec_map_size (ck_req k).
Definition nA : Z := Z.of_nat (length arr).
Definition idx : Z := Z.of_nat i.
Definition qi : Z := ly_Q ly + 8 * idx.
Definition lst : Z := ly_sec ly lastr.
Definition own : bool := idx =? nA - 1.

(* The window: YFf4.v:78-87, with as_inst B for cgif's A_ALLOCATOR. *)
Definition rsDS (a : Z) : Prop := sp - YFeu.KSTACK <= a < sp.
Definition rsDI (a : Z) : Prop :=
(as_inst B + 680 <= a < as_inst B + 684) \/ (as_inst B + 120 <= a < as_inst B + 129) \/
(as_inst B + 144 <= a < as_inst B + 160) \/ (as_inst B + 704 <= a < as_inst B + 720).
Definition rsDJ (a : Z) : Prop := (T + t_stats + 40 <= a < T + t_stats + 56) \/ (T + t_stats + 88 <= a < T + t_stats + 104).
Definition rsDQ (a : Z) : Prop := qi <= a < qi + 8.
Definition rsDL (a : Z) : Prop := own = false /\ lst + 24 <= a < lst + 32.
Definition rsDH (a : Z) : Prop := shadow_addr MAP <= a < shadow_addr MAP + LEN / 8.
Definition rsDM (a : Z) : Prop := MAP <= a < MAP + LEN.
Definition rsD (a : Z) : Prop := rsDS a \/ rsDI a \/ rsDJ a \/ rsDQ a \/ rsDL a \/ rsDH a \/ rsDM a.

Hypothesis MR : ARcfR im_segs B ly X Hp W mem md.
Hypothesis Hk : In k (st_chunks X).
Hypothesis Hst : ck_state k = CQuarantined.
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hni : ~ In (ck_beg k) (map ck_beg (q_items X)).
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Hypothesis Hsp : ly_stk_lo ly + YFeu.KSTACK <= sp <= ly_stk_hi ly.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> ~ rsD a -> rd' a = rd a.
Hypothesis VIS : forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> ~ rsDM a -> rd' a <> None.
Hypothesis MUT' : forall j, 0 <= j < 4 -> rd' (as_inst B + 680 + j) = Some 0.
Hypothesis NS' : forall kk, (kk < 8)%nat -> rd' (as_inst B + 120 + Z.of_nat kk) = Some (le_byte (nA - 1) 8 kk).
Hypothesis QI' : forall kk, (kk < 8)%nat -> rd' (qi + Z.of_nat kk) = Some (le_byte lst 8 kk).
Hypothesis LST' : own = false -> forall kk, (kk < 8)%nat -> rd' (lst + 24 + Z.of_nat kk) = Some (le_byte idx 8 kk).
Hypothesis CONST' : Forall (cell_holds B ly rd') (as_const B ly).
Hypothesis TS : im_syms B.
Hypothesis ISA : IMG_SAPART.
Hypothesis IJ : IMG_JUNK.
(* the errbuf object apart from the allocator object: the errbuf cells of ARmcfR at rsX2 *)
Hypothesis EAPm : YGcfImgRows.ERRB_QAPART.

Lemma rM : ARmcfR B ly X Hp rd. Proof. exact (proj1 MR). Qed.
Lemma rLO : layout_ok ly. Proof. exact (amr_layout _ _ _ _ _ rM). Qed.
Lemma rWF : WfR_cf (as_universe B) 0 0 0 X. Proof. exact (amr_wfr _ _ _ _ _ rM). Qed.
Lemma rSY : asyms_ok B. Proof. exact (amr_syms _ _ _ _ _ rM). Qed.
Lemma rLED : ALedger_cf im_segs ly X md. Proof. exact (proj1 (proj2 MR)). Qed.

Lemma SX : forall i0 j x y, (i0 < j)%nat -> nth_error (static_extents ly) i0 = Some x -> nth_error (static_extents ly) j = Some y ->
zdisjoint x y.
Proof. intros i0 j x y Hij Hx Hy. exact (pairwise_nth_f zdisjoint _ i0 j x y (lo_disj _ rLO) Hij Hx Hy). Qed.
Ltac sx i0 j := let D := fresh "DJ" in pose proof (SX i0 j _ _ ltac:(lia) eq_refl eq_refl) as D; unfold zdisjoint in D; cbn [fst snd] in D.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The chunk, the map and the pointer array.                                                                        *)
Lemma SPLIT : exists l1 l2, st_chunks X = l1 ++ k :: l2 /\ st_chunks X1 = l1 ++ l2 /\
~ In (ck_beg k) (map ck_beg l1) /\ ~ In (ck_beg k) (map ck_beg l2).
Proof.
destruct (In_split_beg _ _ Hk (wfr_chunks_nodup _ _ _ _ _ rWF)) as (l1 & l2 & E & N1 & N2). exists l1, l2.
split; [exact E|]. split; [|split; [exact N1 | exact N2]]. unfold YFf3.X1. cbn [st_chunks set_chunks]. rewrite E.
apply del_chunk_present. exact N1.
Qed.

Lemma KFACTS : o = kPage /\ sm_len sm = LEN /\ 0 <= ck_req k /\ from_primary (ck_req k) = false /\
In (MAP, LEN) (sec_extents ly X) /\ (r < length (st_secs X))%nat /\ ck_base B ly k = MAP + kPage /\
ck_extent k = LEN - kPage /\ page_aligned MAP.
Proof.
pose proof (RL.chunk_facts_cf B ly X Hp _ k rM Hk) as CF. unfold RL.cfacts_cf in CF.
destruct CF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite Hb in GG.
destruct GG as (Eo & Hfp & Gbase & Gext & Gin & Gal & Glt).
pose proof (proj1 (Forall_forall _ _) (wfr_chunks _ _ _ _ _ rWF) k Hk) as [Hn CK]. rewrite Hb in CK.
destruct CK as (P1 & P2 & sm' & Q1 & Q2 & Q3 & Q4). rewrite Hsm in Q1. injection Q1 as <-.
unfold MAP, LEN. split; [exact Eo|]. split; [exact Q4|]. split; [lia|]. split; [exact Hfp|].
split; [exact Gin|]. split; [exact (nth_error_lt _ _ _ Hsm)|]. split; [exact Gbase|]. split; [exact Gext | exact Gal].
Qed.

Lemma ARR : In r arr /\ (i < length arr)%nat /\ NoDup arr /\ 1 <= nA <= kPtrArrayEntriesPerCommit /\ 0 <= idx < nA /\
nth_error arr (length arr - 1) = Some lastr /\ In lastr arr /\ (own = true <-> lastr = r).
Proof.
pose proof (wfr_secondary _ _ _ _ _ rWF) as XS.
pose proof (wsc_nodup _ XS) as Snd. pose proof (wsc_reserved _ XS) as Sres.
assert (Hin : In r (st_sec_arr X)) by (eapply nth_error_In; exact Hi).
assert (Hlt : (i < length (st_sec_arr X))%nat) by (exact (nth_error_lt _ _ _ Hi)).
assert (NE : st_sec_arr X <> []) by (intros E; rewrite E in Hin; destruct Hin).
pose proof (last_nth_error (st_sec_arr X) r NE) as HL.
unfold own, idx, nA, lastr, arr. repeat split; try assumption; try lia.
- eapply nth_error_In. exact HL.
- intros Ho. apply Z.eqb_eq in Ho. replace i with (length (st_sec_arr X) - 1)%nat in Hi by lia. rewrite HL in Hi.
  injection Hi as E. exact E.
- intros E. rewrite E in HL. apply Z.eqb_eq.
  pose proof (proj1 (NoDup_nth_error _) Snd i (length (st_sec_arr X) - 1)%nat Hlt ltac:(rewrite Hi, HL; reflexivity)). lia.
Qed.

Lemma ARR' : length arr' = (length arr - 1)%nat /\ (forall j, (j < length arr')%nat -> j <> i -> nth_error arr' j = nth_error arr j) /\
(own = false -> nth_error arr' i = Some lastr) /\ NoDup arr' /\ ~ In r arr' /\ (forall r', In r' arr' <-> In r' arr /\ r' <> r).
Proof.
pose proof ARR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (NE : lupd arr i lastr <> []) by (intros E; apply (f_equal (@length nat)) in E; rewrite lupd_length in E;
  unfold nA, idx in *; cbn in E; lia).
assert (PA : Permutation (r :: arr') arr) by (unfold arr', lastr; exact (swap_remove_perm arr i r Hi)).
assert (ND2 : NoDup (r :: arr')) by (eapply Permutation_NoDup; [apply Permutation_sym; exact PA | exact A3]).
assert (NDA : NoDup arr' /\ ~ In r arr') by (inversion ND2 as [|x0 l0 Hnin Hnd]; subst; split; [exact Hnd | exact Hnin]).
destruct NDA as [NDA NIA].
assert (L' : length arr' = (length arr - 1)%nat)
  by (unfold arr'; rewrite removelast_length by exact NE; rewrite lupd_length; reflexivity).
split; [exact L'|]. split.
{ intros j Hj Hne. unfold arr'. rewrite nth_error_removelast_lt by (rewrite lupd_length; lia).
  apply nth_error_lupd_other. congruence. }
split.
{ intros Ho. unfold own in Ho. apply Z.eqb_neq in Ho. unfold nA, idx in Ho. unfold arr'.
  rewrite nth_error_removelast_lt by (rewrite lupd_length; lia). apply nth_error_lupd_same. exact A2. }
split; [exact NDA|]. split; [exact NIA|].
intros r'. split.
- intros H. split; [eapply Permutation_in; [exact PA | right; exact H] | intros ->; exact (NIA H)].
- intros [H Hne]. pose proof (Permutation_in _ (Permutation_sym PA) H) as [<-|H']; [congruence | exact H'].
Qed.

Lemma WS2 : WfR_cf (as_universe B) 0 0 0 rsX2.
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof KFACTS as (Eo & _).
assert (EX : X1 = set_chunks (l1 ++ l2) X) by (unfold YFf3.X1; rewrite <- E1; reflexivity).
unfold rsX2, arr', lastr, arr. rewrite EX.
exact (WfR_del_sec_cf (as_universe B) 0 0 0 X l1 k l2 r sm i rWF E ltac:(rewrite Hb, Eo; reflexivity) Hst Hni Hsm Hi).
Qed.

Lemma X2_chunks : st_chunks rsX2 = st_chunks X1. Proof. reflexivity. Qed.
Lemma X2_regions : st_regions rsX2 = st_regions X. Proof. reflexivity. Qed.
Lemma X2_cache : st_cache rsX2 = st_cache X. Proof. reflexivity. Qed.
Lemma X2_cinit : st_cache_inited rsX2 = st_cache_inited X. Proof. reflexivity. Qed.
Lemma X2_secs : st_secs rsX2 = lupd (st_secs X) r (mkSec (sm_len sm) (sm_size sm) false). Proof. reflexivity. Qed.
Lemma X2_sec_arr : st_sec_arr rsX2 = arr'. Proof. reflexivity. Qed.
Lemma X2_sec_res : st_sec_reserved rsX2 = st_sec_reserved X. Proof. reflexivity. Qed.
Lemma X2_fs : st_fs rsX2 = st_fs X. Proof. reflexivity. Qed.
Lemma X2_qglobal : st_qglobal rsX2 = st_qglobal X. Proof. reflexivity. Qed.
Lemma X2_qthread : st_qthread rsX2 = st_qthread X. Proof. reflexivity. Qed.
Lemma X2_depot : st_depot rsX2 = st_depot X. Proof. reflexivity. Qed.
Lemma X2_inited : st_internal_inited rsX2 = st_internal_inited X. Proof. reflexivity. Qed.
Lemma X2_secs_len : length (st_secs rsX2) = length (st_secs X). Proof. rewrite X2_secs. apply lupd_length. Qed.
Lemma reg' : forall c', reg rsX2 c' = reg X c'. Proof. reflexivity. Qed.
Lemma cache' : forall c', cache rsX2 c' = cache X c'. Proof. reflexivity. Qed.
Lemma frames' : frames rsX2 = frames X. Proof. reflexivity. Qed.
Lemma all_batches' : all_batches rsX2 = all_batches X. Proof. reflexivity. Qed.

Lemma sec_extents_split : exists E1 E2, sec_extents ly X = E1 ++ (MAP, LEN) :: E2 /\ sec_extents ly rsX2 = E1 ++ E2.
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & _). pose proof KFACTS as (Eo & _).
unfold sec_extents. rewrite X2_chunks, E1, E, !flat_map_app. cbn [flat_map]. rewrite Hb. cbn [app].
eexists _, _. split; reflexivity.
Qed.

Lemma sec_extents_sub : forall e, In e (sec_extents ly rsX2) -> In e (sec_extents ly X).
Proof.
intros e He. destruct sec_extents_split as (E1 & E2 & A & A'). rewrite A' in He. rewrite A.
apply in_app_iff in He as [He|He]; apply in_app_iff; [left | right; right]; exact He.
Qed.

Lemma fa_poison' : exists F1 F2, fa_poison_ranges ly X = F1 ++ (MAP, LEN) :: F2 /\ fa_poison_ranges ly rsX2 = F1 ++ F2.
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & _). unfold fa_poison_ranges, reg.
rewrite X2_regions, X2_chunks, E1, E, !flat_map_app. cbn [flat_map]. rewrite Hb. cbn [app].
lazymatch goal with |- exists F1 F2, ?F ++ (?A ++ ?e :: ?C) = _ /\ _ => exists (F ++ A), C end.
rewrite <- app_assoc. split; reflexivity.
Qed.

Lemma aareas_split : exists A1 A2, aareas X = A1 ++ (ASec r 0, LEN) :: A2 /\ aareas rsX2 = A1 ++ A2.
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & _). unfold aareas, reg.
rewrite X2_regions, X2_sec_res, X2_chunks, E1, E, !flat_map_app. cbn [flat_map]. rewrite Hb. cbn [app].
lazymatch goal with |- exists F1 F2, ?F ++ ?g :: (?A ++ ?e :: ?C) ++ ?R = _ /\ _ => exists (F ++ g :: A), (C ++ R) end.
rewrite <- !app_assoc. cbn [app]. split; reflexivity.
Qed.

Lemma sec_cells_X2_shape : sec_cells rsX2 =
c8 (AInst o_sec_reserved) (ANum (st_sec_reserved X)) :: z8 (AInst o_sec_n) (Z.of_nat (length arr'))
:: z1 (AInst o_sec_mutex) 0
:: map (fun ir => c8 (AQ (8 * Z.of_nat (fst ir))) (ASec (snd ir) 0)) (combine (seq 0 (length arr')) arr')
++ flat_map (fun y => match ck_beg y with
| PSec r0 _ => [ c8 (ASec r0 0) (ASec r0 0); z8 (ASec r0 8) (sec_map_size (ck_req y));
z8 (ASec r0 16) (needed_size (ck_req y)); z8 (ASec r0 24) (index_ofZ arr' r0) ]
| _ => [] end) (st_chunks X1).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The geometry of the map and of the layout.                                                                       *)
Lemma geom : page_aligned MAP /\ 8192 <= LEN /\ LEN mod kPage = 0 /\ in_app MAP LEN /\ MAP + LEN <= ASAN_CEIL /\
4096 <= MAP.
Proof.
pose proof KFACTS as (Eo & Esm & Hq & Hfp & Gin & Glt & Gbase & Gext & Gal).
pose proof (proj1 (Forall_forall _ _) (proj1 (amr_placed _ _ _ _ _ rM)) _ Gin) as (PA & IA & I3).
cbn [fst snd] in PA, IA, I3.
pose proof (secondary_geometry (ck_req k) ltac:(lia) Hfp) as (S1 & S2 & S3 & S4 & S5 & S6).
pose proof (RL.chunk_facts_cf B ly X Hp _ k rM Hk) as (G1 & G2 & _).
assert (LB : 8192 <= sec_map_size (ck_req k)).
{ unfold sec_map_size, needed_size. rewrite Hfp. pose proof Hfp as FP. unfold from_primary in FP. apply Z.leb_gt in FP.
  pose proof (round_up_ge (needed_primary (ck_req k) + rz_size (ck_req k)) kPage ltac:(unfold kPage; lia)) as [R1 _].
  pose proof (rz_size_bounds (ck_req k)) as [RZ _]. unfold kMaxSize, kPage in *. lia. }
unfold MAP, LEN in *. split; [exact PA|]. split; [exact LB|]. split; [exact S5|]. split; [exact IA|].
split; [exact I3 | exact (proj1 IA)].
Qed.

Lemma rT : in_app T kThreadObjSize /\ kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\ ly_stk_lo ly mod 4096 = 0 /\ in_app (ly_Q ly) kPtrArrayResv.
Proof.
pose proof (lo_high _ rLO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (proj1 (Forall_forall _ _) (lo_app _ rLO) (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as IT.
pose proof (proj1 (Forall_forall _ _) (lo_app _ rLO) (ly_Q ly, kPtrArrayResv) ltac:(unfold owned_extents; cbn; tauto)) as IQ.
cbn [fst snd] in IT, IQ. pose proof (lo_top _ rLO) as (_ & _ & _ & T4 & T5 & _ & T7). unfold page_aligned in T5.
split; [exact IT|]. split; [lia|]. split; [lia|]. split; [exact T7|]. split; [exact T4|]. split; [exact T5 | exact IQ].
Qed.

Lemma MAPX : forall j y, nth_error (static_extents ly) j = Some y -> zdisjoint (MAP, LEN) y.
Proof.
intros j y Hj. pose proof KFACTS as (_ & _ & _ & _ & Gin & _).
eapply (pairwise_In zdisjoint _ (MAP, LEN) y (sec_extents ly X) (static_extents ly) eq_refl
  (proj2 (amr_placed _ _ _ _ _ rM)) Gin). eapply nth_error_In. exact Hj.
Qed.

Lemma SECX : forall e j y, In e (sec_extents ly X) -> nth_error (static_extents ly) j = Some y -> zdisjoint e y.
Proof.
intros e j y He Hj. eapply (pairwise_In zdisjoint _ e y (sec_extents ly X) (static_extents ly) eq_refl
  (proj2 (amr_placed _ _ _ _ _ rM)) He). eapply nth_error_In. exact Hj.
Qed.

Lemma DH_zone : forall a, rsDH a -> SHADOW_OFF <= a < kHighMemBeg.
Proof.
intros a Ha. unfold rsDH, shadow_addr in Ha. pose proof geom as (M1 & M2 & M3 & M4 & M5 & M6).
assert (D1 : 0 <= MAP / 8) by (apply Z.div_pos; lia).
assert (D2 : (MAP + LEN) / 8 <= ASAN_CEIL / 8) by (apply Z.div_le_mono; lia).
assert (D3 : MAP / 8 + LEN / 8 <= (MAP + LEN) / 8).
{ apply Z.mod_divide in M1 as [q Hq]; [|lia]. apply Z.mod_divide in M3 as [l Hl]; [|unfold kPage; lia].
  unfold kPage in Hl. rewrite Hq, Hl.
  replace (q * 4096) with ((q * 512) * 8) by lia. replace (l * 4096) with ((l * 512) * 8) by lia.
  replace ((q * 512) * 8 + (l * 512) * 8) with (((q * 512) + (l * 512)) * 8) by lia. rewrite !Z_div_mult by lia. lia. }
assert (D4 : ASAN_CEIL / 8 <= 17592184995840) by (ceil; apply Z.div_le_upper_bound; [lia | unfold ASAN_CEIL in *; lia]).
unfold kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

Lemma DH_iff : forall g, g mod 8 = 0 -> (rsDH (shadow_addr g) <-> MAP <= g < MAP + LEN).
Proof.
intros g Hg. pose proof geom as (M1 & M2 & M3 & _). unfold rsDH, shadow_addr.
apply Z.mod_divide in Hg as [c0 Hc0]; [|lia]. apply Z.mod_divide in M1 as [a Ha]; [|lia].
apply Z.mod_divide in M3 as [l Hl]; [|unfold kPage; lia]. unfold kPage in Hl. rewrite Hc0, Ha, Hl.
replace (a * 4096) with ((a * 512) * 8) by lia. replace (l * 4096) with ((l * 512) * 8) by lia.
rewrite !Z_div_mult by lia. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The bytes the call does not touch.                                                                               *)
Definition ok (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ rsD a.
Definition okr (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ok a.
Lemma AGok : forall a, ok a -> rd' a = rd a. Proof. intros a [H1 H2]. apply AG; assumption. Qed.

Lemma lst_sec : exists y, In y (st_chunks X) /\ ck_beg y = PSec lastr kPage /\
In (lst, sec_map_size (ck_req y)) (sec_extents ly X) /\ 8192 <= sec_map_size (ck_req y).
Proof.
pose proof ARR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
pose proof (wfr_secondary _ _ _ _ _ rWF) as XS.
destruct (proj1 (wsc_arr_chunks _ XS lastr) A7) as (y & Hy & Eby).
pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
rewrite Eby in GG. destruct GG as (_ & Hfp & Gbase & Gext & Gin & _).
assert (LB : 8192 <= sec_map_size (ck_req y)).
{ unfold sec_map_size, needed_size. rewrite Hfp. pose proof Hfp as FP. unfold from_primary in FP. apply Z.leb_gt in FP.
  pose proof (round_up_ge (needed_primary (ck_req y) + rz_size (ck_req y)) kPage ltac:(unfold kPage; lia)) as [R1 _].
  pose proof (rz_size_bounds (ck_req y)) as [RZ _]. unfold kMaxSize, kPage in *. lia. }
exists y. split; [exact Hy|]. split; [exact Eby|]. split; [exact Gin | exact LB].
Qed.

Lemma img_area : forall r0 a, In r0 (asyms_areas B) -> fst r0 <= a < fst r0 + snd r0 -> in_zr a (ly_img ly).
Proof.
intros r0 a Hr Ha. pose proof (proj1 (Forall_forall _ _) (aso_cover _ rSY) r0 Hr) as E.
apply Exists_exists in E as (r' & Hr' & [Z1 Z2]).
pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ rM) r' ltac:(apply in_app_iff; left; exact Hr')) as [I1 I2].
unfold in_zr. lia.
Qed.
Lemma img_inst : forall a, as_inst B <= a < as_inst B + 3632 -> in_zr a (ly_img ly).
Proof. intros a Ha. apply (img_area (as_inst B, 3632)); [unfold asyms_areas; cbn; tauto | exact Ha]. Qed.

(* Every part of the window lies in one of seven zones: the stack [rsDS], the image [rsDI], the thread object
   [rsDJ], the pointer array [rsDQ], the last entry's page [rsDL], the shadow band [rsDH] and the dead map
   [rsDM].  A zone lemma below gives, for an address of one zone, the six or seven negations. *)
Lemma ok_mk : forall a, 0 <= a < 2 ^ 64 -> ~ rsDS a -> ~ rsDI a -> ~ rsDJ a -> ~ rsDQ a -> ~ rsDL a ->
~ rsDH a -> ~ rsDM a -> ok a.
Proof. intros a H0 N1 N2 N3 N4 N5 N6 N7. split; [exact H0|]. intros [H|[H|[H|[H|[H|[H|H]]]]]]; tauto. Qed.

Lemma sec_in_app : forall e, In e (sec_extents ly X) -> in_app (fst e) (snd e) /\ 8192 <= snd e.
Proof.
intros e He. pose proof (proj1 (Forall_forall _ _) (proj1 (amr_placed _ _ _ _ _ rM)) e He) as (PA & IA & I3).
split; [exact IA|].
apply in_flat_map in He as (y & Hy & Hin). destruct (ck_beg y) as [|oy|ry oy|c0 p0] eqn:Eby; try solve [destruct Hin].
destruct Hin as [EE|[]]. subst e. cbn [snd].
pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy) as (_ & _ & _ & _ & _ & _ & G7 & _ & GG).
rewrite Eby in GG. destruct GG as (_ & Hfp & _).
unfold sec_map_size, needed_size. rewrite Hfp. pose proof Hfp as FP. unfold from_primary in FP. apply Z.leb_gt in FP.
pose proof (round_up_ge (needed_primary (ck_req y) + rz_size (ck_req y)) kPage ltac:(unfold kPage; lia)) as [R1 _].
pose proof (rz_size_bounds (ck_req y)) as [RZ _]. unfold kMaxSize, kPage in *. lia.
Qed.

Lemma band_off_app : forall a lo len, in_app lo len -> lo <= a < lo + len -> ~ (SHADOW_OFF <= a < kHighMemBeg).
Proof.
intros a lo len [H0 [HL|[HH1 HH2]]] Ha; ceil; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia.
Qed.

Lemma in_app_64 : forall lo len a, in_app lo len -> lo <= a < lo + len -> 0 <= a < 2 ^ 64.
Proof. intros lo len a [H0 [HL|[H1 H2]]] Ha; ceil; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia. Qed.

(* The dead map and the last entry's page are secondary extents, so a zone apart from every secondary extent is
   apart from rsDL and rsDM. *)
Lemma off_DL : forall a, (forall e, In e (sec_extents ly X) -> ~ (fst e <= a < fst e + snd e)) -> ~ rsDL a.
Proof.
intros a NE [Ho HL]. destruct lst_sec as (y & Hy & Eby & Gy & LBy).
apply (NE (lst, sec_map_size (ck_req y)) Gy). cbn [fst snd]. lia.
Qed.
Lemma off_DM : forall a, (forall e, In e (sec_extents ly X) -> ~ (fst e <= a < fst e + snd e)) -> ~ rsDM a.
Proof.
intros a NE HM. pose proof KFACTS as (_ & _ & _ & _ & Gin & _).
apply (NE (MAP, LEN) Gin). cbn [fst snd]. unfold rsDM in HM. lia.
Qed.
Lemma off_DI : forall a, ~ in_zr a (ly_img ly) -> ~ rsDI a.
Proof. intros a NI HI. apply NI. apply img_inst. unfold rsDI in HI. lia. Qed.
Lemma off_DJ : forall a, ~ (T <= a < T + kThreadObjSize) -> ~ rsDJ a.
Proof. intros a NT HJ. apply NT. unfold rsDJ, t_stats, kThreadObjSize in *. lia. Qed.
Lemma off_DQ : forall a, ~ (ly_Q ly <= a < ly_Q ly + kPtrArrayResv) -> ~ rsDQ a.
Proof.
intros a NQ HQ. pose proof ARR as (_ & _ & _ & A4 & A5 & _). apply NQ.
unfold rsDQ, qi, idx, nA, kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
Qed.
Lemma off_DS : forall a, ~ (ly_stk_lo ly <= a < ly_stk_hi ly) -> ~ rsDS a.
Proof. intros a NS HS. apply NS. unfold rsDS, YFeu.KSTACK in *. lia. Qed.
Lemma off_DH : forall a, ~ (SHADOW_OFF <= a < kHighMemBeg) -> ~ rsDH a.
Proof. intros a NH HH. exact (NH (DH_zone a HH)). Qed.

Lemma ok_T : forall a, T <= a < T + kThreadObjSize -> ~ rsDJ a -> ok a.
Proof.
intros a Ha NJ. pose proof rT as (IT & _).
assert (NE : forall e, In e (sec_extents ly X) -> ~ (fst e <= a < fst e + snd e)).
{ intros e He Hae. pose proof (SECX e 2%nat _ He eq_refl) as D0. unfold zdisjoint in D0. cbn [fst snd] in D0.
  unfold kThreadObjSize in *. lia. }
apply ok_mk.
- exact (in_app_64 _ _ a IT Ha).
- apply off_DS. intros HS. sx 2%nat 8%nat. unfold kThreadObjSize in *. lia.
- apply off_DI. intros HI. sx 2%nat 9%nat. unfold in_zr, kThreadObjSize in *. lia.
- exact NJ.
- apply off_DQ. intros HQ. sx 1%nat 2%nat. unfold kThreadObjSize in *. lia.
- exact (off_DL a NE).
- apply off_DH. exact (band_off_app a _ _ IT Ha).
- exact (off_DM a NE).
Qed.

Lemma ok_Q : forall a, ly_Q ly <= a < ly_Q ly + kPtrArrayResv -> ~ rsDQ a -> ok a.
Proof.
intros a Ha NQ. pose proof rT as (_ & _ & _ & _ & _ & _ & IQ).
assert (NE : forall e, In e (sec_extents ly X) -> ~ (fst e <= a < fst e + snd e)).
{ intros e He Hae. pose proof (SECX e 1%nat _ He eq_refl) as D0. unfold zdisjoint in D0. cbn [fst snd] in D0. lia. }
apply ok_mk.
- exact (in_app_64 _ _ a IQ Ha).
- apply off_DS. intros HS. sx 1%nat 8%nat. lia.
- apply off_DI. intros HI. sx 1%nat 9%nat. unfold in_zr in *. lia.
- apply off_DJ. intros HT. sx 1%nat 2%nat. unfold kThreadObjSize in *. lia.
- exact NQ.
- exact (off_DL a NE).
- apply off_DH. exact (band_off_app a _ _ IQ Ha).
- exact (off_DM a NE).
Qed.

Lemma ok_static : forall j e a, (3 <= j <= 7)%nat -> nth_error (static_extents ly) j = Some e ->
fst e <= a < fst e + snd e -> ok a.
Proof.
intros j e a Hj He Ha.
pose proof (proj1 (Forall_forall _ _) (lo_app _ rLO) e ltac:(unfold static_extents in He;
  rewrite nth_error_app1 in He by (cbn; lia); eapply nth_error_In; exact He)) as HE. cbn [fst snd] in HE.
assert (NE : forall e0, In e0 (sec_extents ly X) -> ~ (fst e0 <= a < fst e0 + snd e0)).
{ intros e0 He0 Hae. pose proof (SECX e0 j _ He0 He) as D0. unfold zdisjoint in D0. cbn [fst snd] in D0. lia. }
apply ok_mk.
- exact (in_app_64 _ _ a HE Ha).
- apply off_DS. intros HS. pose proof (SX j 8%nat _ _ ltac:(lia) He eq_refl) as D0. unfold zdisjoint in D0.
  cbn [fst snd] in D0. lia.
- apply off_DI. intros HI. pose proof (SX j 9%nat _ _ ltac:(lia) He eq_refl) as D0. unfold zdisjoint in D0.
  cbn [fst snd] in D0. unfold in_zr in *. lia.
- apply off_DJ. intros HT. pose proof (SX 2%nat j _ _ ltac:(lia) eq_refl He) as D0. unfold zdisjoint in D0.
  cbn [fst snd] in D0. unfold kThreadObjSize in *. lia.
- apply off_DQ. intros HQ. pose proof (SX 1%nat j _ _ ltac:(lia) eq_refl He) as D0. unfold zdisjoint in D0.
  cbn [fst snd] in D0. lia.
- exact (off_DL a NE).
- apply off_DH. exact (band_off_app a _ _ HE Ha).
- exact (off_DM a NE).
Qed.

Lemma ok_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ok a.
Proof.
intros a Ha. pose proof (in_high_app (ly_prim ly) kPrimResvSize (lo_high _ rLO)) as IP.
assert (NE : forall e, In e (sec_extents ly X) -> ~ (fst e <= a < fst e + snd e)).
{ intros e He Hae. pose proof (SECX e 0%nat _ He eq_refl) as D0. unfold zdisjoint in D0. cbn [fst snd] in D0. lia. }
apply ok_mk.
- exact (in_app_64 _ _ a IP Ha).
- apply off_DS. intros HS. sx 0%nat 8%nat. lia.
- apply off_DI. intros HI. sx 0%nat 9%nat. unfold in_zr in *. lia.
- apply off_DJ. intros HT. sx 0%nat 2%nat. unfold kThreadObjSize in *. lia.
- apply off_DQ. intros HQ. sx 0%nat 1%nat. lia.
- exact (off_DL a NE).
- apply off_DH. exact (band_off_app a _ _ IP Ha).
- exact (off_DM a NE).
Qed.

Lemma ok_img : forall a, in_zr a (ly_img ly) -> ~ rsDI a -> ok a.
Proof.
intros a Ha NI. pose proof (lo_img _ rLO) as (I1 & I2 & I3 & _). unfold in_zr in Ha. rewrite I1 in Ha.
assert (NE : forall e, In e (sec_extents ly X) -> ~ (fst e <= a < fst e + snd e)).
{ intros e He Hae. pose proof (SECX e 9%nat _ He eq_refl) as D0. unfold zdisjoint in D0. cbn [fst snd] in D0.
  unfold kImgLo, kImgEnd in *. lia. }
apply ok_mk.
- ceil. unfold kImgLo, kImgEnd in *. lia.
- apply off_DS. intros HS. sx 8%nat 9%nat. unfold kImgLo, kImgEnd in *. lia.
- exact NI.
- apply off_DJ. intros HT. sx 2%nat 9%nat. unfold kImgLo, kImgEnd, kThreadObjSize in *. lia.
- apply off_DQ. intros HQ. sx 1%nat 9%nat. unfold kImgLo, kImgEnd in *. lia.
- exact (off_DL a NE).
- apply off_DH. intros HB. unfold kImgLo, kImgEnd, SHADOW_OFF in *. lia.
- exact (off_DM a NE).
Qed.

Lemma ok_band : forall a, SHADOW_OFF <= a < kHighMemBeg -> ~ rsDH a -> ok a.
Proof.
intros a Ha NH.
assert (NE : forall e, In e (sec_extents ly X) -> ~ (fst e <= a < fst e + snd e)).
{ intros e He Hae. destruct (sec_in_app e He) as [IA _]. exact (band_off_app a _ _ IA Hae Ha). }
pose proof rT as (IT & H1 & H2 & H4 & H5 & _ & IQ). pose proof (lo_img _ rLO) as (I1 & I2 & I3 & _).
apply ok_mk.
- unfold SHADOW_OFF, kHighMemBeg in *. lia.
- apply off_DS. intros HS. unfold SHADOW_OFF, kHighMemBeg in *. lia.
- apply off_DI. intros HI. unfold in_zr in HI. rewrite I1 in HI. unfold kImgLo, kImgEnd, SHADOW_OFF in *. lia.
- apply off_DJ. intros HT. exact (band_off_app a _ _ IT HT Ha).
- apply off_DQ. intros HQ. exact (band_off_app a _ _ IQ HQ Ha).
- exact (off_DL a NE).
- exact NH.
- exact (off_DM a NE).
Qed.

Lemma ok_sec : forall e a, In e (sec_extents ly X) -> fst e <= a < fst e + snd e -> ~ rsDL a -> ~ rsDM a -> ok a.
Proof.
intros e a He Ha NL NM. destruct (sec_in_app e He) as [IA LB].
apply ok_mk.
- exact (in_app_64 _ _ a IA Ha).
- apply off_DS. intros HS. pose proof (SECX e 8%nat _ He eq_refl) as D0. unfold zdisjoint in D0.
  cbn [fst snd] in D0. lia.
- apply off_DI. intros HI. pose proof (SECX e 9%nat _ He eq_refl) as D0. unfold zdisjoint in D0.
  cbn [fst snd] in D0. unfold in_zr in *. lia.
- apply off_DJ. intros HT. pose proof (SECX e 2%nat _ He eq_refl) as D0. unfold zdisjoint in D0.
  cbn [fst snd] in D0. unfold kThreadObjSize in *. lia.
- apply off_DQ. intros HQ. pose proof (SECX e 1%nat _ He eq_refl) as D0. unfold zdisjoint in D0.
  cbn [fst snd] in D0. lia.
- exact NL.
- apply off_DH. exact (band_off_app a _ _ IA Ha).
- exact NM.
Qed.

(* The symbol table's areas other than the instance object's written words. *)
Lemma ok_area : forall r0 a, In r0 (asyms_areas B) -> fst r0 <= a < fst r0 + snd r0 -> ~ sdeal_inst B a -> ok a.
Proof. intros r0 a Hr Ha NI. apply ok_img; [exact (img_area r0 a Hr Ha)|]. intros HI. apply NI. exact HI. Qed.
Lemma ns_depot : forall a, as_depot B <= a < as_depot B + 4 * 2 ^ 20 + 32 -> ~ sdeal_inst B a.
Proof. intros a Ha Hs. exact (proj1 (ISA B TS a Hs) Ha). Qed.
Lemma ns_store : forall a, as_store B <= a < as_store B + 32 -> ~ sdeal_inst B a.
Proof. intros a Ha Hs. exact (proj1 (proj2 (ISA B TS a Hs)) Ha). Qed.
Lemma ns_ialloc : forall a, as_ialloc_lo B <= a < as_ialloc_hi B -> ~ sdeal_inst B a.
Proof. intros a Ha Hs. exact (proj1 (proj2 (proj2 (ISA B TS a Hs))) Ha). Qed.
Lemma ns_iflag : forall a, as_ialloc_flag B <= a < as_ialloc_flag B + 2 -> ~ sdeal_inst B a.
Proof. intros a Ha Hs. exact (proj2 (proj2 (proj2 (ISA B TS a Hs))) Ha). Qed.

(* Every other chunk's extent: a primary one is in the primary reserve; a secondary one is past its map's header
   page, in a map other than the dead one. *)
Lemma ok_chunk : forall y a, In y (st_chunks X) -> ck_beg y <> ck_beg k ->
ck_base B ly y <= a < ck_base B ly y + ck_extent y -> ok a.
Proof.
intros y a Hy Hne Ha. pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof KFACTS as (Eo & _ & _ & _ & GI & _).
destruct (ck_beg y) as [|oy|ry oy|c0 p0] eqn:Eby; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
  pose proof (region_in_prim ly (prim_class oy) rLO ltac:(lia)) as (R1 & R2 & _).
  apply ok_prim. unfold kFreeArrayOffset in *. lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
  apply (ok_sec (ly_sec ly ry, sec_map_size (ck_req y)) a Gin); [cbn [fst snd]; unfold kPage in *; lia | |].
  + intros [Ho HL]. destruct lst_sec as (y' & Hy' & Eby' & Gy & LBy).
    destruct (Nat.eq_dec ry lastr) as [->|Hnl].
    * unfold lst in HL. unfold kPage in *. lia.
    * assert (Hne' : ck_beg y <> ck_beg y') by (rewrite Eby, Eby'; intros E; injection E as E; exact (Hnl E)).
      pose proof (RL.secmaps_disjoint_cf B ly X Hp _ y y' ry kPage lastr kPage rM Hy Hy' Eby Eby' Hne') as D0.
      unfold zdisjoint in D0. cbn [fst snd] in D0. unfold lst, kPage in *. lia.
  + intros HM.
    pose proof (RL.secmaps_disjoint_cf B ly X Hp _ y k ry kPage r o rM Hy Hk Eby Hb ltac:(rewrite Eby; exact Hne)) as D0.
    unfold zdisjoint in D0. cbn [fst snd] in D0. unfold rsDM, MAP, LEN in HM. unfold kPage in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The cells other than the secondary allocator's.                                                                  *)
Lemma oldc : forall c, In c (acells_cf B ly X) -> cell_holds B ly rd c.
Proof. intros c Hc. exact (proj1 (Forall_forall _ _) (amr_cells _ _ _ _ _ rM) c Hc). Qed.

Lemma cells_xfer : forall l, Forall (fun c => forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> ok (aeval B ly (c_at c) + j)) l ->
Forall (cell_holds B ly rd) l -> Forall (cell_holds B ly rd') l.
Proof.
intros l OK H. apply Forall_forall. intros c Hc.
eapply cell_holds_agree; [exact (proj1 (Forall_forall _ _) H c Hc)|]. intros j Hj.
exact (AGok _ (proj1 (Forall_forall _ _) OK c Hc j Hj)).
Qed.

Lemma cells_rng : forall lo len l, (forall a, lo <= a < lo + len -> ok a) ->
Forall (fun c => lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len) l ->
Forall (cell_holds B ly rd) l -> Forall (cell_holds B ly rd') l.
Proof.
intros lo len l OK R H. apply (cells_xfer l); [|exact H].
eapply Forall_impl; [|exact R]. intros c [R1 R2] j Hj. apply OK. lia.
Qed.

Ltac fcons := apply Forall_cons; [cbn; lia|].

Lemma ok_rinfo : forall a, ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 -> ok a.
Proof.
intros a Ha. pose proof (lo_space_in _ rLO) as [S1 S2]. apply ok_prim. unfold kRegionInfoOff, kSpaceSize in *. lia.
Qed.

Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells_cf rsX2) (zseq 1 31)).
Proof.
apply cells_xfer.
- apply Forall_forall. intros c Hc. apply in_flat_map in Hc as (cl & Hcl & Hc). apply zseq_In in Hcl.
  unfold region_cells_cf, region_cells, z8, z1, c8, c1 in Hc. cbn [removelast] in Hc.
  assert (HA : ly_space ly + kRegionInfoOff + 128 * cl <= aeval B ly (c_at c) /\
    aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= ly_space ly + kRegionInfoOff + 128 * cl + 64).
  { destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [c_at c_w aeval aoff]; lia. }
  intros j Hj. apply ok_rinfo. lia.
- apply Forall_forall. intros c HIN. apply oldc. unfold acells_cf. rewrite !in_app_iff. left. exact HIN.
Qed.

Lemma cells_cache : forall c, 1 <= c <= 31 -> Forall (cell_holds B ly rd) (cache_cells X c) -> Forall (cell_holds B ly rd') (cache_cells rsX2 c).
Proof.
intros c Hc O. unfold cache_cells in O |- *. rewrite cache', X2_cinit.
apply (cells_rng (T + t_cache + 80) (80 * 31)); [| |exact O].
- intros a Ha. apply ok_T; [unfold t_cache, kThreadObjSize in *; lia|]. unfold rsDJ, t_cache, t_stats in *. lia.
- pose proof (wfr_classes _ _ _ _ _ rWF c Hc) as CL. pose proof (wrc_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c Hc) as (_ & _ & _ & K4 & _).
  destruct (st_cache_inited X) eqn:Eci.
  + cbv zeta in WC. try rewrite Eci in WC. destruct WC as [PM PL]. unfold t_cache. repeat fcons.
    apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i0 v] & <- & Hiv).
    cbn [fst snd c_at c_w z4 c4 aeval aoff]. apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
  + unfold t_cache. repeat fcons. apply Forall_nil.
Qed.

Lemma cells_chunk : forall y, In y (st_chunks X) -> ck_beg y <> ck_beg k ->
Forall (cell_holds B ly rd) (chunk_cells y) -> Forall (cell_holds B ly rd') (chunk_cells y).
Proof.
intros y Hy Hne O. pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
apply (cells_rng (ck_base B ly y) (ck_rz y)); [| |exact O].
- intros a Ha. apply (ok_chunk y a Hy Hne). pose proof (req_size_bounds (ck_req y) ltac:(lia)) as (_ & Q1 & _). lia.
- assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg y)) d) = ck_base B ly y + d).
  { intros d. unfold ck_base, sptr_addr. destruct (ck_beg y) as [|oy|ry oy|c p]; try solve [destruct GG]; cbn; lia. }
  assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg y)) d) d') = ck_base B ly y + d + d').
  { intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg y) as [|oy|ry oy|c p]; try solve [destruct GG]; cbn; lia. }
  assert (EA0 : aeval B ly (sptr_exp (ck_beg y)) = ck_base B ly y) by reflexivity.
  unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
  + repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
    apply Forall_nil.
  + destruct (Z.eqb_spec (ck_rz y) 16); [apply Forall_nil|].
    assert (32 <= ck_rz y). { apply Z.mod_divide in G6 as [q Hq]; [|lia]. lia. }
    repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
    apply Forall_nil.
Qed.

Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks rsX2)).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2).
pose proof (amr_cells _ _ _ _ _ rM) as C. unfold acells_cf in C. rewrite !Forall_app in C. destruct C as (_ & _ & C3 & _).
rewrite E, flat_map_app in C3. cbn [flat_map] in C3. apply Forall_app in C3 as [C3a C3b]. apply Forall_app in C3b as [_ C3b].
rewrite X2_chunks, E1, flat_map_app, Forall_app. split.
- apply Forall_flat_map'. intros y Hy. apply cells_chunk;
  [rewrite E; apply in_app_iff; left; exact Hy | intros Ey; apply N1; rewrite <- Ey; apply in_map; exact Hy |
   exact (Forall_flat_map_in _ _ _ y C3a Hy)].
- apply Forall_flat_map'. intros y Hy. apply cells_chunk;
  [rewrite E; apply in_app_iff; right; right; exact Hy | intros Ey; apply N2; rewrite <- Ey; apply in_map; exact Hy |
   exact (Forall_flat_map_in _ _ _ y C3b Hy)].
Qed.

(* A live secondary's header page, below the index word the arm may write. *)
Lemma ok_secpage : forall y ry a, In y (st_chunks X) -> ck_beg y = PSec ry kPage -> ry <> r ->
ly_sec ly ry <= a < ly_sec ly ry + 32 -> (ry = lastr -> own = false -> a < lst + 24) -> ok a.
Proof.
intros y ry a Hy Eby Hry Ha HL0.
pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG). rewrite Eby in GG.
destruct GG as (_ & _ & Gbase & Gext & Gin & _). destruct (sec_in_app _ Gin) as [_ LBy]. cbn [snd] in LBy.
apply (ok_sec _ a Gin); [cbn [fst snd]; lia | |].
- intros [Ho HL]. destruct (Nat.eq_dec ry lastr) as [->|Hnl]; [pose proof (HL0 eq_refl Ho); lia|].
  destruct lst_sec as (y' & Hy' & Eby' & Gy & LBy').
  assert (Hne' : ck_beg y <> ck_beg y') by (rewrite Eby, Eby'; intros E; injection E as E; exact (Hnl E)).
  pose proof (RL.secmaps_disjoint_cf B ly X Hp _ y y' ry kPage lastr kPage rM Hy Hy' Eby Eby' Hne') as D0.
  unfold zdisjoint in D0. cbn [fst snd] in D0. unfold lst in *. lia.
- intros HM. pose proof KFACTS as (Eo & _).
  assert (Hne : ck_beg y <> ck_beg k) by (rewrite Eby, Hb, Eo; intros E; injection E as E; exact (Hry E)).
  pose proof (RL.secmaps_disjoint_cf B ly X Hp _ y k ry kPage r o rM Hy Hk Eby Hb Hne) as D0.
  unfold zdisjoint in D0. cbn [fst snd] in D0. unfold rsDM, MAP, LEN in HM. lia.
Qed.

Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells rsX2).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof (wfr_secondary _ _ _ _ _ rWF) as XS.
pose proof ARR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). pose proof ARR' as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof KFACTS as (Eo & _).
assert (OLDS : Forall (cell_holds B ly rd) (sec_cells X)).
{ apply Forall_forall. intros c Hc. apply oldc. unfold acells_cf. rewrite !in_app_iff. do 3 right. left. exact Hc. }
rewrite sec_cells_X2_shape. unfold sec_cells in OLDS. fold arr in OLDS. rewrite E in OLDS.
rewrite flat_map_app in OLDS. cbn [flat_map] in OLDS. rewrite Hb in OLDS. cbn [app] in OLDS.
apply Forall_cons_iff in OLDS as [O1 OLDS]. apply Forall_cons_iff in OLDS as [O2 OLDS].
apply Forall_cons_iff in OLDS as [O3 OLDS]. apply Forall_app in OLDS as [O4 O5].
apply Forall_cons.
{ eapply cell_holds_agree; [exact O1|]. intros j Hj. cbn [c_at c_w c8 aeval] in Hj |- *. apply AGok.
  apply ok_img; [apply img_inst; unfold o_sec_reserved in *; lia | unfold rsDI, o_sec_reserved in *; lia]. }
apply Forall_cons.
{ intros kk Hkk. cbn [c_at c_w z8 c8 aeval]. rewrite B1. unfold o_sec_n.
  replace (Z.of_nat (length arr - 1)) with (nA - 1) by (unfold nA; lia). exact (NS' kk Hkk). }
apply Forall_cons.
{ intros kk Hkk. cbn [c_at c_w z1 c1 aeval]. unfold o_sec_mutex. destruct kk; [|cbn in Hkk; lia]. cbn [Z.of_nat].
  pose proof (MUT' 0 ltac:(lia)) as MU. rewrite !Z.add_0_r in MU |- *. rewrite MU. reflexivity. }
apply Forall_app. split.
- apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([j r'] & <- & Hjr). apply in_combine_seq0 in Hjr. cbn [fst snd].
  destruct (Nat.eq_dec j i) as [->|Hne].
  + pose proof (nth_error_lt _ _ _ Hjr) as LT. rewrite B1 in LT.
    assert (Ho : own = false) by (unfold own, idx, nA; apply Z.eqb_neq; lia).
    rewrite (B3 Ho) in Hjr. injection Hjr as <-. intros kk Hkk. cbn [c_at c_w c8 aeval]. fold lst. rewrite Z.add_0_r.
    unfold qi, idx in QI'. exact (QI' kk Hkk).
  + rewrite (B2 j (nth_error_lt _ _ _ Hjr) Hne) in Hjr.
    assert (OC : cell_holds B ly rd (c8 (AQ (8 * Z.of_nat j)) (ASec r' 0))).
    { apply (proj1 (Forall_forall _ _) O4). apply in_map_iff. exists (j, r'). split; [reflexivity|]. apply in_combine_seq0. exact Hjr. }
    eapply cell_holds_agree; [exact OC|]. intros jj Hjj. cbn [c_at c_w c8 aeval] in Hjj |- *. pose proof (nth_error_lt _ _ _ Hjr) as LT.
    apply AGok. apply ok_Q; [unfold kPtrArrayResv, kPtrArrayEntriesPerCommit, nA in *; lia | unfold rsDQ, qi, idx; lia].
- apply Forall_forall. intros ce Hce. rewrite E1 in Hce. apply in_flat_map in Hce as (y & Hy & Hce).
  assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy]).
  assert (Hne : ck_beg y <> ck_beg k) by (intros Ey; apply in_app_iff in Hy as [Hy|Hy]; [apply N1 | apply N2]; rewrite <- Ey; apply in_map; exact Hy).
  destruct (ck_beg y) as [|oy|ry oy|c' p] eqn:Eby; try solve [destruct Hce].
  pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy') as (_ & _ & _ & _ & _ & _ & _ & _ & GG). rewrite Eby in GG.
  destruct GG as (Eoy & _). subst oy.
  assert (Hry : ry <> r) by (intros ->; apply Hne; rewrite Hb, Eo; reflexivity).
  assert (OC : forall ce', In ce' [c8 (ASec ry 0) (ASec ry 0); z8 (ASec ry 8) (sec_map_size (ck_req y));
    z8 (ASec ry 16) (needed_size (ck_req y)); z8 (ASec ry 24) (index_ofZ arr ry)] -> cell_holds B ly rd ce').
  { intros ce' H'. apply (proj1 (Forall_forall _ _) O5). destruct (in_app_or _ _ _ Hy) as [Hy1|Hy2].
    - apply in_app_iff. left. apply in_flat_map. exists y. split; [exact Hy1|]. rewrite Eby. exact H'.
    - apply in_app_iff. right. do 4 right. apply in_flat_map. exists y. split; [exact Hy2|]. rewrite Eby. exact H'. }
  assert (INY : In ry arr) by (apply (wsc_arr_chunks _ XS); exists y; split; [exact Hy' | exact Eby]).
  assert (OKP : forall a, ly_sec ly ry <= a < ly_sec ly ry + 24 -> ok a).
  { intros a Ha. apply (ok_secpage y ry a Hy' Eby Hry); [lia | intros -> _; unfold lst; lia]. }
  destruct Hce as [<-|[<-|[<-|[<-|[]]]]].
  + eapply cell_holds_agree; [apply OC; left; reflexivity | intros j Hj; apply AGok, OKP; cbn in Hj |- *; lia].
  + eapply cell_holds_agree; [apply OC; right; left; reflexivity | intros j Hj; apply AGok, OKP; cbn in Hj |- *; lia].
  + eapply cell_holds_agree; [apply OC; right; right; left; reflexivity | intros j Hj; apply AGok, OKP; cbn in Hj |- *; lia].
  + destruct (In_nth_error _ _ INY) as [j Hj].
    destruct (Nat.eq_dec ry lastr) as [->|Hnl].
    * assert (Ho : own = false) by (destruct own eqn:Eo'; [exfalso; apply Hry; apply A8; reflexivity | reflexivity]).
      rewrite (index_ofZ_nth arr' i lastr B4 (B3 Ho)). intros kk Hkk. cbn [c_at c_w z8 c8 aeval]. fold lst.
      unfold idx in LST'. exact (LST' Ho kk Hkk).
    * assert (Hji : j <> i) by (intros ->; unfold arr in Hj; rewrite Hi in Hj; injection Hj as ->; exact (Hry eq_refl)).
      assert (Hjl : j <> (length arr - 1)%nat) by (intros ->; rewrite A6 in Hj; injection Hj as EL; exact (Hnl (eq_sym EL))).
      pose proof (nth_error_lt _ _ _ Hj) as LT.
      rewrite (index_ofZ_nth arr' j ry B4 ltac:(rewrite (B2 j ltac:(rewrite B1; lia) Hji); exact Hj)).
      rewrite <- (index_ofZ_nth arr j ry A3 Hj).
      eapply cell_holds_agree; [apply OC; right; right; right; left; reflexivity |]. intros jj Hjj. cbn [c_at c_w z8 c8 aeval] in Hjj |- *.
      apply AGok. apply (ok_secpage y ry _ Hy' Eby Hry); [lia | intros E0; exfalso; exact (Hnl E0)].
Qed.

(* The batch objects lie in class kBatchClass's user part, inside the primary reserve. *)
Lemma ok_batch : forall b a, In b (all_batches X) -> ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> ok a.
Proof.
intros b a Hbb Ha. pose proof (wfr_classes _ _ _ _ _ rWF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs X kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1' X2].
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as MB.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2, AA.
assert (XB : x + 8192 <= rg_alloc_user (reg X kBatchClass))
  by (apply Z.mod_divide in X2 as [q Hq]; [|lia]; apply Z.mod_divide in AA as [q' Hq']; [|lia]; nia).
pose proof (region_in_prim ly kBatchClass rLO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
apply ok_prim. unfold region_base, kBatchBytes, kFreeArrayOffset in *. subst x. lia.
Qed.

Definition cell_in (lo len : Z) (ce : acell) : Prop :=
lo <= aeval B ly (c_at ce) /\ aeval B ly (c_at ce) + Z.max 1 (Z.of_nat (c_w ce)) <= lo + len.

(* copy of YFf3.v:423 *)
Lemma batch_cells_within : forall l ce, In ce (batch_cells l) ->
exists b2, In b2 l /\ cell_in (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))) ce.
Proof.
induction l as [|b2 t IH]; intros ce Hce; [destruct Hce|]. cbn [batch_cells] in Hce.
destruct Hce as [<-|[<-|[<-|Hce]]]; try (exists b2; split; [left; reflexivity | unfold cell_in; cbn; lia]).
apply in_app_iff in Hce as [Hce|Hce].
- apply in_map_iff in Hce as ([i0 y] & <- & Hiy). apply in_combine_l in Hiy. apply in_seq in Hiy. exists b2.
  split; [left; reflexivity | unfold cell_in; cbn; lia].
- destruct (IH ce Hce) as (b3 & H3 & R3). exists b3. split; [right; exact H3 | exact R3].
Qed.

Lemma cells_quar : Forall (cell_holds B ly rd) (quar_cells X) -> Forall (cell_holds B ly rd') (quar_cells rsX2).
Proof.
intros O. unfold quar_cells in O |- *. rewrite X2_qthread, X2_qglobal. apply cells_xfer; [|exact O].
assert (OI : forall a, as_inst B + 720 <= a < as_inst B + 3632 -> ok a).
{ intros a Ha. apply ok_img; [apply img_inst; lia | unfold rsDI; lia]. }
assert (OT : forall a, ly_T ly + t_qc <= a < ly_T ly + t_qc + 32 -> ok a).
{ intros a Ha. apply ok_T; unfold rsDJ, t_qc, t_stats, kThreadObjSize in *; lia. }
assert (BB : forall l, incl l (all_batches X) ->
  Forall (fun c => forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> ok (aeval B ly (c_at c) + j)) (batch_cells l)).
{ intros l IL. apply Forall_forall. intros ce Hce j Hj. destruct (batch_cells_within l ce Hce) as (b2 & I2 & [R1 R2]).
  pose proof (IL b2 I2) as Hb2.
  pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfr_quarantine _ _ _ _ _ rWF)) b2 Hb2) as [L1 L2].
  apply (ok_batch b2 _ Hb2). unfold kBatchSlots, kBatchBytes in *. lia. }
unfold qc_cells.
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval z1 c1] in *; apply OI; unfold o_q_cmutex in *; lia|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval z1 c1] in *; apply OI; unfold o_q_rmutex in *; lia|].
apply Forall_app. split.
- apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval aoff z8 c8] in *; apply OT; lia|].
  apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval aoff z8 c8] in *; apply OT; lia|].
  apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval aoff z8 c8] in *; apply OT; lia|].
  apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval aoff z8 c8] in *; apply OT; lia|].
  apply BB. intros b Hbb. unfold all_batches. apply in_app_iff. left. exact Hbb.
- apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval aoff z8 c8] in *; apply OI; unfold o_q_size in *; lia|].
  apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval aoff z8 c8] in *; apply OI; unfold o_q_size in *; lia|].
  apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval aoff z8 c8] in *; apply OI; unfold o_q_size in *; lia|].
  apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval aoff z8 c8] in *; apply OI; unfold o_q_size in *; lia|].
  apply BB. intros b Hbb. unfold all_batches. apply in_app_iff. right. exact Hbb.
Qed.

Lemma cells_fs : Forall (cell_holds B ly rd) (fs_cells X) -> Forall (cell_holds B ly rd') (fs_cells rsX2).
Proof.
intros O. unfold fs_cells in O |- *. rewrite X2_fs. apply (cells_rng (ly_F ly) kFakeFramesOff); [| |exact O].
- intros a Ha. apply (ok_static 3 (ly_F ly, kFakeStackSize)); [lia | reflexivity | cbn [fst snd]; unfold kFakeFramesOff, kFakeStackSize in *; lia].
- unfold kFakeFramesOff. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|].
  apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i0 h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. lia.
Qed.

Lemma cells_depot : Forall (cell_holds B ly rd) (depot_cells ly X) -> Forall (cell_holds B ly rd') (depot_cells ly rsX2).
Proof.
intros O. unfold depot_cells, depot_ids, depot_frames in O |- *. rewrite X2_depot. apply cells_xfer; [|exact O].
unfold d_nuniq, d_map1, s_total, s_block0.
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c4 z4] in *;
  apply (ok_area (as_depot B, 4 * 2 ^ 20 + 32)); [cbn; tauto | cbn [fst snd]; lia | apply ns_depot; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
  apply (ok_area (as_depot B, 4 * 2 ^ 20 + 32)); [cbn; tauto | cbn [fst snd]; lia | apply ns_depot; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
  apply (ok_area (as_store B, 32)); [cbn; tauto | cbn [fst snd]; lia | apply ns_store; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
  apply (ok_area (as_store B, 32)); [cbn; tauto | cbn [fst snd]; lia | apply ns_store; lia]|].
apply Forall_nil.
Qed.

Lemma cells_ialloc : Forall (cell_holds B ly rd) (ialloc_cells B X) -> Forall (cell_holds B ly rd') (ialloc_cells B rsX2).
Proof.
intros O. unfold ialloc_cells in O |- *. rewrite X2_inited. apply cells_xfer; [|exact O].
pose proof (aso_ialloc _ rSY) as [I1 I2]. cbv zeta.
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c1 z1] in *;
  apply (ok_area (as_ialloc_flag B, 2)); [cbn; tauto | cbn [fst snd]; lia | apply ns_iflag; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c1 z1] in *;
  apply (ok_area (as_ialloc_flag B, 2)); [cbn; tauto | cbn [fst snd]; lia | apply ns_iflag; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
  apply (ok_area (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [cbn; tauto | cbn [fst snd]; lia | apply ns_ialloc; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
  apply (ok_area (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [cbn; tauto | cbn [fst snd]; lia | apply ns_ialloc; lia]|].
apply Forall_nil.
Qed.

Lemma cells_thread : Forall (cell_holds B ly rd) thread_cells -> Forall (cell_holds B ly rd') thread_cells.
Proof.
intros O. apply cells_xfer; [|exact O]. unfold thread_cells. apply Forall_cons; [|apply Forall_nil].
intros j Hj. cbn [c_at c_w aeval c1 z1] in *. apply ok_T; unfold rsDJ, t_unwinding, t_stats, kThreadObjSize in *; lia.
Qed.

Lemma cells_X2 : Forall (cell_holds B ly rd') (acells_cf B ly rsX2).
Proof.
pose proof (amr_cells _ _ _ _ _ rM) as C. unfold acells_cf in C. rewrite !Forall_app in C.
destruct C as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9).
unfold acells_cf. rewrite !Forall_app.
split; [exact cells_regions|].
split; [apply Forall_flat_map'; intros c Hc0; pose proof Hc0 as Hc; apply zseq_In in Hc;
  exact (cells_cache c ltac:(lia) (Forall_flat_map_in _ _ _ c O2 Hc0))|].
split; [exact cells_chunks|].
split; [exact cells_sec|].
split; [exact (cells_quar O5)|].
split; [exact (cells_fs O6)|].
split; [exact (cells_depot O7)|].
split; [exact (cells_ialloc O8) | exact (cells_thread O9)].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The record fields that read values.                                                                             *)
Lemma fa' : fa_entries_ok ly rd' rsX2.
Proof.
intros c i0 v Hc Hi0 Hv kk Hkk. change (reg rsX2 c) with (reg X c) in *.
pose proof (wfr_classes _ _ _ _ _ rWF c Hc) as CL. pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL.
pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
rewrite AGok; [exact (amr_fa _ _ _ _ _ rM c i0 v Hc Hi0 Hv kk Hkk)|].
pose proof (region_in_prim ly c rLO Hc) as (R1 & R2 & _). apply ok_prim.
unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *. lia.
Qed.

Lemma flags' : fs_flags_ok ly rd' rsX2.
Proof.
intros cid pos Hc Hpos. pose proof (flag_off_bounds cid pos Hc Hpos) as FB.
rewrite AGok; [exact (amr_flags _ _ _ _ _ rM cid pos Hc Hpos)|].
apply (ok_static 3 (ly_F ly, kFakeStackSize)); [lia | reflexivity |
  cbn [fst snd]; unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *; lia].
Qed.

Lemma depot' : depot_ok B ly rd' rsX2.
Proof.
pose proof (amr_depot _ _ _ _ _ rM) as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
- intros b Hb0. destruct (D1 b Hb0) as [H1 H2]. split; [exact H1|]. intros kk Hkk.
  assert (Ha : as_depot B <= as_depot B + 4 * b + Z.of_nat kk < as_depot B + 4 * 2 ^ 20 + 32) by (unfold d_tab_words in Hb0; lia).
  rewrite AGok; [exact (H2 kk Hkk)|].
  apply (ok_area (as_depot B, 4 * 2 ^ 20 + 32)); [cbn; tauto | cbn [fst snd]; lia | apply ns_depot; lia].
- intros id Hid. change (depot_ids rsX2) with (depot_ids X) in Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|].
  assert (NB : depot_ids X <= 4097).
  { unfold depot_ids. pose proof (depot_len_bound _ _ (amr_universe _ _ _ _ _ rM) (wfr_depot _ _ _ _ _ rWF)) as DL.
    unfold DEPOT_MAX in DL. lia. }
  assert (OR : forall x, ly_NB ly + 16 * id <= x < ly_NB ly + 16 * id + 16 -> rd' x = rd x).
  { intros x Hx. apply AGok. apply (ok_static 4 (ly_NB ly, kNodesBlockSize)); [lia | reflexivity | cbn [fst snd]; unfold kNodesBlockSize; lia]. }
  split; intros kk Hkk; rewrite OR by lia; [exact (H2 kk Hkk) | exact (H3 kk Hkk)].
Qed.

Lemma zero' : Forall (range_zero B ly rd') (ialloc_zero B).
Proof.
apply Forall_forall. intros r0 Hr i0 Hi0. pose proof (aso_ialloc _ rSY) as [I1 I2].
assert (Ha : as_ialloc_lo B <= aeval B ly (fst r0) + i0 < as_ialloc_lo B + (as_ialloc_hi B - as_ialloc_lo B)).
{ unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia. }
rewrite AGok; [exact (proj1 (Forall_forall _ _) (amr_zero _ _ _ _ _ rM) r0 Hr i0 Hi0)|].
apply (ok_area (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [cbn; tauto | exact Ha | apply ns_ialloc; lia].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The shadow after the unmap.                                                                                      *)
Lemma ext_off_map : forall y, In y (st_chunks X) -> ck_beg y <> ck_beg k -> zdisjoint (ck_base B ly y, ck_extent y) (MAP, LEN).
Proof.
intros y Hy Hne. pose proof KFACTS as (Eo & _ & _ & _ & GI & _).
pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy) as (G1 & G2 & _ & _ & _ & _ & G7 & G8 & GG).
destruct (ck_beg y) as [|oy|ry oy|c0 p0] eqn:Eby; try solve [destruct GG].
- exact (RL.prim_vs_secmap_cf B ly X Hp _ y oy _ rM Hy Eby GI).
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
  pose proof (RL.secmaps_disjoint_cf B ly X Hp _ y k ry kPage r o rM Hy Hk Eby Hb ltac:(rewrite Eby; exact Hne)) as D0.
  unfold zdisjoint, MAP, LEN in *. cbn [fst snd] in *. unfold kPage in *. lia.
Qed.

Lemma fa_off_map : forall lo len, In (lo, len) (fa_poison_ranges ly rsX2) -> zdisjoint (lo, len) (MAP, LEN) /\ 4096 <= lo /\ lo + len <= ASAN_CEIL.
Proof.
intros lo len Hin. pose proof KFACTS as (Eo & _ & _ & _ & GI & _). destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2).
unfold fa_poison_ranges, reg in Hin. rewrite X2_regions, X2_chunks, E1 in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'. fold (reg X c') in Hin.
  pose proof (region_in_prim ly c' rLO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
  pose proof (wfr_classes _ _ _ _ _ rWF c' ltac:(lia)) as CL.
  pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1. pose proof (wrc_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as A3.
  pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as MB.
  pose proof (MAPX 0 _ eq_refl) as DJ0. unfold zdisjoint in DJ0 |- *. cbn [fst snd] in DJ0 |- *. pose proof rT as (_ & H1 & H2 & _).
  unfold fa_base, kFreeArrayOffset, kFreeArrayMax in *. unfold region_base in *.
  destruct Hin as [EE|[EE|[]]]; injection EE as <- <-; unfold kHighMemBeg, kPrimResvSize in *; lia.
- apply in_flat_map in Hin as (y & Hy & Hin).
  assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy]).
  assert (Hne : ck_beg y <> ck_beg k) by (intros Ey; apply in_app_iff in Hy as [Hy|Hy]; [apply N1 | apply N2]; rewrite <- Ey; apply in_map; exact Hy).
  pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy') as (G1 & G2 & _ & _ & _ & _ & G7 & G8 & GG).
  destruct (ck_beg y) as [|oy|ry oy|c0 p0] eqn:Eby; try solve [destruct Hin]. destruct Hin as [EE|[]]. injection EE as <- <-.
  destruct GG as (-> & _ & Gbase & Gext & Gin & _).
  pose proof (proj1 (Forall_forall _ _) (proj1 (amr_placed _ _ _ _ _ rM)) _ Gin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3.
  split; [|split; [exact I1 | exact I3]].
  exact (RL.secmaps_disjoint_cf B ly X Hp _ y k ry kPage r o rM Hy' Hk Eby Hb ltac:(rewrite Eby; exact Hne)).
Qed.

Lemma ashadow_X2 : forall g v, g mod 8 = 0 -> ashadow B ly rsX2 g = Some v ->
(g + 8 <= MAP \/ MAP + LEN <= g) /\ ashadow B ly X g = Some v /\ 4096 <= g < ASAN_CEIL.
Proof.
intros g v Hg8 HS'. destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof geom as (M1 & M2 & M3 & M4 & M5 & M6).
apply Z.mod_divide in Hg8 as [c0 Hc0]; [|lia].
assert (AL8 : forall lo, lo mod 4096 = 0 -> g < lo -> g + 8 <= lo) by (intros lo Hlo Hlt; apply Z.mod_divide in Hlo as [q Hq]; [|lia]; subst; nia).
unfold ashadow in HS' |- *. rewrite X2_chunks, E1 in HS'. rewrite E. rewrite find_chunk_at_app_cf in HS' |- *. cbn [find_chunk_at].
destruct (find_chunk_at B ly l1 g) as [y|] eqn:F1.
- apply find_chunk_at_In in F1 as [Hy Hgy].
  assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff; left; exact Hy).
  assert (Hne : ck_beg y <> ck_beg k) by (intros Ey; apply N1; rewrite <- Ey; apply in_map; exact Hy).
  pose proof (ext_off_map y Hy' Hne) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0.
  pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy') as (G1 & G2 & G3 & _). unfold in_app in G1.
  split; [|split; [exact HS' | lia]].
  destruct DJ0 as [D0|D0]; [left; apply AL8; [exact M1 | lia] | right; lia].
- destruct ((ck_base B ly k <=? g) && (g <? ck_base B ly k + ck_extent k)) eqn:TK.
  + exfalso. apply andb_prop in TK as [T1 T2]. apply Z.leb_le in T1. apply Z.ltb_lt in T2.
    pose proof KFACTS as (_ & _ & _ & _ & _ & _ & Gb & Ge & _).
    destruct (find_chunk_at B ly l2 g) as [y|] eqn:F2.
    * apply find_chunk_at_In in F2 as [Hy Hgy]. assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff; right; right; exact Hy).
      assert (Hne : ck_beg y <> ck_beg k) by (intros Ey; apply N2; rewrite <- Ey; apply in_map; exact Hy).
      pose proof (ext_off_map y Hy' Hne) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0. unfold kPage in *. lia.
    * destruct (in_rangesb g (fa_poison_ranges ly rsX2)) eqn:R; [|discriminate]. apply in_rangesb_true in R as (lo & len & Hin & Hg).
      pose proof (fa_off_map lo len Hin) as (DJ0 & _). unfold zdisjoint in DJ0. cbn [fst snd] in DJ0. unfold kPage in *. lia.
  + destruct (find_chunk_at B ly l2 g) as [y|] eqn:F2.
    * apply find_chunk_at_In in F2 as [Hy Hgy]. assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff; right; right; exact Hy).
      assert (Hne : ck_beg y <> ck_beg k) by (intros Ey; apply N2; rewrite <- Ey; apply in_map; exact Hy).
      pose proof (ext_off_map y Hy' Hne) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0.
      pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy') as (G1 & G2 & _). unfold in_app in G1.
      split; [|split; [exact HS' | lia]].
      destruct DJ0 as [D0|D0]; [left; apply AL8; [exact M1 | lia] | right; lia].
    * destruct (in_rangesb g (fa_poison_ranges ly rsX2)) eqn:R; [|discriminate]. pose proof R as R'.
      apply in_rangesb_true in R as (lo & len & Hin & Hg).
      pose proof (fa_off_map lo len Hin) as (DJ0 & I1 & I2). unfold zdisjoint in DJ0. cbn [fst snd] in DJ0.
      assert (OFF : g + 8 <= MAP \/ MAP + LEN <= g) by (destruct DJ0 as [D0|D0]; [left; apply AL8; [exact M1 | lia] | right; lia]).
      split; [exact OFF|]. split; [|lia].
      destruct fa_poison' as (FP1 & FP2 & EF & EF2). rewrite EF. rewrite EF2 in R'. rewrite in_rangesb_remove by lia. rewrite R'. exact HS'.
Qed.

(* The weak shadow (CfF2b 68f3ef3b4ba): a pending chunk other than the dead one is still pending at rsX2; the dead
   chunk's user granules lie in its map, which ashadow_X2 excludes. *)
Lemma shadow' : shadow_ok_weak_cf B ly Hp rd' rsX2.
Proof.
intros g v Hg8 HS'. destruct (ashadow_X2 g v Hg8 HS') as (OFF & HS & G1 & G2).
assert (EQ : rd' (shadow_addr g) = rd (shadow_addr g)).
{ apply AGok. destruct (shadow_addr_bounds g ltac:(lia)) as [SB1 SB2].
  apply ok_band; [split; [exact SB1 | apply SB2; ceil; unfold ASAN_CEIL, kHighMemEnd in *; lia]|].
  intros HD. apply (DH_iff g Hg8) in HD. lia. }
rewrite EQ.
destruct (amr_shadow _ _ _ _ _ rM g v Hg8 HS) as [L|[(k0 & (Hk0 & Hst0 & Hni0) & HR) HP]]; [left; exact L|].
right. split; [|exact HP]. exists k0. split; [|exact HR]. split; [|split; [exact Hst0 | exact Hni0]].
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). rewrite X2_chunks, E1. rewrite E in Hk0.
apply in_app_iff in Hk0 as [H|[<-|H]]; [apply in_app_iff; left; exact H | exfalso | apply in_app_iff; right; exact H].
pose proof KFACTS as (Eo & Esm & Hq & Hfp & GI & Glt & Gbase & Gext & Gal).
pose proof (RL.chunk_facts_cf B ly X Hp _ k rM Hk) as (G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & _).
pose proof geom as (M1 & M2 & M3 & M4 & M5 & M6).
assert (XE : (ck_extent k - ck_rz k) mod 8 = 0).
{ rewrite Gext. unfold LEN in *. apply Z.mod_divide in M3 as [p Hp']; [|unfold kPage; lia].
  apply Z.mod_divide in G6' as [q Hq']; [|lia]. apply Z.mod_divide; [lia|]. unfold kPage in *. exists (p * 512 - 512 - 2 * q). lia. }
assert (RD : (ck_n k + 7) / 8 * 8 <= ck_extent k - ck_rz k).
{ apply Z.mod_divide in XE as [e Heq]; [|lia]. assert (ck_n k <= e * 8) by (unfold ck_n in *; lia).
  assert ((ck_n k + 7) / 8 < e + 1) by (apply Z.div_lt_upper_bound; lia). lia. }
rewrite Gbase in HR. rewrite Gext in RD. unfold kPage in *. lia.
Qed.

Lemma zshadow' : zshadow_ok B ly rd'.
Proof.
pose proof (amr_zshadow _ _ _ _ _ rM) as ZS. unfold zshadow_ok in ZS |- *. apply Forall_forall. intros r0 Hr i0 Hi0.
pose proof (proj1 (Forall_forall _ _) ZS r0 Hr i0 Hi0) as Z0. unfold shadow_of_addr in Z0 |- *.
change (SHADOW_OFF + fst r0 / 8) with (shadow_addr (fst r0)) in Z0 |- *.
rewrite AGok; [exact Z0|].
apply ok_band; [exact (RL.zshadow_low_cf B ly X Hp _ r0 i0 rM Hr Hi0)|]. intros HD.
destruct (RL.zshadow_range_facts_cf B ly X Hp _ r0 rM Hr) as (Z1 & Z2 & Z3 & Z4 & Z5).
apply Z.mod_divide in Z1 as [q Hq]; [|lia].
assert (E8 : shadow_addr (fst r0) + i0 = shadow_addr (fst r0 + 8 * i0)).
{ unfold shadow_addr. rewrite Hq. replace (q * 8 + 8 * i0) with ((q + i0) * 8) by lia. rewrite !Z_div_mult by lia. lia. }
rewrite E8 in HD. apply DH_iff in HD; [|rewrite Hq; replace (q * 8 + 8 * i0) with ((q + i0) * 8) by lia; apply Z_mod_mult].
assert (IN : fst r0 <= fst r0 + 8 * i0 < fst r0 + snd r0) by (pose proof (Z.mul_div_le (snd r0) 8 ltac:(lia)); lia).
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr]; cbn [fst snd] in IN, HD.
- pose proof (MAPX 8 _ eq_refl) as D0. unfold zdisjoint in D0. cbn [fst snd] in D0. lia.
- pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ rM) r0 ltac:(apply in_app_iff; right; exact Hr)) as [R1 R2].
  pose proof (MAPX 9 _ eq_refl) as D0. unfold zdisjoint in D0. cbn [fst snd] in D0. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Visibility: only the dead map's bytes may disappear.                                                             *)
Lemma vis_dm : forall e len, range_vis B ly rd (e, len) ->
(forall j, 0 <= j < len -> 0 <= aeval B ly e + j < 2 ^ 64 /\ ~ rsDM (aeval B ly e + j)) -> range_vis B ly rd' (e, len).
Proof. intros e len V H j Hj. cbn [fst snd] in *. destruct (H j Hj) as [H1 H2]. exact (VIS _ H1 (V j Hj) H2). Qed.
Lemma vis_ok : forall e len, range_vis B ly rd (e, len) -> (forall j, 0 <= j < len -> ok (aeval B ly e + j)) ->
range_vis B ly rd' (e, len).
Proof.
intros e len V H. apply (vis_dm e len V). intros j Hj. destruct (H j Hj) as [H1 H2]. split; [exact H1|].
intros HM. apply H2. right; right; right; right; right; right. exact HM.
Qed.
Lemma dm_static : forall j y a, nth_error (static_extents ly) j = Some y -> fst y <= a < fst y + snd y -> ~ rsDM a.
Proof.
intros j y a Hj Ha. apply off_DM. intros e He Hae. pose proof (SECX e j y He Hj) as D0. unfold zdisjoint in D0. lia.
Qed.
Lemma img_64 : forall a, in_zr a (ly_img ly) -> 0 <= a < 2 ^ 64 /\ ~ rsDM a.
Proof.
intros a Ha. pose proof (lo_img _ rLO) as (I1 & I2 & I3 & _). split.
- unfold in_zr in Ha. rewrite I1 in Ha. unfold kImgLo, kImgEnd in *. lia.
- exact (dm_static 9 (ly_img ly) a eq_refl Ha).
Qed.
Lemma T_64 : forall a, T <= a < T + kThreadObjSize -> 0 <= a < 2 ^ 64 /\ ~ rsDM a.
Proof.
intros a Ha. pose proof rT as (IT & _). split; [exact (in_app_64 _ _ a IT Ha)|].
exact (dm_static 2 (ly_T ly, kThreadObjSize) a eq_refl Ha).
Qed.
Lemma st_64 : forall j y a, (j < 8)%nat -> nth_error (static_extents ly) j = Some y -> fst y <= a < fst y + snd y ->
0 <= a < 2 ^ 64 /\ ~ rsDM a.
Proof.
intros j y a Hj He Ha.
pose proof (proj1 (Forall_forall _ _) (lo_app _ rLO) y ltac:(unfold static_extents in He;
  rewrite nth_error_app1 in He by (cbn; lia); eapply nth_error_In; exact He)) as HE.
split; [exact (in_app_64 _ _ a HE Ha) | exact (dm_static j y a He Ha)].
Qed.
Lemma band_64 : forall a, SHADOW_OFF <= a < kHighMemBeg -> 0 <= a < 2 ^ 64 /\ ~ rsDM a.
Proof.
intros a Ha. pose proof geom as (_ & _ & _ & M4 & _). split; [unfold SHADOW_OFF, kHighMemBeg in *; lia|].
intros HM. exact (band_off_app a MAP LEN M4 HM Ha).
Qed.
Lemma F_shadow_band : forall j, 0 <= j < (kFakeStackSize - kFakeFramesOff) / 8 ->
SHADOW_OFF <= shadow_addr (ly_F ly + kFakeFramesOff) + j < kHighMemBeg.
Proof.
intros j Hj. pose proof (proj1 (Forall_forall _ _) (lo_app _ rLO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as IF.
cbn [fst snd] in IF. unfold shadow_addr.
assert (D1 : 0 <= (ly_F ly + kFakeFramesOff) / 8) by (apply Z.div_pos; destruct IF; unfold kFakeFramesOff in *; lia).
assert (D2 : (ly_F ly + kFakeFramesOff) / 8 + (kFakeStackSize - kFakeFramesOff) / 8 <= (ly_F ly + kFakeStackSize) / 8).
{ assert (E : ly_F ly + kFakeStackSize = (ly_F ly + kFakeFramesOff) + (kFakeStackSize - kFakeFramesOff)) by lia. rewrite E.
  apply Z.div_le_lower_bound; [lia|].
  pose proof (Z.mul_div_le (ly_F ly + kFakeFramesOff) 8 ltac:(lia)).
  pose proof (Z.mul_div_le (kFakeStackSize - kFakeFramesOff) 8 ltac:(lia)). lia. }
assert (D3 : (ly_F ly + kFakeStackSize) / 8 <= 17592184995840).
{ apply Z.div_le_upper_bound; [lia|]. ceil. destruct IF as [IF0 [IL|[IH1 IH2]]];
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kFakeStackSize in *; lia. }
unfold SHADOW_OFF, kHighMemBeg in *. lia.
Qed.

Lemma junk' : Forall (range_vis B ly rd') (ajunk_cf B ly rsX2).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof (amr_junk _ _ _ _ _ rM) as J.
pose proof ARR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). pose proof ARR' as (B1 & _).
pose proof (wfr_secondary _ _ _ _ _ rWF) as XS.
unfold ajunk_cf in J |- *. unfold quar_junk, cache_junk, cache, sec_junk in J |- *.
rewrite all_batches', X2_cinit, X2_cache, X2_sec_arr, X2_sec_res, X2_chunks, E1. rewrite E in J. fold arr in J.
apply Forall_cons_iff in J as [J1 J]. apply Forall_cons_iff in J as [J2 J].
apply Forall_app in J as [J3 J]. apply Forall_app in J as [J4 J]. apply Forall_app in J as [J5 J].
apply Forall_app in J as [J6 J]. apply Forall_app in J as [J7 J]. apply Forall_app in J as [J8 J].
apply Forall_app in J as [J9 J10].
pose proof (lo_space_in _ rLO) as [SP1 SP2].
apply Forall_cons; [apply (vis_ok _ _ J1); intros j Hj; cbn [aeval fst snd] in *; apply ok_rinfo; lia|].
apply Forall_cons; [intros j Hj; cbn [snd] in Hj; lia|].
apply Forall_app. split.
{ apply Forall_forall. intros [e len] Hin. apply (vis_ok _ _ (proj1 (Forall_forall _ _) J3 _ Hin)).
  apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'.
  unfold region_junk_cf, region_junk in Hin.
  destruct Hin as [EE|[EE|[EE|[]]]]; injection EE as <- <-; intros j Hj; apply ok_rinfo; cbn [aeval aoff fst snd] in Hj |- *;
  unfold kRegionInfoOff in *; lia. }
apply Forall_app. split.
{ apply Forall_forall. intros [e len] Hin. pose proof (proj1 (Forall_forall _ _) J4 _ Hin) as V.
  apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'. destruct Hin as [EE|[]]. injection EE as <- <-.
  apply (vis_dm _ _ V). intros j Hj. cbn [aeval fst snd] in *. apply T_64. unfold t_cache, kThreadObjSize in *.
  destruct (st_cache_inited X); lia. }
apply Forall_app. split.
{ rewrite flat_map_app in J5 |- *. cbn [flat_map] in J5. apply Forall_app in J5 as [J5a J5]. apply Forall_app in J5 as [_ J5b].
  assert (CJ : forall l, (forall y, In y l -> In y (st_chunks X) /\ ck_beg y <> ck_beg k) ->
    Forall (range_vis B ly rd) (flat_map chunk_junk l) -> Forall (range_vis B ly rd') (flat_map chunk_junk l)).
  { intros l SUB JJ. apply Forall_forall. intros [e len] Hin. pose proof (proj1 (Forall_forall _ _) JJ _ Hin) as V.
    apply in_flat_map in Hin as (y & Hy & Hin). destruct (SUB y Hy) as [Hy' Hne].
    pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy') as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
    pose proof (req_size_bounds (ck_req y) ltac:(lia)) as (_ & Q2 & _).
    assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg y)) d) = ck_base B ly y + d).
    { intros d. unfold ck_base, sptr_addr. destruct (ck_beg y) as [|oy|ry oy|c p]; try solve [destruct GG]; cbn; lia. }
    apply (vis_ok _ _ V). intros j Hj. apply (ok_chunk y _ Hy' Hne).
    unfold chunk_junk in Hin. rewrite !in_app_iff in Hin. unfold kChunkHeaderSize in Hin.
    destruct Hin as [Hin|[[EE|[]]|[Hin|[EE|[]]]]];
    [destruct (ck_rz y =? 16); [destruct Hin | destruct Hin as [EE|[]]] | | destruct (ck_state y); [destruct Hin | destruct Hin as [EE|[]]] |];
    injection EE as <- <-; rewrite ?EA in *; cbn [snd] in Hj; unfold ck_n in *; lia. }
  apply Forall_app. split.
  - apply CJ; [|exact J5a]. intros y Hy. split; [rewrite E; apply in_app_iff; left; exact Hy | intros Ey; apply N1; rewrite <- Ey; apply in_map; exact Hy].
  - apply CJ; [|exact J5b]. intros y Hy. split; [rewrite E; apply in_app_iff; right; right; exact Hy | intros Ey; apply N2; rewrite <- Ey; apply in_map; exact Hy]. }
apply Forall_app. split.
{ apply Forall_cons_iff in J6 as [J6a J6]. apply Forall_cons_iff in J6 as [J6b J6]. apply Forall_cons_iff in J6 as [J6c J6].
  assert (OI : forall a, as_inst B <= a < as_inst B + 3632 -> 0 <= a < 2 ^ 64 /\ ~ rsDM a) by (intros a Ha; apply img_64; apply img_inst; exact Ha).
  apply Forall_cons; [apply (vis_dm _ _ J6a); intros j Hj; cbn [aeval fst snd] in *; apply OI; unfold o_sec_sorted in *; lia|].
  apply Forall_cons; [apply (vis_dm _ _ J6b); intros j Hj; cbn [aeval fst snd] in *; apply OI; unfold o_sec_stats, o_sec_mutex in *; lia|].
  apply Forall_cons.
  { intros j Hj. cbn [fst snd aeval] in Hj |- *. rewrite B1 in Hj |- *. pose proof (wsc_reserved _ XS) as SR.
    assert (QZ : 0 <= ly_Q ly + 8 * Z.of_nat (length arr - 1) + j < 2 ^ 64 /\ ~ rsDM (ly_Q ly + 8 * Z.of_nat (length arr - 1) + j)).
    { apply (st_64 1 (ly_Q ly, kPtrArrayResv)); [lia | reflexivity | cbn [fst snd]; unfold kPtrArrayResv, kPtrArrayEntriesPerCommit, nA, arr in *; lia]. }
    destruct QZ as [Q1 Q2]. apply (VIS _ Q1); [|exact Q2].
    destruct (Z_lt_le_dec j 8) as [LOW|HIGH'].
    - assert (OC : cell_holds B ly rd (c8 (AQ (8 * Z.of_nat (length arr - 1))) (ASec lastr 0))).
      { apply oldc. unfold acells_cf. rewrite !in_app_iff. do 3 right. left. unfold sec_cells. do 3 right. apply in_app_iff. left.
        apply in_map_iff. exists ((length arr - 1)%nat, lastr). split; [reflexivity|]. apply in_combine_seq0. exact A6. }
      specialize (OC (Z.to_nat j) ltac:(cbn; lia)). cbn [c_at c_w c8 aeval] in OC. rewrite Z2Nat.id in OC by lia.
      rewrite OC. discriminate.
    - specialize (J6c (j - 8) ltac:(cbn [snd]; unfold nA, arr in *; lia)). cbn [fst snd aeval] in J6c.
      replace (ly_Q ly + 8 * Z.of_nat (length arr) + (j - 8)) with (ly_Q ly + 8 * Z.of_nat (length arr - 1) + j) in J6c
        by (unfold nA, arr in *; lia). exact J6c. }
  rewrite flat_map_app in J6 |- *. cbn [flat_map] in J6. rewrite Hb in J6. cbn [app] in J6.
  apply Forall_app in J6 as [J6l J6]. apply Forall_cons_iff in J6 as [_ J6r].
  assert (PJ : forall l, (forall y, In y l -> In y (st_chunks X) /\ ck_beg y <> ck_beg k) ->
    Forall (range_vis B ly rd) (flat_map (fun y => match ck_beg y with PSec r' _ => [(ASec r' 32, kPage - 32)] | _ => [] end) l) ->
    Forall (range_vis B ly rd') (flat_map (fun y => match ck_beg y with PSec r' _ => [(ASec r' 32, kPage - 32)] | _ => [] end) l)).
  { intros l SUB JJ. apply Forall_forall. intros [e len] Hin. pose proof (proj1 (Forall_forall _ _) JJ _ Hin) as V.
    apply in_flat_map in Hin as (y & Hy & Hin). destruct (SUB y Hy) as [Hy' Hne].
    destruct (ck_beg y) as [|oy|ry oy|c0 p0] eqn:Eby; try solve [destruct Hin]. destruct Hin as [EE|[]]. injection EE as <- <-.
    pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy') as (_ & _ & _ & _ & _ & _ & _ & _ & GG). rewrite Eby in GG.
    destruct GG as (Eoy & _ & _ & _ & Gin & _). destruct (sec_in_app _ Gin) as [IA LB]. cbn [fst snd] in IA, LB.
    pose proof (RL.secmaps_disjoint_cf B ly X Hp _ y k ry oy r o rM Hy' Hk Eby Hb ltac:(rewrite Eby; exact Hne)) as D0.
    apply (vis_dm _ _ V). intros j Hj. cbn [aeval fst snd] in Hj |- *. split; [apply (in_app_64 _ _ _ IA); unfold kPage in *; lia|].
    intros HM. unfold rsDM, MAP, LEN in HM. unfold zdisjoint in D0. cbn [fst snd] in D0. unfold kPage in *. lia. }
  apply Forall_app. split.
  - apply PJ; [|exact J6l]. intros y Hy. split; [rewrite E; apply in_app_iff; left; exact Hy | intros Ey; apply N1; rewrite <- Ey; apply in_map; exact Hy].
  - apply PJ; [|exact J6r]. intros y Hy. split; [rewrite E; apply in_app_iff; right; right; exact Hy | intros Ey; apply N2; rewrite <- Ey; apply in_map; exact Hy]. }
apply Forall_app. split.
{ apply Forall_forall. intros [e len] Hin. pose proof (proj1 (Forall_forall _ _) J7 _ Hin) as V.
  apply in_flat_map in Hin as (b2 & Hb2 & Hin). destruct Hin as [EE|[]]. injection EE as <- <-.
  pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfr_quarantine _ _ _ _ _ rWF)) b2 Hb2) as [L1 L2].
  apply (vis_ok _ _ V). intros j Hj. cbn [aeval aoff batch_exp fst snd] in Hj |- *. apply (ok_batch b2 _ Hb2).
  unfold kBatchSlots, kBatchBytes in *. lia. }
apply Forall_app. split.
{ unfold thread_junk in J8 |- *. apply Forall_forall. intros [e len] Hin. pose proof (proj1 (Forall_forall _ _) J8 _ Hin) as V.
  apply (vis_dm _ _ V). intros j Hj. destruct Hin as [EE|[EE|[EE|[EE|[]]]]]; injection EE as <- <-; cbn [aeval fst snd] in Hj |- *; apply T_64;
  unfold t_cache, t_cache_stats, t_stats, t_unwinding, kThreadObjSize in *; lia. }
apply Forall_app. split.
{ apply Forall_forall. intros [e len] Hin. pose proof (proj1 (Forall_forall _ _) J9 _ Hin) as V. pose proof (aso_cells _ rSY) as AC.
  apply (vis_dm _ _ V). intros j Hj. apply img_64.
  destruct Hin as [EE|[EE|[EE|[EE|[]]]]]; injection EE as <- <-; cbn [aeval fst snd] in Hj |- *.
  - apply (img_area (as_oom_byte B, 1)); [cbn; tauto | cbn [fst snd]; lia].
  - apply (img_area (as_depot B, 4 * 2 ^ 20 + 32)); [cbn; tauto | cbn [fst snd]; unfold d_nuniq in *; lia].
  - apply (img_area (as_store B, 32)); [cbn; tauto | cbn [fst snd]; lia].
  - apply (img_area (as_store B, 32)); [cbn; tauto | cbn [fst snd]; lia]. }
apply Forall_forall. intros [e len] Hin. pose proof (proj1 (Forall_forall _ _) J10 _ Hin) as V.
apply (vis_dm _ _ V). intros j Hj. apply img_64.
destruct (IJ B ly (e, len) TS rLO Hin j Hj) as (sg & Hsg & S1 & S2). pose proof (alc_img _ _ _ _ rLED sg Hsg) as [G1 G2].
cbn [fst snd] in S1, S2. unfold in_zr. lia.
Qed.

Lemma areas' : Forall (range_vis B ly rd') (aareas rsX2).
Proof.
destruct aareas_split as (AA1 & AA2 & EA1 & EA2). pose proof (amr_areas _ _ _ _ _ rM) as A. rewrite EA1 in A.
assert (GEN : forall el, In el (aareas rsX2) -> range_vis B ly rd el -> range_vis B ly rd' el).
{ intros [e len] Hin V. destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof (lo_space_in _ rLO) as [SP1 SP2].
  unfold aareas, reg in Hin. rewrite X2_regions, X2_sec_res, X2_chunks, E1 in Hin. rewrite !in_app_iff in Hin.
  destruct Hin as [Hin|[[EE|[]]|[Hin|Hin]]].
  - apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'. fold (reg X c') in Hin.
    pose proof (region_in_prim ly c' rLO ltac:(lia)) as (R1 & R2 & _).
    pose proof (wfr_classes _ _ _ _ _ rWF c' ltac:(lia)) as CL. pose proof (wrc_fa _ _ _ _ _ _ CL) as [F1 _].
    pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as F2. pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as MB.
    pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL.
    destruct Hin as [EE|[EE|[]]]; injection EE as <- <-; apply (vis_ok _ _ V); intros j Hj; cbn [aeval fst snd] in Hj |- *;
    apply ok_prim; unfold region_base, kFreeArrayOffset, kFreeArrayMax in *; lia.
  - injection EE as <- <-. pose proof (wsc_reserved _ (wfr_secondary _ _ _ _ _ rWF)) as SR.
    apply (vis_dm _ _ V). intros j Hj. cbn [aeval fst snd] in Hj |- *.
    apply (st_64 1 (ly_Q ly, kPtrArrayResv)); [lia | reflexivity | cbn [fst snd]; unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *; lia].
  - apply in_flat_map in Hin as (y & Hy & Hin).
    assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy]).
    assert (Hne : ck_beg y <> ck_beg k) by (intros Ey; apply in_app_iff in Hy as [Hy|Hy]; [apply N1 | apply N2]; rewrite <- Ey; apply in_map; exact Hy).
    destruct (ck_beg y) as [|oy|ry oy|c0 p0] eqn:Eby; try solve [destruct Hin]. destruct Hin as [EE|[]]. injection EE as <- <-.
    pose proof (RL.secmaps_disjoint_cf B ly X Hp _ y k ry oy r o rM Hy' Hk Eby Hb ltac:(rewrite Eby; exact Hne)) as D0.
    pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy') as (_ & _ & _ & _ & _ & _ & _ & _ & GG). rewrite Eby in GG.
    destruct GG as (_ & _ & _ & _ & Gin & _). destruct (sec_in_app _ Gin) as [IA LB]. cbn [fst snd] in IA, LB.
    apply (vis_dm _ _ V). intros j Hj. cbn [aeval fst snd] in Hj |- *. rewrite Z.add_0_r in *.
    split; [apply (in_app_64 _ _ _ IA); lia|].
    intros HM. unfold rsDM, MAP, LEN in HM. unfold zdisjoint in D0. cbn [fst snd] in D0. lia.
  - destruct Hin as [EE|[EE|[EE|[EE|[EE|[EE|[]]]]]]]; injection EE as <- <-; apply (vis_dm _ _ V); intros j Hj;
    cbn [aeval fst snd] in Hj |- *.
    + apply (st_64 3 (ly_F ly, kFakeStackSize)); [lia | reflexivity | cbn [fst snd]; lia].
    + apply (st_64 4 (ly_NB ly, kNodesBlockSize)); [lia | reflexivity | cbn [fst snd]; lia].
    + apply (st_64 5 (ly_SB ly, kStoreBlockSize)); [lia | reflexivity | cbn [fst snd]; lia].
    + apply T_64. lia.
    + destruct (ok_rinfo (ly_space ly + kRegionInfoOff + j) ltac:(lia)) as [H1 H2]. split; [exact H1|].
      intros HM. apply H2. right; right; right; right; right; right. exact HM.
    + apply band_64. exact (F_shadow_band j Hj). }
rewrite EA2. apply Forall_forall. intros el Hel. apply GEN; [rewrite EA2; exact Hel|].
apply in_app_iff in Hel as [Hel|Hel]; apply (proj1 (Forall_forall _ _) A); apply in_app_iff; [left; exact Hel | right; right; exact Hel].
Qed.

Lemma client' : Forall (range_vis B ly rd') (aclient rsX2).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof (amr_client _ _ _ _ _ rM) as A.
apply Forall_forall. intros [e len] Hin.
assert (V : range_vis B ly rd (e, len)).
{ apply (proj1 (Forall_forall _ _) A). unfold aclient in Hin |- *. rewrite X2_chunks, E1 in Hin. rewrite E.
  rewrite !in_app_iff in Hin |- *. destruct Hin as [Hin|Hin]; [left|right; exact Hin].
  apply in_flat_map in Hin as (y & Hy & Hin). apply in_flat_map. exists y. split; [|exact Hin].
  apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy]. }
unfold aclient in Hin. rewrite X2_chunks, E1 in Hin. rewrite !in_app_iff in Hin. destruct Hin as [Hin|[Hin|Hin]].
- apply in_flat_map in Hin as (y & Hy & Hin).
  assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy]).
  assert (Hne : ck_beg y <> ck_beg k) by (intros Ey; apply in_app_iff in Hy as [Hy|Hy]; [apply N1 | apply N2]; rewrite <- Ey; apply in_map; exact Hy).
  unfold chunk_user in Hin. destruct (ck_state y); [|destruct Hin]. destruct Hin as [EE|[]]. injection EE as <- <-.
  pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy') as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
  pose proof (req_size_bounds (ck_req y) ltac:(lia)) as (_ & Q2 & Q3).
  apply (vis_ok _ _ V). intros j Hj. apply (ok_chunk y _ Hy' Hne).
  change (aeval B ly (sptr_exp (ck_user y))) with (sptr_addr B ly (ck_user y)). rewrite G4. cbn [snd] in Hj. unfold ck_n in *. lia.
- apply in_map_iff in Hin as ([cid pos] & EE & Hcp). injection EE as <- <-. cbn [fst snd] in *.
  pose proof (proj1 (Forall_forall _ _) (wfs_live _ (wfr_fakestack _ _ _ _ _ rWF)) (cid, pos) Hcp) as [C1 C2]. cbn [fst snd] in C1, C2.
  pose proof (frame_off_bounds cid pos C1 C2) as (FB1 & FB2 & FB3 & FB4 & FB5 & FB6).
  apply (vis_dm _ _ V). intros j Hj. cbn [aeval fst snd] in Hj |- *.
  apply (st_64 3 (ly_F ly, kFakeStackSize)); [lia | reflexivity | cbn [fst snd]; unfold kFakeStackSize, kFakeFramesOff in *; lia].
- apply in_map_iff in Hin as ([cid pos] & EE & Hcp). injection EE as <- <-. cbn [fst snd] in *.
  pose proof (proj1 (Forall_forall _ _) (wfs_live _ (wfr_fakestack _ _ _ _ _ rWF)) (cid, pos) Hcp) as [C1 C2]. cbn [fst snd] in C1, C2.
  pose proof (frame_off_bounds cid pos C1 C2) as (FB1 & FB2 & FB3 & FB4 & FB5 & FB6).
  apply (vis_dm _ _ V). intros j Hj. cbn [aeval fst snd] in Hj |- *. apply band_64.
  pose proof (proj1 (Forall_forall _ _) (lo_app _ rLO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as IF.
  cbn [fst snd] in IF. unfold shadow_addr.
  change (2 ^ 20) with 1048576 in *. unfold kFakeFramesOff in *.
  assert (D1 : 0 <= (ly_F ly + fs_frame_off cid pos) / 8) by (apply Z.div_pos; destruct IF; lia).
  assert (D2 : (ly_F ly + fs_frame_off cid pos) / 8 + fs_frame_bytes cid / 8 <= (ly_F ly + kFakeStackSize) / 8).
  { transitivity ((ly_F ly + fs_frame_off cid pos + fs_frame_bytes cid) / 8).
    - apply Z.div_le_lower_bound; [lia|].
      pose proof (Z.mul_div_le (ly_F ly + fs_frame_off cid pos) 8 ltac:(lia)).
      pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)). lia.
    - apply Z.div_le_mono; lia. }
  assert (D3 : (ly_F ly + kFakeStackSize) / 8 <= 17592184995840).
  { apply Z.div_le_upper_bound; [lia|]. ceil. destruct IF as [IF0 [IL|[IH1 IH2]]];
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kFakeStackSize in *; lia. }
  unfold SHADOW_OFF, kHighMemBeg in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The placement facts and the record.                                                                              *)
Lemma pairwise_remove_mid' : forall {Y} (R : Y -> Y -> Prop) l1 x l2, pairwise R (l1 ++ x :: l2) -> pairwise R (l1 ++ l2).
Proof.
intros Y R l1 x l2. induction l1 as [|y t IH]; cbn [app pairwise].
- intros [_ P]. exact P.
- intros [F P]. split; [| exact (IH P)]. apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) F z).
  apply in_app_iff in Hz as [Hz|Hz]; apply in_app_iff; [left | right; right]; exact Hz.
Qed.

Lemma placed' : sec_placed ly rsX2.
Proof.
destruct (amr_placed _ _ _ _ _ rM) as [PF PD]. destruct sec_extents_split as (E1 & E2 & EX & EX2). split.
- apply Forall_forall. intros e He. apply (proj1 (Forall_forall _ _) PF). apply sec_extents_sub. exact He.
- rewrite EX2. rewrite EX in PD. rewrite <- app_assoc in PD |- *. exact (pairwise_remove_mid' _ _ _ _ PD).
Qed.

Lemma hp' : Forall (fun p => exists k0, In k0 (st_chunks rsX2) /\ ck_state k0 = CAllocated /\ p = sptr_addr B ly (ck_user k0) /\
  cf_head <= ck_n k0) Hp.
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof (amr_hp_live _ _ _ _ _ rM) as H.
eapply Forall_impl; [|exact H]. cbv beta. intros p (y & Hy & Hsy & Ep & Hn). exists y. split; [|exact (conj Hsy (conj Ep Hn))].
rewrite X2_chunks, E1. rewrite E in Hy.
apply in_app_iff in Hy as [Hy|[<-|Hy]]; [apply in_app_iff; left; exact Hy | rewrite Hst in Hsy; discriminate | apply in_app_iff; right; exact Hy].
Qed.

Lemma sm_not_cap : is_errb_cap sm = false.
Proof.
pose proof (proj1 (Forall_forall _ _) (wfr_chunks _ _ _ _ _ rWF) k Hk) as [Hn CK]. rewrite Hb in CK.
destruct CK as (P1 & P2 & sm' & Q1 & Q2 & Q3 & Q4). rewrite Hsm in Q1. injection Q1 as <-.
unfold is_errb_cap, ERRB_CAP_TAG. apply Z.eqb_neq. rewrite Q3. unfold needed_size. rewrite P1.
pose proof KFACTS as (_ & _ & Hq & _). pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q5 & Q6 & Q7).
pose proof (rounded_size_bounds (ck_req k) ltac:(lia)) as [R1 _]. pose proof (rz_size_bounds (ck_req k)) as [RZ _].
unfold needed_primary. lia.
Qed.

Lemma xs_cf_X2 : xs_cf ly rsX2 = xs_cf ly X.
Proof.
assert (HC : forall sm0, nth_error (st_secs X) r = Some sm0 -> is_errb_cap (mkSec (sm_len sm) (sm_size sm) false) = is_errb_cap sm0).
{ intros sm0 H0. rewrite Hsm in H0. injection H0 as <-. reflexivity. }
unfold xs_cf. rewrite X2_secs. rewrite (last_cap_idx_lupd _ _ _ 0%nat None HC).
destruct (last_cap_idx (st_secs X) 0 None); [|reflexivity]. f_equal. f_equal.
unfold errb_cap_cf, errb_e. rewrite X2_secs. rewrite (filter_lupd_same _ _ _ _ HC). reflexivity.
unfold is_errb_cap at 1. cbn [sm_size]. fold (is_errb_cap sm). exact sm_not_cap.
Qed.

Lemma xs' : xs_placed_cf ly rsX2.
Proof.
pose proof (amr_xs_placed _ _ _ _ _ rM) as XP. unfold xs_placed_cf in XP |- *. rewrite xs_cf_X2.
eapply Forall_impl; [|exact XP]. cbv beta. intros e (P1 & P2 & P3 & P4). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) P4).
apply in_app_iff in Hz as [Hz|Hz]; apply in_app_iff; [left; exact (sec_extents_sub z Hz) | right; exact Hz].
Qed.

Lemma errb_cap_X2 : errb_cap_cf rsX2 = errb_cap_cf X.
Proof.
assert (HC : forall sm0, nth_error (st_secs X) r = Some sm0 -> is_errb_cap (mkSec (sm_len sm) (sm_size sm) false) = is_errb_cap sm0).
{ intros sm0 H0. rewrite Hsm in H0. injection H0 as <-. reflexivity. }
assert (HV : is_errb_cap (mkSec (sm_len sm) (sm_size sm) false) = false).
{ unfold is_errb_cap at 1. cbn [sm_size]. fold (is_errb_cap sm). exact sm_not_cap. }
unfold errb_cap_cf, errb_e. rewrite X2_secs. rewrite (filter_lupd_same (st_secs X) r _ is_errb_cap HC HV). reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The two machine cells of ARmcfR at rsX2.                                                                          *)
Lemma exh_X2 : YGcfInstDrainX.EXH_OFF_OK -> exh_cell_cf B ly X rd -> exh_cell_cf B ly rsX2 rd'.
Proof.
intros EXO HE. apply (YGcfInstBase.exh_cell_cf_frame B ly ly X rsX2 rd rd' HE); [intros c; reflexivity|].
intros c Hc. destruct EXO as (E1 & _).
assert (EA : aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) cf_exh_off) = ly_space ly + kRegionInfoOff + (128 * c + cf_exh_off))
  by (cbn; lia).
rewrite EA. apply AGok. apply ok_rinfo. unfold kRegionInfoOff in *. lia.
Qed.

Lemma errb_X2 : errb_obj_owned_t B -> YGcfImgRows.ERRB_QAPART ->
errb_cells_cf B ly X rd -> errb_cells_cf B ly rsX2 rd'.
Proof.
intros EOO EAP HEB.
assert (HC : forall sm0, nth_error (st_secs X) r = Some sm0 -> is_errb_cap (mkSec (sm_len sm) (sm_size sm) false) = is_errb_cap sm0).
{ intros sm0 H0. rewrite Hsm in H0. injection H0 as <-. reflexivity. }
assert (HZ : forall sm0, nth_error (st_secs X) r = Some sm0 -> is_errb_sz (mkSec (sm_len sm) (sm_size sm) false) = is_errb_sz sm0).
{ intros sm0 H0. rewrite Hsm in H0. injection H0 as <-. reflexivity. }
apply (RL.errb_cells_cf_frame_on B ly ly X rsX2 rd rd' HEB).
- unfold errb_mapped_cf. rewrite X2_secs. exact (existsb_lupd_same _ _ _ _ HC).
- unfold errb_data_cf. rewrite X2_secs, (last_cap_idx_lupd _ _ _ 0%nat None HC). reflexivity.
- exact errb_cap_X2.
- unfold errb_size_cf. rewrite X2_secs, (find_sz_lupd _ _ _ 0%nat HZ).
  destruct (find_sz (st_secs X) 0) as [ix|]; [|reflexivity].
  destruct (Nat.eq_dec ix r) as [->|Hne].
  + rewrite nth_error_lupd_same by exact (nth_error_lt _ _ _ Hsm). rewrite Hsm. reflexivity.
  + rewrite nth_error_lupd_other by congruence. reflexivity.
- intros a Ha. pose proof (EOO a Ha) as HS. apply AGok. apply ok_img.
  + apply Exists_exists in HS as (r0 & Hr0 & Hin).
    pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ rM) r0 ltac:(apply in_app_iff; left; exact Hr0)) as [Z1 Z2].
    unfold in_zr in *. lia.
  + intros HI. apply (EAP B TS a Ha). unfold rsDI in HI. lia.
- intros a Ha Hr. pose proof KFACTS as (_ & _ & _ & _ & GI & _).
  unfold errb_data_cf in Ha. destruct (last_cap_idx (st_secs X) 0 None) as [ix|] eqn:EL.
  + assert (Hxs : In (ly_sec ly ix, errb_cap_cf X) (xs_cf ly X)) by (unfold xs_cf; rewrite EL; left; reflexivity).
    pose proof (proj1 (Forall_forall _ _) (amr_xs_placed _ _ _ _ _ rM) _ Hxs) as (P1 & P2 & P3 & P4).
    pose proof (proj1 (Forall_forall _ _) P4 (MAP, LEN) ltac:(apply in_app_iff; left; exact GI)) as D.
    cbn [fst snd] in P2, D. unfold zdisjoint in D. cbn [fst snd] in D.
    apply VIS; [exact (in_app_64 _ _ a P2 Ha) | exact Hr | unfold rsDM; lia].
  + exfalso. destruct (last_cap_none _ _ _ EL) as [_ HF].
    unfold errb_cap_cf, errb_e in Ha. rewrite HF in Ha. cbn [last sm_len] in Ha. lia.
Qed.

(* Printf's two cells at X2 (field round 3): owned static, inside the image and apart from the instance object. *)
Lemma pf_X2 : pf_cells_owned_t B -> pf_cells_cf B ly rd -> pf_cells_cf B ly rd'.
Proof.
intros PO HP. apply (YG0qcf.pf_cells_frame_cf B ly rd rd'); [|exact HP].
intros a Ha. destruct (proj1 PO a Ha) as [HS NI]. apply AGok. apply ok_img.
- apply Exists_exists in HS as (r0 & Hr0 & Hin).
  pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ rM) r0 ltac:(apply in_app_iff; left; exact Hr0)) as [Z1 Z2].
  unfold in_zr in *. lia.
- intros HI. apply NI. unfold rsDI in HI. unfold kInstObjSize. lia.
Qed.

Lemma ARmcfR_X2 : ARmcfR B ly rsX2 Hp rd'.
Proof.
pose proof rM as M0.
destruct M0 as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient
  Xzero Xtsd Ximg Xhp Xxs Xexh Xerrb Xown Xpf Xpfo].
constructor.
- exact WS2.
- exact Xuni.
- exact Xsyms.
- exact Xlay.
- exact placed'.
- exact CONST'.
- exact Xcowned.
- exact cells_X2.
- exact fa'.
- exact flags'.
- exact depot'.
- exact shadow'.
- exact zshadow'.
- exact junk'.
- exact areas'.
- exact client'.
- exact zero'.
- exact Xtsd.
- exact Ximg.
- exact hp'.
- exact xs'.
- exact (exh_X2 (YGcfInstDrainX.EXH_OFF_OK_of_t (proj1 Xown)) Xexh).
- exact (errb_X2 (proj1 (proj2 Xown)) EAPm Xerrb).
- exact Xown.
- exact (pf_X2 Xpfo Xpf).
- exact Xpfo.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The owned set, the window and the client bytes.                                                                 *)
Lemma aclient_byte_X2 : forall a, aclient_byte B ly rsX2 a <-> aclient_byte B ly X a.
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). intros a. unfold aclient_byte. rewrite frames', X2_chunks, E1, E.
split; intros [(y & Hy & Hsy & Hr)|H2].
- left. exists y. split; [|split; [exact Hsy | exact Hr]]. apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy].
- right. exact H2.
- left. exists y. split; [|split; [exact Hsy | exact Hr]].
  apply in_app_iff in Hy as [Hy|[<-|Hy]]; [apply in_app_iff; left; exact Hy | rewrite Hst in Hsy; discriminate | apply in_app_iff; right; exact Hy].
- right. exact H2.
Qed.

Lemma aowned_X2 : forall a, aowned B ly rsX2 a -> aowned B ly X a.
Proof.
intros a [OW NC]. split; [|intros C; apply NC; apply (proj2 (aclient_byte_X2 a)); exact C].
destruct OW as [O|[O|[O|[O|O]]]]; [left; exact O | right; left; exact O | right; right; left; exact O | |].
- right; right; right; left. apply Exists_exists in O as (e & He & Ha). apply Exists_exists. exists e. split; [exact (sec_extents_sub e He) | exact Ha].
- right; right; right; right. apply Exists_exists in O as (e & He & Ha). apply Exists_exists. exists e. split; [|exact Ha].
  rewrite !in_app_iff in He |- *. destruct He as [He|[He|He]]; [left; exact He | right; left; exact (sec_extents_sub e He) | right; right; exact He].
Qed.

Lemma D_owned : forall a, 0 <= a -> rsD a -> aowned B ly X a \/ rsDS a.
Proof.
pose proof geom as (M1 & M2 & M3 & M4 & M5 & M6). pose proof KFACTS as (Eo & _ & _ & _ & GI & _).
pose proof ARR as (A1 & A2 & A3 & A4 & A5 & _).
intros a Ha0 HD. destruct HD as [Y|[Y|[Y|[Y|[Y|[Y|Y]]]]]].
- right. exact Y.
- left. unfold rsDI in Y. apply (RL.own_area_cf B ly X Hp _ (as_inst B, 3632) a rM); [unfold asyms_areas; cbn; tauto | cbn [fst snd]; lia].
- left. apply (RL.own_core_cf B ly X Hp _ (T, kThreadObjSize) a rM); [unfold core_extents; cbn; tauto|].
  cbn [fst snd]. unfold rsDJ, t_stats, kThreadObjSize in *. lia.
- left. apply (RL.own_core_cf B ly X Hp _ (ly_Q ly, kPtrArrayResv) a rM); [unfold core_extents; cbn; tauto|].
  cbn [fst snd]. unfold rsDQ, qi, idx, nA, kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- left. destruct Y as [Ho Y]. destruct lst_sec as (y2 & Hy2 & Ey2 & Gy & LBy).
  apply (RL.own_meta_cf B ly X Hp _ y2 a rM Hy2). rewrite Ey2.
  pose proof (RL.chunk_facts_cf B ly X Hp _ y2 rM Hy2) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite Ey2 in GG.
  destruct GG as (_ & _ & Gbase & _). unfold lst in *. rewrite Gbase. unfold kPage in *. lia.
- left. pose proof M1 as M1'. apply Z.mod_divide in M1' as [a0 Hua]; [|lia].
  unfold rsDH, shadow_addr in Y. rewrite Hua in Y. replace (a0 * 4096) with ((a0 * 512) * 8) in Y by lia. rewrite Z_div_mult in Y by lia.
  replace a with (shadow_addr ((a0 * 512 + (a - (SHADOW_OFF + a0 * 512))) * 8)).
  2:{ unfold shadow_addr. rewrite Z_div_mult by lia. lia. }
  apply (RL.own_shadow_sec_cf B ly X Hp _ MAP LEN _ rM GI). rewrite Hua.
  pose proof (Z.mul_div_le LEN 8 ltac:(lia)). nia.
- left. apply (RL.own_ext_cf B ly X Hp _ a rM).
  + right. apply Exists_exists. exists (MAP, LEN). split; [exact GI | unfold in_zr; cbn [fst snd]; unfold rsDM in Y; lia].
  + intros y Hy Hsy [R1 R2]. destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof Hy as Hy0. rewrite E in Hy0.
    assert (Hne : ck_beg y <> ck_beg k).
    { intros EE. apply in_app_iff in Hy0 as [Hy0|[Hy0|Hy0]];
      [apply N1; rewrite <- EE; apply in_map; exact Hy0 | subst y; rewrite Hst in Hsy; discriminate | apply N2; rewrite <- EE; apply in_map; exact Hy0]. }
    pose proof (ext_off_map y Hy Hne) as DD. pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
    unfold zdisjoint in DD. cbn [fst snd] in DD. unfold rsDM in Y. unfold ck_n in *. lia.
  + pose proof (MAPX 3 _ eq_refl) as DD. unfold zdisjoint in DD. cbn [fst snd] in DD. unfold rsDM in Y. unfold kFakeStackSize, kFakeFramesOff in *. lia.
Qed.

Lemma puser_notD : forall a, YFeuC.puser ly X a -> ~ rsD a.
Proof.
intros a (c' & Hc' & Hr) HD. pose proof (region_in_prim ly c' rLO Hc') as (R1 & R2 & _).
pose proof (wfr_classes _ _ _ _ _ rWF c' Hc') as CL. pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1.
pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as MB.
assert (IP : ly_prim ly <= a < ly_prim ly + kPrimResvSize) by (unfold region_base, kFreeArrayOffset in *; lia).
destruct (ok_prim a IP) as [_ ND]. exact (ND HD).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The hidden shadow: the window's only band part is the dead map's shadow, which the unmap zeroes.                *)
Lemma band_zone : forall a, in_band_rw a -> kLowShadowBeg <= a < kHighMemBeg.
Proof.
intros a Ha. unfold in_band_rw in Ha. unfold kHighMemBeg, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia.
Qed.
Lemma band_off_app2 : forall a lo len, in_app lo len -> lo <= a < lo + len -> ~ (kLowShadowBeg <= a < kHighMemBeg).
Proof.
intros a lo len [H0 [HL|[HH1 HH2]]] Ha; ceil; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia.
Qed.

Lemma BAND : forall a, in_band_rw a -> rsD a -> rsDH a.
Proof.
intros a Ha HD. pose proof (band_zone a Ha) as HB.
destruct HD as [Y|[Y|[Y|[Y|[Y|[Y|Y]]]]]]; [exfalso | exfalso | exfalso | exfalso | exfalso | exact Y | exfalso].
- unfold rsDS in Y. unfold YFeu.KSTACK in *. pose proof rT as (_ & _ & _ & H4 & _). unfold kLowShadowBeg, kHighMemBeg in *. lia.
- pose proof (img_inst a ltac:(unfold rsDI in Y; lia)) as HI. pose proof (lo_img _ rLO) as (I1 & I2 & I3 & _).
  unfold in_zr in HI. rewrite I1 in HI. unfold kImgLo, kImgEnd, kLowShadowBeg in *. lia.
- pose proof rT as (IT & _). apply (band_off_app2 a _ _ IT); [unfold rsDJ, t_stats, kThreadObjSize in *; lia | exact HB].
- pose proof rT as (_ & _ & _ & _ & _ & _ & IQ). pose proof ARR as (_ & _ & _ & A4 & A5 & _).
  apply (band_off_app2 a _ _ IQ); [unfold rsDQ, qi, idx, nA, kPtrArrayResv, kPtrArrayEntriesPerCommit in *; lia | exact HB].
- destruct Y as [Ho Y]. destruct lst_sec as (y & Hy & Eby & Gy & LBy). destruct (sec_in_app _ Gy) as [IA _]. cbn [fst snd] in IA.
  apply (band_off_app2 a _ _ IA); [lia | exact HB].
- pose proof geom as (_ & _ & _ & M4 & _). apply (band_off_app2 a _ _ M4); [unfold rsDM in Y; lia | exact HB].
Qed.

Lemma ahs' : (forall a, in_band_rw a -> ~ rsD a -> mem' (w64 a) = mem (w64 a)) ->
(forall a, rsDH a -> mem' (w64 a) = Some (Z_to_bv 8 0)) -> ahs B ly rsX2 (w_H W) mem'.
Proof.
intros EQ ZE. pose proof MR as (_ & _ & _ & _ & [HA HZ]). unfold ahs, ahs_pres, ahz in *. unfold YG0d.w64, YG0n.w64 in *. split.
- intros a Ha NC HH. assert (Hd : rsDH a \/ ~ rsDH a) by (unfold rsDH; lia). destruct Hd as [Hd|Nd].
  + rewrite (ZE a Hd). discriminate.
  + rewrite (EQ a Ha (fun HD => Nd (BAND a Ha HD))). apply (HA a Ha); [|exact HH]. intros C. apply NC. apply (proj2 (aclient_byte_X2 a)). exact C.
- intros g Hg HAPP HF. assert (Hm : (MAP <= g < MAP + LEN) \/ ~ (MAP <= g < MAP + LEN)) by lia. destruct Hm as [Hin|Hout].
  + apply ZE. apply (proj2 (DH_iff g Hg)). exact Hin.
  + assert (HF0 : hfree ly X g).
    { unfold hfree in *. destruct sec_extents_split as (E1 & E2 & EX & EX2). rewrite EX2 in HF. rewrite EX.
      apply Forall_app in HF as [HFs HF]. apply Forall_app in HF as [HFv HF]. apply Forall_app in HF as [HF1 HF2].
      apply Forall_app; split; [exact HFs|]. apply Forall_app; split; [exact HFv|]. apply Forall_app; split; [exact HF1|]. constructor; [|exact HF2].
      cbn [fst snd]. pose proof geom as (M1 & _). apply Z.mod_divide in M1 as [q Hq]; [|lia]. apply Z.mod_divide in Hg as [c0 Hc0]; [|lia]. lia. }
    rewrite (EQ (shadow_addr g) (shadow_addr_band_rw g HAPP)); [exact (HZ g Hg HAPP HF0)|].
    intros HD. apply Hout. apply (proj1 (DH_iff g Hg)). exact (BAND _ (shadow_addr_band_rw g HAPP) HD).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The refund and the relation at the post state.                                                                  *)
Definition W2 : world im_segs := YFfn.wrefund im_segs W (MAP, MAP + LEN).

Lemma APART2 : forall e, In e (sec_extents ly rsX2) -> zdisjoint e (MAP, LEN).
Proof.
intros e He. destruct sec_extents_split as (S1 & S2 & EX & EX2). rewrite EX2 in He.
destruct (amr_placed _ _ _ _ _ rM) as [_ PD]. rewrite EX, <- app_assoc in PD. cbn [app] in PD.
destruct (YG0j.pairwise_app_mid zdisjoint S1 (MAP, LEN) (S2 ++ static_extents ly) PD) as [D1 D2].
apply in_app_iff in He as [He|He]; [exact (D1 e He)|]. pose proof (D2 e ltac:(apply in_app_iff; left; exact He)) as D. unfold zdisjoint in *. lia.
Qed.

Lemma asecA_X2 : asecA ly X (w_A W) -> asecA ly rsX2 (YFfn.A_drop (MAP, MAP + LEN) (w_A W)).
Proof.
intros H e He. pose proof (sec_extents_sub e He) as He0. destruct (H e He0) as [HA HH].
destruct (sec_in_app e He0) as [IA LB].
pose proof (proj1 (Forall_forall _ _) (proj1 (amr_placed _ _ _ _ _ rM)) _ He0) as (_ & _ & I3).
pose proof geom as (G1 & G2 & G3 & G4 & G5 & G6). pose proof (APART2 e He) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0.
split; apply YFfn.A_drop_In; (split; [assumption|]).
- intros EQ. injection EQ as Q1 Q2. lia.
- intros EQ. apply (f_equal fst) in EQ. unfold shull in EQ. cbn [fst] in EQ. unfold shadow_addr in EQ.
  destruct IA as [IA0 _].
  assert (D0 : 0 <= fst e / 8) by (apply Z.div_pos; lia).
  assert (D1 : fst e / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  pose proof alloc_ceiling_lt as AC. change (2 ^ 47) with 140737488355328 in AC.
  assert (D4 : alloc_ceiling / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
  assert (D2 : 4096 * ((SHADOW_OFF + fst e / 8) / 4096) <= SHADOW_OFF + fst e / 8) by (apply Z.mul_div_le; lia).
  assert (D3 : SHADOW_OFF / 4096 <= (SHADOW_OFF + fst e / 8) / 4096) by (apply Z.div_le_mono; lia).
  change (SHADOW_OFF / 4096) with 524280 in D3.
  set (q := (SHADOW_OFF + fst e / 8) / 4096) in *.
  destruct G4 as [G40 [GL|[GH1 GH2]]]; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia.
Qed.


(* The recycled entry: live, with its requested size (chunk_ok_cf's secondary clause). *)
Lemma sm_live_size : sm_live sm = true /\ 0 <= sm_size sm.
Proof.
pose proof (proj1 (Forall_forall _ _) (wfr_chunks _ _ _ _ _ rWF) k Hk) as [Hn CK]. rewrite Hb in CK.
destruct CK as (P1 & P2 & sm' & Q1 & Q2 & Q3 & Q4). rewrite Hsm in Q1. injection Q1 as <-.
split; [exact Q2|]. rewrite Q3. unfold needed_size. rewrite P1.
pose proof KFACTS as (_ & _ & Hq & _).
pose proof (rounded_size_bounds (ck_req k) ltac:(lia)) as [R1 _]. pose proof (rz_size_bounds (ck_req k)) as [RZ _].
unfold needed_primary. lia.
Qed.

(* The budget after the free: the map leaves abudget_cf with its sec_live_bytes, and the unit's hull term cf_hull
   drops by at most the per-recycle charge cf_rec_drop (sm_len sm) (YGcfAbudget.abudget_recycle_cf, by CfParams's
   cf_hull_recycle); the refund (YFfn.A_bytes_refund) takes only the map out of A_bytes, so the post's budget holds
   loosened by that charge. *)
Lemma abudget_X2 : abudget_cf X - LEN - cf_rec_drop (sm_len sm) <= abudget_cf rsX2.
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & _). pose proof KFACTS as (_ & EL & _). pose proof sm_live_size as [SL SZ].
apply (YGcfAbudget.abudget_recycle_cf X rsX2 l1 k l2 r o sm E ltac:(rewrite X2_chunks; exact E1) Hb Hsm SL SZ
  ltac:(rewrite EL; reflexivity) X2_secs X2_regions X2_sec_res).
Qed.

Lemma ARcfR_X2 : forall md',
m_vmmaps md' = m_vmmaps (YK0v.munmap_model (w64 MAP) (w64 LEN) md) ->
m_vm_lazy md' = m_vm_lazy (YK0v.munmap_model (w64 MAP) (w64 LEN) md) ->
eager_used md' = eager_used (YK0v.munmap_model (w64 MAP) (w64 LEN) md) ->
(forall a, in_band_rw a -> ~ rsD a -> mem' (w64 a) = mem (w64 a)) ->
(forall a, rsDH a -> mem' (w64 a) = Some (Z_to_bv 8 0)) ->
YGcfRehideAR.ARcfR_sl im_segs B ly rsX2 Hp W2 mem' md' (cf_rec_drop (sm_len sm)).
Proof.
intros md' Ev El Ee EQ ZE. pose proof MR as (M & LED & BUD & MW & HSH).
pose proof KFACTS as (_ & _ & _ & _ & GI & _).
destruct (in_split _ _ (alc_sec _ _ _ _ LED _ GI)) as (l1 & l2 & EVM).
assert (MW0 : amwf (YK0v.munmap_model (w64 MAP) (w64 LEN) md)) by (exact (YFfn.munmap_amwf md (w64 MAP, w64 LEN) l1 l2 MW EVM)).
assert (SZ : Forall (fun e => 4096 <= snd e < 2 ^ 64) (sec_extents ly X)).
{ apply Forall_forall. intros e He. destruct (sec_in_app e He) as [IA LB].
  pose proof (proj1 (Forall_forall _ _) (proj1 (amr_placed _ _ _ _ _ rM)) e He) as (_ & _ & I3).
  destruct IA as [I0 _]. ceil. unfold ASAN_CEIL in *. lia. }
assert (LED2 : ALedger_cf im_segs ly rsX2 (YK0v.munmap_model (w64 MAP) (w64 LEN) md)).
{ destruct sec_extents_split as (E1 & E2 & EX & EX2).
  exact (ALedger_cf_munmap ly X rsX2 md (MAP, LEN) E1 E2 rLO SZ (amr_placed _ _ _ _ _ rM) (amr_xs_placed _ _ _ _ _ rM) MW LED EX EX2
    (fun c _ => reg' c) eq_refl eq_refl xs_cf_X2 errb_cap_X2). }
split; [exact ARmcfR_X2|]. split; [|split; [|split]].
- eapply YG0qcf.ALedger_same_cf; [exact LED2 | exact Ev | exact El | exact Ee].
- destruct BUD as (BU1 & BU2 & BU3). split; [|split; [exact (asecA_X2 BU2) | exact BU3]].
  pose proof abudget_X2 as AB.
  assert (IN : In (MAP, MAP + LEN) (w_A W)) by exact (proj1 (BU2 _ GI)).
  pose proof (YFfn.A_bytes_refund (MAP, MAP + LEN) (w_A W) (w_Awf W) IN) as RF. cbn [fst snd] in RF.
  unfold W2. rewrite YFfn.wrefund_A. lia.
- exact (amwf_same _ md' Ev El MW0).
- exact (ahs' EQ ZE).
Qed.

(* The xs keep: the unmap removes the dead map only, and no xs extent is based there. *)
Lemma xs_keep : forall md', amwf md -> xs_mapped_cf ly X md ->
m_vmmaps md' = m_vmmaps (YK0v.munmap_model (w64 MAP) (w64 LEN) md) -> xs_mapped_cf ly rsX2 md'.
Proof.
intros md' MW Hm Ev. apply (YGcfXsMapped.xs_mapped_cf_frame ly X md ly rsX2 md' [(MAP, LEN)] Hm xs_cf_X2).
- intros q Hq HD. rewrite Ev. exact (YGcfXsMapped.mkeep_munmap MAP LEN (w64 LEN) md q Hq HD).
- apply Forall_forall. intros e He. constructor; [|constructor]. cbn [fst].
  pose proof (proj1 (Forall_forall _ _) (amr_xs_placed _ _ _ _ _ rM) e He) as (P1 & P2 & P3 & P4).
  pose proof KFACTS as (_ & _ & _ & _ & GI & _).
  pose proof (proj1 (Forall_forall _ _) P4 (MAP, LEN) ltac:(apply in_app_iff; left; exact GI)) as D.
  pose proof (proj1 (Forall_forall _ _) (YGcfXsMapped.cfxm_xs_pos ly X md MW (amr_xs_placed _ _ _ _ _ rM) Hm) e He) as (E1 & E2 & E3).
  pose proof geom as (_ & G2 & _ & G4 & G5 & _). pose proof alloc_ceiling_lt as CL. destruct G4 as [G40 _].
  intros EE. apply YGcfXsMapped.cfxm_w64_inj in EE; [| lia | ceil; unfold ASAN_CEIL in *; lia]. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

End M.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The field.                                                                                                       *)
Section F.
Variable B : asyms.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
(* the errbuf object apart from the allocator object (the errbuf cells of ARmcfR at the post state) *)
Hypothesis EAP : YGcfImgRows.ERRB_QAPART.

(* The secondary arm's step at the cut relation, its budget LOOSENED: at the post state (the chunk deleted, the
   secmap dead, the pointer array swap-removed; the world refunded by the dead map's allowance; the model unmapped)
   the issuer row, YGcfRehideAR.ARcfR_sl at slack cf_rec_drop (sm_len sm) and the xs keep hold, the window is in
   the owned set or the stack scratch, the owned set shrinks, and the window is apart from every primary user byte.
   The world still holds the dead map's hull (the re-hide, YGcfRehideAR.ARcfR_rehide, pays it), so the unloosened
   ARcfR is false here at a real recycle: this is the only step form.
   Premises: the call's frame (MEQ off rsD, presence off the dead map, the written words, the constant cells, the
   band bytes off rsD keep their memory, the dead map's shadow reads 0), the model after the unmap, the two named
   image premises IMG_SAPART / IMG_JUNK and the row ERRB_QAPART.  FLAG-FREE (H4's request for the big arm's Recycle): no premise on
   st_cache_inited; the secondary arm never reads the per-class caches' flag (the cache cells are kept whatever it is). *)
Theorem rc_sec_step_sl_cf : forall inst ly X k r o sm i sp W mem md mem' md',
ARXr_cf B IOK Hp inst ly X W mem md ->
In k (st_chunks X) -> ck_state k = CQuarantined -> ck_beg k = PSec r o -> ~ In (ck_beg k) (map ck_beg (q_items X)) ->
nth_error (st_secs X) r = Some sm -> nth_error (st_sec_arr X) i = Some r ->
ly_stk_lo ly + YFeu.KSTACK <= sp <= ly_stk_hi ly ->
im_syms B -> IMG_SAPART -> IMG_JUNK ->
(forall a, 0 <= a < 2 ^ 64 -> ~ rsD B ly X k r i sp a -> aview im_segs (w_H W) mem' a = aview im_segs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> aview im_segs (w_H W) mem a <> None -> ~ rsDM ly k r a -> aview im_segs (w_H W) mem' a <> None) ->
(forall j, 0 <= j < 4 -> aview im_segs (w_H W) mem' (as_inst B + 680 + j) = Some 0) ->
(forall kk, (kk < 8)%nat -> aview im_segs (w_H W) mem' (as_inst B + 120 + Z.of_nat kk) = Some (le_byte (nA X - 1) 8 kk)) ->
(forall kk, (kk < 8)%nat -> aview im_segs (w_H W) mem' (qi ly i + Z.of_nat kk) = Some (le_byte (lst ly X r) 8 kk)) ->
(own X i = false -> forall kk, (kk < 8)%nat -> aview im_segs (w_H W) mem' (lst ly X r + 24 + Z.of_nat kk) = Some (le_byte (idx i) 8 kk)) ->
Forall (cell_holds B ly (aview im_segs (w_H W) mem')) (as_const B ly) ->
(forall a, in_band_rw a -> ~ rsD B ly X k r i sp a -> mem' (w64 a) = mem (w64 a)) ->
(forall a, rsDH ly k r a -> mem' (w64 a) = Some (Z_to_bv 8 0)) ->
m_vmmaps md' = m_vmmaps (YK0v.munmap_model (w64 (MAP ly r)) (w64 (LEN k)) md) ->
m_vm_lazy md' = m_vm_lazy (YK0v.munmap_model (w64 (MAP ly r)) (w64 (LEN k)) md) ->
eager_used md' = eager_used (YK0v.munmap_model (w64 (MAP ly r)) (w64 (LEN k)) md) ->
IOK inst /\ YGcfRehideAR.ARcfR_sl im_segs B ly (rsX2 X k r sm i) Hp (W2 ly k r W) mem' md' (cf_rec_drop (sm_len sm)) /\
xs_mapped_cf ly (rsX2 X k r sm i) md' /\
(forall a, 0 <= a -> rsD B ly X k r i sp a -> aowned B ly X a \/ rsDS sp a) /\
(forall a, aowned B ly (rsX2 X k r sm i) a -> aowned B ly X a) /\
(forall a, YFeuC.puser ly X a -> ~ rsD B ly X k r i sp a).
Proof.
intros inst ly X k r o sm i sp W mem md mem' md' (HI & HA & HX) Hk Hst Hb Hni Hsm Hi Hsp TS ISA IJ
  AG VIS MUT NS QI LST CONST EQ ZE Ev El Ee.
pose proof (proj1 (proj2 (proj2 (proj2 HA)))) as MW.
split; [exact HI|]. split; [|split].
- eapply ARcfR_X2; eassumption.
- eapply xs_keep; eassumption.
- split; [intros a Ha0 HD; eapply D_owned; eassumption|].
  split; [intros a Ha; eapply aowned_X2; eassumption|].
  intros a Ha. eapply puser_notD; eassumption.
Qed.
End F.
End U.
