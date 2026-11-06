(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0b YK05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0h YG00 YG0a YG01 YG07 YG10 YG0u YG0y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Fixpoint asec_lt (n : nat) (e : aexp) : Prop :=
match e with ASec r _ => (r < n)%nat | ASh e' => asec_lt n e' | _ => True end.
Section Le. Context {imgk : img}.
Variable B : asyms.
Variables (ly ly' : alayout) (n : nat).
Hypothesis LE : layout_le n ly ly'.
Lemma aeval_le : forall e, asec_lt n e -> aeval B ly' e = aeval B ly e.
Proof.
destruct LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & EI & E15).
induction e; cbn; intros H; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8, ?E9, ?E10, ?E11, ?E12, ?ED, ?EI; try img_refl.
- rewrite E15 by img_exact H. img_refl.
- rewrite (IHe H). img_refl.
Qed.
Definition cell_lt (c : acell) : Prop := asec_lt n (c_at c) /\ match c_val c with AV e => asec_lt n e | AVmask _ _ => True end.
Lemma cell_holds_le : forall rd c, cell_lt c -> cell_holds B ly rd c -> cell_holds B ly' rd c.
Proof.
intros rd c [Ha Hv] H. unfold cell_holds in *. rewrite (aeval_le _ Ha). destruct (c_val c) as [e|m v]; [|img_try (img_exact H)].
rewrite (aeval_le _ Hv). img_exact H.
Qed.
Lemma Forall_cell_holds_le : forall rd l, Forall cell_lt l -> Forall (cell_holds B ly rd) l -> Forall (cell_holds B ly' rd) l.
Proof.
intros rd l HL H. img_apply Forall_forall. intros c Hc.
img_exact (cell_holds_le rd c (proj1 (Forall_forall _ _) HL c Hc) (proj1 (Forall_forall _ _) H c Hc)).
Qed.
Lemma range_vis_le : forall rd r, asec_lt n (fst r) -> range_vis B ly rd r -> range_vis B ly' rd r.
Proof. intros rd r Ha H i Hi. unfold range_vis in *. rewrite (aeval_le _ Ha). img_exact (H i Hi). Qed.
Lemma Forall_range_vis_le : forall rd l, Forall (fun r => asec_lt n (fst r)) l -> Forall (range_vis B ly rd) l -> Forall (range_vis B ly' rd) l.
Proof.
intros rd l HL H. img_apply Forall_forall. intros r Hr.
img_exact (range_vis_le rd r (proj1 (Forall_forall _ _) HL r Hr) (proj1 (Forall_forall _ _) H r Hr)).
Qed.
Lemma sptr_exp_lt : forall p, match p with PSec r _ => (r < n)%nat | _ => True end -> asec_lt n (sptr_exp p).
Proof. intros p Hp. destruct p; cbn; try img_exact I. img_exact Hp. Qed.
Lemma asec_lt_aoff : forall e d, asec_lt n e -> asec_lt n (aoff e d).
Proof. intros e d H. destruct e; cbn in *; try img_exact I; img_exact H. Qed.
End Le.
Lemma set_ly_sec_ok : forall ly r a, layout_ok ly -> layout_ok (set_ly_sec ly r a).
Proof. intros ly r a LO. destruct LO. constructor; cbn; assumption. Qed.
Section j. Context {imgk : img}.
Variable B : asyms.
Variables (ly : alayout) (S : astate) (U : list (list Z)) (pp cc bb : Z).
Hypothesis WF : WfP U pp cc bb S.
Let n : nat := length (st_secs S).
Lemma chunk_lt : forall k, In k (st_chunks S) -> match ck_beg k with PSec r _ => (r < n)%nat | _ => True end.
Proof.
intros k Hk. pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [_ C].
destruct (ck_beg k) as [|o|r o|c p]; try img_exact I. destruct C as (_ & _ & sm & Hsm & _). unfold n. eapply nth_error_lt. img_exact Hsm.
Qed.
Lemma padd_lt : forall p d, match p with PSec r _ => (r < n)%nat | _ => True end -> match padd p d with PSec r _ => (r < n)%nat | _ => True end.
Proof. intros p d H. destruct p; cbn; try img_exact I. img_exact H. Qed.
Ltac cell_tac := unfold cell_lt; cbn [c_at c_val]; split; cbn; try img_exact I.
Lemma acells_lt : Forall (cell_lt (length (st_secs S))) (acells B ly S).
Proof.
unfold acells.
img_apply Forall_app. split.
{   img_apply (proj2 (Forall_flat_map _ _ _)). img_apply Forall_forall. intros c _. unfold region_cells.
destruct (rg_mapped_user (reg S c) =? 0); repeat (img_apply Forall_cons; [img_try (cell_tac)|]); img_apply Forall_nil. }
img_apply Forall_app. split.
{   img_apply (proj2 (Forall_flat_map _ _ _)). img_apply Forall_forall. intros c _. unfold cache_cells.
destruct (st_cache_inited S).
+ repeat (img_apply Forall_cons; [img_try (cell_tac)|]).
img_apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (io & <- & _). cell_tac.
+ repeat (img_apply Forall_cons; [img_try (cell_tac)|]); img_apply Forall_nil. }
img_apply Forall_app. split.
{   img_apply (proj2 (Forall_flat_map _ _ _)). img_apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT. unfold chunk_cells.
img_apply Forall_app. split.
+ repeat (img_apply Forall_cons; [img_try (split; cbn [c_at c_val]; try img_exact I; repeat img_apply asec_lt_aoff; img_apply sptr_exp_lt; img_exact LT)|]). img_apply Forall_nil.
+ destruct (ck_rz k =? kChunkHeaderSize); [img_try (img_apply Forall_nil)|].
repeat (img_apply Forall_cons; [img_try (split; cbn [c_at c_val]; try img_exact I; repeat img_apply asec_lt_aoff; img_apply sptr_exp_lt; img_exact LT)|]). img_apply Forall_nil. }
img_apply Forall_app. split.
{   unfold sec_cells. img_apply Forall_cons; [img_try (cell_tac)|]. img_apply Forall_cons; [img_try (cell_tac)|]. img_apply Forall_cons; [img_try (cell_tac)|]. img_apply Forall_app. split.
+ img_apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i r] & <- & Hin). apply in_combine_r in Hin.
pose proof (proj1 (ws_arr_chunks _ (wf_secondary _ _ _ _ _ WF) r) Hin) as (k & Hk & Eb). pose proof (chunk_lt k Hk) as LT. rewrite Eb in LT.
cell_tac. img_exact LT.
+ img_apply (proj2 (Forall_flat_map _ _ _)). img_apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT.
destruct (ck_beg k) as [|o|r o|c p]; try img_apply Forall_nil. repeat (img_apply Forall_cons; [img_try (cell_tac; img_exact LT)|]). img_apply Forall_nil. }
img_apply Forall_app. split.
{   unfold quar_cells. img_apply Forall_cons; [img_try (cell_tac)|]. img_apply Forall_cons; [img_try (cell_tac)|].
assert (ITEMS : forall k, In k (q_items S) -> match ck_hdr k with PSec r _ => (r < n)%nat | _ => True end).
{ intros k Hk. pose proof (proj1 (Forall_forall _ _) (wq_items _ (wf_quarantine _ _ _ _ _ WF)) k Hk) as [Hin _]. unfold ck_hdr. img_apply padd_lt. img_exact (chunk_lt k Hin). }
assert (BATCH : forall bl, incl (flat_map b_items bl) (q_items S) -> Forall (cell_lt (length (st_secs S))) (batch_cells bl)).
{ induction bl as [|b t IH]; intros INC; [img_try (img_apply Forall_nil)|]. cbn [batch_cells].
img_apply Forall_cons; [img_try (unfold cell_lt; cbn [c_at c_val]; split; [cbn; img_exact I|]; destruct t; cbn; img_exact I)|].
img_apply Forall_cons; [img_try (cell_tac)|]. img_apply Forall_cons; [img_try (cell_tac)|]. img_apply Forall_app. split.
- img_apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i k] & <- & Hin). apply in_combine_r in Hin.
unfold cell_lt; cbn [c_at c_val fst snd]. split; [img_try (cbn; img_exact I)|]. img_apply sptr_exp_lt. img_apply ITEMS. img_apply INC. cbn. img_apply in_app_iff. left. img_exact Hin.
- img_apply IH. intros k Hk. img_apply INC. cbn. img_apply in_app_iff. right. img_exact Hk. }
assert (QC : forall root q, asec_lt n root -> (forall e, root <> ASh e) -> incl (flat_map b_items (qc_list q)) (q_items S) -> Forall (cell_lt (length (st_secs S))) (qc_cells root q)).
{ intros root q Hr Hsh INC. unfold qc_cells.
img_apply Forall_cons; [img_try (split; cbn [c_at c_val]; [img_exact Hr | cbn; img_exact I])|].
img_apply Forall_cons; [img_try (split; cbn [c_at c_val]; [img_apply asec_lt_aoff; img_exact Hr | destruct (qc_list q); cbn; img_exact I])|].
img_apply Forall_cons; [img_try (split; cbn [c_at c_val]; [img_apply asec_lt_aoff; img_exact Hr | destruct (rev (qc_list q)); cbn; img_exact I])|].
img_apply Forall_cons; [img_try (split; cbn [c_at c_val]; [img_apply asec_lt_aoff; img_exact Hr | cbn; img_exact I])|].
img_apply BATCH. img_exact INC. }
img_apply Forall_app. split; img_apply QC; cbn; try img_exact I; try (intros e E; discriminate E); unfold q_items, all_batches; intros k Hk; rewrite flat_map_app; img_apply in_app_iff; [img_try (left) | img_try (right)]; img_exact Hk. }
img_apply Forall_app. split.
{   unfold fs_cells. img_apply Forall_cons; [img_try (cell_tac)|]. img_apply Forall_cons; [img_try (cell_tac)|].
img_apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i h] & <- & _). cell_tac. }
img_apply Forall_app. split.
{   unfold depot_cells. repeat (img_apply Forall_cons; [img_try (cell_tac)|]). img_apply Forall_nil. }
img_apply Forall_app. split.
{   unfold ialloc_cells. repeat (img_apply Forall_cons; [img_try (cell_tac)|]); [img_try (destruct (st_internal_inited S); cbn; img_exact I) | img_try (img_apply Forall_nil)]. }
{   unfold thread_cells. img_apply Forall_cons; [img_try (cell_tac) | img_try (img_apply Forall_nil)]. }
Qed.
Lemma ajunk_lt : Forall (fun r => asec_lt n (fst r)) (as_junk B ly) -> Forall (fun r => asec_lt n (fst r)) (ajunk B ly S).
Proof.
intros JUNK. unfold ajunk. img_apply Forall_cons; [img_try (cbn; img_exact I)|]. img_apply Forall_cons; [img_try (cbn; img_exact I)|].
img_apply Forall_app. split.
{ img_apply (proj2 (Forall_flat_map _ _ _)). img_apply Forall_forall. intros c _. unfold region_junk. repeat (img_apply Forall_cons; [img_try (cbn; img_exact I)|]). img_apply Forall_nil. }
img_apply Forall_app. split.
{ img_apply (proj2 (Forall_flat_map _ _ _)). img_apply Forall_forall. intros c _. unfold cache_junk. img_apply Forall_cons; [img_try (cbn; img_exact I) | img_try (img_apply Forall_nil)]. }
img_apply Forall_app. split.
{ img_apply (proj2 (Forall_flat_map _ _ _)). img_apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT. unfold chunk_junk.
repeat (img_apply Forall_app; split); try (destruct (ck_rz k =? kChunkHeaderSize)); try (destruct (ck_state k)); try img_apply Forall_nil;
repeat (img_apply Forall_cons; [img_try (cbn [fst]; img_apply asec_lt_aoff; img_apply sptr_exp_lt; img_exact LT)|]); img_apply Forall_nil. }
img_apply Forall_app. split.
{ unfold sec_junk. img_apply Forall_cons; [img_try (cbn; img_exact I)|]. img_apply Forall_cons; [img_try (cbn; img_exact I)|]. img_apply Forall_cons; [img_try (cbn; img_exact I)|].
img_apply (proj2 (Forall_flat_map _ _ _)). img_apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT.
destruct (ck_beg k) as [|o|r o|c p]; try img_apply Forall_nil. img_apply Forall_cons; [img_try (cbn; img_exact LT) | img_try (img_apply Forall_nil)]. }
img_apply Forall_app. split.
{ unfold quar_junk. img_apply (proj2 (Forall_flat_map _ _ _)). img_apply Forall_forall. intros b _. unfold batch_junk. img_apply Forall_cons; [img_try (cbn; img_exact I) | img_try (img_apply Forall_nil)]. }
img_apply Forall_app. split.
{ unfold thread_junk. repeat (img_apply Forall_cons; [img_try (cbn; img_exact I)|]). img_apply Forall_nil. }
img_apply Forall_app. split.
{ repeat (img_apply Forall_cons; [img_try (cbn; img_exact I)|]). img_apply Forall_nil. }
{ img_exact JUNK. }
Qed.
Lemma aareas_lt : Forall (fun r => asec_lt n (fst r)) (aareas S).
Proof.
unfold aareas. img_apply Forall_app. split.
{ img_apply (proj2 (Forall_flat_map _ _ _)). img_apply Forall_forall. intros c _. repeat (img_apply Forall_cons; [img_try (cbn; img_exact I)|]). img_apply Forall_nil. }
img_apply Forall_app. split. { img_apply Forall_cons; [img_try (cbn; img_exact I) | img_try (img_apply Forall_nil)]. }
img_apply Forall_app. split.
{ img_apply (proj2 (Forall_flat_map _ _ _)). img_apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT.
destruct (ck_beg k) as [|o|r o|c p]; try img_apply Forall_nil. img_apply Forall_cons; [img_try (cbn; img_exact LT) | img_try (img_apply Forall_nil)]. }
repeat (img_apply Forall_cons; [img_try (cbn; img_exact I)|]). img_apply Forall_nil.
Qed.
Lemma aclient_lt : Forall (fun r => asec_lt n (fst r)) (aclient S).
Proof.
unfold aclient. img_apply Forall_app. split.
{ img_apply (proj2 (Forall_flat_map _ _ _)). img_apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT. unfold chunk_user.
destruct (ck_state k); [|img_try (img_apply Forall_nil)]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. cbn [fst]. img_apply sptr_exp_lt. unfold ck_user. img_apply padd_lt. img_exact LT. }
img_apply Forall_app. split; img_apply Forall_forall; intros x Hx; apply in_map_iff in Hx as (cp & <- & _); cbn; img_exact I.
Qed.
End j.
Section s. Context {imgk : img}.
Variable B : asyms.
Variables (ly ly' : alayout) (S : astate) (rd : reader).
Hypothesis M : ARm B ly S rd.
Hypothesis LE : layout_le (length (st_secs S)) ly ly'.
Hypothesis LO' : layout_ok ly'.
Hypothesis CONST : as_const B ly' = as_const B ly.
Hypothesis CONSTlt : Forall (cell_lt (length (st_secs S))) (as_const B ly).
Hypothesis JUNK : as_junk B ly' = as_junk B ly.
Hypothesis JUNKlt : Forall (fun r => asec_lt (length (st_secs S)) (fst r)) (as_junk B ly).
Let WF := am_wf _ _ _ _ M.
Let E := LE.
Lemma acells_ly : acells B ly' S = acells B ly S.
Proof. destruct LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & E15). unfold acells, depot_cells. rewrite E13. img_refl. Qed.
Lemma ajunk_ly : ajunk B ly' S = ajunk B ly S.
Proof. unfold ajunk. rewrite JUNK. img_refl. Qed.
Lemma ashadow_ly : forall g, ashadow B ly' S g = ashadow B ly S g.
Proof.
intros g. destruct LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & E15). unfold ashadow.
assert (CB : forall k, In k (st_chunks S) -> ck_base B ly' k = ck_base B ly k).
{ intros k Hk. unfold ck_base. img_apply (sptr_addr_le B ly ly' (length (st_secs S))); [img_try (img_exact LE)|]. img_exact (chunk_lt S _ _ _ _ WF k Hk). }
assert (FC : find_chunk_at B ly' (st_chunks S) g = find_chunk_at B ly (st_chunks S) g).
{ assert (H : forall l, incl l (st_chunks S) -> find_chunk_at B ly' l g = find_chunk_at B ly l g).
{ induction l as [|k t IH]; intros INC; [img_refl|]. cbn [find_chunk_at]. rewrite (CB k (INC k (or_introl eq_refl))).
rewrite (IH (fun x Hx => INC x (or_intror Hx))). img_refl. }
img_apply H. intros k Hk. img_exact Hk. }
assert (FIN : forall l k, find_chunk_at B ly l g = Some k -> In k l).
{ induction l as [|k0 t IH]; intros k Hf; [img_try (discriminate Hf)|]. cbn [find_chunk_at] in Hf.
destruct ((ck_base B ly k0 <=? g) && (g <? ck_base B ly k0 + ck_extent k0)); [img_try (injection Hf as <-; left; img_refl) | img_try (right; img_exact (IH k Hf))]. }
rewrite FC. destruct (find_chunk_at B ly (st_chunks S) g) as [k|] eqn:Hf; [img_try (rewrite (CB k (FIN _ k Hf)); img_refl)|].
assert (FP : fa_poison_ranges ly' S = fa_poison_ranges ly S).
{ unfold fa_poison_ranges. f_equal.
- unfold region_base, fa_base. rewrite E2. img_refl.
- pose proof (sec_extents_le ly ly' S _ _ _ _ LE WF) as SE. unfold sec_extents in SE. img_exact SE. }
rewrite FP. img_refl.
Qed.
Theorem ARm_layout_le : ARm B ly' S rd.
Proof.
pose proof LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & EI & E15).
pose proof M as MM. destruct MM as [M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 M12 M13 M14 M15 M16 M17 M18 M19].
constructor.
- img_exact M1.
- img_exact M2.
- img_exact M3.
- img_exact LO'.
-   unfold sec_placed in *. rewrite (sec_extents_le ly ly' S _ _ _ _ LE M1).
replace (static_extents ly') with (static_extents ly); [img_try (img_exact M5)|]. unfold static_extents, owned_extents. rewrite E1, E3, E4, E5, E6, E7, E8, E10, E11, ED, EI. img_refl.
- rewrite CONST. img_exact (Forall_cell_holds_le B ly ly' _ LE rd _ CONSTlt M6).
- rewrite CONST. img_apply Forall_forall. intros c Hc k Hk. pose proof (proj1 (Forall_forall _ _) M7 c Hc k Hk) as O.
pose proof (proj1 (Forall_forall _ _) CONSTlt c Hc) as [Ha _]. rewrite (aeval_le B ly ly' _ LE _ Ha).
unfold owned_core in *. replace (core_extents ly') with (core_extents ly); [img_try (img_exact O)|].
unfold core_extents. rewrite ?E1, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8, ?E9, ?E10, ?E11, ?E12, ?ED. img_refl.
- rewrite acells_ly. img_exact (Forall_cell_holds_le B ly ly' _ LE rd _ (acells_lt B ly S _ _ _ _ M1) M8).
-   intros c i v Hc Hi Hv. unfold fa_base. rewrite E2. img_exact (M9 c i v Hc Hi Hv).
-   intros cid pos Hc Hp. unfold flag_addr. rewrite E6. img_exact (M10 cid pos Hc Hp).
-   destruct M11 as (heads & links & D1 & D2 & D3). exists heads, links.
replace (depot_traces ly' S) with (depot_traces ly S) by (img_try (unfold depot_traces; rewrite E13; img_refl)). rewrite E7. img_exact (conj D1 (conj D2 D3)).
-   intros g v Hg Hs. rewrite ashadow_ly in Hs. img_exact (M12 g v Hg Hs).
-   unfold zshadow_ok in *. replace (zero_shadow_ranges B ly') with (zero_shadow_ranges B ly); [img_try (img_exact M13)|]. unfold zero_shadow_ranges. rewrite E10, E11. img_refl.
- rewrite ajunk_ly. img_exact (Forall_range_vis_le B ly ly' _ LE rd _ (ajunk_lt B ly S _ _ _ _ M1 JUNKlt) M14).
- img_exact (Forall_range_vis_le B ly ly' _ LE rd _ (aareas_lt S _ _ _ _ M1) M15).
- img_exact (Forall_range_vis_le B ly ly' _ LE rd _ (aclient_lt S _ _ _ _ M1) M16).
-   img_apply Forall_forall. intros r Hr i Hi. pose proof (proj1 (Forall_forall _ _) M17 r Hr i Hi) as X.
unfold ialloc_zero in Hr. cbn in Hr. destruct Hr as [<-|[<-|[]]]; cbn in X |- *; img_exact X.
- rewrite E12. img_exact M18.
-   rewrite EI. img_exact M19.
Qed.
End s.
Section u. Context {imgk : img}.
Variables (S : astate) (n : Z) (tr : list Z) (z : Z) (ms nd : Z) (grow : bool).
Definition rS : nat := length (st_secs S).
Definition KS : chunk := mkChunk (PSec rS kPage) n CAllocated.
Definition resF : Z := if grow then st_sec_reserved S + kPtrArrayEntriesPerCommit else st_sec_reserved S.
Definition depF : list (list Z) := if z =? 0 then st_depot S else st_depot S ++ [tr].
Definition sfinal : astate :=
mkA (st_regions S) (st_cache_inited S) (st_cache S) (st_chunks S ++ [KS]) (st_secs S ++ [mkSec ms nd true]) (st_sec_arr S ++ [rS]) resF
(st_qthread S) (st_qglobal S) (st_fs S) depF (st_internal_inited S) (st_nev S + 1).
Definition s_secs : astate := set_secs (st_secs S ++ [mkSec ms nd true]) (set_nev (st_nev S + 1) S).
Definition s_resv : astate := if grow then set_sec_reserved (st_sec_reserved s_secs + kPtrArrayEntriesPerCommit) s_secs else s_secs.
Definition s_arr : astate := set_sec_arr (st_sec_arr s_resv ++ [rS]) s_resv.
Definition s_dep : astate := depot_after z tr s_arr.
Lemma upd_chunk_fresh : forall lst k, (forall k', In k' lst -> sptr_eqb (ck_beg k') (ck_beg k) = false) -> upd_chunk lst k = lst ++ [k].
Proof.
induction lst as [|k0 t IH]; intros k H; [img_refl|]. cbn [upd_chunk app]. rewrite (H k0 (or_introl eq_refl)). f_equal. img_apply IH. intros k' Hk'. img_apply H. right. img_exact Hk'.
Qed.

Lemma KS_fresh : forall U pp cc bb, WfP U pp cc bb S -> forall k', In k' (st_chunks S) -> sptr_eqb (ck_beg k') (PSec rS kPage) = false.
Proof.
intros U pp cc bb WF k' Hk'. pose proof (chunk_lt S U pp cc bb WF k' Hk') as LT.
destruct (ck_beg k') as [|o|r o|c p]; cbn; try img_refl. unfold rS. destruct (Nat.eqb_spec r (length (st_secs S))); [img_try (exfalso; img_lia)|]. img_refl.
Qed.
End u.
Lemma tfxsegs_readable {imgk : img} : forall sg, In sg tfxsegs -> seg_readable sg = true.
Proof. assert (H : forallb seg_readable tfxsegs = true) by (img_try ((img_case; vm_compute); img_refl)). intros sg Hin. img_exact (proj1 (forallb_forall _ _) H sg Hin). Qed.
Lemma writable_visible {imgk : img} : forall (Hh : word -> bool) (m : word -> option byte) a, 0 <= a < 2 ^ 64 ->
writable_at tfxsegs (mrestrict Hh m) a -> aview tfxsegs Hh m a <> None.
Proof.
intros Hh m a Ra HW. unfold writable_at, wview in HW. unfold aview, mbyte.
destruct (mrestrict Hh m (Z_to_bv 64 a)) as [b|] eqn:E; [img_try (cbn; discriminate)|].
destruct (find_segment tfxsegs (bv_unsigned (Z_to_bv 64 a)) 1) as [sg|] eqn:F; [|img_try (exfalso; img_exact (HW eq_refl))].
destruct (seg_writable sg) eqn:Wr; [|img_try (exfalso; img_exact (HW eq_refl))].
pose proof (find_segment_some_spec _ _ _ _ F) as (Hin & _ & _).
unfold seg_rom, memory_read. img_change (Z.of_N 1) with 1. rewrite F, (tfxsegs_readable sg Hin). img_change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base sg)))) as [b|]; [img_try (cbn; discriminate) | img_try (exfalso; img_exact (HW eq_refl))].
Qed.
End f.
