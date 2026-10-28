(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP09 YK04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0f YG00 YG0a YG01 YG07 YG0v YG0n YG0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Fixpoint asec_lt (n : nat) (e : aexp) : Prop :=
match e with ASec r _ => (r < n)%nat | ASh e' => asec_lt n e' | _ => True end.
Section Le.
Variable B : asyms.
Variables (ly ly' : alayout) (n : nat).
Hypothesis LE : layout_le n ly ly'.
Lemma aeval_le : forall e, asec_lt n e -> aeval B ly' e = aeval B ly e.
Proof.
destruct LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & EI & E15).
induction e; cbn; intros H; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8, ?E9, ?E10, ?E11, ?E12, ?ED, ?EI; try reflexivity.
- rewrite E15 by exact H. reflexivity.
- rewrite (IHe H). reflexivity.
Qed.
Definition cell_lt (c : acell) : Prop := asec_lt n (c_at c) /\ match c_val c with AV e => asec_lt n e | AVmask _ _ => True end.
Lemma cell_holds_le : forall rd c, cell_lt c -> cell_holds B ly rd c -> cell_holds B ly' rd c.
Proof.
intros rd c [Ha Hv] H. unfold cell_holds in *. rewrite (aeval_le _ Ha). destruct (c_val c) as [e|m v]; [|exact H].
rewrite (aeval_le _ Hv). exact H.
Qed.
Lemma Forall_cell_holds_le : forall rd l, Forall cell_lt l -> Forall (cell_holds B ly rd) l -> Forall (cell_holds B ly' rd) l.
Proof.
intros rd l HL H. apply Forall_forall. intros c Hc.
exact (cell_holds_le rd c (proj1 (Forall_forall _ _) HL c Hc) (proj1 (Forall_forall _ _) H c Hc)).
Qed.
Lemma range_vis_le : forall rd r, asec_lt n (fst r) -> range_vis B ly rd r -> range_vis B ly' rd r.
Proof. intros rd r Ha H i Hi. unfold range_vis in *. rewrite (aeval_le _ Ha). exact (H i Hi). Qed.
Lemma Forall_range_vis_le : forall rd l, Forall (fun r => asec_lt n (fst r)) l -> Forall (range_vis B ly rd) l -> Forall (range_vis B ly' rd) l.
Proof.
intros rd l HL H. apply Forall_forall. intros r Hr.
exact (range_vis_le rd r (proj1 (Forall_forall _ _) HL r Hr) (proj1 (Forall_forall _ _) H r Hr)).
Qed.
Lemma sptr_exp_lt : forall p, match p with PSec r _ => (r < n)%nat | _ => True end -> asec_lt n (sptr_exp p).
Proof. intros p Hp. destruct p; cbn; try exact I. exact Hp. Qed.
Lemma asec_lt_aoff : forall e d, asec_lt n e -> asec_lt n (aoff e d).
Proof. intros e d H. destruct e; cbn in *; try exact I; exact H. Qed.
End Le.
Lemma set_ly_sec_ok : forall ly r a, layout_ok ly -> layout_ok (set_ly_sec ly r a).
Proof. intros ly r a LO. destruct LO. constructor; cbn; assumption. Qed.
Section j.
Variable B : asyms.
Variables (ly : alayout) (S : astate) (U : list (list Z)) (pp cc bb : Z).
Hypothesis WF : WfP U pp cc bb S.
Let n : nat := length (st_secs S).
Lemma chunk_lt : forall k, In k (st_chunks S) -> match ck_beg k with PSec r _ => (r < n)%nat | _ => True end.
Proof.
intros k Hk. pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [_ C].
destruct (ck_beg k) as [|o|r o|c p]; try exact I. destruct C as (_ & _ & sm & Hsm & _). unfold n. eapply nth_error_lt. exact Hsm.
Qed.
Lemma padd_lt : forall p d, match p with PSec r _ => (r < n)%nat | _ => True end -> match padd p d with PSec r _ => (r < n)%nat | _ => True end.
Proof. intros p d H. destruct p; cbn; try exact I. exact H. Qed.
Ltac cell_tac := unfold cell_lt; cbn [c_at c_val]; split; cbn; try exact I.
Lemma acells_lt : Forall (cell_lt (length (st_secs S))) (acells B ly S).
Proof.
unfold acells.
apply Forall_app. split.
{   apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros c _. unfold region_cells.
destruct (rg_mapped_user (reg S c) =? 0); repeat (apply Forall_cons; [cell_tac|]); apply Forall_nil. }
apply Forall_app. split.
{   apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros c _. unfold cache_cells.
destruct (st_cache_inited S).
+ repeat (apply Forall_cons; [cell_tac|]).
apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (io & <- & _). cell_tac.
+ repeat (apply Forall_cons; [cell_tac|]); apply Forall_nil. }
apply Forall_app. split.
{   apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT. unfold chunk_cells.
apply Forall_app. split.
+ repeat (apply Forall_cons; [split; cbn [c_at c_val]; try exact I; repeat apply asec_lt_aoff; apply sptr_exp_lt; exact LT|]). apply Forall_nil.
+ destruct (ck_rz k =? kChunkHeaderSize); [apply Forall_nil|].
repeat (apply Forall_cons; [split; cbn [c_at c_val]; try exact I; repeat apply asec_lt_aoff; apply sptr_exp_lt; exact LT|]). apply Forall_nil. }
apply Forall_app. split.
{   unfold sec_cells. apply Forall_cons; [cell_tac|]. apply Forall_cons; [cell_tac|]. apply Forall_cons; [cell_tac|]. apply Forall_app. split.
+ apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i r] & <- & Hin). apply in_combine_r in Hin.
pose proof (proj1 (ws_arr_chunks _ (wf_secondary _ _ _ _ _ WF) r) Hin) as (k & Hk & Eb). pose proof (chunk_lt k Hk) as LT. rewrite Eb in LT.
cell_tac. exact LT.
+ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT.
destruct (ck_beg k) as [|o|r o|c p]; try apply Forall_nil. repeat (apply Forall_cons; [cell_tac; exact LT|]). apply Forall_nil. }
apply Forall_app. split.
{   unfold quar_cells. apply Forall_cons; [cell_tac|]. apply Forall_cons; [cell_tac|].
assert (ITEMS : forall k, In k (q_items S) -> match ck_hdr k with PSec r _ => (r < n)%nat | _ => True end).
{ intros k Hk. pose proof (proj1 (Forall_forall _ _) (wq_items _ (wf_quarantine _ _ _ _ _ WF)) k Hk) as [Hin _]. unfold ck_hdr. apply padd_lt. exact (chunk_lt k Hin). }
assert (BATCH : forall bl, incl (flat_map b_items bl) (q_items S) -> Forall (cell_lt (length (st_secs S))) (batch_cells bl)).
{ induction bl as [|b t IH]; intros INC; [apply Forall_nil|]. cbn [batch_cells].
apply Forall_cons; [unfold cell_lt; cbn [c_at c_val]; split; [cbn; exact I|]; destruct t; cbn; exact I|].
apply Forall_cons; [cell_tac|]. apply Forall_cons; [cell_tac|]. apply Forall_app. split.
- apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i k] & <- & Hin). apply in_combine_r in Hin.
unfold cell_lt; cbn [c_at c_val fst snd]. split; [cbn; exact I|]. apply sptr_exp_lt. apply ITEMS. apply INC. cbn. apply in_app_iff. left. exact Hin.
- apply IH. intros k Hk. apply INC. cbn. apply in_app_iff. right. exact Hk. }
assert (QC : forall root q, asec_lt n root -> (forall e, root <> ASh e) -> incl (flat_map b_items (qc_list q)) (q_items S) -> Forall (cell_lt (length (st_secs S))) (qc_cells root q)).
{ intros root q Hr Hsh INC. unfold qc_cells.
apply Forall_cons; [split; cbn [c_at c_val]; [exact Hr | cbn; exact I]|].
apply Forall_cons; [split; cbn [c_at c_val]; [apply asec_lt_aoff; exact Hr | destruct (qc_list q); cbn; exact I]|].
apply Forall_cons; [split; cbn [c_at c_val]; [apply asec_lt_aoff; exact Hr | destruct (rev (qc_list q)); cbn; exact I]|].
apply Forall_cons; [split; cbn [c_at c_val]; [apply asec_lt_aoff; exact Hr | cbn; exact I]|].
apply BATCH. exact INC. }
apply Forall_app. split; apply QC; cbn; try exact I; try (intros e E; discriminate E); unfold q_items, all_batches; intros k Hk; rewrite flat_map_app; apply in_app_iff; [left | right]; exact Hk. }
apply Forall_app. split.
{   unfold fs_cells. apply Forall_cons; [cell_tac|]. apply Forall_cons; [cell_tac|].
apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i h] & <- & _). cell_tac. }
apply Forall_app. split.
{   unfold depot_cells. repeat (apply Forall_cons; [cell_tac|]). apply Forall_nil. }
apply Forall_app. split.
{   unfold ialloc_cells. repeat (apply Forall_cons; [cell_tac|]); [destruct (st_internal_inited S); cbn; exact I | apply Forall_nil]. }
{   unfold thread_cells. apply Forall_cons; [cell_tac | apply Forall_nil]. }
Qed.
Lemma ajunk_lt : Forall (fun r => asec_lt n (fst r)) (as_junk B ly) -> Forall (fun r => asec_lt n (fst r)) (ajunk B ly S).
Proof.
intros JUNK. unfold ajunk. apply Forall_cons; [cbn; exact I|]. apply Forall_cons; [cbn; exact I|].
apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros c _. unfold region_junk. repeat (apply Forall_cons; [cbn; exact I|]). apply Forall_nil. }
apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros c _. unfold cache_junk. apply Forall_cons; [cbn; exact I | apply Forall_nil]. }
apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT. unfold chunk_junk.
repeat (apply Forall_app; split); try (destruct (ck_rz k =? kChunkHeaderSize)); try (destruct (ck_state k)); try apply Forall_nil;
repeat (apply Forall_cons; [cbn [fst]; apply asec_lt_aoff; apply sptr_exp_lt; exact LT|]); apply Forall_nil. }
apply Forall_app. split.
{ unfold sec_junk. apply Forall_cons; [cbn; exact I|]. apply Forall_cons; [cbn; exact I|]. apply Forall_cons; [cbn; exact I|].
apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT.
destruct (ck_beg k) as [|o|r o|c p]; try apply Forall_nil. apply Forall_cons; [cbn; exact LT | apply Forall_nil]. }
apply Forall_app. split.
{ unfold quar_junk. apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros b _. unfold batch_junk. apply Forall_cons; [cbn; exact I | apply Forall_nil]. }
apply Forall_app. split.
{ unfold thread_junk. repeat (apply Forall_cons; [cbn; exact I|]). apply Forall_nil. }
apply Forall_app. split.
{ repeat (apply Forall_cons; [cbn; exact I|]). apply Forall_nil. }
{ exact JUNK. }
Qed.
Lemma aareas_lt : Forall (fun r => asec_lt n (fst r)) (aareas S).
Proof.
unfold aareas. apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros c _. repeat (apply Forall_cons; [cbn; exact I|]). apply Forall_nil. }
apply Forall_app. split. { apply Forall_cons; [cbn; exact I | apply Forall_nil]. }
apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT.
destruct (ck_beg k) as [|o|r o|c p]; try apply Forall_nil. apply Forall_cons; [cbn; exact LT | apply Forall_nil]. }
repeat (apply Forall_cons; [cbn; exact I|]). apply Forall_nil.
Qed.
Lemma aclient_lt : Forall (fun r => asec_lt n (fst r)) (aclient S).
Proof.
unfold aclient. apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT. unfold chunk_user.
destruct (ck_state k); [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil]. cbn [fst]. apply sptr_exp_lt. unfold ck_user. apply padd_lt. exact LT. }
apply Forall_app. split; apply Forall_forall; intros x Hx; apply in_map_iff in Hx as (cp & <- & _); cbn; exact I.
Qed.
End j.
Section s.
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
Proof. destruct LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & E15). unfold acells, depot_cells. rewrite E13. reflexivity. Qed.
Lemma ajunk_ly : ajunk B ly' S = ajunk B ly S.
Proof. unfold ajunk. rewrite JUNK. reflexivity. Qed.
Lemma ashadow_ly : forall g, ashadow B ly' S g = ashadow B ly S g.
Proof.
intros g. destruct LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & E15). unfold ashadow.
assert (CB : forall k, In k (st_chunks S) -> ck_base B ly' k = ck_base B ly k).
{ intros k Hk. unfold ck_base. apply (sptr_addr_le B ly ly' (length (st_secs S))); [exact LE|]. exact (chunk_lt S _ _ _ _ WF k Hk). }
assert (FC : find_chunk_at B ly' (st_chunks S) g = find_chunk_at B ly (st_chunks S) g).
{ assert (H : forall l, incl l (st_chunks S) -> find_chunk_at B ly' l g = find_chunk_at B ly l g).
{ induction l as [|k t IH]; intros INC; [reflexivity|]. cbn [find_chunk_at]. rewrite (CB k (INC k (or_introl eq_refl))).
rewrite (IH (fun x Hx => INC x (or_intror Hx))). reflexivity. }
apply H. intros k Hk. exact Hk. }
assert (FIN : forall l k, find_chunk_at B ly l g = Some k -> In k l).
{ induction l as [|k0 t IH]; intros k Hf; [discriminate Hf|]. cbn [find_chunk_at] in Hf.
destruct ((ck_base B ly k0 <=? g) && (g <? ck_base B ly k0 + ck_extent k0)); [injection Hf as <-; left; reflexivity | right; exact (IH k Hf)]. }
rewrite FC. destruct (find_chunk_at B ly (st_chunks S) g) as [k|] eqn:Hf; [rewrite (CB k (FIN _ k Hf)); reflexivity|].
assert (FP : fa_poison_ranges ly' S = fa_poison_ranges ly S).
{ unfold fa_poison_ranges. f_equal.
- unfold region_base, fa_base. rewrite E2. reflexivity.
- pose proof (sec_extents_le ly ly' S _ _ _ _ LE WF) as SE. unfold sec_extents in SE. exact SE. }
rewrite FP. reflexivity.
Qed.
Theorem ARm_layout_le : ARm B ly' S rd.
Proof.
pose proof LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & EI & E15).
pose proof M as MM. destruct MM as [M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 M12 M13 M14 M15 M16 M17 M18 M19].
constructor.
- exact M1.
- exact M2.
- exact M3.
- exact LO'.
-   unfold sec_placed in *. rewrite (sec_extents_le ly ly' S _ _ _ _ LE M1).
replace (static_extents ly') with (static_extents ly); [exact M5|]. unfold static_extents, owned_extents. rewrite E1, E3, E4, E5, E6, E7, E8, E10, E11, ED, EI. reflexivity.
- rewrite CONST. exact (Forall_cell_holds_le B ly ly' _ LE rd _ CONSTlt M6).
- rewrite CONST. apply Forall_forall. intros c Hc k Hk. pose proof (proj1 (Forall_forall _ _) M7 c Hc k Hk) as O.
pose proof (proj1 (Forall_forall _ _) CONSTlt c Hc) as [Ha _]. rewrite (aeval_le B ly ly' _ LE _ Ha).
unfold owned_core in *. replace (core_extents ly') with (core_extents ly); [exact O|].
unfold core_extents. rewrite ?E1, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8, ?E9, ?E10, ?E11, ?E12, ?ED. reflexivity.
- rewrite acells_ly. exact (Forall_cell_holds_le B ly ly' _ LE rd _ (acells_lt B ly S _ _ _ _ M1) M8).
-   intros c i v Hc Hi Hv. unfold fa_base. rewrite E2. exact (M9 c i v Hc Hi Hv).
-   intros cid pos Hc Hp. unfold flag_addr. rewrite E6. exact (M10 cid pos Hc Hp).
-   destruct M11 as (heads & links & D1 & D2 & D3). exists heads, links.
replace (depot_traces ly' S) with (depot_traces ly S) by (unfold depot_traces; rewrite E13; reflexivity). rewrite E7. exact (conj D1 (conj D2 D3)).
-   intros g v Hg Hs. rewrite ashadow_ly in Hs. exact (M12 g v Hg Hs).
-   unfold zshadow_ok in *. replace (zero_shadow_ranges B ly') with (zero_shadow_ranges B ly); [exact M13|]. unfold zero_shadow_ranges. rewrite E10, E11. reflexivity.
- rewrite ajunk_ly. exact (Forall_range_vis_le B ly ly' _ LE rd _ (ajunk_lt B ly S _ _ _ _ M1 JUNKlt) M14).
- exact (Forall_range_vis_le B ly ly' _ LE rd _ (aareas_lt S _ _ _ _ M1) M15).
- exact (Forall_range_vis_le B ly ly' _ LE rd _ (aclient_lt S _ _ _ _ M1) M16).
-   apply Forall_forall. intros r Hr i Hi. pose proof (proj1 (Forall_forall _ _) M17 r Hr i Hi) as X.
unfold ialloc_zero in Hr. cbn in Hr. destruct Hr as [<-|[<-|[]]]; cbn in X |- *; exact X.
- rewrite E12. exact M18.
-   rewrite EI. exact M19.
Qed.
End s.
Section u.
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
induction lst as [|k0 t IH]; intros k H; [reflexivity|]. cbn [upd_chunk app]. rewrite (H k0 (or_introl eq_refl)). f_equal. apply IH. intros k' Hk'. apply H. right. exact Hk'.
Qed.
Lemma sfinal_eq : (forall k', In k' (st_chunks S) -> sptr_eqb (ck_beg k') (PSec rS kPage) = false) ->
set_chunks (upd_chunk (st_chunks s_dep) KS) s_dep = sfinal.
Proof.
intros FR. pose proof (upd_chunk_fresh _ KS FR) as UF. unfold s_dep, depot_after, s_arr, s_resv, s_secs, sfinal, depF, resF, rS in *.
destruct S; cbn in *. destruct grow; destruct (z =? 0); cbn; rewrite UF; reflexivity.
Qed.
Lemma KS_fresh : forall U pp cc bb, WfP U pp cc bb S -> forall k', In k' (st_chunks S) -> sptr_eqb (ck_beg k') (PSec rS kPage) = false.
Proof.
intros U pp cc bb WF k' Hk'. pose proof (chunk_lt S U pp cc bb WF k' Hk') as LT.
destruct (ck_beg k') as [|o|r o|c p]; cbn; try reflexivity. unfold rS. destruct (Nat.eqb_spec r (length (st_secs S))); [exfalso; lia|]. reflexivity.
Qed.
End u.
Lemma tfibsegs_readable : forall sg, In sg tfibsegs -> seg_readable sg = true.
Proof. assert (H : forallb seg_readable tfibsegs = true) by (vm_compute; reflexivity). intros sg Hin. exact (proj1 (forallb_forall _ _) H sg Hin). Qed.
Lemma writable_visible : forall (Hh : word -> bool) (m : word -> option byte) a, 0 <= a < 2 ^ 64 ->
writable_at tfibsegs (mrestrict Hh m) a -> aview tfibsegs Hh m a <> None.
Proof.
intros Hh m a Ra HW. unfold writable_at, wview in HW. unfold aview, mbyte.
destruct (mrestrict Hh m (Z_to_bv 64 a)) as [b|] eqn:E; [cbn; discriminate|].
destruct (find_segment tfibsegs (bv_unsigned (Z_to_bv 64 a)) 1) as [sg|] eqn:F; [|exfalso; exact (HW eq_refl)].
destruct (seg_writable sg) eqn:Wr; [|exfalso; exact (HW eq_refl)].
pose proof (find_segment_some_spec _ _ _ _ F) as (Hin & _ & _).
unfold seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite F, (tfibsegs_readable sg Hin). change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base sg)))) as [b|]; [cbn; discriminate | exfalso; exact (HW eq_refl)].
Qed.
End f.
