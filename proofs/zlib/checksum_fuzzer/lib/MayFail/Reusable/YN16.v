(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN16.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN31.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN13.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Local Open Scope mm_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation B := src0_msyms.
Ltac inlist := cbn; repeat (first [left; reflexivity | right]).
Ltac lits := unfold LOCK, CTX, LIBC, ERRNO, TP, GOT, GUARD, SCT, SCNT, MCNT, ASF, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp,
src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab in *.
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma pure_queue : forall h q s, pure (queue h q s).
Proof.
intros h q s. unfold queue, bind. apply pure_ibind; [apply pure_get_links|]. intros [l s1].
apply pure_ibind; [unfold massert; destruct (_ && _); exact I|]. intros [u s2].
apply pure_ibind; [unfold get_head, bind, get, ret; cbn; destruct h; exact I|]. intros [hd s3].
destruct hd as [head|].
- apply pure_ibind; [apply pure_get_links|]. intros [lh s4]. destruct (fst lh) as [hp|]; [|exact I].
unfold set_next, set_prev, bind. apply pure_ibind; [apply pure_set_links|]. intros [u2 s5].
apply pure_ibind; [apply pure_ibind; [apply pure_get_links | intros [l2 s6]; apply pure_set_links]|]. intros [u3 s6].
apply pure_ibind; [apply pure_get_links | intros [l3 s7]; apply pure_set_links].
- apply pure_ibind; [apply pure_set_links|]. intros [u2 s5]. unfold set_head, modify. destruct h; exact I.
Qed.
Lemma pure_free_meta : forall q s, pure (free_meta q s).
Proof. intros q s. unfold free_meta, bind. apply pure_ibind; [unfold setslot, modify; exact I | intros [u s1]; apply pure_queue]. Qed.
Definition nonusedb (x : option mslot) : bool := match x with Some (MUsed _) => false | _ => true end.
Lemma used_metas_ext_list : forall (l l' : list (sptr * mslot)),
List.NoDup (map fst l) -> map fst l' = map fst l ->
(forall q, mlookup l' q = mlookup l q \/ (nonusedb (mlookup l q) = true /\ nonusedb (mlookup l' q) = true)) ->
flat_map (fun e : sptr * mslot => match e with (p, MUsed am) => [(p, am)] | _ => [] end) l' =
flat_map (fun e : sptr * mslot => match e with (p, MUsed am) => [(p, am)] | _ => [] end) l.
Proof.
induction l as [|[q y] t IH]; intros [|[q' y'] t'] ND EK HM; cbn in *; try discriminate; [reflexivity|].
injection EK as -> EK. inversion ND as [|a b Hnin ND']; subst.
pose proof (HM q) as Hq. rewrite sptr_eqb_refl in Hq.
assert (TL : flat_map (fun e : sptr * mslot => match e with (p, MUsed am) => [(p, am)] | _ => [] end) t' =
flat_map (fun e : sptr * mslot => match e with (p, MUsed am) => [(p, am)] | _ => [] end) t).
{ apply IH; [exact ND' | exact EK |]. intros p. specialize (HM p). destruct (sptr_eqb p q) eqn:E; [| exact HM].
apply sptr_eqb_eq in E. subst p.
assert (N1 : mlookup t q = None).
{ clear - Hnin. induction t as [|[r z] t IH2]; cbn; [reflexivity|]. cbn in Hnin. destruct (sptr_eqb q r) eqn:E2; [apply sptr_eqb_eq in E2; subst; exfalso; apply Hnin; left; reflexivity|].
apply IH2. intros H. apply Hnin. right. exact H. }
assert (N2 : mlookup t' q = None).
{ rewrite <- EK in Hnin. clear - Hnin. induction t' as [|[r z] t' IH2]; cbn; [reflexivity|]. cbn in Hnin. destruct (sptr_eqb q r) eqn:E2; [apply sptr_eqb_eq in E2; subst; exfalso; apply Hnin; left; reflexivity|].
apply IH2. intros H. apply Hnin. right. exact H. }
left. rewrite N1, N2. reflexivity. }
rewrite TL. destruct Hq as [Hq|[H1 H2]]; [injection Hq as ->; reflexivity|].
destruct y as [| |am]; destruct y' as [| |am']; cbn in H1, H2; try discriminate; reflexivity.
Qed.
Lemma used_metas_ext : forall s s', List.NoDup (keys s) -> keys s' = keys s ->
(forall q, MT s' q = MT s q \/ (nonusedb (MT s q) = true /\ nonusedb (MT s' q) = true)) ->
used_metas s' = used_metas s.
Proof. intros s s' ND EK HM. unfold used_metas. apply used_metas_ext_list; [exact ND | exact EK | exact HM]. Qed.
Section a0.
Variables (X : list sptr) (U : Z -> Z) (s : astate) (m : sptr).
Hypothesis HI : Inv (m :: X) None U s.
Hypothesis Mm : MT s m = Some MRaw \/ MT s m = Some (MFree None None).
Let s1 : astate := upd_meta m (MFree None None) s.
Definition fm_post (ms : list sptr) (s' : astate) : Prop :=
same_but_metas_heads s s' /\ st_active s' = st_active s /\
st_free_meta_head s' = Some (hd m ms) /\
MT s' m = Some (MFree (Some (last ms m)) (Some (hd m ms))) /\
(forall q, ~ In q (m :: ms) -> MT s' q = MT s q) /\
(forall y xy, In y ms -> MT s y = Some xy ->
MT s' y = Some (with_links xy (if sptr_eqb y (hd m ms) then Some m else fst (links_of xy))
(if sptr_eqb y (last ms m) then Some m else snd (links_of xy)))).
Theorem fm_shape : exists ms s',
ring_ok (flinks (m :: X) s) (st_free_meta_head s) ms /\
(forall q, In q ms -> exists qp qn, MT s q = Some (MFree qp qn) /\ memb q (m :: X) = false) /\
~ In m ms /\
(forall h0 rest, ms = h0 :: rest -> exists hn, MT s h0 = Some (MFree (Some (last ms m)) hn)) /\
free_meta m s = IRet (tt, s') /\ fm_post ms s'.
Proof.
assert (Hm : In m (m :: X)) by (left; reflexivity).
pose proof (proj1 (inv_X HI m Hm)) as Km.
assert (HI1 : Inv (m :: X) None U s1) by (apply Inv_upd_exempt; [exact HI | exact Hm | exact I]).
assert (Mm1 : MT s1 m = Some (MFree None None)) by (subst s1; apply MT_upd_same).
destruct (inv_rings HI) as ((ms & FR & Fall) & _).
assert (MEMS : forall q, In q ms -> exists qp qn, MT s q = Some (MFree qp qn) /\ memb q (m :: X) = false).
{ intros q Hq. destruct (fring_members_free (m :: X) s _ ms q FR Hq) as (qp & qn & M1 & M2). exists qp, qn. auto. }
assert (Hmn : ~ In m ms).
{ intros Hin. destruct (MEMS m Hin) as (qp & qn & _ & M). cbn in M. rewrite sptr_eqb_refl in M. discriminate. }
assert (MT1 : forall q, q <> m -> MT s1 q = MT s q) by (intros q Hq; subst s1; apply MT_upd_other; exact Hq).
assert (FR1 : ring_ok (flinks (m :: X) s1) (st_free_meta_head s1) ms).
{ destruct FR as [[ND CH] HD]. split; [split; [exact ND|] | exact HD].
destruct ms as [|h0 rest]; [exact I|].
assert (CHg : forall lk lk' pr l f, (forall q, In q l -> lk' q = lk q) -> chain lk pr l f -> chain lk' pr l f).
{ intros lk lk' pr l f. revert pr. induction l as [|x t IH]; intros pr Hl Hc; [exact I|]. cbn in Hc |- *. destruct Hc as [H1 H2].
split; [rewrite (Hl x (or_introl eq_refl)); exact H1 | apply IH; [intros q Hq; apply Hl; right; exact Hq | exact H2]]. }
apply (CHg (flinks (m :: X) s)); [| exact CH]. intros q Hq. unfold flinks, MTX. rewrite (MT1 q) by (intros ->; exact (Hmn Hq)). reflexivity. }
exists ms.
assert (LKs : forall q l, In q ms -> flinks (m :: X) s1 q = Some l -> LK s1 q = Some l) by (intros q l Hq Hl; eapply LK_of_flinks; exact Hl).
assert (OP : itok (queue HFreeMeta m s1) (fun r => fm_post ms (snd r))).
{ apply (queue_op HFreeMeta m s1 (MFree None None) ms (flinks (m :: X) s1) _ Mm1 eq_refl FR1 Hmn LKs I).
intros s' S1 S2 S3 S4 S5 S6. unfold fm_post. cbn [snd].
split; [eapply sbmh_trans; [apply sbmh_upd_meta; exact Km | exact S1]|]. split.
- destruct S2 as (A1 & _ & A3). transitivity (st_active s1); [| reflexivity]. apply (nth_ext _ _ None None A3). intros k _. apply A1. intros sc' H; discriminate.
- split; [exact S3|]. split; [exact S4|]. split.
+ intros q Hq. rewrite (S5 q Hq). apply MT1. intros ->. apply Hq. left. reflexivity.
+ intros y xy Hy My. apply S6; [exact Hy|]. rewrite MT1; [exact My|]. intros ->. exact (Hmn Hy).
}
assert (FMeq : free_meta m s = queue HFreeMeta m s1) by reflexivity.
destruct (itok_pure _ _ (pure_queue HFreeMeta m s1) OP) as ([[] s'] & Eq & P). cbn [snd] in P.
exists s'. split; [exact FR|]. split; [exact MEMS|]. split; [exact Hmn|]. split.
- intros h0 rest ->. destruct FR as [[ND CH] HD]. cbn [chain] in CH. destruct CH as [H0 _].
destruct (flinks_free _ _ _ _ H0) as (pr & nx & _ & M0 & E0). injection E0 as <- <-. exists (Some (hd h0 rest)).
rewrite M0, !last_cons. destruct rest; reflexivity.
- split; [rewrite FMeq; exact Eq | exact P].
Qed.
End a0.
Lemma image_word : forall L1 A1 m1 md1 p v, midrep B L1 A1 m1 md1 -> In (MCell (LMem p) 8 v) (image A1) -> (forall z, v <> VLo5 z) ->
word_mem src0segs m1 (ptr_addr L1 p) (sval_num L1 v).
Proof.
intros L1 A1 m1 md1 p v MID1 Hin Hv. pose proof (memrep_cell B L1 A1 m1 _ (mid_mem _ _ _ _ _ MID1) Hin) as C.
unfold cell_mem in C. cbn [mc_loc mc_w mc_val] in C. change (loc_addr L1 (LMem p)) with (ptr_addr L1 p) in C. change (ms_segs B) with src0segs in C.
destruct v as [z|q|z|]; try exact C. exfalso. exact (Hv z eq_refl).
Qed.
Lemma with_links_same : forall pr nx, with_links (MFree pr nx) (fst (links_of (MFree pr nx))) (snd (links_of (MFree pr nx))) = MFree pr nx.
Proof. reflexivity. Qed.
Lemma key_facts : forall X' U' L1 A1 mm md1 q, Inv X' None U' A1 -> midrep B L1 A1 mm md1 -> In q (keys A1) ->
(forall x, ptr_addr L1 q <= x < ptr_addr L1 q + META_SIZE -> present mm x /\ ~ in_img B x /\ 4096 <= x < alloc_ceiling) /\
ptr_addr L1 q mod 8 = 0 /\
(forall c, In c (meta_slot_cells q (MT A1 q)) -> In c (image A1)) /\
(exists a k, In a (st_areas A1) /\ 0 <= k < METAS_PER_AREA /\ q = slot_of a k).
Proof.
intros X' U' L1 A1 mm md1 q HIq HM Hq.
pose proof (inv_keys HIq) as (_ & KP & _ & _ & Kc). destruct (KP q Hq) as (a & k & Ha & Hk & Eq).
assert (Hk' : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk; destruct (sptr_eqb a _); lia).
assert (PG : forall x, ptr_addr L1 q <= x < ptr_addr L1 q + META_SIZE -> ptr_addr L1 a <= x < ptr_addr L1 a + PGSZ).
{ intros x Hx. rewrite Eq, ptr_addr_padd in Hx. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia. }
split; [| split; [| split]].
- intros x Hx. specialize (PG x Hx). pose proof (areas_off_img B X' None U' L1 A1 mm md1 HIq HM a x Ha PG) as [NI Rx].
split; [| split; [exact NI | exact Rx]].
pose proof (mid_mem _ _ _ _ _ HM) as (_ & _ & FT).
assert (Hin : In (LMem a, PGSZ) (footprint A1)) by (right; apply in_app_iff; left; apply in_map_iff; eexists; split; [reflexivity | exact Ha]).
pose proof (proj1 (Forall_forall _ _) FT _ Hin) as FO. cbn [foot_ok fst snd] in FO. apply FO. exact PG.
- pose proof (inv_areas HIq) as (_ & Hareas & _). destruct (Hareas a Ha) as (r & o & rg & Ear & Ho & Hlo & Hr & Hl & _).
pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ HM) r rg Hr Hl) as (Hal & _).
rewrite Eq, ptr_addr_padd, Ear. unfold ptr_addr. cbn [loc_addr]. unfold PGSZ in Hal, Ho. unfold AREA_HDR, META_SIZE.
pose proof (proj2 (Z.div_exact (ly_reg L1 r) 4096 ltac:(lia)) Hal) as Hb. pose proof (proj2 (Z.div_exact o 4096 ltac:(lia)) Ho) as Hob.
replace (ly_reg L1 r + o + (24 + 40 * k)) with ((512 * (ly_reg L1 r / 4096) + 512 * (o / 4096) + 3 + 5 * k) * 8) by lia. apply Z_mod_mult.
- intros c Hc. unfold image. rewrite !in_app_iff. right. left. apply (slot_cells_in_areas A1 (st_areas A1) a k c Ha Hk'). unfold slot_of. rewrite <- Eq. exact Hc.
- exists a, k. split; [exact Ha|]. split; [exact Hk'|]. exact Eq.
Qed.
Lemma ctx_cells_fm : forall s s' c, same_but_metas_heads s s' -> st_active s' = st_active s -> In c (ctx_cells s') ->
c = MCell (LCtx CTX_free_meta_head) 8 (optr (st_free_meta_head s')) \/
(In c (ctx_cells s) /\ exists off, mc_loc c = LCtx off /\ 0 <= off /\ (off + Z.of_nat (mc_w c) <= CTX_free_meta_head \/ CTX_free_meta_head + 8 <= off)).
Proof.
intros s s' c SB EA H.
pose proof SB as (Sid & Smc & Sam & Samc & Saac & Ssh & Sah & Sat & Sama & Su & Suq & Sb & Ssq & Sbrk & Srg & Sar & Sk).
unfold ctx_cells in H. rewrite Sid, Smc, Sam, Samc, Saac, Ssh, Sah, Sat, Sama, Su, Suq, Sb, Ssq, Sbrk, Sar, EA in H. rewrite !in_app_iff in H.
unfold CTX_free_meta_head, CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_avail_meta, CTX_avail_meta_count, CTX_avail_meta_area_count, CTX_meta_alloc_shift,
CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk, CTX_active, CTX_usage, CTX_unmap_seq, CTX_bounces in *.
destruct H as [H|[H|[H|[H|H]]]].
- cbn [In] in H. destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
try (left; reflexivity); right; (split; [unfold ctx_cells; apply in_app_iff; left; inlist | eexists; split; [reflexivity|]; cbn [mc_w]; lia]).
- apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. right. split; [unfold ctx_cells; rewrite !in_app_iff; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
eexists; split; [reflexivity|]. cbn [mc_w]. lia.
- apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. right. split; [unfold ctx_cells; rewrite !in_app_iff; right; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
eexists; split; [reflexivity|]. cbn [mc_w]. lia.
- apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. right. split; [unfold ctx_cells; rewrite !in_app_iff; right; right; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
eexists; split; [reflexivity|]. cbn [mc_w]. lia.
- apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. right. split; [unfold ctx_cells; rewrite !in_app_iff; right; right; right; right; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
eexists; split; [reflexivity|]. cbn [mc_w]. unfold CTX_bounces. lia.
Qed.
Lemma cell_of_word : forall L1 mm p off q, word_mem src0segs mm (ptr_addr L1 p + off) (ptr_addr L1 q) -> cell_mem B L1 mm (MCell (LMem (padd p off)) 8 (VP q)).
Proof.
intros L1 mm p off q W. unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num]. change (loc_addr L1 (LMem (padd p off))) with (ptr_addr L1 (padd p off)). rewrite ptr_addr_padd. exact W.
Qed.
Section b0.
Variables (X : list sptr) (U : Z -> Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (sc n stk : Z).
Hypothesis HI : Inv X None U A.
Hypothesis XR : rawX X A.
Hypothesis AMA : ama_ok A.
Hypothesis BND : bounded A.
Hypothesis RSV : rsv_ok A.
Hypothesis SPOK : span_ok A.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hn : 0 <= n < MMAP_THRESHOLD.
Hypothesis MID : midrep B L A mem md.
Hypothesis AUXP : st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem.
Hypothesis PRE : callee_pre B regs mem stk.
Hypothesis Hstk : ASF <= stk <= AS_STACK.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 sc.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 n.
Hypothesis AMH : alloc_meta_hyp B.
Variable g : Z.
Hypothesis Hg : word_mem src0segs mem GUARD g.
Variables (j1 j2 : Z).
Let sp : Z := bv_unsigned (getr regs 2).
Local Notation csn := (cs L A sc g j1 j2).
Local Notation E00 := (E0 regs csn).
Local Notation WSn := (WS regs).
Local Notation POSTn := (POST X L A regs mem md sc stk g).
Let agree_cs' := agree_cs L A regs sc g j1 j2.
Let agree_reg' := agree_reg L A regs sc g j1 j2.
Let cs_facts' := cs_facts X U L A regs mem md sc HI Hsc MID g j1 j2.
Let pre_facts' := pre_facts regs mem stk PRE.
Let XC : Xclean X A := fun x am Hx H => ltac:(destruct (XR x Hx) as [EXR|EXR]; rewrite EXR in H; discriminate).
Section MD.
Variables (m : sptr) (s1 : astate) (L1 : layout) (mem1 : word -> option byte) (md1 : Model).
Hypothesis HI1 : Inv (m :: X) None U s1.
Hypothesis RX1 : rawX X s1.
Hypothesis Mm : MT s1 m = Some MRaw \/ MT s1 m = Some (MFree None None).
Hypothesis Km : In m (keys s1).
Hypothesis NXm : memb m X = false.
Hypothesis US1 : forall g' am, usedX (m :: X) s1 g' am <-> usedX X A g' am.
Hypothesis LE1 : layout_le A L L1.
Hypothesis AK1 : as_keep X A s1.
Hypothesis MID1 : midrep B L1 s1 mem1 md1.
Hypothesis AMA1 : ama_ok s1.
Hypothesis BND1 : bounded s1.
Hypothesis VM1 : exists vm', md1 = with_vmmaps vm' md.
Hypothesis FR1 : forall x, 0 <= x < 2 ^ 64 -> ~ WSn x -> ~ (ERRNO <= x < ERRNO + 4) -> ~ (CTX <= x < CTX + CTX_SIZE) -> ~ in_nonmap_region L1 s1 x ->
mem1 (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Hypothesis ERRW1 : forall a, ERRNO <= a < ERRNO + 4 -> writable_at src0segs mem1 a.
Variable E6 : env.
Hypothesis AG6 : env_agree 40 E00 E6.
Hypothesis E6_40 : ew E6 40 = Z_to_bv 64 (ptr_addr L1 m).
Let s3 : astate := seq_st (ab_st sc s1).
Let Mh1 : m_halted md1 = None := proj1 (mid_md _ _ _ _ _ MID1).
Let Mlz1 : m_vm_lazy md1 = [] := proj1 (proj2 (mid_md _ _ _ _ _ MID1)).
Let Mmat1 : m_vm_materialized md1 = [] := proj2 (proj2 (mid_md _ _ _ _ _ MID1)).
Local Notation FRcB := (YN14.FRcB regs mem1).
Lemma s3_factsD : Inv (m :: X) None U s3 /\ Xclean (m :: X) s3 /\ ama_ok s3 /\ keys s3 = keys s1 /\ (forall q, MT s3 q = MT s1 q) /\ bounded s3 /\
st_regions s3 = st_regions s1 /\ st_areas s3 = st_areas s1 /\ st_active s3 = st_active s1 /\ st_usage s3 = st_usage s1.
Proof.
pose proof (s3_facts X U sc m s1 HI1 RX1 Mm AMA1 BND1) as (I3 & X3 & A3 & _ & B3).
pose proof (ab_st_fields sc s1) as (F1 & F2 & F3 & _ & F5 & F6 & _). pose proof (seq_st_fields (ab_st sc s1)) as (G1 & G2 & G3 & _ & G5 & G6 & _).
split; [exact I3|]. split; [exact X3|]. split; [exact A3|]. subst s3. unfold keys, MT. rewrite G1, F1, G3, F3, G2, F2, G6, F6, G5, F5. split; [reflexivity|]. split; [intros q; reflexivity|]. split; [exact B3|]. repeat split; reflexivity.
Qed.
Lemma s3_fmh : st_free_meta_head s3 = st_free_meta_head s1.
Proof. subst s3. pose proof (ab_st_fields sc s1) as (_&_&_&_&_&_&_&_&_&_&F11&_). pose proof (seq_st_fields (ab_st sc s1)) as (_&_&_&_&_&_&_&_&_&G10&_). rewrite G10, F11. reflexivity. Qed.
Lemma m_range : forall x, ptr_addr L1 m <= x < ptr_addr L1 m + 40 -> ~ in_img B x /\ 4096 <= x < alloc_ceiling.
Proof. intros x Hx. destruct (key_facts (m :: X) U L1 s1 mem1 md1 m HI1 MID1 Km) as (RB & _). destruct (RB x Hx) as (_ & NI & R). exact (conj NI R). Qed.
Lemma E6_factsD : ew E6 10 = Z_to_bv 64 sc /\ ew E6 33 = Z_to_bv 64 (csn 33) /\ ew E6 2 = getr regs 2 /\ bv_unsigned (ew E6 40) = ptr_addr L1 m.
Proof.
pose proof (proj1 alloc_ceiling_val) as AC.
split; [rewrite (agree_reg' E6 10 AG6) by lia; exact R10|]. split; [exact (agree_cs' E6 33 AG6 ltac:(lia))|]. split; [exact (agree_reg' E6 2 AG6 ltac:(lia))|].
rewrite E6_40. apply lit64_small. destruct (m_range (ptr_addr L1 m) ltac:(lia)) as [_ R]. lia.
Qed.
Lemma fm_shape3 : exists ms s',
ring_ok (flinks (m :: X) s3) (st_free_meta_head s3) ms /\
(forall q, In q ms -> exists qp qn, MT s3 q = Some (MFree qp qn) /\ memb q (m :: X) = false) /\
~ In m ms /\
(forall h0 rest, ms = h0 :: rest -> exists hn, MT s3 h0 = Some (MFree (Some (last ms m)) hn)) /\
free_meta m s3 = IRet (tt, s') /\ fm_post s3 m ms s' /\
Inv X None U s' /\ (forall q am, usedX X s' q am <-> usedX X A q am) /\ rawX X s' /\ ama_ok s' /\ bounded s' /\
st_regions s' = st_regions s1 /\ st_areas s' = st_areas s1 /\ as_keep X A s'.
Proof.
destruct s3_factsD as (I3 & X3 & A3 & K3 & M3 & B3 & R3 & Ar3 & Ac3 & U3).
assert (Mm3 : MT s3 m = Some MRaw \/ MT s3 m = Some (MFree None None)) by (rewrite M3; exact Mm).
destruct (fm_shape X U s3 m I3) as (ms & s' & FRg & MEMS & Hmn & HD0 & Efm & FP). exists ms, s'.
assert (SPEC : itok (free_meta m s3) (fun r => Inv (remove sptr_eq_dec m (m :: X)) None U (snd r) /\ (forall q am, usedX (remove sptr_eq_dec m (m :: X)) (snd r) q am <-> usedX (m :: X) s3 q am))).
{ apply (free_meta_spec (m :: X) None U s3 m); [exact I3 | left; reflexivity |]. intros s'' HI'' _ _ EU _. split; [exact HI'' | exact EU]. }
rewrite Efm in SPEC. cbn [itok snd] in SPEC. destruct SPEC as [HI' EU'].
assert (RM : remove sptr_eq_dec m (m :: X) = X).
{ cbn. destruct (sptr_eq_dec m m) as [_|NE]; [| exfalso; apply NE; reflexivity]. apply notin_remove. intros Hin. apply (proj2 (memb_In m X)) in Hin. rewrite NXm in Hin. discriminate. }
rewrite RM in HI', EU'.
assert (EU : forall q am, usedX X s' q am <-> usedX X A q am).
{ intros q am. rewrite (EU' q am). rewrite <- (US1 q am). unfold usedX, MTX. rewrite M3. tauto. }
pose proof FP as (SB & EA & Hhd & MTm & MTo & MTr).
pose proof SB as (Sid & Smc & Sam & Samc & Saac & Ssh & Sah & Sat & Sama & Su & Suq & Sb & Ssq & Sbrk & Srg & Sar & Sk).
assert (RXs : rawX X s').
{ intros x Hx. rewrite MTo; [rewrite M3; exact (RX1 x Hx)|]. intros [<-|Hin]; [apply (proj2 (memb_In _ X)) in Hx; rewrite NXm in Hx; discriminate|].
destruct (MEMS x Hin) as (qp & qn & _ & Mx). cbn [memb existsb] in Mx. apply Bool.orb_false_iff in Mx as [_ Mx]. change (memb x X = false) in Mx.
apply (proj2 (memb_In x X)) in Hx. rewrite Hx in Mx. discriminate. }
split; [exact FRg|]. split; [exact MEMS|]. split; [exact Hmn|]. split; [exact HD0|]. split; [exact Efm|]. split; [exact FP|]. split; [exact HI'|]. split; [exact EU|]. split; [exact RXs|]. split.
- unfold ama_ok. rewrite Sar, Sama, Srg. exact A3.
- split; [| split; [rewrite Srg; exact R3 | split; [rewrite Sar; exact Ar3 |]]].
+ destruct B3 as (B1 & B2 & B3'). unfold bounded, usage_of in *. rewrite Su, Ssh, Sar. exact (conj B1 (conj B2 B3')).
+ eapply as_keep_trans; [exact AK1|]. apply as_keep_same; [| rewrite Sar; exact Ar3 | rewrite Srg; exact R3].
intros x Hx _. exact (RXs x Hx).
Qed.
Definition SK0 : list (option nat * Z * Z) := [(Some 2%nat, -ASF, 0); (None, ERRNO, ERRNO + 4); (Some 40%nat, 0, 40)].
Definition WD0 (x : Z) : Prop := WSn x \/ ERRNO <= x < ERRNO + 4 \/ ptr_addr L1 m <= x < ptr_addr L1 m + 40.
Definition SK1 : list (option nat * Z * Z) := (None, LOCK + 24, LOCK + 32) :: SK0.
Definition WD1 (x : Z) : Prop := WD0 x \/ LOCK + 24 <= x < LOCK + 32.
Definition SK2 : list (option nat * Z * Z) := (Some 87%nat, 0, 8) :: (Some 88%nat, 8, 16) :: SK1.
Definition WD2 (h0 hp : Z) (x : Z) : Prop := WD1 x \/ h0 <= x < h0 + 8 \/ hp + 8 <= x < hp + 16.
Lemma SK0_WD0 : forall E b lo hi x, env_agree 40 E00 E -> ew E 40 = Z_to_bv 64 (ptr_addr L1 m) ->
In (b, lo, hi) SK0 -> base_val E b + lo <= x < base_val E b + hi -> WD0 x.
Proof.
intros E b lo hi x HA E40 Hin Hx. destruct E6_factsD as (_ & _ & _ & U40). rewrite <- E6_40 in E40.
unfold SK0 in Hin. cbn [In] in Hin. unfold WD0.
destruct Hin as [H|[H|[H|[]]]]; injection H as <- <- <-; cbn [base_val] in Hx.
- left. exact (YN13.win_stack L A regs sc g j1 j2 s1 E x HA Hx).
- right. left. lia.
- right. right. rewrite E40, U40 in Hx. lia.
Qed.
Lemma SK1_WD1 : forall E b lo hi x, env_agree 40 E00 E -> ew E 40 = Z_to_bv 64 (ptr_addr L1 m) ->
In (b, lo, hi) SK1 -> base_val E b + lo <= x < base_val E b + hi -> WD1 x.
Proof.
intros E b lo hi x HA E40 Hin Hx. unfold SK1 in Hin. cbn [In] in Hin. unfold WD1.
destruct Hin as [H|Hin]; [injection H as <- <- <-; cbn [base_val] in Hx; right; lia |].
left. exact (SK0_WD0 E b lo hi x HA E40 Hin Hx).
Qed.
Lemma SK2_WD2 : forall E b lo hi x h0 hp, env_agree 40 E00 E -> ew E 40 = Z_to_bv 64 (ptr_addr L1 m) ->
bv_unsigned (ew E 87) = h0 -> bv_unsigned (ew E 88) = hp ->
In (b, lo, hi) SK2 -> base_val E b + lo <= x < base_val E b + hi -> WD2 h0 hp x.
Proof.
intros E b lo hi x h0 hp HA E40 E87 E88 Hin Hx. unfold SK2 in Hin. cbn [In] in Hin. unfold WD2.
destruct Hin as [H|[H|Hin]]; [injection H as <- <- <-; cbn [base_val] in Hx; rewrite E87 in Hx; right; left; lia
| injection H as <- <- <-; cbn [base_val] in Hx; rewrite E88 in Hx; right; right; lia |].
left. exact (SK1_WD1 E b lo hi x HA E40 Hin Hx).
Qed.
Lemma frame_keep : forall (W : Z -> Prop) E rs sk mm mm' mm0,
frame_of E rs mm mm' -> wsub rs sk = true ->
(forall b lo hi x, In (b, lo, hi) sk -> base_val E b + lo <= x < base_val E b + hi -> W x) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ W x -> mm (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)) ->
forall x, 0 <= x < 2 ^ 64 -> ~ W x -> mm' (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x).
Proof.
intros W E rs sk mm mm' mm0 Hfr WSB HW HF x Hx Hw. rewrite <- (HF x Hx Hw). apply (frame_of_at E _ _ _ x Hfr Hx). intros Hin.
destruct (in_wrange_wsub regs E _ sk x WSB Hin) as (b & lo & hi & Hl & Hx'). exact (Hw (HW b lo hi x Hl Hx')).
Qed.
Lemma skels : wsub (ss_mem ss_Kf) SK0 = true /\ wsub (ss_mem ss_FM1) SK1 = true /\ wsub (ss_mem (add_cond ss_fm1 C_fe)) SK1 = true /\
wsub (ss_mem (add_cond ss_fm1 C_fne)) SK1 = true /\ wsub (ss_mem ss_FM2) SK2 = true /\
ss_atoms_lt 87 ss_fm0 = true /\ ss_atoms_lt 88 ss_fm2 = true /\
map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_fm0) = (None, ERRNO, ERRNO + 4) :: (Some 40%nat, 0, 40) :: skel_M1 /\
map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_fm2) = (None, LOCK + 24, LOCK + 32) :: (None, ERRNO, ERRNO + 4) :: (Some 40%nat, 0, 40) :: skel_M1 /\
ss_FM1 = mkSS (ss_pc ss_fm0) (ss_regs ss_fm0) (R_fmh :: ss_mem ss_fm0) None (addfact 87 F_ptr0 (ss_facts ss_fm0)) /\
ss_FM2 = mkSS (ss_pc ss_fm2) (ss_regs ss_fm2) (R_hd :: R_hp :: ss_mem ss_fm2) None (addfact 88 F_ptr0 (ss_facts ss_fm2)).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma finals_fm : finalS_check ss_feE (SLit (2 ^ 64 - 1)) = true /\ finalS_check ss_fneE (SLit (2 ^ 64 - 1)) = true /\
firstn 3 (ss_mem ss_feE) =
[YP09.mkRegion None (LOCK + 24) (LOCK + 32) (LOCK + 24) (LOCK + 32) [mkChunk (LOCK + 24) (CVal 8 (SOff 40 0))];
YP09.mkRegion None ERRNO (ERRNO + 4) ERRNO (ERRNO + 4) [mkChunk ERRNO (CVal 4 (SLit 12))];
YP09.mkRegion (Some 40%nat) 0 40 0 40 [mkChunk 8 (CVal 8 (SOff 40 0)); mkChunk 0 (CVal 8 (SOff 40 0)); mkChunk 16 (CVal 8 (SLit 0)); mkChunk 24 (CVal 8 (SLit 0)); mkChunk 32 (CVal 8 (SLit 0))]] /\
(exists rstk, nth_error (ss_mem ss_feE) 4 = Some rstk /\ r_base rstk = Some 2%nat /\ r_wlo rstk = - ASF /\ r_whi rstk = 0) /\
firstn 5 (ss_mem ss_fneE) =
[YP09.mkRegion (Some 87%nat) 0 8 0 8 [mkChunk 0 (CVal 8 (SOff 40 0))];
YP09.mkRegion (Some 88%nat) 8 16 8 16 [mkChunk 8 (CVal 8 (SOff 40 0))];
YP09.mkRegion None (LOCK + 24) (LOCK + 32) (LOCK + 24) (LOCK + 32) [mkChunk (LOCK + 24) (CVal 8 (SOff 87 0))];
YP09.mkRegion None ERRNO (ERRNO + 4) ERRNO (ERRNO + 4) [mkChunk ERRNO (CVal 4 (SLit 12))];
YP09.mkRegion (Some 40%nat) 0 40 0 40 [mkChunk 0 (CVal 8 (SOff 88 0)); mkChunk 8 (CVal 8 (SOff 87 0)); mkChunk 16 (CVal 8 (SLit 0)); mkChunk 24 (CVal 8 (SLit 0)); mkChunk 32 (CVal 8 (SLit 0))]] /\
(exists rstk, nth_error (ss_mem ss_fneE) 6 = Some rstk /\ r_base rstk = Some 2%nat /\ r_wlo rstk = - ASF /\ r_whi rstk = 0).
Proof. vm_compute. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [eexists; repeat split; reflexivity|]. split; [reflexivity|]. eexists; repeat split; reflexivity. Qed.
Definition fmh : Z := onum L1 (st_free_meta_head s3).
Let E8 : env := ewset E6 87 (Z_to_bv 64 fmh).
Lemma fmh_facts : 0 <= fmh <= alloc_ceiling - 40 /\ fmh mod 8 = 0 /\
(forall mm, midrep B L1 s3 mm md1 -> word_mem src0segs mm (LOCK + 24) fmh) /\
(forall h, st_free_meta_head s3 = Some h -> fmh = ptr_addr L1 h /\ In h (keys s3)).
Proof.
pose proof (proj1 alloc_ceiling_val) as AC. destruct s3_factsD as (I3 & X3 & A3 & K3 & M3 & _).
assert (W : forall mm, midrep B L1 s3 mm md1 -> word_mem src0segs mm (LOCK + 24) fmh).
{ intros mm HM. replace (LOCK + 24) with (CTX + CTX_free_meta_head) by (lits; unfold CTX_free_meta_head; lia). unfold fmh.
replace (onum L1 (st_free_meta_head s3)) with (sval_num L1 (optr (st_free_meta_head s3))) by (destruct (st_free_meta_head s3); reflexivity).
apply (ctx_word_gen L1 s3 mm md1 CTX_free_meta_head (optr (st_free_meta_head s3)) HM); [| destruct (st_free_meta_head s3); intros z; discriminate].
unfold ctx_cells. apply in_app_iff. left. do 3 right. left. reflexivity. }
destruct (inv_rings I3) as ((ms & FRg & _) & _).
destruct (st_free_meta_head s3) as [h|] eqn:Eh.
- destruct (ring_head_In _ _ _ FRg) as [Hin _]. destruct (fring_members_free _ _ _ _ h FRg Hin) as (pr & nx & _ & Mh).
pose proof (In_keys_of_MT _ _ _ Mh) as Kh. destruct (key_facts (m :: X) U L1 s1 mem1 md1 h HI1 MID1 ltac:(rewrite <- K3; exact Kh)) as (RB & AL & _).
unfold fmh. rewrite Eh. cbn [onum]. destruct (RB (ptr_addr L1 h) ltac:(unfold META_SIZE; lia)) as (_ & _ & R). destruct (RB (ptr_addr L1 h + 39) ltac:(unfold META_SIZE; lia)) as (_ & _ & R').
split; [lia|]. split; [exact AL|]. split; [unfold fmh in W; rewrite Eh in W; exact W|]. intros h' Hh'. injection Hh' as <-. split; [reflexivity | exact Kh].
- unfold fmh in *. rewrite Eh in *. cbn [onum] in *. split; [lia|]. split; [reflexivity|]. split; [exact W|]. intros h' Hh'. discriminate.
Qed.
Lemma apart_fm : forall E lo hi r, env_agree 40 E00 E -> ew E 40 = Z_to_bv 64 (ptr_addr L1 m) -> lo < hi ->
(forall x, lo <= x < hi -> ~ in_img B x /\ x < alloc_ceiling) -> (hi <= ptr_addr L1 m \/ ptr_addr L1 m + 40 <= lo) ->
In (r_base r, r_lo r, r_hi r) ((None, LOCK + 24, LOCK + 32) :: (None, ERRNO, ERRNO + 4) :: (Some 40%nat, 0, 40) :: skel_M1) ->
hi <= base_val E (r_base r) + r_lo r \/ base_val E (r_base r) + r_hi r <= lo.
Proof.
intros E lo hi r HA E40 Hlh Hoff Hm Hin. destruct E6_factsD as (_ & _ & _ & U40). rewrite <- E6_40 in E40.
assert (IMG : forall a b, 0x1e000 <= a -> b <= 0x51000 -> a < b -> hi <= a \/ b <= lo).
{ intros a b Ha Hb Hab. destruct (Z_lt_le_dec lo a) as [H1|H1].
- destruct (Z_le_dec hi a); [left; lia|]. exfalso. exact (proj1 (Hoff a ltac:(lia)) (src0_rwseg_img a ltac:(lia))).
- destruct (Z_le_dec b lo); [right; lia|]. exfalso. exact (proj1 (Hoff lo ltac:(lia)) (src0_rwseg_img lo ltac:(lia))). }
cbn [In] in Hin. destruct Hin as [H|[H|[H|Hin]]].
- apply (f_equal (fun t => match t with (b, l, h) => (b, l, h) end)) in H. cbn in H. injection H as X1 X2 X3. rewrite <- X1, <- X2, <- X3. cbn [base_val]. lits. apply IMG; lia.
- apply (f_equal (fun t => match t with (b, l, h) => (b, l, h) end)) in H. cbn in H. injection H as X1 X2 X3. rewrite <- X1, <- X2, <- X3. cbn [base_val]. lits. apply IMG; lia.
- apply (f_equal (fun t => match t with (b, l, h) => (b, l, h) end)) in H. cbn in H. injection H as X1 X2 X3. rewrite <- X1, <- X2, <- X3. cbn [base_val]. rewrite E40, U40. lia.
- exact (skel_M1_apart X U L A regs mem md sc stk HI Hsc MID PRE Hstk g j1 j2 s1 E lo hi r HA Hlh Hoff Hin).
Qed.
Lemma station_FM1 : forall ms0 mm0, st_ok src0segs E6 ss_fm0 ms0 -> midrep B L1 s3 mm0 md1 -> FRcB mm0 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WD0 x -> ms_mem ms0 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)) ->
st_ok src0segs E8 ss_FM1 ms0 /\ env_agree 87 E6 E8 /\ env_agree 40 E00 E8 /\ ew E8 87 = Z_to_bv 64 fmh /\ ew E8 40 = Z_to_bv 64 (ptr_addr L1 m).
Proof.
intros ms0 mm0 HS HM HF F0. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
destruct E6_factsD as (E10 & E33 & E2 & U40). destruct cs_facts' as (C33 & _). pose proof fmh_facts as (Hr & Hal & Wf & _).
destruct skels as (_ & _ & _ & _ & _ & AT87 & _ & SKf0 & _ & EFM1 & _).
assert (AG68 : env_agree 87 E6 E8) by (apply env_agree_ewset).
assert (AG8 : env_agree 40 E00 E8) by (eapply env_agree_trans; [exact AG6 | split; [intros k Hk; apply (proj1 AG68); lia | exact (proj2 AG68)]]).
assert (E8_87 : ew E8 87 = Z_to_bv 64 fmh) by (subst E8; apply ew_ewset_same).
assert (E8_40 : ew E8 40 = Z_to_bv 64 (ptr_addr L1 m)) by (rewrite <- E6_40; apply (proj1 AG68); lia).
split; [| exact (conj AG68 (conj AG8 (conj E8_87 E8_40)))].
assert (HS0 : st_ok src0segs E8 ss_fm0 ms0) by (eapply (st_ok_agree src0segs 87 E6 E8); [exact HS | exact AG68 | exact AT87]).
rewrite EFM1.
assert (DJm : LOCK + 32 <= ptr_addr L1 m \/ ptr_addr L1 m + 40 <= LOCK + 24).
{ destruct (Z_le_dec (ptr_addr L1 m + 40) (LOCK + 24)); [right; lia|]. left. destruct (Z_le_dec (LOCK + 32) (ptr_addr L1 m)); [lia|]. exfalso.
destruct (Z_lt_le_dec (ptr_addr L1 m) (LOCK + 24)).
- destruct (m_range (LOCK + 24) ltac:(lia)) as [NI' _]. apply NI'. apply src0_rwseg_img. lits. lia.
- destruct (m_range (ptr_addr L1 m) ltac:(lia)) as [NI _]. apply NI. apply src0_rwseg_img. lits. lia. }
assert (HS1 : st_ok src0segs E8 (mkSS (ss_pc ss_fm0) (ss_regs ss_fm0) (R_fmh :: ss_mem ss_fm0) None (ss_facts ss_fm0)) ms0).
{ apply (st_ok_add_region src0segs E8 _ _ R_fmh HS0); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_fmh ms_mem]; [lits; lia | lits; lia | |].
+ intros o Ho. rewrite Z.add_0_l. apply (proj1 (so_ctx_rw B (mid_syms _ _ _ _ _ MID) (ms_mem ms0) o ltac:(change (ms_ctx B) with CTX; unfold CTX_SIZE; lits; lia))).
+ apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs E8 (ms_mem ms0) 0 (LOCK + 24) (SOff 87 0) fmh); [apply den_off0; exact E8_87|].
rewrite Z.add_0_l. apply (word_mem_ext1 mm0); [| exact (Wf mm0 HM)].
intros k Hk. apply F0; [lits; lia|]. unfold WD0, WS. intros [Hw|[Hw|Hw]]; [lits; lia | lits; lia |]. destruct (m_range (LOCK + 24 + Z.of_nat k) Hw) as [NI _]. apply NI. apply src0_rwseg_img. lits. lia.
- apply Forall_forall. intros r Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite SKf0 in Hr'.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_fmh base_val]. cbn [In] in Hr'. unfold skel_M1 in Hr'. cbn [In] in Hr'.
destruct Hr' as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; apply (f_equal (fun t => match t with (b, l, h) => (b, l, h) end)) in H; cbn in H; injection H as X1 X2 X3;
rewrite <- X1, <- X2, <- X3; cbn [base_val]; rewrite ?(proj1 AG68 40%nat) by lia; rewrite ?U40, ?(agree_cs' E8 33 AG8), ?(agree_reg' E8 2 AG8) by lia; rewrite ?lit64_small by (lits; lia);
try replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity); fold sp; lits; lia. }
apply (st_ok_add_fact src0segs E8 _ ms0 87 F_ptr0) in HS1. 2:{ unfold afact_ok, F_ptr0. cbn [af_lo af_hi af_al2]. rewrite E8_87, lit64_small by lia. change (2 ^ 3) with 8. repeat split; lia. }
exact HS1.
Qed.
Lemma key_slot_area : forall q x, In q (keys s3) -> ptr_addr L1 q <= x < ptr_addr L1 q + 40 ->
exists a, In a (st_areas s3) /\ ptr_addr L1 a <= x < ptr_addr L1 a + PGSZ.
Proof.
intros q x Hq Hx. destruct s3_factsD as (I3 & X3 & A3 & K3 & M3 & _ & _ & Ar3 & _).
destruct (key_facts (m :: X) U L1 s1 mem1 md1 q HI1 MID1 ltac:(rewrite <- K3; exact Hq)) as (_ & _ & _ & a & k & Ha & Hk & Eq).
exists a. rewrite Ar3. split; [exact Ha|]. rewrite Eq in Hx. unfold slot_of in Hx. rewrite ptr_addr_padd in Hx. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia.
Qed.
Lemma key_range3 : forall q x, In q (keys s3) -> ptr_addr L1 q <= x < ptr_addr L1 q + 40 -> ~ in_img B x /\ 4096 <= x < alloc_ceiling /\ present mem1 x.
Proof.
intros q x Hq Hx. destruct s3_factsD as (I3 & X3 & A3 & K3 & _).
destruct (key_facts (m :: X) U L1 s1 mem1 md1 q HI1 MID1 ltac:(rewrite <- K3; exact Hq)) as (RB & _). destruct (RB x Hx) as (P & NI & R). exact (conj NI (conj R P)).
Qed.
Lemma key_present : forall mm q x, midrep B L1 s3 mm md1 -> In q (keys s3) -> ptr_addr L1 q <= x < ptr_addr L1 q + 40 -> present mm x.
Proof.
intros mm q x HM Hq Hx. destruct s3_factsD as (I3 & _). destruct (key_facts (m :: X) U L1 s3 mm md1 q I3 HM Hq) as (RB & _). exact (proj1 (RB x Hx)).
Qed.
Lemma keys_apart3 : forall p q, In p (keys s3) -> In q (keys s3) -> p <> q -> ptr_addr L1 p + 40 <= ptr_addr L1 q \/ ptr_addr L1 q + 40 <= ptr_addr L1 p.
Proof.
intros p q Hp Hq Hne. destruct s3_factsD as (I3 & X3 & A3 & K3 & _). rewrite K3 in Hp, Hq.
exact (keys_apart (m :: X) None U L1 s1 regs mem1 md1 HI1 MID1 p q Hp Hq Hne).
Qed.
Lemma present_keep : forall mm mm' x, mm' (Z_to_bv 64 x) = mm (Z_to_bv 64 x) -> present mm x -> present mm' x.
Proof. intros mm mm' x E [b Hb]. exists b. rewrite E. exact Hb. Qed.
Lemma midrep_fm : forall ms s' mm0 mem' (W : Z -> Prop),
ring_ok (flinks (m :: X) s3) (st_free_meta_head s3) ms ->
(forall q, In q ms -> exists qp qn, MT s3 q = Some (MFree qp qn) /\ memb q (m :: X) = false) ->
~ In m ms ->
(forall h0 rest, ms = h0 :: rest -> exists hn, MT s3 h0 = Some (MFree (Some (last ms m)) hn)) ->
fm_post s3 m ms s' ->
midrep B L1 s3 mm0 md1 ->
(forall x, W x \/ ~ W x) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ W x -> mem' (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)) ->
(forall x, W x -> WSn x \/ ERRNO <= x < ERRNO + 4 \/ LOCK + 24 <= x < LOCK + 32 \/ ptr_addr L1 m <= x < ptr_addr L1 m + 16 \/
(ms <> [] /\ (ptr_addr L1 (hd m ms) <= x < ptr_addr L1 (hd m ms) + 8 \/ ptr_addr L1 (last ms m) + 8 <= x < ptr_addr L1 (last ms m) + 16))) ->
(forall x, ptr_addr L1 m <= x < ptr_addr L1 m + 16 -> present mem' x) ->
(ms <> [] -> forall x, (ptr_addr L1 (hd m ms) <= x < ptr_addr L1 (hd m ms) + 8 \/ ptr_addr L1 (last ms m) + 8 <= x < ptr_addr L1 (last ms m) + 16) -> present mem' x) ->
word_mem src0segs mem' (LOCK + 24) (ptr_addr L1 (hd m ms)) ->
word_mem src0segs mem' (ptr_addr L1 m) (ptr_addr L1 (last ms m)) ->
word_mem src0segs mem' (ptr_addr L1 m + 8) (ptr_addr L1 (hd m ms)) ->
(ms <> [] -> word_mem src0segs mem' (ptr_addr L1 (hd m ms)) (ptr_addr L1 m) /\ word_mem src0segs mem' (ptr_addr L1 (last ms m) + 8) (ptr_addr L1 m)) ->
midrep B L1 s' mem' md1.
Proof.
intros ms s' mm0 mem' W FRg MEMS Hmn HD0 FP HM Wdec FR Wsub PRESm PRESh Wfmh Wm0 Wm8 Wring.
pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
destruct s3_factsD as (I3 & X3 & A3 & K3 & M3 & B3 & R3 & Ar3 & _).
pose proof FP as (SB & EA & Hhd & MTm & MTo & MTr).
pose proof SB as (Sid & Smc & Sam & Samc & Saac & Ssh & Sah & Sat & Sama & Su & Suq & Sb & Ssq & Sbrk & Srg & Sar & Sk).
pose proof (mid_syms _ _ _ _ _ HM) as SO.
assert (Km3 : In m (keys s3)) by (rewrite K3; exact Km).
assert (Kms : forall q, In q ms -> In q (keys s3)) by (intros q Hq; destruct (MEMS q Hq) as (qp & qn & Mq & _); exact (In_keys_of_MT _ _ _ Mq)).
assert (Kh0 : ms <> [] -> In (hd m ms) (keys s3)) by (intros Hne; apply Kms; destruct ms; [exfalso; exact (Hne eq_refl) | left; reflexivity]).
assert (INlast : forall (l : list sptr) d, l <> [] -> In (last l d) l).
{ intros l. induction l as [|x t IH]; intros d Hne; [exfalso; exact (Hne eq_refl)|]. destruct t as [|y t']; [left; reflexivity|]. right. apply IH. discriminate. }
assert (Khp : ms <> [] -> In (last ms m) (keys s3)) by (intros Hne; apply Kms; apply INlast; exact Hne).
assert (Hh0m : ms <> [] -> hd m ms <> m) by (intros Hne E; apply Hmn; rewrite <- E; destruct ms; [exfalso; exact (Hne eq_refl) | left; reflexivity]).
assert (Hhpm : ms <> [] -> last ms m <> m) by (intros Hne E; apply Hmn; rewrite <- E; apply INlast; exact Hne).
assert (CTXhi : CTX + CTX_SIZE <= alloc_ceiling) by exact (so_ctx_hi _ SO).
assert (Wlow : forall x, W x -> alloc_ceiling <= x \/ in_img B x \/ (exists q, In q (keys s3) /\ ptr_addr L1 q <= x < ptr_addr L1 q + 40 /\
(q = m /\ x < ptr_addr L1 m + 16 \/ ms <> [] /\ (q = hd m ms /\ x < ptr_addr L1 q + 8 \/ q = last ms m /\ ptr_addr L1 q + 8 <= x < ptr_addr L1 q + 16)))).
{ intros x Wx. destruct (Wsub x Wx) as [Hw|[Hw|[Hw|[Hw|[Hne [Hw|Hw]]]]]].
- left. unfold WS, ASF in *. lia.
- right. left. apply src0_rwseg_img. lits. lia.
- right. left. apply src0_rwseg_img. lits. lia.
- right. right. exists m. split; [exact Km3|]. split; [lia|]. left. split; [reflexivity | lia].
- right. right. exists (hd m ms). split; [exact (Kh0 Hne)|]. split; [lia|]. right. split; [exact Hne|]. left. split; [reflexivity | lia].
- right. right. exists (last ms m). split; [exact (Khp Hne)|]. split; [lia|]. right. split; [exact Hne|]. right. split; [reflexivity | lia]. }
assert (UM : used_metas s' = used_metas s3).
{ apply used_metas_ext; [exact (proj1 (inv_keys I3)) | exact Sk |]. intros q.
destruct (sptr_eq_dec q m) as [->|Hqm]; [right; rewrite MTm, M3; destruct Mm as [E|E]; rewrite E; split; reflexivity|].
destruct (In_dec sptr_eq_dec q ms) as [Hq|Hq].
- right. destruct (MEMS q Hq) as (qp & qn & Mq & _). rewrite (MTr q _ Hq Mq), Mq. cbn. split; reflexivity.
- left. apply MTo. intros [E|E]; [exact (Hqm (eq_sym E)) | exact (Hq E)]. }
assert (RO : forall k, region_of s' k = region_of s3 k) by (intros k; unfold region_of; rewrite Srg; reflexivity).
assert (MR' : memrep B L1 s' mem').
{ refine (memrep_xfer B (m :: X) None U L1 L1 s3 s' mm0 mem' md1 I3 X3 A3 HM UM [] _ _ _ _ _ eq_refl eq_refl _ W Wdec FR _
(m :: (match ms with [] => [] | _ => [hd m ms; last ms m] end)) _ _ _ _ _ _ _ _ _).
- rewrite app_nil_r. exact Sar.
- intros p q l H. discriminate.
- rewrite Sar. exact (proj1 (inv_areas I3)).
- intros k rg H Hl Hk. rewrite RO in H. exact H.
- intros k rg H _ _. rewrite RO. exact H.
- intros; reflexivity.
-
intros x k rg Wx Hk Hl Hkd Hin. pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ HM) k rg Hk Hl) as (_ & _ & Phi & Pimg).
destruct (Wlow x Wx) as [Hlo|[Hi|(q & Hq & Hqx & _)]]; [lia | exact (Pimg x Hin Hi) |].
destruct (key_slot_area q x Hq Hqx) as (a & Ha & Hax).
pose proof (area_nonmap B (m :: X) None U L1 s3 mm0 md1 I3 HM s3 L1 a x Ha Hax
ltac:(intros k' rg' Hk' Hl' Hkd'; exists rg'; repeat split; try assumption; lia) ltac:(intros k' rg' Hk' _ _; exact Hk') ltac:(intros; reflexivity)) as [_ NM].
apply NM. exists k, rg. split; [exact Hk|]. split; [exact Hl|]. split; [exact Hkd | exact Hin].
-
intros x a Wx Ha Hax. left. destruct (areas_off_img B (m :: X) None U L1 s3 mm0 md1 I3 HM a x Ha Hax) as [NI Rx].
destruct (Wlow x Wx) as [Hlo|[Hi|(q & Hq & Hqx & Hc)]]; [lia | exfalso; exact (NI Hi) |].
destruct Hc as [[-> Hx16]|[Hne [[-> Hx8]|[-> Hx8]]]].
+ exists m. split; [left; reflexivity | lia].
+ exists (hd m ms). split; [destruct ms; [exfalso; exact (Hne eq_refl) | right; left; reflexivity] | lia].
+ exists (last ms m). split; [destruct ms; [exfalso; exact (Hne eq_refl) | right; right; left; reflexivity] | lia].
-
intros x a Wx Ha Hax. destruct (areas_off_img B (m :: X) None U L1 s3 mm0 md1 I3 HM a x Ha Hax) as [NI Rx].
destruct (Wlow x Wx) as [Hlo|[Hi|(q & Hq & Hqx & Hc)]]; [lia | exfalso; exact (NI Hi) |].
destruct Hc as [[-> Hx16]|[Hne [[-> Hx8]|[-> Hx8]]]]; [apply PRESm; lia | apply (PRESh Hne); left; lia | apply (PRESh Hne); right; lia].
-
intros q Hq. assert (Kq : In q (keys s3)).
{ destruct Hq as [<-|Hq]; [exact Km3|]. destruct ms as [|h0 rest]; [destruct Hq|]. cbn [In] in Hq. destruct Hq as [<-|[<-|[]]]; [apply Kh0; discriminate | apply Khp; discriminate]. }
destruct (key_facts (m :: X) U L1 s1 mem1 md1 q HI1 MID1 ltac:(rewrite <- K3; exact Kq)) as (_ & _ & _ & a & k & Ha & Hk & Eq). exists a, k. rewrite Ar3. auto.
-
intros q Hq.
assert (OFFW : forall q' off, In q' (keys s3) -> q' <> m -> (ms <> [] -> q' = hd m ms -> 8 <= off) -> (ms <> [] -> q' = last ms m -> off + 8 <= 8) -> 0 <= off -> off + 8 <= 40 ->
forall j, (j < 8)%nat -> ~ W (ptr_addr L1 q' + off + Z.of_nat j)).
{ intros q' off Kq' Hq'm Hnh Hnl Ho1 Ho2 j Hj Wx. destruct (key_range3 q' (ptr_addr L1 q' + off + Z.of_nat j) Kq' ltac:(lia)) as (NI & Rx & _).
destruct (Wlow _ Wx) as [Hlo|[Hi|(q2 & Hq2 & Hq2x & Hc)]]; [lia | exact (NI Hi) |].
destruct (sptr_eq_dec q2 q') as [->|Hne2].
- destruct Hc as [[E Hx16]|[Hne [[E Hx8]|[E Hx8]]]]; [exact (Hq'm E) | pose proof (Hnh Hne E); lia | pose proof (Hnl Hne E); lia].
- destruct (keys_apart3 q2 q' Hq2 Kq' Hne2); lia. }
assert (OLD : forall q' off v, In q' (keys s3) -> q' <> m -> (ms <> [] -> q' = hd m ms -> 8 <= off) -> (ms <> [] -> q' = last ms m -> off + 8 <= 8) -> 0 <= off -> off + 8 <= 40 ->
In (MCell (LMem (padd q' off)) 8 v) (meta_slot_cells q' (MT s3 q')) -> cell_mem B L1 mem' (MCell (LMem (padd q' off)) 8 v)).
{ intros q' off v Kq' H1 H2 H3 H4 H5 Hin.
destruct (key_facts (m :: X) U L1 s1 mem1 md1 q' HI1 MID1 ltac:(rewrite <- K3; exact Kq')) as (RB & _ & CE & _).
assert (Hin3 : In (MCell (LMem (padd q' off)) 8 v) (image s3)).
{ unfold image. rewrite !in_app_iff. right. left. destruct (key_facts (m :: X) U L1 s1 mem1 md1 q' HI1 MID1 ltac:(rewrite <- K3; exact Kq')) as (_ & _ & _ & a & k & Ha & Hk & Eq).
rewrite Ar3. apply (slot_cells_in_areas s3 (st_areas s1) a k _ Ha Hk). rewrite <- Eq. exact Hin. }
apply (YN2d.cell_mem_ext B L1 mm0 mem'); [| exact (memrep_cell B L1 s3 mm0 _ (mid_mem _ _ _ _ _ HM) Hin3)].
cbn [mc_w mc_loc]. intros j Hj. change (loc_addr L1 (LMem (padd q' off))) with (ptr_addr L1 (padd q' off)). rewrite ptr_addr_padd.
apply FR; [| exact (OFFW q' off Kq' H1 H2 H3 H4 H5 j Hj)]. destruct (RB (ptr_addr L1 q' + off + Z.of_nat j) ltac:(unfold META_SIZE; lia)) as (_ & _ & R). lia. }
destruct Hq as [<-|Hq].
+   rewrite MTm, M3. split; [destruct Mm as [E|E]; rewrite E; exact I|]. split; [exact I|]. cbn [lnk_prev lnk_next optr].
split; [apply cell_of_word; rewrite Z.add_0_r; exact Wm0 | apply cell_of_word; exact Wm8].
+ destruct ms as [|h0 rest] eqn:Ems; [destruct Hq|]. rewrite <- Ems in *.
assert (Hne : ms <> []) by (rewrite Ems; discriminate).
assert (Eh0 : hd m ms = h0) by (rewrite Ems; reflexivity).
destruct (HD0 h0 rest Ems) as (hn & Mh0). destruct (Wring Hne) as [Wh0 Whp].
pose proof (INlast ms m Hne) as Hlast. destruct (MEMS _ Hlast) as (lp & ln & Mlast & _).
cbn [In] in Hq. destruct Hq as [<-|[<-|[]]].
*   rewrite Eh0 in *. split; [rewrite Mh0; exact I|].
rewrite (MTr h0 _ ltac:(rewrite Ems; left; reflexivity) Mh0). rewrite sptr_eqb_refl. cbn [with_links lnk_prev lnk_next optr fst snd links_of nonused].
split; [exact I|]. split; [apply cell_of_word; rewrite Z.add_0_r; exact Wh0|].
destruct (sptr_eqb h0 (last ms m)) eqn:El.
-- apply sptr_eqb_eq in El. apply cell_of_word. rewrite El at 1. exact Whp.
-- apply sptr_eqb_neq in El. apply (OLD h0 8 (optr hn) (Kh0 Hne) (Hh0m Hne)); [intros; lia | intros _ E; exfalso; exact (El E) | lia | lia |].
rewrite Mh0. cbn [meta_slot_cells]. right. left. reflexivity.
*   split; [rewrite Mlast; exact I|].
rewrite (MTr _ _ Hlast Mlast). rewrite sptr_eqb_refl. rewrite Eh0. cbn [with_links lnk_prev lnk_next optr fst snd links_of nonused].
split; [exact I|]. split; [| apply cell_of_word; exact Whp].
destruct (sptr_eqb (last ms m) h0) eqn:El.
-- apply sptr_eqb_eq in El. apply cell_of_word. rewrite Z.add_0_r, El. rewrite Eh0 in Wh0. exact Wh0.
-- apply sptr_eqb_neq in El. apply (OLD (last ms m) 0 (optr lp) (Khp Hne) (Hhpm Hne)); [intros _ E; exfalso; rewrite Eh0 in E; exact (El E) | intros; lia | lia | lia |].
rewrite Mlast. cbn [meta_slot_cells]. left. reflexivity.
-
intros a k Ha Hk Hnin. set (q := slot_of a k) in *.
assert (Hqm : q <> m) by (intros E; apply Hnin; left; symmetry; exact E).
destruct (In_dec sptr_eq_dec q ms) as [Hq|Hq]; [| apply MTo; intros [E|E]; [exact (Hqm (eq_sym E)) | exact (Hq E)]].
destruct (MEMS q Hq) as (qp & qn & Mq & _). rewrite (MTr q _ Hq Mq), Mq.
assert (Hne : ms <> []) by (intros E; rewrite E in Hq; exact Hq).
destruct (sptr_eqb q (hd m ms)) eqn:E1; [apply sptr_eqb_eq in E1; exfalso; apply Hnin; rewrite E1; destruct ms; [exfalso; exact (Hne eq_refl) | right; left; reflexivity]|].
destruct (sptr_eqb q (last ms m)) eqn:E2; [apply sptr_eqb_eq in E2; exfalso; apply Hnin; rewrite E2; destruct ms; [exfalso; exact (Hne eq_refl) | right; right; left; reflexivity]|].
reflexivity.
- intros p H. discriminate.
- intros p c H. discriminate.
- intros p x H. discriminate.
-
intros c Hc. destruct (ctx_cells_fm s3 s' c SB EA Hc) as [-> | (Hin & off & Hloc & Hoff & Hapart)].
+ right. rewrite Hhd. unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num optr loc_addr]. rewrite (mid_ctx _ _ _ _ _ HM). change (ms_ctx B) with CTX.
replace (CTX + CTX_free_meta_head) with (LOCK + 24) by (unfold CTX_free_meta_head; lits; lia). exact Wfmh.
+ left. split; [exact Hin|]. intros k Hk. rewrite Hloc. change (ms_ctx B) with CTX. intros Wx.
destruct (In_ctx_cells s3 c Hin) as (off' & Hloc' & _ & Hsz). rewrite Hloc in Hloc'. injection Hloc' as <-.
destruct (Wlow _ Wx) as [Hlo|[Hi|(q & Hq & Hqx & _)]]; [unfold CTX_SIZE in *; lia | |].
* destruct (Wsub _ Wx) as [Hw|[Hw|[Hw|[Hw|[Hne [Hw|Hw]]]]]].
-- unfold WS, ASF, CTX_SIZE in *. lia.
-- lits. unfold CTX_SIZE in *. lia.
-- unfold CTX_free_meta_head in Hapart. lits. lia.
-- destruct (key_range3 m (CTX + off + Z.of_nat k) Km3 ltac:(lia)) as (NI & _). apply NI. apply (so_ctx_img _ SO). change (ms_ctx B) with CTX. unfold CTX_SIZE in *. lia.
-- destruct (key_range3 (hd m ms) (CTX + off + Z.of_nat k) (Kh0 Hne) ltac:(lia)) as (NI & _). apply NI. apply (so_ctx_img _ SO). change (ms_ctx B) with CTX. unfold CTX_SIZE in *. lia.
-- destruct (key_range3 (last ms m) (CTX + off + Z.of_nat k) (Khp Hne) ltac:(lia)) as (NI & _). apply NI. apply (so_ctx_img _ SO). change (ms_ctx B) with CTX. unfold CTX_SIZE in *. lia.
* destruct (key_range3 q (CTX + off + Z.of_nat k) Hq Hqx) as (NI & _). apply NI. apply (so_ctx_img _ SO). change (ms_ctx B) with CTX. unfold CTX_SIZE in *. lia. }
pose proof (YN2i.ledger_same B L1 s3 md1 (mid_ledger _ _ _ _ _ HM) (mid_ledgerx _ _ _ _ _ HM) s' md1 Srg Sbrk eq_refl eq_refl eq_refl) as [LG2 LX2].
split.
- exact SO.
- exact MR'.
- eapply (tail_geom_xfer B (m :: X) None U L1 L1 s3 s' mm0 md1 I3 X3 HM); [exact UM | intros k rg H _ _; rewrite RO; exact H | reflexivity | intros; reflexivity].
- apply (YN2d.statics_ok_ext B s3 0 mm0); [| exact (mid_statics _ _ _ _ _ HM)]. intros x Hx.
pose proof (so_img_hi _ SO x (so_statics_img _ SO x Hx)) as Hhi. apply FR; [lia|]. intros Wx.
destruct (Wlow _ Wx) as [Hlo|[Hi|(q & Hq & Hqx & _)]]; [lia | | destruct (key_range3 q x Hq Hqx) as (NI & _); exact (NI (so_statics_img _ SO x Hx))].
destruct (Wsub _ Wx) as [Hw|[Hw|[Hw|[Hw|[Hne [Hw|Hw]]]]]].
+ unfold WS, ASF in *. lia.
+ exact (src0_ENS x ltac:(change (errno_addr B) with ERRNO; exact Hw) Hx).
+ apply (src0_SNC x Hx). change (ms_ctx B) with CTX. unfold CTX_SIZE. lits. lia.
+ destruct (key_range3 m x Km3 ltac:(lia)) as (NI & _). exact (NI (so_statics_img _ SO x Hx)).
+ destruct (key_range3 (hd m ms) x (Kh0 Hne) ltac:(lia)) as (NI & _). exact (NI (so_statics_img _ SO x Hx)).
+ destruct (key_range3 (last ms m) x (Khp Hne) ltac:(lia)) as (NI & _). exact (NI (so_statics_img _ SO x Hx)).
- exact LG2.
- exact LX2.
- apply (YN2d.layout_ok_same L1 s3 s' (mid_layout _ _ _ _ _ HM) Srg). unfold footprint. rewrite Sar, Srg. f_equal. f_equal.
apply YN2c.flat_map_ext_in. intros k _. rewrite RO. reflexivity.
- exact (mid_ctx _ _ _ _ _ HM).
- exact (mid_sec _ _ _ _ _ HM).
- exact (mid_md _ _ _ _ _ HM).
Qed.
Lemma mbyte_present : forall mm x b, mbyte src0segs mm x = Some b -> present mm x -> mm (Z_to_bv 64 x) = Some b.
Proof. intros mm x b Hb [b' Hb']. unfold mbyte in Hb. rewrite Hb' in Hb. rewrite Hb'. exact Hb. Qed.
Lemma station_FM2 : forall ms h0 rest hn mm0 ms2,
ring_ok (flinks (m :: X) s3) (st_free_meta_head s3) ms ->
(forall q, In q ms -> exists qp qn, MT s3 q = Some (MFree qp qn) /\ memb q (m :: X) = false) ->
~ In m ms -> ms = h0 :: rest -> MT s3 h0 = Some (MFree (Some (last ms m)) hn) ->
midrep B L1 s3 mm0 md1 -> st_ok src0segs E8 ss_fm2 ms2 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WD1 x -> ms_mem ms2 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)) ->
let hp := last ms m in let E9 := ewset E8 88 (Z_to_bv 64 (ptr_addr L1 hp)) in
st_ok src0segs E9 ss_FM2 ms2 /\ env_agree 88 E8 E9 /\ env_agree 40 E00 E9 /\
ew E9 88 = Z_to_bv 64 (ptr_addr L1 hp) /\ ew E9 87 = Z_to_bv 64 (ptr_addr L1 h0) /\ ew E9 40 = Z_to_bv 64 (ptr_addr L1 m) /\
In h0 (keys s3) /\ In hp (keys s3) /\ h0 <> m /\ hp <> m.
Proof.
intros ms h0 rest hn mm0 ms2 FRg MEMS Hmn Ems Mh0 HM HS F2 hp E9. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
destruct E6_factsD as (E10 & E33 & E2 & U40). destruct s3_factsD as (I3 & X3 & A3 & K3 & M3 & _).
pose proof fmh_facts as (Hr & Hal & Wf & Hfm). destruct skels as (_ & _ & _ & _ & _ & _ & AT88 & _ & SKf2 & _ & EFM2).
assert (Ehd : st_free_meta_head s3 = Some h0) by (destruct FRg as [_ HD]; rewrite HD, Ems; reflexivity).
destruct (Hfm h0 Ehd) as [Efmh Kh0].
assert (INlast : forall (l : list sptr) d, l <> [] -> In (last l d) l).
{ intros l. induction l as [|x t IH]; intros d Hne; [exfalso; exact (Hne eq_refl)|]. destruct t as [|y t']; [left; reflexivity|]. right. apply IH. discriminate. }
assert (Hhp : In hp ms) by (apply INlast; rewrite Ems; discriminate).
destruct (MEMS hp Hhp) as (lp & ln & Mhp & _). pose proof (In_keys_of_MT _ _ _ Mhp) as Khp.
assert (Hh0m : h0 <> m) by (intros ->; apply Hmn; rewrite Ems; left; reflexivity).
assert (Hhpm : hp <> m) by (intros E; apply Hmn; rewrite <- E; exact Hhp).
assert (Km3 : In m (keys s3)) by (rewrite K3; exact Km).
assert (E8_87 : ew E8 87 = Z_to_bv 64 (ptr_addr L1 h0)) by (subst E8; rewrite ew_ewset_same, Efmh; reflexivity).
assert (E8_40 : ew E8 40 = Z_to_bv 64 (ptr_addr L1 m)) by (subst E8; rewrite ew_ewset_other by lia; exact E6_40).
assert (AG8 : env_agree 40 E00 E8) by (eapply env_agree_trans; [exact AG6 | eapply env_agree_le; [| apply env_agree_ewset]; lia]).
assert (AG89 : env_agree 88 E8 E9) by (apply env_agree_ewset).
assert (AG9 : env_agree 40 E00 E9) by (eapply env_agree_trans; [exact AG8 | eapply env_agree_le; [| exact AG89]; lia]).
assert (E9_88 : ew E9 88 = Z_to_bv 64 (ptr_addr L1 hp)) by (subst E9; apply ew_ewset_same).
assert (E9_87 : ew E9 87 = Z_to_bv 64 (ptr_addr L1 h0)) by (rewrite <- E8_87; apply (proj1 AG89); lia).
assert (E9_40 : ew E9 40 = Z_to_bv 64 (ptr_addr L1 m)) by (rewrite <- E8_40; apply (proj1 AG89); lia).
pose proof (key_range3 h0) as Rh0. specialize (Rh0) . pose proof (key_range3 hp) as Rhp.
destruct (Rh0 (ptr_addr L1 h0) Kh0 ltac:(lia)) as (_ & Rh0a & _). destruct (Rh0 (ptr_addr L1 h0 + 39) Kh0 ltac:(lia)) as (_ & Rh0b & _).
destruct (Rhp (ptr_addr L1 hp) Khp ltac:(lia)) as (_ & Rhpa & _). destruct (Rhp (ptr_addr L1 hp + 39) Khp ltac:(lia)) as (_ & Rhpb & _).
assert (U87 : bv_unsigned (ew E9 87) = ptr_addr L1 h0) by (rewrite E9_87; apply lit64_small; lia).
assert (U88 : bv_unsigned (ew E9 88) = ptr_addr L1 hp) by (rewrite E9_88; apply lit64_small; lia).
assert (ALp : ptr_addr L1 hp mod 8 = 0) by exact (proj1 (proj2 (key_facts (m :: X) U L1 s1 mem1 md1 hp HI1 MID1 ltac:(rewrite <- K3; exact Khp)))).
assert (OFF1 : forall q x, In q (keys s3) -> q <> m -> ptr_addr L1 q <= x < ptr_addr L1 q + 40 -> ~ WD1 x).
{ intros q x Kq Hqm Hx Wx. destruct (key_range3 q x Kq Hx) as (NI & Rx & _). unfold WD1, WD0, WS in Wx.
destruct Wx as [[Hw|[Hw|Hw]]|Hw]; [unfold ASF in *; lia | apply NI; apply src0_rwseg_img; lits; lia | destruct (keys_apart3 q m Kq Km3 Hqm); lia | apply NI; apply src0_rwseg_img; lits; lia]. }
split; [| split; [exact AG89 | split; [exact AG9 | split; [exact E9_88 | split; [exact E9_87 | split; [exact E9_40 | split; [exact Kh0 | split; [exact Khp | exact (conj Hh0m Hhpm)]]]]]]]].
assert (HS0 : st_ok src0segs E9 ss_fm2 ms2) by (eapply (st_ok_agree src0segs 88 E8 E9); [exact HS | exact AG89 | exact AT88]).
rewrite EFM2.
assert (APART : forall lo hi r q, In q (keys s3) -> q <> m -> ptr_addr L1 q <= lo -> hi <= ptr_addr L1 q + 40 -> lo < hi -> In r (ss_mem ss_fm2) ->
hi <= base_val E9 (r_base r) + r_lo r \/ base_val E9 (r_base r) + r_hi r <= lo).
{ intros lo hi r q Kq Hqm Hlo Hhi Hlh Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite SKf2 in Hr'.
apply (apart_fm E9 lo hi r AG9 E9_40 Hlh); [| destruct (keys_apart3 q m Kq Km3 Hqm); lia | exact Hr'].
intros x Hx. destruct (key_range3 q x Kq ltac:(lia)) as (NI & Rx & _). split; [exact NI | lia]. }
assert (HS1 : st_ok src0segs E9 (mkSS (ss_pc ss_fm2) (ss_regs ss_fm2) (R_hp :: ss_mem ss_fm2) None (ss_facts ss_fm2)) ms2).
{ apply (st_ok_add_region src0segs E9 _ _ R_hp HS0); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_hp ms_mem]; rewrite U88; [lia | lia | | apply Forall_nil].
intros o Ho. apply present_writable. apply (present_keep mm0); [apply F2; [lia | apply (OFF1 hp _ Khp Hhpm); lia]|].
exact (key_present mm0 hp (ptr_addr L1 hp + o) HM Khp ltac:(lia)).
- apply Forall_forall. intros r Hr'. unfold extent_disjoint. cbn [r_base r_lo r_hi R_hp base_val]. rewrite U88. exact (APART (ptr_addr L1 hp + 8) (ptr_addr L1 hp + 16) r hp Khp Hhpm ltac:(lia) ltac:(lia) ltac:(lia) Hr'). }
assert (HS2 : st_ok src0segs E9 (mkSS (ss_pc ss_fm2) (ss_regs ss_fm2) (R_hd :: R_hp :: ss_mem ss_fm2) None (ss_facts ss_fm2)) ms2).
{ apply (st_ok_add_region src0segs E9 _ _ R_hd HS1); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_hd ms_mem]; rewrite U87; [lia | lia | |].
+ intros o Ho. apply present_writable. apply (present_keep mm0); [apply F2; [lia | apply (OFF1 h0 _ Kh0 Hh0m); lia]|].
exact (key_present mm0 h0 (ptr_addr L1 h0 + o) HM Kh0 ltac:(lia)).
+ apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs E9 (ms_mem ms2) (ptr_addr L1 h0) 0 (SOff 88 0) (ptr_addr L1 hp)); [apply den_off0; exact E9_88|].
apply (word_mem_ext1 mm0); [intros k Hk; apply F2; [lia | apply (OFF1 h0 _ Kh0 Hh0m); lia]|].
replace (ptr_addr L1 h0 + 0) with (ptr_addr L1 (padd h0 META_prev)) by (rewrite ptr_addr_padd; unfold META_prev; lia).
change (ptr_addr L1 hp) with (sval_num L1 (VP hp)). apply (image_word L1 s3 mm0 md1 _ _ HM); [| intros z; discriminate].
destruct (key_facts (m :: X) U L1 s1 mem1 md1 h0 HI1 MID1 ltac:(rewrite <- K3; exact Kh0)) as (_ & _ & CE & _).
pose proof (CE (MCell (LMem (padd h0 META_prev)) 8 (VP hp))) as CE'. rewrite <- M3, Mh0 in CE'.
assert (Him : image s3 = image s3) by reflexivity.
destruct s3_factsD as (_ & _ & _ & _ & _ & _ & _ & Ar3 & _).
unfold image. rewrite !in_app_iff. right. left.
destruct (key_facts (m :: X) U L1 s1 mem1 md1 h0 HI1 MID1 ltac:(rewrite <- K3; exact Kh0)) as (_ & _ & _ & a & k & Ha & Hk & Eq).
rewrite Ar3. apply (slot_cells_in_areas s3 (st_areas s1) a k _ Ha Hk). rewrite <- Eq, Mh0. cbn [meta_slot_cells optr]. left. reflexivity.
- apply Forall_cons.
+ unfold extent_disjoint. cbn [r_base r_lo r_hi R_hd R_hp base_val]. rewrite U87, U88.
destruct (sptr_eq_dec h0 hp) as [E|Hne]; [rewrite E; left; lia|]. destruct (keys_apart3 h0 hp Kh0 Khp Hne); lia.
+ apply Forall_forall. intros r Hr'. unfold extent_disjoint. cbn [r_base r_lo r_hi R_hd base_val]. rewrite U87. exact (APART (ptr_addr L1 h0 + 0) (ptr_addr L1 h0 + 8) r h0 Kh0 Hh0m ltac:(lia) ltac:(lia) ltac:(lia) Hr'). }
apply (st_ok_add_fact src0segs E9 _ ms2 88 F_ptr0) in HS2. 2:{ unfold afact_ok, F_ptr0. cbn [af_lo af_hi af_al2]. rewrite U88. change (2 ^ 3) with 8. repeat split; lia. }
exact HS2.
Qed.
Lemma finish_fm : forall Ef ssF ms4 s' i rstk ig,
st_ok src0segs Ef ssF ms4 -> finalS_check ssF (SLit (2 ^ 64 - 1)) = true -> env_agree 40 E00 Ef ->
nth_error (ss_mem ssF) i = Some rstk -> r_base rstk = Some 2%nat -> r_wlo rstk = - ASF -> r_whi rstk = 0 -> nth_error (ss_mem ssF) ig = Some R_guard ->
Inv X None U s' -> rawX X s' -> as_keep X A s' -> (forall q am, usedX X s' q am <-> usedX X A q am) -> ama_ok s' -> bounded s' ->
st_regions s' = st_regions s1 ->
midrep B L1 s' (ms_mem ms4) md1 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WSn x -> ~ (ERRNO <= x < ERRNO + 4) -> ~ (CTX <= x < CTX + CTX_SIZE) -> ~ in_nonmap_region L1 s' x ->
ms_mem ms4 (Z_to_bv 64 x) = mem1 (Z_to_bv 64 x)) ->
(forall a, ERRNO <= a < ERRNO + 4 -> writable_at src0segs (ms_mem ms4) a) ->
(forall a, sp - stk <= a < sp - ASF -> ms_mem ms4 (Z_to_bv 64 a) = mem1 (Z_to_bv 64 a)) ->
SR src0segs (mkCfg ms4 md1) (POSTn (-1, s')).
Proof.
intros Ef ssF ms4 s' i rstk ig HS4 CK HA Hi Hb Hwlo Hwhi Hig HI' RX' AKs EU AMA' BND' Rs MID4 FR4 ERRW4 STK4.
pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7). assert (Esp : sp = bv_unsigned (getr regs 2)) by reflexivity. assert (EASF : ASF = 384) by reflexivity.
assert (XCs : Xclean X s') by (intros x am Hx Hm'; destruct (RX' x Hx) as [EXR|EXR]; rewrite EXR in Hm'; discriminate).
destruct (finalS L A regs mem sc stk PRE g j1 j2 Ef ssF ms4 (SLit (2 ^ 64 - 1)) CK HS4 HA) as (PRS & E1 & Hra & Hpc & Hrv & RA0).
apply (SR_final_retS Ef ssF ms4 md1 _ HS4 Hrv Hpc Hra); [rewrite E1; exact P1 | exact Mh1 | exact Mlz1 |].
exists L1, (ms_regs ms4), (ms_mem ms4), md1. cbn [fst snd].
split; [rewrite E1; reflexivity|]. split; [exact MID4|]. split; [exact AMA'|]. split; [exact BND'|]. split.
{ apply (rsv_ok_xfer X U A regs HI XR RSV X s' HI' XCs). intros g' am H. exact (proj1 (EU g' am) H). }
split. { apply (span_ok_xfer X A SPOK X s' XCs). intros g' am H. exact (proj1 (EU g' am) H). }
split; [exact LE1|]. split; [exact PRS|]. split; [exact VM1|]. split.
{ intros x Hx Nc No No' Nn Ns. unfold call_scratch, spZ in Ns. change (errno_addr B) with ERRNO in Ns. fold sp in Ns. change (ms_ctx B) with CTX in Nc.
assert (Nn1 : ~ in_nonmap_region L1 s1 x) by (intros [P Q]; apply Nn; split; [| intros (r & rg & H); apply Q; exists r, rg; unfold region_of; rewrite <- Rs; exact H]; destruct P as (r & rg & H); exists r, rg; unfold region_of; rewrite Rs; exact H).
rewrite (FR4 x Hx) by (unfold WS; first [lia | exact Nc | exact Nn]). apply (FR1 x Hx); [unfold WS; lia | lia | exact Nc | exact Nn1]. }
split.
{ intros a Ha. unfold call_scratch, spZ in Ha. change (errno_addr B) with ERRNO in Ha. fold sp in Ha. destruct Ha as [Ha|Ha].
- destruct (Z_lt_le_dec a (sp - ASF)) as [Hlo|Hhi].
+ apply (writable_ext1 mem1); [apply STK4; lia |]. apply (writable_ext1 mem); [apply FR1; [lia | unfold WS; lia | lits; lia | lits; unfold CTX_SIZE; lia | intros Hnm; destruct (nonmap_low regs L1 s1 mem1 md1 a MID1 Hnm); lia] |].
apply P5. lia.
+ apply (writable_of_region regs Ef ssF ms4 i rstk a HS4 Hi). rewrite Hb, Hwlo, Hwhi. cbn [base_val]. rewrite (agree_reg' Ef 2 HA ltac:(lia)).
replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity). fold sp. lia.
- apply ERRW4. exact Ha. }
split; [rewrite RA0; apply bv_eq; reflexivity|].
split; [intros H; lia|]. split; [exact AKs | exact (guard_of_state L A regs sc g j1 j2 Ef ssF ms4 ig HS4 HA Hig)].
Qed.
Theorem leaf_free : forall c, KfPost regs sc s1 L1 mem1 md1 E6 c -> mreal src0segs c (ibind ((free_meta m ;; ret None) s3) KS) POSTn.
Proof.
intros c (ms0 & -> & HS0 & HM0 & HF0). pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7). assert (Esp : sp = bv_unsigned (getr regs 2)) by reflexivity. assert (EASF : ASF = 384) by reflexivity.
destruct E6_factsD as (E10 & E33 & E2 & U40). destruct s3_factsD as (I3 & X3 & A3 & K3 & M3 & _).
destruct fm_shape3 as (ms & s' & FRg & MEMS & Hmn & HD0 & Efm & FP & HI' & EU & RXs & AMAs & BNDs & Rs & As & AKs).
pose proof fmh_facts as (Hr & Hal & Wf & Hfm). destruct skels as (W0 & W1 & W2 & W3 & W4 & _).
pose proof finals_fm as (CK1 & CK2 & FM1 & (rs1 & Hrs1 & Hb1 & Hlo1 & Hhi1) & FM2 & (rs2 & Hrs2 & Hb2 & Hlo2 & Hhi2)).
assert (Km3 : In m (keys s3)) by (rewrite K3; exact Km).
assert (INlast : forall (l : list sptr) d, l <> [] -> In (last l d) l).
{ intros l. induction l as [|x t IH]; intros d Hne; [exfalso; exact (Hne eq_refl)|]. destruct t as [|y t']; [left; reflexivity|]. right. apply IH. discriminate. }
assert (Et : ibind ((free_meta m ;; ret None) s3) KS = IRet (-1, s')).
{ unfold bind at 1. rewrite Efm. reflexivity. }
rewrite Et. cbn [mreal].
set (mm0 := ms_mem ms0) in *.
destruct (mslot_facts X U L A regs sc g j1 j2 m s1 L1 md1 HI1 RX1 Mm Km AMA1 BND1 mm0 HM0) as [ZB RB].
assert (ZEROS : forall Ef ssF ms4 j, st_ok src0segs Ef ssF ms4 -> ew Ef 40 = Z_to_bv 64 (ptr_addr L1 m) ->
nth_error (ss_mem ssF) j = Some (YP09.mkRegion (Some 40%nat) 0 40 0 40 (firstn 2 (r_chunks (nth j (ss_mem ssF) R_mslot)) ++ [mkChunk 16 (CVal 8 (SLit 0)); mkChunk 24 (CVal 8 (SLit 0)); mkChunk 32 (CVal 8 (SLit 0))])) ->
forall x, ptr_addr L1 m + 16 <= x < ptr_addr L1 m + 40 -> ms_mem ms4 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
{ intros Ef ssF ms4 j HS4 E40 Hj x Hx.
assert (Uf : bv_unsigned (ew Ef 40) = ptr_addr L1 m) by (rewrite E40, <- E6_40; exact U40).
destruct (RB x ltac:(lia)) as (PR0 & NI & Rx).
rewrite (mbyte_present mm0 x (Z_to_bv 8 0)); [| replace x with (ptr_addr L1 m + (x - ptr_addr L1 m)) by lia; apply ZB; lia | exact PR0].
apply (mbyte_present (ms_mem ms4) x (Z_to_bv 8 0)).
- assert (CASE : exists off, In off [16; 24; 32] /\ ptr_addr L1 m + off <= x < ptr_addr L1 m + off + 8).
{ destruct (Z_lt_le_dec x (ptr_addr L1 m + 24)); [exists 16; split; [inlist | lia]|]. destruct (Z_lt_le_dec x (ptr_addr L1 m + 32)); [exists 24; split; [inlist | lia]|]. exists 32; split; [inlist | lia]. }
destruct CASE as (off & Hoff & Hxo). replace x with (bv_unsigned (ew Ef 40) + off + (x - ptr_addr L1 m - off)) by lia.
apply (zword_of_chunk_at regs Ef ssF ms4 j _ 40 off HS4 Hj eq_refl); [| lia]. cbn [r_chunks]. apply in_app_iff. right.
cbn [In] in Hoff. destruct Hoff as [<-|[<-|[<-|[]]]]; inlist.
- apply (writable_off_img_present (ms_mem ms4) x ltac:(lia) ltac:(intros Hi; exact (NI (in_img1_img x Hi)))).
apply (writable_of_region regs Ef ssF ms4 j _ x HS4 Hj). cbn [r_base r_wlo r_whi base_val]. rewrite Uf. lia. }
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E6 ss_Kf ss_fm0); [exact Mh1 | exact Mlz1 | exact HS0 | apply run_Kf |].
intros ms1 HS1 Hfr1.
assert (F1 : forall x, 0 <= x < 2 ^ 64 -> ~ WD0 x -> ms_mem ms1 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
{ apply (frame_keep WD0 E6 (ss_mem ss_Kf) SK0 mm0 _ mm0 Hfr1 W0); [intros b lo hi x Hin Hx; exact (SK0_WD0 E6 b lo hi x AG6 E6_40 Hin Hx) | intros; reflexivity]. }
destruct (station_FM1 ms1 mm0 HS1 HM0 HF0 F1) as (HS2 & AG68 & AG8 & E8_87 & E8_40).
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E8 ss_FM1 ss_fm1); [exact Mh1 | exact Mlz1 | exact HS2 | apply run_FM1 |].
intros ms3 HS3 Hfr3.
assert (F3 : forall x, 0 <= x < 2 ^ 64 -> ~ WD1 x -> ms_mem ms3 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
{ apply (frame_keep WD1 E8 (ss_mem ss_FM1) SK1 (ms_mem ms1) _ mm0 Hfr3 W1); [intros b lo hi x Hin Hx; exact (SK1_WD1 E8 b lo hi x AG8 E8_40 Hin Hx) |].
intros x Hx Hw. apply F1; [exact Hx | intros Hw0; apply Hw; left; exact Hw0]. }
assert (ERRW_of : forall Ef ssF ms4 j, st_ok src0segs Ef ssF ms4 -> nth_error (ss_mem ssF) j = Some (YP09.mkRegion None ERRNO (ERRNO + 4) ERRNO (ERRNO + 4) [mkChunk ERRNO (CVal 4 (SLit 12))]) ->
forall a, ERRNO <= a < ERRNO + 4 -> writable_at src0segs (ms_mem ms4) a).
{ intros Ef ssF ms4 j HS4 Hj a Ha. apply (writable_of_region regs Ef ssF ms4 j _ a HS4 Hj). cbn [r_base r_wlo r_whi base_val]. lia. }
assert (NONMAP : forall x, ptr_addr L1 m <= x < ptr_addr L1 m + 40 \/ (exists q, In q ms /\ ptr_addr L1 q <= x < ptr_addr L1 q + 40) -> in_nonmap_region L1 s' x).
{ intros x Hx. assert (Hq : exists q, In q (keys s3) /\ ptr_addr L1 q <= x < ptr_addr L1 q + 40).
{ destruct Hx as [Hx|(q & Hq & Hx)]; [exists m; exact (conj Km3 Hx)|]. exists q. destruct (MEMS q Hq) as (qp & qn & Mq & _). exact (conj (In_keys_of_MT _ _ _ Mq) Hx). }
destruct Hq as (q & Kq & Hqx). destruct (key_slot_area q x Kq Hqx) as (a & Ha & Hax).
apply (area_nonmap B (m :: X) None U L1 s3 mm0 md1 I3 HM0 s' L1 a x Ha Hax).
- intros k rg Hk Hl Hkd. exists rg. unfold region_of in *. rewrite Rs. destruct s3_factsD as (_ & _ & _ & _ & _ & _ & R3 & _). rewrite R3 in Hk. repeat split; try assumption. lia.
- intros k rg Hk _ _. unfold region_of in *. rewrite Rs in Hk. destruct s3_factsD as (_ & _ & _ & _ & _ & _ & R3 & _). rewrite R3. exact Hk.
- intros; reflexivity. }
apply (SR_sym_branch src0segs E8 ss_fm1 ms3 md1 _ BC_EQ (SOff 87 0) (SLit 0) HS3).
-
intros Hb HSb. rewrite (den_off0 E8 87 fmh E8_87), den_lit, branch_eq, !lit64_small in Hb by lia. apply Z.eqb_eq in Hb.
assert (Ems : ms = []).
{ destruct FRg as [_ HD]. destruct ms as [|h0 rest]; [reflexivity|]. exfalso. cbn [hd_error] in HD. destruct (Hfm h0 HD) as [Efmh Kh0].
destruct (key_range3 h0 (ptr_addr L1 h0) Kh0 ltac:(lia)) as (_ & R0 & _). lia. }
subst ms. cbn [hd last] in *.
change (add_cond ss_fm1 (mkAC BC_EQ (SOff 87 0) (SLit 0))) with (add_cond ss_fm1 C_fe) in HSb.
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E8 (add_cond ss_fm1 C_fe) ss_feE); [exact Mh1 | exact Mlz1 | exact HSb | apply run_fe |].
intros ms4 HS4 Hfr4.
assert (F4 : forall x, 0 <= x < 2 ^ 64 -> ~ WD1 x -> ms_mem ms4 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
{ apply (frame_keep WD1 E8 (ss_mem (add_cond ss_fm1 C_fe)) SK1 (ms_mem ms3) _ mm0 Hfr4 W2); [intros b lo hi x Hin Hx; exact (SK1_WD1 E8 b lo hi x AG8 E8_40 Hin Hx) | exact F3]. }
assert (R0 : nth_error (ss_mem ss_feE) 0 = Some (YP09.mkRegion None (LOCK + 24) (LOCK + 32) (LOCK + 24) (LOCK + 32) [mkChunk (LOCK + 24) (CVal 8 (SOff 40 0))])) by (apply (f_equal (fun l => nth_error l 0)) in FM1; exact FM1).
assert (R1 : nth_error (ss_mem ss_feE) 1 = Some (YP09.mkRegion None ERRNO (ERRNO + 4) ERRNO (ERRNO + 4) [mkChunk ERRNO (CVal 4 (SLit 12))])) by (apply (f_equal (fun l => nth_error l 1)) in FM1; exact FM1).
assert (R2 : nth_error (ss_mem ss_feE) 2 = Some (YP09.mkRegion (Some 40%nat) 0 40 0 40 [mkChunk 8 (CVal 8 (SOff 40 0)); mkChunk 0 (CVal 8 (SOff 40 0)); mkChunk 16 (CVal 8 (SLit 0)); mkChunk 24 (CVal 8 (SLit 0)); mkChunk 32 (CVal 8 (SLit 0))]))
by (apply (f_equal (fun l => nth_error l 2)) in FM1; exact FM1).
pose proof (ZEROS E8 ss_feE ms4 2%nat HS4 E8_40 ltac:(rewrite R2; reflexivity)) as Z4.
set (W := fun x => WD1 x /\ ~ (ptr_addr L1 m + 16 <= x < ptr_addr L1 m + 40)).
assert (HM4 : midrep B L1 s' (ms_mem ms4) md1).
{ apply (midrep_fm [] s' mm0 (ms_mem ms4) W FRg MEMS Hmn HD0 FP HM0).
- intros x. subst W. unfold WD1, WD0, WS. lia.
- intros x Hx HW. destruct (Z_le_dec (ptr_addr L1 m + 16) x); [destruct (Z_lt_dec x (ptr_addr L1 m + 40)); [apply Z4; lia|]|]; (apply F4; [exact Hx | intros HW1; apply HW; split; [exact HW1 | lia]]).
- intros x [HW1 Hn16]. unfold WD1, WD0 in HW1. cbn [hd last]. destruct HW1 as [[Hw|[Hw|Hw]]|Hw]; [left; exact Hw | right; left; exact Hw | right; right; right; left; lia | right; right; left; exact Hw].
- intros x Hx. destruct (RB x ltac:(lia)) as (_ & NI & Rx). apply (writable_off_img_present _ x ltac:(lia) ltac:(intros Hi; exact (NI (in_img1_img x Hi)))).
apply (writable_of_region regs E8 ss_feE ms4 2 _ x HS4 R2). cbn [r_base r_wlo r_whi base_val]. rewrite (proj1 AG68 40%nat), U40 by lia. lia.
- intros H. exfalso. exact (H eq_refl).
- cbn [hd]. apply (word_of_chunk regs E8 ss_feE ms4 0 _ (LOCK + 24) (SOff 40 0) _ HS4 R0 eq_refl ltac:(left; reflexivity)). exact (den_off0 E8 40 _ E8_40).
- cbn [last]. replace (ptr_addr L1 m) with (bv_unsigned (ew E8 40) + 0) at 1 by (rewrite (proj1 AG68 40%nat) by lia; lia).
apply (word_of_chunk_at E8 ss_feE ms4 2 _ 40 0 (SOff 40 0) _ HS4 R2 eq_refl ltac:(right; left; reflexivity)). exact (den_off0 E8 40 _ E8_40).
- cbn [hd]. replace (ptr_addr L1 m + 8) with (bv_unsigned (ew E8 40) + 8) by (rewrite (proj1 AG68 40%nat) by lia; lia).
apply (word_of_chunk_at E8 ss_feE ms4 2 _ 40 8 (SOff 40 0) _ HS4 R2 eq_refl ltac:(left; reflexivity)). exact (den_off0 E8 40 _ E8_40).
- intros H. exfalso. exact (H eq_refl). }
apply (finish_fm E8 ss_feE ms4 s' 4%nat rs1 6%nat HS4 CK1 AG8 Hrs1 Hb1 Hlo1 Hhi1 ltac:(vm_compute; reflexivity) HI' RXs AKs EU AMAs BNDs Rs HM4).
+ intros x Hx Nw Ne Nc Nn. rewrite (F4 x Hx); [apply HF0; [exact Hx | exact Nw | exact Nc]|].
unfold WD1, WD0. intros [[Hw|[Hw|Hw]]|Hw]; [exact (Nw Hw) | exact (Ne Hw) | apply Nn; apply NONMAP; left; exact Hw | apply Nc; unfold CTX_SIZE; lits; lia].
+ exact (ERRW_of E8 ss_feE ms4 1%nat HS4 R1).
+ intros a Ha. rewrite (F4 a ltac:(lia)); [apply HF0; [lia | unfold WS; lia | unfold CTX_SIZE; lits; lia]|].
unfold WD1, WD0, WS. intros [[Hw|[Hw|Hw]]|Hw]; [lia | lits; lia | destruct (RB a ltac:(lia)) as (_ & _ & Ra); lia | lits; lia].
-
intros Hb HSb. rewrite (den_off0 E8 87 fmh E8_87), den_lit, branch_eq, !lit64_small in Hb by lia. apply Z.eqb_neq in Hb.
destruct ms as [|h0 rest] eqn:Ems; [exfalso; apply Hb; unfold fmh; destruct FRg as [_ HD]; rewrite HD; reflexivity|]. rewrite <- Ems in *.
assert (Hne : ms <> []) by (rewrite Ems; discriminate).
destruct (HD0 h0 rest Ems) as (hn & Mh0).
change (add_cond ss_fm1 (mkAC (neg_bc BC_EQ) (SOff 87 0) (SLit 0))) with (add_cond ss_fm1 C_fne) in HSb.
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E8 (add_cond ss_fm1 C_fne) ss_fm2); [exact Mh1 | exact Mlz1 | exact HSb | apply run_fne |].
intros ms4 HS4 Hfr4.
assert (F4 : forall x, 0 <= x < 2 ^ 64 -> ~ WD1 x -> ms_mem ms4 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
{ apply (frame_keep WD1 E8 (ss_mem (add_cond ss_fm1 C_fne)) SK1 (ms_mem ms3) _ mm0 Hfr4 W3); [intros b lo hi x Hin Hx; exact (SK1_WD1 E8 b lo hi x AG8 E8_40 Hin Hx) | exact F3]. }
destruct (station_FM2 ms h0 rest hn mm0 ms4 FRg MEMS Hmn Ems Mh0 HM0 HS4 F4) as (HS5 & AG89 & AG9 & E9_88 & E9_87 & E9_40 & Kh0 & Khp & Hh0m & Hhpm).
set (hp := last ms m) in *. set (E9 := ewset E8 88 (Z_to_bv 64 (ptr_addr L1 hp))) in *.
assert (Eh0 : hd m ms = h0) by (rewrite Ems; reflexivity).
destruct (key_range3 h0 (ptr_addr L1 h0) Kh0 ltac:(lia)) as (_ & Rh0a & _). destruct (key_range3 h0 (ptr_addr L1 h0 + 39) Kh0 ltac:(lia)) as (_ & Rh0b & _).
destruct (key_range3 hp (ptr_addr L1 hp) Khp ltac:(lia)) as (_ & Rhpa & _). destruct (key_range3 hp (ptr_addr L1 hp + 39) Khp ltac:(lia)) as (_ & Rhpb & _).
assert (U87 : bv_unsigned (ew E9 87) = ptr_addr L1 h0) by (rewrite E9_87; apply lit64_small; lia).
assert (U88 : bv_unsigned (ew E9 88) = ptr_addr L1 hp) by (rewrite E9_88; apply lit64_small; lia).
assert (U40' : bv_unsigned (ew E9 40) = ptr_addr L1 m) by (rewrite E9_40, <- E6_40; exact U40).
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E9 ss_FM2 ss_fneE); [exact Mh1 | exact Mlz1 | exact HS5 | apply run_FM2 |].
intros ms5 HS6 Hfr5.
assert (F5 : forall x, 0 <= x < 2 ^ 64 -> ~ WD2 (ptr_addr L1 h0) (ptr_addr L1 hp) x -> ms_mem ms5 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
{ apply (frame_keep (WD2 (ptr_addr L1 h0) (ptr_addr L1 hp)) E9 (ss_mem ss_FM2) SK2 (ms_mem ms4) _ mm0 Hfr5 W4); [intros b lo hi x Hin Hx; exact (SK2_WD2 E9 b lo hi x _ _ AG9 E9_40 U87 U88 Hin Hx) |].
intros x Hx Hw. apply F4; [exact Hx | intros Hw1; apply Hw; left; exact Hw1]. }
assert (R0 : nth_error (ss_mem ss_fneE) 0 = Some (YP09.mkRegion (Some 87%nat) 0 8 0 8 [mkChunk 0 (CVal 8 (SOff 40 0))])) by (apply (f_equal (fun l => nth_error l 0)) in FM2; exact FM2).
assert (R1 : nth_error (ss_mem ss_fneE) 1 = Some (YP09.mkRegion (Some 88%nat) 8 16 8 16 [mkChunk 8 (CVal 8 (SOff 40 0))])) by (apply (f_equal (fun l => nth_error l 1)) in FM2; exact FM2).
assert (R2 : nth_error (ss_mem ss_fneE) 2 = Some (YP09.mkRegion None (LOCK + 24) (LOCK + 32) (LOCK + 24) (LOCK + 32) [mkChunk (LOCK + 24) (CVal 8 (SOff 87 0))])) by (apply (f_equal (fun l => nth_error l 2)) in FM2; exact FM2).
assert (R3 : nth_error (ss_mem ss_fneE) 3 = Some (YP09.mkRegion None ERRNO (ERRNO + 4) ERRNO (ERRNO + 4) [mkChunk ERRNO (CVal 4 (SLit 12))])) by (apply (f_equal (fun l => nth_error l 3)) in FM2; exact FM2).
assert (R4 : nth_error (ss_mem ss_fneE) 4 = Some (YP09.mkRegion (Some 40%nat) 0 40 0 40 [mkChunk 0 (CVal 8 (SOff 88 0)); mkChunk 8 (CVal 8 (SOff 87 0)); mkChunk 16 (CVal 8 (SLit 0)); mkChunk 24 (CVal 8 (SLit 0)); mkChunk 32 (CVal 8 (SLit 0))]))
by (apply (f_equal (fun l => nth_error l 4)) in FM2; exact FM2).
pose proof (ZEROS E9 ss_fneE ms5 4%nat HS6 E9_40 ltac:(rewrite R4; reflexivity)) as Z5.
set (W := fun x => WD2 (ptr_addr L1 h0) (ptr_addr L1 hp) x /\ ~ (ptr_addr L1 m + 16 <= x < ptr_addr L1 m + 40)).
assert (HM5 : midrep B L1 s' (ms_mem ms5) md1).
{ apply (midrep_fm ms s' mm0 (ms_mem ms5) W FRg MEMS Hmn HD0 FP HM0).
- intros x. subst W. unfold WD2, WD1, WD0, WS. lia.
- intros x Hx HW. destruct (Z_le_dec (ptr_addr L1 m + 16) x); [destruct (Z_lt_dec x (ptr_addr L1 m + 40)); [apply Z5; lia|]|]; (apply F5; [exact Hx | intros HW1; apply HW; split; [exact HW1 | lia]]).
- intros x [HW1 Hn16]. unfold WD2, WD1, WD0 in HW1. rewrite Eh0.
destruct HW1 as [[[Hw|[Hw|Hw]]|Hw]|[Hw|Hw]]; [left; exact Hw | right; left; exact Hw | right; right; right; left; lia | right; right; left; exact Hw | right; right; right; right; split; [exact Hne | left; exact Hw] | right; right; right; right; split; [exact Hne | right; exact Hw]].
- intros x Hx. destruct (RB x ltac:(lia)) as (_ & NI & Rx). apply (writable_off_img_present _ x ltac:(lia) ltac:(intros Hi; exact (NI (in_img1_img x Hi)))).
apply (writable_of_region regs E9 ss_fneE ms5 4 _ x HS6 R4). cbn [r_base r_wlo r_whi base_val]. rewrite U40'. lia.
- intros _ x Hx. rewrite Eh0 in Hx. fold hp in Hx.
assert (NI : ~ in_img1 x) by (intros Hi; apply in_img1_img in Hi; destruct Hx as [Hx|Hx]; [exact (proj1 (key_range3 h0 x Kh0 ltac:(lia)) Hi) | exact (proj1 (key_range3 hp x Khp ltac:(lia)) Hi)]).
apply (writable_off_img_present _ x ltac:(lia) NI). destruct Hx as [Hx|Hx].
+ apply (writable_of_region regs E9 ss_fneE ms5 0 _ x HS6 R0). cbn [r_base r_wlo r_whi base_val]. rewrite U87. lia.
+ apply (writable_of_region regs E9 ss_fneE ms5 1 _ x HS6 R1). cbn [r_base r_wlo r_whi base_val]. rewrite U88. lia.
- rewrite Eh0. apply (word_of_chunk regs E9 ss_fneE ms5 2 _ (LOCK + 24) (SOff 87 0) _ HS6 R2 eq_refl ltac:(left; reflexivity)). exact (den_off0 E9 87 _ E9_87).
- replace (ptr_addr L1 m) with (bv_unsigned (ew E9 40) + 0) at 1 by lia. apply (word_of_chunk_at E9 ss_fneE ms5 4 _ 40 0 (SOff 88 0) _ HS6 R4 eq_refl ltac:(left; reflexivity)). exact (den_off0 E9 88 _ E9_88).
- rewrite Eh0. replace (ptr_addr L1 m + 8) with (bv_unsigned (ew E9 40) + 8) by lia. apply (word_of_chunk_at E9 ss_fneE ms5 4 _ 40 8 (SOff 87 0) _ HS6 R4 eq_refl ltac:(right; left; reflexivity)). exact (den_off0 E9 87 _ E9_87).
- intros _. rewrite Eh0. split.
+ replace (ptr_addr L1 h0) with (bv_unsigned (ew E9 87) + 0) at 1 by lia. apply (word_of_chunk_at E9 ss_fneE ms5 0 _ 87 0 (SOff 40 0) _ HS6 R0 eq_refl ltac:(left; reflexivity)). exact (den_off0 E9 40 _ E9_40).
+ fold hp. replace (ptr_addr L1 hp + 8) with (bv_unsigned (ew E9 88) + 8) by lia. apply (word_of_chunk_at E9 ss_fneE ms5 1 _ 88 8 (SOff 40 0) _ HS6 R1 eq_refl ltac:(left; reflexivity)). exact (den_off0 E9 40 _ E9_40). }
apply (finish_fm E9 ss_fneE ms5 s' 6%nat rs2 8%nat HS6 CK2 AG9 Hrs2 Hb2 Hlo2 Hhi2 ltac:(vm_compute; reflexivity) HI' RXs AKs EU AMAs BNDs Rs HM5).
+ intros x Hx Nw Ne Nc Nn. rewrite (F5 x Hx); [apply HF0; [exact Hx | exact Nw | exact Nc]|].
unfold WD2, WD1, WD0. intros [[[Hw|[Hw|Hw]]|Hw]|[Hw|Hw]]; [exact (Nw Hw) | exact (Ne Hw) | apply Nn; apply NONMAP; left; exact Hw | apply Nc; unfold CTX_SIZE; lits; lia | |].
* apply Nn. apply NONMAP. right. exists h0. split; [rewrite Ems; left; reflexivity | lia].
* apply Nn. apply NONMAP. right. exists hp. split; [apply INlast; exact Hne | lia].
+ exact (ERRW_of E9 ss_fneE ms5 3%nat HS6 R3).
+ intros a Ha. rewrite (F5 a ltac:(lia)); [apply HF0; [lia | unfold WS; lia | unfold CTX_SIZE; lits; lia]|].
unfold WD2, WD1, WD0, WS. intros [[[Hw|[Hw|Hw]]|Hw]|[Hw|Hw]]; [lia | lits; lia | destruct (RB a ltac:(lia)) as (_ & _ & Ra); lia | lits; lia | lia | lia].
Qed.
End MD.
End b0.
End w.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
