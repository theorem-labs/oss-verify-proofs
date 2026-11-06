(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC44.v for libreac/fuzz_scene's program walk: the listing's names are ssym; uar_got_regionP is the side-stack flag's GOT slot, object 0; PALibF holds fuzz_scene.asan-ubsan's side-stack entries for frame classes 1, 2 and 8 and the separation of its two GOT slots (objects 1 and 0), the shadow-base cell (object 16) and the side-stack flag cell; palf_got_uar and palf_uar_img are lemmas from PALib (flag cell object 17, image end 0x5f9000) in place of fields; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied by path from a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (a working branch acae397d926) for libreac/fuzz_scene's program walk; the module path and the listing's names changed. PALibF holds fuzz_scene.asan-ubsan (sha256 e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f)'s side-stack entries for the frame classes 1, 2 and 8 (the classes its three fake-stack functions use: reac_ctrl_parse 1, check_step 2, LLVMFuzzerTestOneInput 8) in place of fuzz_grant's 0, 1, 2 and 4, and the separation of objects 1, 0, 16 and the flag cell. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow SceneSyms ScenePa PaJournal ScenePaLib YC1g.
(* palf_sm8 binds the class-8 helper to a Theorem Labs lane's per-unit constant, not to the shared field
   pc_stack_malloc (as_code B) 8: scene's only Tfib_code (A/AF0l.v:12) has cid 8 = 0, so the field form makes
   PALibF unsatisfiable (a review ruling, 2026-10-29 00:47Z, option (a)). The value, 0x3f438 =
   __asan_stack_malloc_8 in fuzz_scene.asan-ubsan, is measured in that file (lib/AU/Rt/StackMalloc8Tbl.v:67). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Rt Require StackMalloc8Tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition set_window (r : YP09.region) (wlo whi : Z) : YP09.region :=
YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) wlo whi (YP09.r_chunks r).
Fixpoint list_upd {A} (l : list A) (i : nat) (x : A) : list A :=
match l, i with
| [], _ => []
| _ :: t, O => x :: t
| h :: t, S i' => h :: list_upd t i' x
end.
Lemma zall_disjoint_of_all : forall E r rs,
all_disjoint E r rs -> zall_disjoint (extent_of_region E r) (map (extent_of_region E) rs).
Proof.
intros E r rs. induction rs as [|r' rs IH]; cbn; intros H; [exact I|].
destruct H as [H1 H2]. split; [|exact (IH H2)]. unfold zdisj, extent_of_region, extent_disjoint in *. cbn [fst snd]. exact H1.
Qed.
Lemma zpairwise_of_pairwise : forall E rs,
pairwise_disjoint E rs -> zpairwise_disjoint (map (extent_of_region E) rs).
Proof.
intros E rs. induction rs as [|r rs IH]; cbn; intros H; [exact I|].
destruct H as [H1 H2]. split; [exact (zall_disjoint_of_all E r rs H1) | exact (IH H2)].
Qed.
Lemma map_extent_list_upd : forall E rs i r r',
nth_error rs i = Some r -> extent_of_region E r' = extent_of_region E r ->
map (extent_of_region E) (list_upd rs i r') = map (extent_of_region E) rs.
Proof.
intros E rs. induction rs as [|h t IH]; intros [|i] r r' Hn He; cbn in *; try discriminate.
- injection Hn as ->. rewrite He. reflexivity.
- rewrite (IH i r r' Hn He). reflexivity.
Qed.
Lemma Forall_list_upd : forall {A} (P : A -> Prop) (l : list A) i x,
Forall P l -> P x -> Forall P (list_upd l i x).
Proof.
intros A P l. induction l as [|h t IH]; intros [|i] x Hl Hx; cbn; [exact Hl | exact Hl | |]; inversion Hl; subst; constructor; auto.
Qed.
Definition uar_got_regionP (u : nat) : YP09.region :=
YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff u 0))].
Definition uar_cell_regionP (u : nat) : YP09.region :=
YP09.mkRegion (Some u) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
Definition obj8_region (i : nat) (v : sv) : YP09.region := YP09.mkRegion (Some (A_OBJ i)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 v)].
Definition const8_region (a v : Z) : YP09.region := YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SLit v))].
Definition fframe_region (f fl : nat) (cid : Z) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some f) 0 (fs_frame_bytes cid) 0 (fs_frame_bytes cid) (cs ++ [YP09.mkChunk (fs_frame_bytes cid - 8) (CVal 8 (SOff fl 0))]).
Definition fshadow_region (s : nat) (cid wlo whi : Z) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some s) 0 (fs_frame_bytes cid / 8) wlo whi cs.
Definition HPTR (al : Z) : afact := mkAF 4096 140737479966720 al.
Lemma aregs_preserved_eqs : forall regs0 regs2 : bvmap 5 word,
getr regs2 2 = getr regs0 2 -> getr regs2 3 = getr regs0 3 -> getr regs2 4 = getr regs0 4 ->
getr regs2 8 = getr regs0 8 -> getr regs2 9 = getr regs0 9 ->
getr regs2 18 = getr regs0 18 -> getr regs2 19 = getr regs0 19 -> getr regs2 20 = getr regs0 20 ->
getr regs2 21 = getr regs0 21 -> getr regs2 22 = getr regs0 22 -> getr regs2 23 = getr regs0 23 ->
getr regs2 24 = getr regs0 24 -> getr regs2 25 = getr regs0 25 -> getr regs2 26 = getr regs0 26 ->
getr regs2 27 = getr regs0 27 -> aregs_preserved regs0 regs2.
Proof.
intros regs0 regs2 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr.
assert (Hr0 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
clear Hr. repeat (destruct Hr0 as [-> | Hr0]; [assumption|]). subst r. assumption.
Qed.
Lemma count_cid_le_length : forall cid l, count_cid cid l <= Z.of_nat (length l).
Proof. intros cid l. induction l as [|[c p] l IH]; cbn; [lia|]. destruct (c =? cid); lia. Qed.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Fixpoint zseps_from (b : Z * Z) (l : list (Z * Z)) : Prop :=
match l with [] => True | c :: r => (fst b + snd b <= fst c \/ fst c + snd c <= fst b) /\ zseps_from b r end.
Fixpoint zseps (l : list (Z * Z)) : Prop := match l with [] => True | b :: r => zseps_from b r /\ zseps r end.
Section j.
Context {L : ptable ssym} {PI : PAImg L}.
Variable B : asyms.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
Record PALibF : Prop := {
palf_uar_al : as_uar_cell B mod 4 = 0;
palf_sm1 : pa_sigma SS___asan_stack_malloc_1 = pc_stack_malloc (as_code B) 1;
palf_sm2 : pa_sigma SS___asan_stack_malloc_2 = pc_stack_malloc (as_code B) 2;
palf_sm8 : pa_sigma SS___asan_stack_malloc_8 = StackMalloc8Tbl.PC_STACK_MALLOC_8;
palf_sep : zseps [(VAL (A_OBJ 1), 8); (VAL (A_OBJ 0), 8); (VAL (A_OBJ 16), 8); (as_uar_cell B, 4)]
}.
Lemma palf_got_uar : PALib B -> as_got_uar B = VAL (A_OBJ 0).
Proof. intros T. exact (pal_got_uar B T). Qed.
Lemma palf_uar_img : PALib B -> 0x10000 <= as_uar_cell B /\ as_uar_cell B + 8 <= 0x5f9000.
Proof. intros T. rewrite (pal_uar_cell B T). apply pa_obj_img. lia. Qed.
End j.
Lemma val_mem_of_rd32 : forall segs H mem a v,
rd32 (aview segs H mem) a v -> val_mem segs (mrestrict H mem) a 4 v.
Proof.
intros segs H mem a v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
Lemma rdword_of_val_mem : forall segs H mem a v,
val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
Lemma region_ok_rewindow : forall segs E m r wlo whi,
region_ok segs E m r ->
(forall o, wlo <= o < whi -> writable_at segs m (base_val E (YP09.r_base r) + o)) ->
region_ok segs E m (set_window r wlo whi).
Proof.
intros segs E m r wlo whi (H1 & H2 & H3 & H4) Hw. unfold region_ok, set_window.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [exact H1|]. split; [exact H2|]. split; [exact Hw | exact H4].
Qed.
Lemma ast_ok_set_region : forall segs E ss ms i r r',
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r ->
extent_of_region E r' = extent_of_region E r ->
regions_wf (list_upd (ss_mem ss) i r') = true ->
region_ok segs E (ms_mem ms) r' ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (list_upd (ss_mem ss) i r') (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros segs E ss ms i r r' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hn He Hwf' Hr'.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [exact Hwf'|]. split; [exact (Forall_list_upd _ _ i r' Hok Hr')|].
apply pairwise_disjoint_of_extents. rewrite (map_extent_list_upd E _ i r r' Hn He). apply zpairwise_of_pairwise. exact Hpd.
Qed.
Lemma atoms_ok_pick : forall E l idx, atoms_ok E l -> atoms_ok E (pick l idx).
Proof.
intros E l idx H. induction idx as [|i idx IH]; cbn; [exact I|].
destruct (nth_error l i) as [[n f]|] eqn:Hn; [|exact IH].
cbn. split; [|exact IH].
apply nth_error_In in Hn. revert Hn. clear - H. induction l as [|[n' f'] l IHl]; cbn; intros Hin; [destruct Hin|].
destruct H as [H1 H2]. destruct Hin as [E1 | Hin]; [injection E1 as -> ->; exact H1 | exact (IHl H2 Hin)].
Qed.
Lemma st_ok_pick_facts : forall segs E ss ms ai ci li,
st_ok segs E ss ms ->
st_ok segs E (set_facts ss (mkFacts (pick (f_atoms (ss_facts ss)) ai) (pick (f_conds (ss_facts ss)) ci) (pick (f_alias (ss_facts ss)) li))) ms.
Proof.
intros segs E ss ms ai ci li HS. apply st_ok_set_facts; [exact HS|].
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & (Ha & Hc & Hl)).
pose proof (facts_ok_prune E (ss_facts ss) ci li (conj Ha (conj Hc Hl))) as (_ & Hc' & Hl').
split; [apply atoms_ok_pick; exact Ha | split; [exact Hc' | exact Hl']].
Qed.
Lemma val_mem_moved : forall segs H H' (m m' : word -> option byte) a b n v,
(forall k, 0 <= k < Z.of_nat n -> aview segs H' m' (b + k) = aview segs H m (a + k)) ->
val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') b n v.
Proof.
intros segs H H' m m' a b n v Hk Hv k Hkn. specialize (Hk (Z.of_nat k) ltac:(lia)). unfold aview in Hk.
rewrite (Hv k Hkn) in Hk. destruct (mbyte segs (mrestrict H' m') (b + Z.of_nat k)) as [b'|]; cbn in Hk; [|discriminate].
injection Hk as Hk. f_equal. apply bv_eq. exact Hk.
Qed.
Lemma atoms_ok_incl : forall E l l', (forall x, In x l' -> In x l) -> atoms_ok E l -> atoms_ok E l'.
Proof.
intros E l l' Hi H. induction l' as [|[n f] l' IH]; cbn; [exact I|].
split; [|apply IH; intros x Hx; apply Hi; right; exact Hx].
assert (Hin : In (n, f) l) by (apply Hi; left; reflexivity). clear - H Hin.
induction l as [|[n' f'] l IHl]; cbn in *; [destruct Hin|].
destruct H as [H1 H2]. destruct Hin as [E1 | Hin]; [injection E1 as -> ->; exact H1 | exact (IHl H2 Hin)].
Qed.
Lemma alias_ok_incl : forall E l l', (forall x, In x l' -> In x l) -> alias_ok E l -> alias_ok E l'.
Proof.
intros E l l' Hi H. induction l' as [|[a b] l' IH]; cbn; [exact I|].
split; [|apply IH; intros x Hx; apply Hi; right; exact Hx].
assert (Hin : In (a, b) l) by (apply Hi; left; reflexivity). clear - H Hin.
induction l as [|[a' b'] l IHl]; cbn in *; [destruct Hin|].
destruct H as [H1 H2]. destruct Hin as [E1 | Hin]; [injection E1 as -> ->; exact H1 | exact (IHl H2 Hin)].
Qed.
Lemma st_ok_facts_incl : forall segs E ss ms fa al,
st_ok segs E ss ms ->
(forall x, In x fa -> In x (f_atoms (ss_facts ss))) -> (forall x, In x al -> In x (f_alias (ss_facts ss))) ->
st_ok segs E (set_facts ss (mkFacts fa [] al)) ms.
Proof.
intros segs E ss ms fa al HS Hfa Hal. apply st_ok_set_facts; [exact HS|].
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & (Ha & Hc & Hl)).
split; [exact (atoms_ok_incl E _ _ Hfa Ha)|]. split; [exact I | exact (alias_ok_incl E _ _ Hal Hl)].
Qed.
Lemma st_ok_facts_incl3 : forall segs E ss ms fa cs al,
st_ok segs E ss ms ->
(forall x, In x fa -> In x (f_atoms (ss_facts ss))) -> (forall x, In x cs -> In x (f_conds (ss_facts ss))) ->
(forall x, In x al -> In x (f_alias (ss_facts ss))) ->
st_ok segs E (set_facts ss (mkFacts fa cs al)) ms.
Proof.
intros segs E ss ms fa cs al HS Hfa Hcs Hal. apply st_ok_set_facts; [exact HS|].
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & (Ha & Hc & Hl)).
split; [exact (atoms_ok_incl E _ _ Hfa Ha)|]. split; [| exact (alias_ok_incl E _ _ Hal Hl)].
apply (proj2 (conds_ok_forall E cs)). intros c Hin. exact (proj1 (conds_ok_forall E _) Hc c (Hcs c Hin)).
Qed.
Lemma st_ok_cond_In : forall segs E ss ms c,
st_ok segs E ss ms -> In c (f_conds (ss_facts ss)) -> acond_ok E c.
Proof.
intros segs E ss ms c HS Hin. destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & Hc & _)).
exact (proj1 (conds_ok_forall E _) Hc c Hin).
Qed.
Lemma ast_ok_set_reg_fp : forall segs E ss ms (r : bv 5) e,
st_ok segs E ss ms -> bv_eqb r 0 = false -> sv_denot E e = getr (ms_regs ms) r ->
st_ok segs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros segs E ss ms r e HS Hr0 He. apply st_ok_regs; [exact HS|].
intros rr. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. rewrite He. apply (st_ok_reg segs E ss ms r HS).
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
Lemma st_ok_havoc : forall segs k E ss ms ws,
st_ok segs E ss ms -> ss_atoms_lt k ss = true -> st_ok segs (havoc E k ws) ss ms.
Proof.
intros segs k E ss ms ws HS Hk. eapply st_ok_agree; [exact HS | | exact Hk].
apply (env_agree_havoc_ge k k E E ws ltac:(lia) (env_agree_refl k E)).
Qed.
Lemma aview_of_val_mem1 : forall segs H mem a v,
val_mem segs (mrestrict H mem) a 1 v -> 0 <= v < 256 -> aview segs H mem a = Some v.
Proof.
intros segs H mem a v Hv Hr. unfold aview. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. rewrite Hv. cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YO0f.le_byte.
change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.shiftr_0_r. rewrite !Z.mod_mod by lia. apply Z.mod_small. exact Hr.
Qed.
Lemma range_addressable_partial : forall (rd : Z -> option Z) Bs p k,
rd (shadow_of_addr Bs p) = Some k -> p mod 8 = 0 -> 0 <= k < 8 -> range_addressable rd Bs p k.
Proof.
intros rd Bs p k Hk Hp Hr x Hx. exists k.
pose proof (Z.div_mod p 8 ltac:(lia)) as D. rewrite Hp, Z.add_0_r in D.
assert (Hq : x / 8 = p / 8) by (symmetry; apply (Z.div_unique x 8 (p / 8) (x - p)); lia).
assert (Hg : shadow_of_addr Bs x = shadow_of_addr Bs p) by (unfold shadow_of_addr; rewrite Hq; reflexivity).
rewrite Hg, Hk. split; [reflexivity|]. destruct (Z.eq_dec k 0) as [-> | Hnz]; [left; reflexivity | right].
assert (Hxm : x mod 8 = x - p) by (rewrite (Z.mod_eq x 8), Hq by lia; lia).
lia.
Qed.
Section q.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Lemma frame_al64 : forall ly S W mem md cid pos,
AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid.
Proof.
intros ly S W mem md cid pos [M _] Hin.
destruct (frame_facts B ly S _ cid pos M Hin) as (_ & _ & _ & _ & Hpg & _ & _ & Hoff & H64 & Hb & _).
unfold frame_addr, page_aligned in *. split; [|split; [exact Hb | exact H64]].
rewrite Z.add_mod, Hoff, Z.add_0_r, Z.mod_mod by lia.
replace (ly_F ly) with (64 * (ly_F ly / 4096 * 64)) by (pose proof (Z.div_mod (ly_F ly) 4096 ltac:(lia)); lia).
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma shadow_hull_vis_of_frame : forall ly S W mem md cid pos d n,
AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos <= d -> d + n <= frame_addr ly cid pos + fs_frame_bytes cid -> 0 < n ->
shadow_hull_vis (aview segs (w_H W) mem) d n.
Proof.
intros ly S W mem md cid pos d n HAR Hin Hfd Hdn Hn s Hs.
destruct (frame_al64 ly S W mem md cid pos HAR Hin) as (Hal & Hbal & Hb64).
destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & _ & Hsh).
set (f := frame_addr ly cid pos) in *. set (bs := fs_frame_bytes cid) in *.
pose proof (Z.div_mod f 64 ltac:(lia)) as Df. pose proof (Z.div_mod bs 64 ltac:(lia)) as Db.
assert (E8f : f / 8 = 8 * (f / 64)) by (rewrite Hal, Z.add_0_r in Df; rewrite Df at 1; replace (64 * (f / 64)) with (8 * (f / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (E8b : bs / 8 = 8 * (bs / 64)) by (rewrite Hbal, Z.add_0_r in Db; rewrite Db at 1; replace (64 * (bs / 64)) with (8 * (bs / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (Hsf : shadow_addr f = 8 * (268431360 + f / 64)) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (L1 : shadow_addr f <= shadow_addr d / 8 * 8).
{ pose proof (shadow_mono f d Hfd) as M1. rewrite Hsf. rewrite Hsf in M1.
assert (268431360 + f / 64 <= shadow_addr d / 8) by (apply Z.div_le_lower_bound; lia). lia. }
assert (L2 : shadow_addr (d + n - 1) / 8 * 8 + 8 <= shadow_addr f + bs / 8).
{ assert (M2 : shadow_addr (d + n - 1) < shadow_addr f + bs / 8).
{ unfold shadow_addr in *. assert ((d + n - 1) / 8 < f / 8 + bs / 8) by (apply Z.div_lt_upper_bound; lia). lia. }
rewrite Hsf, E8b in M2. rewrite Hsf, E8b.
assert (shadow_addr (d + n - 1) / 8 < 268431360 + f / 64 + bs / 64) by (apply Z.div_lt_upper_bound; lia). lia. }
specialize (Hsh (s - shadow_addr f) ltac:(lia)). replace (shadow_addr f + (s - shadow_addr f)) with s in Hsh by lia.
apply (aview_some_of_apresent segs). exact (proj1 Hsh).
Qed.
Lemma region_kept_block_ajw2 : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs b m ly2 S2 md2,
acall_kept segs B lyc Sc W memc W2 mem2 slo shi Er -> AR segs B ly2 S2 W2 mem2 md2 -> In (b, m) (ablocks B ly2 S2) ->
bv_unsigned (ew E n) = b -> In (b, m) (ablocks B lyc Sc) -> 0 <= lo -> hi <= req_size m -> lo <= wlo -> whi <= hi ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs b m ly2 S2 md2 (_ & K2 & _) HAR2 Hin2 Hn Hin Hlo Hhi Hwlo Hwhi HnE.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hin2) as (_ & _ & _ & _ & Hpres2 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
replace (b + (a - b)) with a by lia. apply HnE. exact Ha.
- intros _. apply (apresent_writable segs). apply (proj1 (Hpres2 a ltac:(lia))).
Qed.
Lemma awr_new_block_any : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 res n blc i lyq ownq,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
AR segs B ly2 S2 W2 mem2 md2 -> ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] -> 0 <= n ->
In (res, n) blc -> 0 <= i < req_size n ->
awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (res + i).
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 res n blc i lyq ownq HJ HAR2 Ebl Hn Hin Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (res, n) (ablocks B ly S)) as [H0 | H0].
- destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (res, n) (ablocks B lyc Sc)) as [Hc | Hc].
+ exfalso. apply in_split in Hc as (l1 & l2 & E1).
pose proof (sep_blocks_pos segs B LAWS ly2 S2 W2 mem2 md2 (res, n) (res, n) l1 l2 [] HAR2) as Hd.
rewrite Ebl, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
assert (0 < req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); cbn; lia). lia.
+ right. left. split; [exact (Hgone res n i H0 Hc Hi)|]. exists res, n. split; [exact Hin | lia].
- right. right. left. exists res, n. split; [exact Hin|]. split; [exact H0 | lia].
Qed.
End q.
Section w.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Lemma region_kept_frame_aj : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs b cid pos,
acall_kept segs B lyc Sc W memc W2 mem2 slo shi Er ->
bv_unsigned (ew E n) = b -> In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= b + lo -> b + hi <= frame_addr lyc cid pos + fs_frame_bytes cid -> whi <= wlo ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs b cid pos (_ & _ & _ & K4 & _) Hn Hin Hlo Hhi Hro HnE.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha; [|lia].
apply (mbyte_of_aview segs). apply (K4 cid pos a Hin); [|apply HnE; exact Ha].
left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
Qed.
Lemma region_kept_ownframe_aj : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs b cid pos,
acall_kept segs B lyc Sc W memc W2 mem2 slo shi Er ->
bv_unsigned (ew E n) = b -> In (cid, pos) (frames Sc) ->
((frame_addr lyc cid pos <= b + lo /\ b + hi <= frame_addr lyc cid pos + fs_frame_bytes cid) \/
(shadow_addr (frame_addr lyc cid pos) <= b + lo /\ b + hi <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8)) ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs b cid pos (_ & _ & _ & K4 & _) Hn Hin Hrng HnE Hpres.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply (K4 cid pos a Hin); [|apply HnE; exact Ha].
destruct Hrng as [[H1 H2] | [H1 H2]]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; lia.
- intros _. apply (apresent_writable segs). apply Hpres. exact Ha.
Qed.
End w.
Section z.
Context {L : ptable ssym} {PI : PAImg L}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
Lemma ast_ok_pi_set_region : forall E ss ms i r r',
st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
extent_of_region E r' = extent_of_region E r ->
regions_wf (list_upd (ss_mem ss) i r') = true ->
region_ok SEGS E (ms_mem ms) r' ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (list_upd (ss_mem ss) i r') (ss_resv ss) (ss_facts ss)) ms.
Proof. intros E ss ms i r r' HS Hn He Hw Hr. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (ast_ok_set_region SEGS E _ ms i r r' HS Hn He Hw Hr). Qed.
Lemma st_ok_pi_pick_facts : forall E ss ms ai ci li,
st_ok_pi SEGS VAL E ss ms ->
st_ok_pi SEGS VAL E (set_facts ss (mkFacts (pick (f_atoms (ss_facts ss)) ai) (pick (f_conds (ss_facts ss)) ci) (pick (f_alias (ss_facts ss)) li))) ms.
Proof. intros E ss ms ai ci li HS. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (st_ok_pick_facts SEGS E _ ms ai ci li HS). Qed.
Lemma st_ok_pi_facts_incl : forall E ss ms fa al,
st_ok_pi SEGS VAL E ss ms ->
(forall x, In x fa -> In x (f_atoms (ss_facts ss))) -> (forall x, In x al -> In x (f_alias (ss_facts ss))) ->
st_ok_pi SEGS VAL E (set_facts ss (mkFacts fa [] al)) ms.
Proof. intros E ss ms fa al HS H1 H2. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (st_ok_facts_incl SEGS E _ ms fa al HS H1 H2). Qed.
Lemma st_ok_pi_facts_incl3 : forall E ss ms fa cs al,
st_ok_pi SEGS VAL E ss ms ->
(forall x, In x fa -> In x (f_atoms (ss_facts ss))) -> (forall x, In x cs -> In x (f_conds (ss_facts ss))) ->
(forall x, In x al -> In x (f_alias (ss_facts ss))) ->
st_ok_pi SEGS VAL E (set_facts ss (mkFacts fa cs al)) ms.
Proof. intros E ss ms fa cs al HS H1 H2 H3. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (st_ok_facts_incl3 SEGS E _ ms fa cs al HS H1 H2 H3). Qed.
Lemma st_ok_pi_cond_In : forall E ss ms c,
st_ok_pi SEGS VAL E ss ms -> In c (f_conds (ss_facts ss)) -> acond_ok E c.
Proof. intros E ss ms c HS Hin. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (st_ok_cond_In SEGS E _ ms c HS Hin). Qed.
Lemma ast_ok_pi_set_reg_fp : forall E ss ms (r : bv 5) e,
st_ok_pi SEGS VAL E ss ms -> bv_eqb r 0 = false -> sv_denot E e = getr (ms_regs ms) r ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof. intros E ss ms r e HS Hr He. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (ast_ok_set_reg_fp SEGS E _ ms r e HS Hr He). Qed.
Lemma st_ok_pi_havoc : forall k E ss ms ws,
st_ok_pi SEGS VAL E ss ms -> ss_atoms_p (pband k A_TEXT) ss = true -> (k + length ws <= A_TEXT)%nat ->
st_ok_pi SEGS VAL (havoc E k ws) ss ms.
Proof.
intros k E ss ms ws HS Hat Hk. unfold st_ok_pi in *.
eapply (st_ok_agree_p (pband k A_TEXT) SEGS); [exact HS | | destruct ss; exact Hat].
split; [| reflexivity]. intros n Hn. unfold pband in Hn.
apply Bool.orb_true_iff in Hn. destruct Hn as [Hn|Hn];
[apply Nat.ltb_lt in Hn; apply ew_havoc_old; exact Hn | apply Nat.leb_le in Hn; apply ew_havoc_above; lia].
Qed.
Lemma st_ok_pi_add_alias : forall E ss ms e1 e2,
st_ok_pi SEGS VAL E ss ms -> sv_denot E e1 = sv_denot E e2 ->
st_ok_pi SEGS VAL E (set_facts ss (mkFacts (f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) ((e1, e2) :: f_alias (ss_facts ss)))) ms.
Proof. intros E ss ms e1 e2 HS He. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (st_ok_add_alias SEGS E _ ms e1 e2 HS He). Qed.
End z.
Section a0.
Context {L : ptable ssym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).
Definition run_post_pi_AJ (W : world SEGS) (E : env) (ss ss' : sstate)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S W0 mem md own lyc Sc (mdc : Model) (k : Z)
(Q : world SEGS -> config -> Prop) : Prop :=
forall ms' mat',
st_ok_pi SEGS VAL E ss' (restrict (w_H W) ms') ->
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
Definition pi_plain_stop (st : prun_status ssym) : Prop :=
match st with PRS_running | PRS_stopped _ => True | _ => False end.
Lemma SRr_run_pi_AJ : forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
img_env VAL A_LIM E ->
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
sym_runN_pi pl_tpi n ss = (ss', st) -> pi_plain_stop st ->
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_AJ W E ss ss' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
unfold sym_runN_pi in Hrun. rewrite <- pl_tpi_eq in Hrun.
destruct (PaRun.sym_run_pi_sound ssym SEGS (clookup pa_tbl) VAL pa_sigma L pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim
_ E ss ss' st _ HE HS Hrun) as (msr' & Hms & HP & _ & Hfr).
eapply (SRr_chain_AJ SEGS B LAWS pa_segs_low pa_wx W E (abs_ss VAL ss) (abs_ss VAL ss') ms msr');
[ exact Hms | destruct st; cbn [prun_post] in HP; first [exact HP | destruct Hst] | destruct ss; exact Hfr | exact HJ | destruct ss; exact Hwr | ].
intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS' HJ'); destruct ss; first [exact HF | exact HF' | exact HG].
Qed.
Lemma SRr_run_to_pi_AJ : forall W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
img_env VAL A_LIM E ->
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
sym_run_toN_pi pl_tpi n stop ss = (ss', st) -> pi_plain_stop st ->
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_AJ W E ss ss' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
unfold sym_run_toN_pi in Hrun. rewrite <- pl_tpi_eq in Hrun.
destruct (PaRun.sym_run_to_pi_sound ssym SEGS (clookup pa_tbl) VAL pa_sigma L pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim
_ _ E ss ss' st _ HE HS Hrun) as (msr' & Hms & HP & _ & Hfr).
eapply (SRr_chain_AJ SEGS B LAWS pa_segs_low pa_wx W E (abs_ss VAL ss) (abs_ss VAL ss') ms msr');
[ exact Hms | destruct st; cbn [prun_post] in HP; first [exact HP | destruct Hst] | destruct ss; exact Hfr | exact HJ | destruct ss; exact Hwr | ].
intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS' HJ'); destruct ss; first [exact HF | exact HF' | exact HG].
Qed.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis frame_flag_law : frame_flag_lawP SEGS B.
Lemma aj_flag_store_pi : forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q,
img_env VAL A_LIM E ->
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
sym_runN_pi pl_tpi n ss = (ss', st) -> pi_plain_stop st ->
ajournal SEGS B STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W (ms_mem ms) mdc k ->
0 <= cid ->
(forall a, in_wrange E (ss_mem ss) a ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a \/ a = flag_addr lyc cid pos) ->
(forall msr, st_ok_pi SEGS VAL E ss' msr -> mbyte SEGS (ms_mem msr) (flag_addr lyc cid pos) = Some (Z_to_bv 8 0)) ->
(forall ms' mat',
st_ok_pi SEGS VAL E ss' (restrict (w_H W) ms') ->
ajournal SEGS B STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q HE HS Hrun Hst HJ Hcid Hwr Hflag0 Hk.
unfold sym_runN_pi in Hrun. rewrite <- pl_tpi_eq in Hrun.
destruct (PaRun.sym_run_pi_sound ssym SEGS (clookup pa_tbl) VAL pa_sigma L pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim
_ E ss ss' st _ HE HS Hrun) as (msr' & Hms & HS'0 & _ & Hfr0).
assert (HS' : st_ok_pi SEGS VAL E ss' msr') by (destruct st; cbn [prun_post] in HS'0; first [exact HS'0 | destruct Hst]). clear HS'0.
assert (Hfr : frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr')) by (destruct ss; exact Hfr0). clear Hfr0.
pose proof pa_wx as Hwx. pose proof pa_segs_low as segs_low.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frame_flag_law lyc Sc W (ms_mem ms) mdc cid pos HAR Hin) as (Hfp & Hfo & Hfr_rng & Hfr_num).
apply (SRr_msteps SEGS Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows SEGS _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
set (memc' := ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) in *.
assert (Hfr' : forall x : word, ~ in_wrange E (ss_mem ss) (bv_unsigned x) -> mrestrict (w_H W) memc' x = mrestrict (w_H W) (ms_mem ms) x).
{ subst memc'. rewrite Hmm. exact Hfr. }
assert (Hgr' : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) memc')) by (subst memc'; rewrite Hmm; exact Hgr).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E (ss_mem ss) a -> aview SEGS (w_H W) memc' a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr'. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact HWa. }
assert (Hsame' : same_but_materialized mdc (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc)).
{ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame. }
pose proof (same_but_materialized_wvb mdc _ Hsame') as Emd.
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (ml_stack_free _ ML Sc cid pos HWF Hin) as (HWF2 & l1 & l2 & E1 & E2).
assert (El1 : l1 = []).
{ destruct l1 as [|f l1']; [reflexivity|]. exfalso.
rewrite Hfrs in E1. cbn in E1. injection E1 as <- E1'.
pose proof (sep_frames_pos SEGS B LAWS lyc Sc W (ms_mem ms) mdc (cid, pos) (cid, pos) [] l1' l2 HAR
ltac:(rewrite Hfrs; cbn; rewrite E1'; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. pose proof (fs_frame_bytes_pos cid Hcid). lia. }
subst l1. cbn in E1, E2. rewrite Hfrs in E1. cbn in E1. injection E1 as E1.
assert (HAR' : AR SEGS B lyc (stack_free_state cid pos Sc) W memc' (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc)).
{ eapply (ASF lyc Sc W (ms_mem ms) mdc memc' _ cid pos HAR Hin).
- unfold aview. subst memc'. rewrite Hmm. rewrite (Hflag0 msr' HS'). reflexivity.
- intros a Ha Ho Hne. apply Heqw; [exact Ha|]. intros HWa.
destruct (Hwr a HWa) as [Hw | Hw]; [|exact (Hne Hw)].
exact (proj1 (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) Ho).
- intros a Hv. eapply aview_keeps_vis; [exact Hgr' | exact Hv].
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- intros a _ Hh. subst memc'. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hh. reflexivity. }
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- eapply (ajournal_after_write SEGS B LAWS segs_low STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W (ms_mem ms) mdc k
memc' _ (in_wrange E (ss_mem ss)) (stack_free_state cid pos Sc) own' HJ Heqw
ltac:(intros a Ha; eapply apresent_grows; [exact Hgr' | exact Ha]) Hsame').
+ intros a Ha. destruct (Hwr a Ha) as [Hw | ->]; [left; exact Hw | right; split; [exact Hfo | exact Hfr_rng]].
+ exact HAR'.
+ unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
+ reflexivity.
+ cbn. lia.
+ etransitivity; [exact E2 | symmetry; exact E1].
+ pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- exact Hfr'.
- exact Hgr'.
Qed.
End a0.
End g.
Ltac paj_after_run_plain HS HJ :=
let ms' := fresh "ms" in let mat := fresh "mat" in
let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
intros ms' mat HS HJ HF HFr HG.
Ltac paj_run_sh RUNP HS HJ :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of RUNP with
| forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "paj_run_sh: no hypothesis  img_env _ _ E" end in
eapply (RUNP W FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
[ clear Hrun | clear Hrun HS HJ; paj_after_run_plain HS HJ ]
end
end
| _ => fail "paj_run_sh: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.
Ltac paj_run_to_sh RUNTOP HS HJ stop :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of RUNTOP with
| forall W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_run_toN_pi ?tpi n stop ss = _ -> _ =>
let r := eval vm_compute in (sym_run_toN_pi tpi FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_pi tpi FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "paj_run_to_sh: no hypothesis  img_env _ _ E" end in
eapply (RUNTOP W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
[ clear Hrun | clear Hrun HS HJ; paj_after_run_plain HS HJ ]
end
end
| _ => fail "paj_run_to_sh: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.
Ltac paj_run_flag_sh RUNF HS HJ :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of RUNF with
| forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "paj_run_flag_sh: no hypothesis  img_env _ _ E" end in
eapply (RUNF W FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
[ clear Hrun | clear Hrun | clear Hrun | clear Hrun HS HJ; paj_after_run_plain HS HJ ]
end
end
| _ => fail "paj_run_flag_sh: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.
