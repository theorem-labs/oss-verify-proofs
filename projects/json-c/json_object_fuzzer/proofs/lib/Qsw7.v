(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.
#[using="Type"] Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
#[using="Type"] Lemma le1_lit : forall z, (0 <= z < 256)%Z -> Z_to_le_bytes 1 z = [Z_to_bv 8 z].
Proof. intros z Hz. cbn [Z_to_le_bytes]. reflexivity. Qed.
End RC__1.
Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
is_Zlit z; let b := eval vm_compute in (Z.modulo z 256) in
replace (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 b] by (apply (f_equal (fun x => [x])); apply bv_eq; vm_compute; reflexivity)
| _ => idtac
end.

Ltac stepz := step; try (fix_litstore; mem_after_store).
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma signed_lit : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Q9A7.Mq1.signed_of_Z. exact Hz. Qed.
End RC__2.
Ltac solve_condx := unfold_cond; fold_lit_ux; rewrite ?unsigned_lit by lia; rewrite ?signed_lit by lia; solve_cond_rec.
Ltac if_truex :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
replace c with true; [cbv iota| symmetry; solve_condx]
end. Ltac mkr__if_truex_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
replace c with true; [cbv iota| symmetry; solve_condx]
end.
Ltac if_falsex :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
replace c with false; [cbv iota| symmetry; solve_condx]
end. Ltac mkr__if_falsex_1 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
replace c with false; [cbv iota| symmetry; solve_condx]
end.
Section RC__3. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rw_cells_recast : forall segs m A cs cs',
rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
rw_cells segs m A cs'.
Proof.
intros segs m A cs cs' [[Hwf HB] HW] Hwf' HBe HSe. split; [split; [exact Hwf'| rewrite HBe; exact HB]| rewrite HSe; exact HW].
Qed.
End RC__3.

Ltac unfold_consts := unfold alloc_ceiling, sp_window_lo, stack_max_size in *. Ltac mkr__unfold_consts_2 := unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
Ltac clia := unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia. Ltac mkr__clia_3 := unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia.
Ltac unfold_consts_goal := unfold alloc_ceiling, sp_window_lo, stack_max_size. Ltac mkr__unfold_consts_goal_4 := unfold alloc_ceiling, sp_window_lo, stack_max_size.

Ltac word_range w H := pose proof (bv_unsigned_in_range 64 w) as H; unfold bv_modulus in H; cbn in H.

Ltac in_solve := cbn [In]; intuition congruence.

Ltac blk_facts L HIx HP Hb Hal Hlo Hhi :=
let X := fresh in
pose proof (heap_blk L HIx _ _ _ _ _ _ HP Hb) as X;
destruct X as (_ & Hal & Hlo & Hhi & _);
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
Section RC__4. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma in_block_facts : forall L (HIx : heap_iface L) A LB m md a n x,
HEAP L HIx A LB m md -> In (a, n) LB -> a <= x < a + n ->
x < alloc_ceiling /\ ~ hl_client_static L x /\
forall a' n', In (a', n') LB -> a' <> a -> ~ (a' <= x < a' + n').
Proof.
intros L HIx A LB m md a n x HP Hb Hx.
pose proof (heap_blk L HIx _ _ _ _ _ _ HP Hb) as (Hn & _ & _ & Hhi & _).
split; [lia|]. split.
- replace x with (a + (x - a)) by lia. eapply heap_blk_not_static; eauto. lia.
- intros a' n' Hb' Hne Hx'.
pose proof (heap_blk_disjoint L HIx _ _ _ _ _ _ _ _ HP Hb Hb' ltac:(congruence)) as Hd.
pose proof (heap_blk L HIx _ _ _ _ _ _ HP Hb') as (Hn' & _). lia.
Qed.

#[using="Type"] Lemma frame_writes_ok : forall L (HIx : heap_iface L) A LB m m' md W,
HEAP L HIx A LB m md ->
munch W m m' ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= hi_top L HIx)
\/ (exists a n, In (a, n) LB /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch L x)) W ->
forall a, 0 <= a < 2^64 -> ~ (client_addr L LB alloc_ceiling a /\ a < hi_top L HIx) -> ~ hl_scratch L a -> m' (wa a) = m (wa a).
Proof.
intros L HIx A LB m m' md W HP MU HW a Ha Hna Hns. apply MU. rewrite wa_unsigned by lia. clear MU.
induction W as [|[lo hi] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW].
cbn in H1. intros Hin. destruct H1 as [H1 | [(b & n & Hb & Hlo & Hhi) | Hsc]].
- apply Hna. split; [left; lia | lia].
- apply Hna. pose proof (heap_blk L HIx _ _ _ _ _ _ HP Hb) as (_ & _ & _ & Hbhi & _). pose proof (hi_top_hi L HIx).
split; [| lia]. right; right. exists (b, n). split; [exact Hb| cbn; lia].
- apply Hns. apply Hsc. lia.
Qed.

#[using="Type"] Lemma nodup_addr_size : forall (LB : list blk) a n n',
List.NoDup (map blk_addr LB) -> In (a, n) LB -> In (a, n') LB -> n = n'.
Proof.
induction LB as [|[b k] LB IH]; cbn; intros a n n' ND H1 H2; [tauto|].
inversion ND as [|x l Hni Hnd]; subst.
destruct H1 as [H1|H1]; destruct H2 as [H2|H2].
- congruence.
- inversion H1; subst. exfalso. apply Hni. exact (in_map blk_addr _ _ H2).
- inversion H2; subst. exfalso. apply Hni. exact (in_map blk_addr _ _ H1).
- eauto.
Qed.

#[using="Type"] Lemma client_outside : forall L (HIx : heap_iface L) A LB LB0 m md W SP,
HEAP L HIx A LB m md ->
(forall b, In b LB0 -> In b LB) ->
alloc_ceiling <= SP ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP)
\/ (exists a n, In (a, n) LB /\ ~ In (a, n) LB0 /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch L x)) W ->
forall a, 0 <= a < 2^64 -> client_addr L LB0 SP a -> outside W a.
Proof.
intros L HIx A LB LB0 m md W SP HP Hsub HSP HW a Ha Hc.
induction W as [|[lo hi] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW]. cbn in H1.
destruct Hc as [Hc | [Hc | (b & Hb0 & Hbr)]].
- destruct H1 as [H1 | [(b & n & Hb & Hnb & Hlo & Hhi) | Hsc]]; [lia| |].
+ pose proof (heap_blk L HIx _ _ _ _ _ _ HP Hb) as (_ & _ & _ & Hbhi & _). lia.
+ intros Hin. pose proof (hl_scratch_in_img L a (Hsc a Hin)). pose proof (hl_img_range L). lia.
- destruct H1 as [H1 | [(b & n & Hb & Hnb & Hlo & Hhi) | Hsc]].
+ intros Hin. pose proof (hl_static_in_img L a Hc). pose proof (hl_img_range L). lia.
+ intros Hin. destruct (in_block_facts L HIx _ _ _ _ _ _ a HP Hb ltac:(lia)) as (_ & Hns & _). exact (Hns Hc).
+ intros Hin. exact (hl_scratch_not_static L a (Hsc a Hin) Hc).
- destruct b as [ba bn]. cbn in Hbr. pose proof (Hsub _ Hb0) as Hb.
destruct H1 as [H1 | [(b & n & Hb' & Hnb & Hlo & Hhi) | Hsc]].
+ pose proof (heap_blk L HIx _ _ _ _ _ _ HP Hb) as (_ & _ & _ & Hbhi & _). lia.
+ intros Hin. assert (Hne : b <> ba).
{ intros ->. apply Hnb. rewrite (nodup_addr_size LB ba n bn (heap_blk_nodup L HIx _ _ _ _ HP) Hb' Hb). exact Hb0. }
destruct (in_block_facts L HIx _ _ _ _ _ _ a HP Hb' ltac:(lia)) as (_ & _ & Hdis).
exact (Hdis ba bn Hb ltac:(congruence) ltac:(lia)).
+ intros Hin. pose proof (heap_blk_img L HIx _ _ _ _ _ _ HP Hb) as Himg.
pose proof (hl_scratch_in_img L a (Hsc a Hin)). lia.
Qed.
End RC__4.

Ltac in_prefix := first [ left; reflexivity | right; in_prefix ].

Ltac solve_frameW :=
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
first [ left; split; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia
| right; left; do 2 eexists; split; [ in_prefix | lia ]
| right; right; intros; simpl hl_scratch; lia ].

Ltac try_blocks LBc tac :=
lazymatch LBc with
| (?a, ?n) :: ?r => first [ exists a, n; tac | try_blocks r tac ]
end.

Ltac try_block_at LBc lo tac :=
lazymatch LBc with
| (?a, ?n) :: ?r => first [ (constr_eq a lo; exists a, n; tac) | try_block_at r lo tac ]
| ?P ++ ?r => try_block_at r lo tac
end.

Ltac solve_frameW_with HPc :=
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
first [ (lazymatch goal with |- _ \/ (exists a n, In (a, n) _ /\ a <= ?lo /\ _) \/ _ =>
right; left;
lazymatch type of HPc with HEAP _ _ _ ?LBc _ _ => try_block_at LBc lo ltac:(split; [ in_prefix | lia ]) end end)
| left; split; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia
| right; left;
lazymatch type of HPc with HEAP _ _ _ ?LBc _ _ =>
try_blocks LBc ltac:(split; [ in_prefix | lia ])
end
| right; right; intros; simpl hl_scratch; lia ].

Ltac heap_now L HIx HP MU WM MI :=
eapply (heap_frame L HIx); [ exact HP | eapply (frame_writes_ok L HIx _ _ _ _ _ _ HP MU); solve_frameW_with HP | exact WM | exact MI ].

Ltac simpl_layout :=
simpl hl_segs in *; simpl hl_stack in *; simpl hl_tp in *; simpl hl_malloc in *; simpl hl_free in *;
simpl hl_calloc in *; simpl hl_realloc in *.
Ltac alloc_side :=
simpl hl_segs; simpl hl_stack; simpl hl_tp; simpl hl_malloc; simpl hl_free; simpl hl_calloc; simpl hl_realloc;
rewrite ?unsigned_lit by lia;
lazymatch goal with
| |- forall _, _ => idtac
| |- _ \/ _ => idtac
| |- _ =>
lazymatch goal with
| |- stk _ _ _ _ => eassumption
| |- rw_cells _ _ _ _ => eassumption
| |- @eq (bv _) _ _ => first [ reflexivity | eassumption | symmetry; eassumption | apply bv_eq; rewrite ?unsigned_lit by lia; lia ]
| |- _ mod 16 = 0 =>
first [ assumption
| match goal with H : bv_unsigned ?sp mod 16 = 0 |- (bv_unsigned ?sp + ?k) mod 16 = 0 =>
rewrite <- Zplus_mod_idemp_l, H; reflexivity end
| lia ]
| |- _ => first [ lia | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia ]
end end. Ltac mkr__alloc_side_5 := simpl hl_segs; simpl hl_stack; simpl hl_tp; simpl hl_malloc; simpl hl_free; simpl hl_calloc; simpl hl_realloc;
rewrite ?unsigned_lit by lia;
lazymatch goal with
| |- forall _, _ => idtac
| |- _ \/ _ => idtac
| |- _ =>
lazymatch goal with
| |- stk _ _ _ _ => eassumption
| |- rw_cells _ _ _ _ => eassumption
| |- @eq (bv _) _ _ => first [ reflexivity | eassumption | symmetry; eassumption | apply bv_eq; rewrite ?unsigned_lit by lia; lia ]
| |- _ mod 16 = 0 =>
first [ assumption
| match goal with H : bv_unsigned ?sp mod 16 = 0 |- (bv_unsigned ?sp + ?k) mod 16 = 0 =>
rewrite <- Zplus_mod_idemp_l, H; reflexivity end
| lia ]
| |- _ => first [ lia | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia ]
end end.

Ltac alloc_call SPEC L HIx HP MU WM MI :=
apply evt_RZ_done; eapply SPEC; [ heap_now L HIx HP MU WM MI | .. ]; try alloc_side.
Section RC__5. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma fresh_not_in : forall L (HIx : heap_iface L) A LB m md r n k,
HEAP L HIx A ((r, n) :: LB) m md -> ~ In (r, k) LB.
Proof.
intros L HIx A LB m md r n k HP Hin.
pose proof (heap_blk_nodup L HIx _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst.
apply Hni. exact (in_map blk_addr _ _ Hin).
Qed.

#[using="Type"] Lemma nodup_prefix_suffix : forall (P LB0 : list blk) a n k,
List.NoDup (map blk_addr (P ++ LB0)) -> In (a, n) P -> ~ In (a, k) LB0.
Proof.
induction P as [|[b j] P IH]; cbn; intros LB0 a n k ND Hin Hin0; [tauto|].
inversion ND as [|x l Hni Hnd]; subst.
destruct Hin as [E | Hin].
- inversion E; subst. apply Hni. rewrite map_app. apply in_app_iff. right. exact (in_map blk_addr _ _ Hin0).
- exact (IH LB0 a n k Hnd Hin Hin0).
Qed.
End RC__5.

Ltac prefix_of LBc LB0 :=
lazymatch LBc with
| LB0 => constr:(@nil blk)
| ?x :: ?r => let p := prefix_of r LB0 in constr:(x :: p)
end.

Ltac not_in_old L HIx HPc :=
lazymatch goal with |- ~ In (?a, ?k) ?LB0 =>
lazymatch type of HPc with HEAP _ _ _ ?LBc _ _ =>
let P := prefix_of LBc LB0 in
eapply (nodup_prefix_suffix P LB0 a _ k);
[ change (P ++ LB0) with LBc; exact (heap_blk_nodup L HIx _ _ _ _ HPc) | in_prefix ]
end
end.

Ltac solve_clientW L HIx HPc :=
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
first [ (lazymatch goal with |- _ \/ (exists a n, In (a, n) _ /\ _ /\ a <= ?lo /\ _) \/ _ =>
right; left;
lazymatch type of HPc with HEAP _ _ _ ?LBc _ _ => try_block_at LBc lo ltac:(split; [ in_prefix | split; [ not_in_old L HIx HPc | lia ] ]) end end)
| left; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia
| right; left;
lazymatch type of HPc with HEAP _ _ _ ?LBc _ _ =>
try_blocks LBc ltac:(split; [ in_prefix | split; [ not_in_old L HIx HPc | lia ] ])
end
| right; right; intros; simpl hl_scratch; lia ].

Ltac in_tail Hb := cbn [In app]; repeat (first [ exact Hb | apply in_or_app; right; exact Hb | right ]).

Ltac extend_pres L HIx HPR MU WM HPc HPR2 :=
lazymatch type of HPR with heap_pres _ ?LB0 ?SP ?me ?m0 =>
lazymatch type of HPR2 with heap_pres _ _ _ _ ?m2 =>
let H := fresh "HPRx" in
assert (H : heap_pres L LB0 SP me m2);
[ eapply heap_pres_trans; [ exact HPR |];
eapply heap_pres_trans;
[ eapply (heap_pres_of_munch L LB0 SP); [ exact MU | exact WM |];
eapply (client_outside L HIx); [ exact HPc | let Hb := fresh in intros ? Hb; first [ solve [in_tail Hb] | cbn; tauto ]
| unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia | solve_clientW L HIx HPc ]
| eapply heap_pres_weaken; [ exact HPR2 | lia | let Hb := fresh in intros ? Hb; first [ solve [in_tail Hb] | cbn; tauto ] ] ]
| clear HPR; rename H into HPR ]
end end.
Ltac extend_pres2 L HIx HPR MU WM HPc HPR2 := extend_pres L HIx HPR MU WM HPc HPR2.
Section RC__6. Context {RC__ : Q6q3.RunConsts}.

Definition stash (P : Prop) : Prop := P.
#[using="Type"] Lemma stash_i : forall P : Prop, P -> stash P. Proof. exact (fun P p => p). Qed.
#[using="Type"] Lemma stash_e : forall P : Prop, stash P -> P. Proof. exact (fun P p => p). Qed.
End RC__6.
Ltac stash H := apply stash_i in H.
Ltac unstash H := apply stash_e in H.

Ltac open_ret RS :=
let a := fresh "u" in
destruct RS as (?u0 & ?u1 & ?u2 & ?v1 & ?v2 & ?v3 & ?v4 & ?v5 & ?v6 & ?v7 & ?u3 & ?u4 & ?u5 & ?u6 & ->).

Ltac reenter MOK :=
apply rz_evt; [ exact MOK |];
try lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end. Ltac mkr__reenter_6 MOK := apply rz_evt; [ exact MOK |];
try lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end.
Section RC__7. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma blk_ne_01 : forall L (HIx : heap_iface L) A a n b k LB m md,
HEAP L HIx A ((a, n) :: (b, k) :: LB) m md -> a <> b.
Proof.
intros L HIx A a n b k LB m md HP E. subst.
pose proof (heap_blk_nodup L HIx _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst.
apply Hni. left. reflexivity.
Qed.

#[using="Type"] Lemma rw_cells_recast_prefix : forall segs m A cs1 cs1' rest,
rw_cells segs m A (cs1 ++ rest) ->
cells_wf cs1' -> cells_bytes cs1' = cells_bytes cs1 -> cells_size cs1' = cells_size cs1 ->
rw_cells segs m A (cs1' ++ rest).
Proof.
intros segs m A cs1 cs1' rest H Hwf HB HS.
destruct H as [[Hwf0 HB0] HW0].
apply cells_wf_app in Hwf0 as [H1 H2].
eapply rw_cells_recast.
- split; [split; [apply cells_wf_app; split; [exact H1| exact H2] | exact HB0] | exact HW0].
- apply cells_wf_app. split; assumption.
- rewrite !cells_bytes_app, HB. reflexivity.
- rewrite !cells_size_app, HS. reflexivity.
Qed.

#[using="Type"] Lemma bytes_eq_by_unsigned : forall l1 l2 : list byte,
map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
injection H as Hb Hl. f_equal; [apply bv_eq; exact Hb | apply IH; exact Hl].
Qed.
End RC__7.

Ltac jhdr_split H :=
lazymatch type of H with
| rw_cells ?segs ?m ?A (C8 (Z_to_bv 64 ?w) :: ?rest) =>
let lo := eval vm_compute in (Z.modulo w 4294967296) in
let hi := eval vm_compute in (Z.div w 4294967296) in
apply (rw_cells_recast_prefix segs m A [C8 (Z_to_bv 64 w)] [C4 (Z_to_bv 64 lo); C4 (Z_to_bv 64 hi)] rest) in H;
[ | cbn; auto | apply bytes_eq_by_unsigned; vm_compute; reflexivity | reflexivity ];
cbn [app] in H
end.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Local Open Scope Z_scope.
Section RC__8. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma land7_of_mod16 : forall p, p mod 16 = 0 -> Z.land p 7 = 0.
Proof.
intros p Hp. change 7 with (2^3 - 1). rewrite zb_land_mask by lia.
apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ 16); [exists 2; reflexivity | apply Z.mod_divide; lia].
Qed.
#[using="Type"] Lemma land3_of_mod16 : forall p, p mod 16 = 0 -> Z.land p 3 = 0.
Proof.
intros p Hp. change 3 with (2^2 - 1). rewrite zb_land_mask by lia.
apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ 16); [exists 4; reflexivity | apply Z.mod_divide; lia].
Qed.
End RC__8.

Ltac ubsan_align H :=
lazymatch type of H with ?p mod 16 = 0 =>
rewrite ?(unsigned_lit p) by lia;
first [ rewrite (land7_of_mod16 p H) | rewrite (land3_of_mod16 p H) ];
if_false
end.
Section RC__9. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma sx32_small : forall vi, -2^31 <= vi < 2^31 -> sx32 (Z_to_bv 64 vi) = Z_to_bv 64 vi.
Proof.
intros vi H. unfold sx32. rewrite Z_to_bv_unsigned. apply Z_to_bv_eqm.
unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2^64). change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
Z.div_mod_to_equations. lia.
Qed.
End RC__9.

Ltac norm_sx32 :=
repeat match goal with
| |- context [sx32 (Z_to_bv 64 ?v)] => rewrite (sx32_small v) by lia
end.
Section RC__10. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma swrap32_id : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
intros x Hx. apply (bv_swrap_small 32). unfold bv_half_modulus, bv_modulus. cbn. cbn in Hx. lia.
Qed.
#[using="Type"] Lemma swrap32_shift : forall x k, bv_swrap 32 (x + k * 4294967296) = bv_swrap 32 x.
Proof. intros. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
replace (x + k * 4294967296 + 4294967296 / 2)%Z with ((x + 4294967296/2) + k * 4294967296)%Z by lia.
rewrite Z_mod_plus_full. reflexivity. Qed.
End RC__10.

Ltac norm_w32 :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?v)] => rewrite (unsigned_lit v) by lia
| |- context [bv_signed (Z_to_bv 64 ?v)] => rewrite (signed_lit v) by lia
| |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
| |- context [sx32 (Z_to_bv 64 ?v)] => rewrite (sx32_small v) by lia
end.

Ltac shr :=
lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?mm _) =>
lazymatch R with
| TNode
(TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
(Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
None
(TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2)
(TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty)))) =>
idtac "pc=" pc "mem=" mm; idtac "ra=" x1 "sp=" x2; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19 "s4=" x20 "s5=" x21;
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16 "a7=" x17;
idtac "t0=" x5 "t1=" x6 "t2=" x7
| _ => idtac "regs not in mkR form"
end end.
