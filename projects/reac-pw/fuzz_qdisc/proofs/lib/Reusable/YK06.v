(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK06.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YK06.v (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_qdisc. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the model's Linux placement rule for anonymous mmaps (the hint and the page-aligned length)); internal commit ids in comments replaced by public commits or removed. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State StackLayout Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK10.
Unset Lia Cache. Unset Nia Cache.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
Import ListNotations.
Open Scope Z_scope.
Definition alloc_ceiling : Z := 0x7fff7f800000.
Lemma alloc_ceiling_val : alloc_ceiling = 0x7fff7f800000.
Proof. reflexivity. Qed.
Definition bottomup_floor : Z := 0x2aaaaaaab000.
Lemma bottomup_floor_val : bottomup_floor = 0x2aaaaaaab000.
Proof. reflexivity. Qed.
(* 08b1429 (the model's Common/AsanCeil.v): the null-hint gate is Linux's placement
   ([Mmap.linux_place], decided by [Placement.linux_place_b]) under either THP setting, and
   [placement_policy] is a theorem.  The floor lemmas are gone upstream: a floor no longer
   implies Linux's address. *)
Definition placement_ok (h : VmMaps) (aZ nZ : Z) : Prop :=
exists thp : bool, linux_place h thp (Z_to_bv 64 0) nZ aZ.
Definition placement_ok_b (h : VmMaps) (aZ nZ : Z) : bool :=
(match linux_place_b h true (Z_to_bv 64 0) nZ with
| Some x => (x =? aZ)%Z | None => false end)
|| (match linux_place_b h false (Z_to_bv 64 0) nZ with
| Some x => (x =? aZ)%Z | None => false end).
Lemma placement_ok_b_iff : forall h aZ nZ,
0 < nZ -> nZ mod page_size = 0 ->
(placement_ok_b h aZ nZ = true <-> placement_ok h aZ nZ).
Proof.
intros h aZ nZ HnPos HnAl. unfold placement_ok_b, placement_ok.
assert (K : forall thp,
(match linux_place_b h thp (Z_to_bv 64 0) nZ with
| Some x => (x =? aZ)%Z | None => false end) = true
<-> linux_place h thp (Z_to_bv 64 0) nZ aZ).
{ intro thp.
destruct (linux_place_b_spec h thp (Z_to_bv 64 0) nZ HnPos HnAl)
as [Hsome Hnone].
destruct (linux_place_b h thp (Z_to_bv 64 0) nZ) as [x|] eqn:Hb.
- split.
+ intro E. apply Z.eqb_eq in E. subst x. now apply Hsome.
+ intro Hp. apply Z.eqb_eq.
exact (linux_place_unique _ _ _ _ _ _ (proj1 (Hsome x) eq_refl) Hp).
- split; [discriminate|]. intro Hp. exfalso.
exact (proj1 Hnone eq_refl aZ Hp). }
rewrite orb_true_iff, (K true), (K false).
split; [intros [H|H]; [now exists true | now exists false]
| intros ([|] & H); [now left | now right]].
Qed.
Lemma placement_ok_thp : forall h thp aZ nZ,
linux_place h thp (Z_to_bv 64 0) nZ aZ -> placement_ok h aZ nZ.
Proof. intros h thp aZ nZ H. now exists thp. Qed.
Definition hint_placement_ok_b (addr : word) (h : VmMaps) (aZ nZ : Z) : bool :=
if w_is0 addr then placement_ok_b h aZ nZ else true.
Lemma hint_placement_ok_b_nonnull : forall addr h aZ nZ,
w_is0 addr = false -> hint_placement_ok_b addr h aZ nZ = true.
Proof. intros addr h aZ nZ H. unfold hint_placement_ok_b. now rewrite H. Qed.
Lemma topdown_search_window : forall h nZ a,
topdown_search h nZ a -> (a + nZ <= mmap_top h)%Z \/ (task_unmapped_base <= a)%Z.
Proof.
intros h nZ a H. unfold topdown_search in H. cbv zeta in H.
destruct H as [[(_ & _ & Hhi & _) _] | [_ [(_ & Hlo & _ & _) _]]];
[now left | now right].
Qed.
Lemma placement_ok_window : forall h aZ nZ,
placement_ok h aZ nZ ->
(aZ + nZ <= mmap_top h)%Z \/ (task_unmapped_base <= aZ)%Z.
Proof.
intros h aZ nZ (thp & Hpl).
unfold linux_place in Hpl. cbv zeta in Hpl.
assert (Hg : hint_address (Z_to_bv 64 0) = 0) by (vm_compute; reflexivity).
rewrite Hg, Z.eqb_refl in Hpl. cbv iota in Hpl.
pose proof pmd_size_pos as Hpmd.
destruct (thp && (nZ mod pmd_size =? 0)%Z)%bool.
- destruct Hpl as [(ret & Hret & ->)|[_ Hts]].
+ pose proof (thp_align_bounds ret) as [Hb1 Hb2].
destruct (topdown_search_window _ _ _ Hret) as [Hhi|Hlo];
[left|right]; lia.
+ exact (topdown_search_window _ _ _ Hts).
- exact (topdown_search_window _ _ _ Hpl).
Qed.
Definition placement_policy : Prop :=
forall (h : VmMaps) (thp : bool) (a : word) (nZ : Z),
0 < nZ -> nZ mod page_size = 0 ->
linux_place h thp (Z_to_bv 64 0) nZ (bv_unsigned a) ->
placement_ok_b h (bv_unsigned a) nZ = true.
Theorem placement_policy_holds : placement_policy.
Proof.
intros h thp a nZ HnPos HnAl Hpl.
apply (placement_ok_b_iff h (bv_unsigned a) nZ HnPos HnAl).
now exists thp.
Qed.
Definition init_sp_ok (h : VmMaps) : Prop := sp_window_lo <= bv_unsigned (vm_init_sp h).
Lemma alloc_ceiling_le_alloc_top : forall h, init_sp_ok h -> alloc_ceiling <= alloc_top h.
Proof. intros h H. unfold init_sp_ok, sp_window_lo in H. unfold alloc_top, alloc_ceiling, stack_max_size. lia. Qed.
Lemma alloc_top_ge_of_ceiling : forall h z, init_sp_ok h -> z <= alloc_ceiling -> z <= alloc_top h.
Proof. intros h z H Hz. pose proof (alloc_ceiling_le_alloc_top h H). lia. Qed.
Lemma init_sp_ok_init_model : forall reserved brk0 mbase sp lim inp,
valid_sp sp -> init_sp_ok (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).
Proof. intros reserved brk0 mbase sp lim inp (Hlo & _ & _). unfold init_sp_ok. cbn. exact Hlo. Qed.
Lemma init_sp_ok_same : forall h h', vm_init_sp h' = vm_init_sp h -> init_sp_ok h -> init_sp_ok h'.
Proof. intros h h' E H. unfold init_sp_ok in *. rewrite E. exact H. Qed.
Lemma init_sp_ok_mkVmMapsFull : forall h r m na sb b l mb,
init_sp_ok h -> init_sp_ok (mkVmMapsFull r m na sb b l mb (vm_init_sp h)).
Proof. intros. unfold init_sp_ok in *. cbn. assumption. Qed.
Lemma page_round_up_Z_ge_all : forall z, z <= page_round_up_Z z.
Proof.
intros z. unfold page_round_up_Z, page_size.
pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hr. lia.
Qed.
Lemma mmap_off_aligned_b_0 : mmap_off_aligned_b (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mmap_anon_b_of_core : forall flags c,
mmap_flags_core flags = c -> Z.testbit c 5 = true -> mmap_anon_b flags = true.
Proof.
intros flags c Hc Hb. unfold mmap_anon_b. apply negb_true_iff. apply Z.eqb_neq. intro H0.
unfold mmap_flags_core in Hc.
pose proof (Z.land_spec (bv_unsigned flags) MAP_ANONYMOUS 5) as HL. rewrite H0, Z.bits_0 in HL.
pose proof (Z.ldiff_spec (bv_unsigned flags) MAP_NORESERVE 5) as HD. rewrite Hc, Hb in HD.
change (Z.testbit MAP_ANONYMOUS 5) with true in HL. change (Z.testbit MAP_NORESERVE 5) with false in HD.
destruct (Z.testbit (bv_unsigned flags) 5); discriminate.
Qed.
Lemma page_round_up_Z_aligned' : forall z, page_round_up_Z z mod page_size = 0.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.
Lemma page_round_up_Z_pos' : forall z, 0 < z -> 0 < page_round_up_Z z.
Proof. intros z Hz. pose proof (page_round_up_Z_ge z). lia. Qed.
Definition zero_random_draw (rdraw : bv 128) : Prop := rdraw = Z_to_bv 128 0.
Lemma at_random_bytes_zero : at_random_bytes (Z_to_bv 128 0) = repeat (Z_to_bv 8 0) 16.
Proof. vm_compute. reflexivity. Qed.
Lemma firstn1_skipn_nth : forall (l : list byte) (i : nat) (d : byte),
(i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
Proof.
induction l as [|x l IH]; intros i d Hi; cbn in Hi; [lia|].
destruct i as [|i]; cbn; [reflexivity|]. apply IH. lia.
Qed.
