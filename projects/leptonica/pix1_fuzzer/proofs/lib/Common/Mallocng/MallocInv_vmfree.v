(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_vm MallocInv_vmops.
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma maps_pw_base : forall l b1 s1 b2 s2, maps_pw l -> In (b1, s1) l -> In (b2, s2) l ->
  0 < u s1 -> 0 < u s2 -> u b1 = u b2 -> (b1, s1) = (b2, s2).
Proof.
  intros l b1 s1 b2 s2 Hpw H1 H2 Hs1 Hs2 E.
  destruct (maps_pw_in2 l b1 s1 b2 s2 Hpw H1 H2) as [H | [H | H]]; [exact H | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma mcov_remove : forall l B L x k, maps_pw l -> In (B, L) l -> 0 < u L ->
  (forall b sz, In (b, sz) l -> 0 < u sz) ->
  mcov l x k -> 0 < k -> (x + k <= u B \/ u B + u L <= x \/ exists y, x <= y < x + k /\ ~ (u B <= y < u B + u L)) ->
  (forall y, x <= y < x + k -> ~ (u B <= y < u B + u L)) ->
  mcov (map_remove l B) x k.
Proof.
  intros l B L x k Hpw HinB HL Hpos (b & sz & Hin & H1 & H2) Hk _ Hout.
  exists b, sz. split; [| lia]. apply in_map_remove. split; [exact Hin|]. cbn [fst]. intros ->.
  pose proof (maps_pw_base l B sz B L Hpw Hin HinB (Hpos _ _ Hin) HL eq_refl) as E. injection E as ->.
  apply (Hout x); lia.
Qed.

Lemma vm_maps_nw : forall A h, VMok A h -> maps_nw (vm_maps h).
Proof. intros A h HV b sz Hin. destruct (vm_maps_wf A h HV b sz Hin) as (_ & H & _). ceil. lia. Qed.

Lemma vm_na_nw : forall A h, VMok A h -> maps_nw (vm_noaccess h).
Proof.
  intros A h HV b sz Hin. destruct (vm_na_in A h HV b sz Hin) as (_ & b' & sz' & Hin' & H1 & H2).
  destruct (vm_maps_wf A h HV b' sz' Hin') as (_ & H & _). ceil. lia.
Qed.

Theorem VMok_munmap_xmap : forall A h B L xs,
  WF A -> VMok A h -> a_xmaps A = (B, L) :: xs ->
  0x1000 <= B -> 0 < L -> B + L <= 2^64 ->
  In (Z_to_bv 64 B, Z_to_bv 64 L) (vm_maps h) ->
  region_free (vm_noaccess h) (Z_to_bv 64 B) (Z_to_bv 64 L) = true ->
  (forall x, B <= x < B + L -> ~ dom A x) ->
  VMok (set_xmaps A xs) (vm_munmap (Z_to_bv 64 B) (Z_to_bv 64 L) h).
Proof.
  intros A h B L xs HW HV Hxs HB HL HBL Hin Hfree Hnodom.
  pose proof HV as [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vtop].
  pose proof (vm_maps_nw A h HV) as NW. pose proof (vm_na_nw A h HV) as NWa.
  assert (POS : forall b sz, In (b, sz) (vm_maps h) -> 0 < u sz) by (intros b sz Hb; exact (proj1 (Vmw b sz Hb))).
  assert (UB : u (Z_to_bv 64 B) = B) by (rewrite uZ by lia; reflexivity).
  assert (UL : u (Z_to_bv 64 L) = L) by (rewrite uZ by lia; reflexivity).
  (* [comment removed for export] *)
  assert (COV : forall x k, mcov (vm_maps h) x k -> 0 < k -> (forall y, x <= y < x + k -> ~ (B <= y < B + L)) ->
            mcov (map_remove (vm_maps h) (Z_to_bv 64 B)) x k).
  { intros x k Hc Hk Hout. apply (mcov_remove (vm_maps h) (Z_to_bv 64 B) (Z_to_bv 64 L) x k Vpw Hin ltac:(rewrite UL; lia) POS Hc Hk).
    - right; right. exists x. split; [lia|]. rewrite UB, UL. apply Hout. lia.
    - intros y Hy. rewrite UB, UL. apply Hout. exact Hy. }
  assert (DOMR : forall pg k, (forall y, pg <= y < pg + k -> dom A y) -> forall y, pg <= y < pg + k -> ~ (B <= y < B + L)).
  { intros pg k Hd y Hy Hr. exact (Hnodom y Hr (Hd y Hy)). }
  constructor; cbn [vm_maps vm_noaccess vm_brk vm_start_brk vm_reserved vm_munmap a_ctx a_areas a_meta a_pages a_mblocks a_xmaps set_xmaps];
    rewrite ?vm_munmap_maps, ?vm_munmap_noaccess, ?vm_munmap_brk, ?vm_munmap_start_brk, ?vm_munmap_reserved; try assumption.
  - (* [comment removed for export] *) intros ma mt aib slots Hma Hr Hml. destruct (Vg ma mt aib slots Hma Hr Hml) as [Hi Hf].
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem & Hfit & Hce & Hpg).
    destruct (Hpg Hml) as [_ Hhr]. unfold heap_range in Hhr. ceil.
    assert (Hlen : 0 < grp_map_len mt) by (unfold grp_map_len; lia).
    split.
    + apply in_map_remove. split; [exact Hi|]. cbn [fst]. intros E.
      apply (f_equal bv_unsigned) in E. rewrite uZ, UB in E by lia.
      apply (Hnodom B ltac:(lia)). right; left. exists ma, mt, aib, slots. repeat split; auto; lia.
    + rewrite UB, UL. apply maps_subtract_free; [exact NWa | exact Hf].
  - (* [comment removed for export] *) intros Hac. destruct (Va Hac) as (P1 & P2 & P3 & P4). split; [exact P1|]. split; [exact P2|].
    apply map_contains_mcov in P3. apply map_contains_mcov in P4. ceil.
    assert (Hac0 : 0 < a_ctx A KAac) by lia. pose proof (wf_ctx_nonneg A HW KAareas) as Hnn.
    rewrite !uZ in P3, P4 by lia || idtac.
    assert (DJ : forall y, a_ctx A KAareas <= y < a_ctx A KAareas + 4096 * a_ctx A KAac -> ~ (B <= y < B + L)).
    { intros y Hy Hr. destruct P4 as (nb & nsz & Hnin & N1 & N2).
      destruct (proj1 (region_free_spec _ _ _) Hfree nb nsz Hnin) as [D | D]; rewrite ?UB, ?UL in D; rewrite ?uZ in N1, N2 by lia; lia. }
    split; apply map_contains_mcov; rewrite ?uZ by lia.
    + apply COV; [exact P3 | lia | exact DJ].
    + rewrite ?UB, ?UL. apply maps_subtract_cover; [exact NWa | exact P4 | lia |].
      destruct P4 as (nb & nsz & Hnin & N1 & N2).
      destruct (proj1 (region_free_spec _ _ _) Hfree nb nsz Hnin) as [D | D]; rewrite ?UB, ?UL in D; lia.
  - (* [comment removed for export] *) unfold map_remove. apply maps_pw_filter. exact Vpw.
  - (* [comment removed for export] *) intros b sz Hb. apply in_map_remove in Hb. exact (Vmw b sz (proj1 Hb)).
  - (* [comment removed for export] *) intros b sz Hb. rewrite UB, UL in Hb. destruct (in_maps_subtract _ _ _ _ _ Hb) as (b0 & sz0 & H0 & H1).
    pose proof (iv_subtract_in b0 sz0 B (B + L) b sz (NWa b0 sz0 H0) H1) as (I1 & I2 & I3 & I4).
    destruct (Vna b0 sz0 H0) as [S0 C0]. split; [exact (I4 S0)|].
    apply COV; [exact (mcov_sub _ _ _ _ _ C0 I1 I2) | exact (I4 S0) | intros y Hy Hr; lia].
  - (* [comment removed for export] *) intros pg Hpg. destruct (Vac pg Hpg) as [C F]. split.
    + apply COV; [exact C | lia | apply DOMR; intros y Hy; left; exists pg; auto].
    + rewrite UB, UL. apply maps_subtract_free; [exact NWa | exact F].
  - (* [comment removed for export] *) intros pg Hpg. destruct (Vpc pg Hpg) as [C F]. split.
    + apply COV; [exact C | lia | apply DOMR; intros y Hy; right; right; exists pg; auto].
    + rewrite UB, UL. apply maps_subtract_free; [exact NWa | exact F].
  - (* [comment removed for export] *) intros b sz Hb. apply in_map_remove in Hb. destruct Hb as [Hb Hne]. cbn [fst] in Hne.
    destruct (Vall b sz Hb) as [G | [Br | (c & l & Hcl & C1 & C2)]]; [left; exact G | right; left; exact Br | right; right].
    apply in_app_iff in Hcl. rewrite Hxs in Hcl. destruct Hcl as [Hcl | [E | Hcl]].
    + exists c, l. split; [apply in_app_iff; left; exact Hcl | auto].
    + exfalso. injection E as <- <-. pose proof (POS b sz Hb) as Hsz.
      destruct (maps_pw_in2 _ _ _ _ _ Vpw Hb Hin) as [E | [D | D]].
      * injection E as -> ->. apply Hne. reflexivity.
      * rewrite ?UB, ?UL in D. lia.
      * rewrite ?UB, ?UL in D. lia.
    + exists c, l. split; [apply in_app_iff; right; exact Hcl | auto].
Qed.

End WithLayout.
