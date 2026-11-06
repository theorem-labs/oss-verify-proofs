(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30: the helper lemmas of lib/A/WrapMallocARet.v (moved verbatim, everything before its wm_ret_A), in a file
   of their own so that the malloc BODY walk (WrapMallocABodyRet.v) needs them without wm_ret_A. *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image A (asan, pin 1be0f53d96cb), field M2 (wm_ret) of
   a Theorem Labs lane's Record wrap_malloc_walk_cf (lib/Reusable/YGcfMallocCompose.v:165, blob e929a4c12d5b) at
   ARX := ARXh_A B, K := K_A (lib/A/WrapMallocADefs.v): Allocate's return (RA_ALLOC) -> __wrap_malloc's return.
   The machine runs are WrapMallocARetM.m_null / m_blk; this file is the allocator-side glue, by the method of
   plugin-hostd/fuzz_reply's lib/A/RGthinS6.v rt_seg_npost (a working branch 66a127cb11e): the same
   SRr / RGtop framework. Rule 24 and the relocation check: the internal file RULE24-W6PRE.md.
   What the glue does:
   - the stack is not in AOXm_cf at either layout (AR_stack_law_ok_cf for aowned; xs_placed_cf's disjointness from
     the stack extent, static_extents ly's index 8, for xs_cf), so AllocG.alloc_post's frame carries K's frame words
     and the caller's window from memA to mem2;
   - on a block, malloc_cf_apath_success (YGcfApath.v:38) puts (q, n) in blocks S2 and block_user_range_cf
     (YGcfBlockRange.v:31) puts it below ASAN_CEIL, hence off the stack and non-zero;
   - after the run, ARcf at mem' by AR_frame_law_ok_cf (YG0qcf.v:667): the run writes only the caller's stack window
     and errno, neither owned (errno is inside the image and not in Tfib_owned_static), and neither in_band_rw.
   No Admitted / Axiom. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YGcfRoom YG0scf YG0qcf YG0lawscf YGcfApath YGcfBlockRange.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG RGtop YGcfRmodel YAkMemnorm YGcfMallocCompose.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB13 AF0l AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w WrapMallocAConsts WrapMallocARetM WrapMallocADefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP03.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The callee-saved registers, one goal per register (RGthinS.v:34-55). *)
Ltac to_lit r Hr :=
  first [ replace r with (2%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (3%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (4%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (8%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (9%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (18%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (19%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (20%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (21%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (22%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (23%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (24%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (25%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (26%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (27%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity) ].
Ltac cs_cases :=
  intros rk rr Hrk Hrr; unfold acallee_saved in Hrk;
  assert (Kc : rk = 2 \/ rk = 3 \/ rk = 4 \/ rk = 8 \/ rk = 9 \/ rk = 18 \/ rk = 19 \/ rk = 20 \/ rk = 21 \/ rk = 22 \/
    rk = 23 \/ rk = 24 \/ rk = 25 \/ rk = 26 \/ rk = 27) by lia; clear Hrk;
  destruct Kc as [Kc|[Kc|[Kc|[Kc|[Kc|[Kc|[Kc|[Kc|[Kc|[Kc|[Kc|[Kc|[Kc|[Kc|Kc]]]]]]]]]]]]]];
  rewrite Kc in Hrr; to_lit rr Hrr; clear Hrr Kc.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* RGthinS.v:62-145, at tfibsegs. *)
Lemma val_mem_pw_r : forall (H : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall x, m' x = m x) -> val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof. intros H m m' a n v E V k Hk. rewrite <- (V k Hk). unfold mbyte, mrestrict. rewrite E. reflexivity. Qed.
Lemma aview_pw_r : forall (H : word -> bool) (m m' : word -> option byte) a,
(forall x, m' x = m x) -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof. intros H m m' a E. apply aview_same. apply E. Qed.
Lemma apresent_pw_r : forall (H : word -> bool) (m m' : word -> option byte) a,
(forall x, m' x = m x) -> apresent H m a -> apresent H m' a.
Proof. intros H m m' a E P. apply (apresent_same H m m' a (E _) P). Qed.
Lemma val_mem_xfer_r : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> aview tfibsegs H' m' (a + Z.of_nat k) = aview tfibsegs H m (a + Z.of_nat k)) ->
val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v E V k Hk. specialize (V k Hk). specialize (E k Hk). unfold aview in E. rewrite V in E. cbn in E.
destruct (mbyte tfibsegs (mrestrict H' m') (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate]. cbn in E. injection E as E.
f_equal. apply bv_eq. exact E.
Qed.
Lemma val_mem_raw_r : forall (H : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof. intros H m m' a n v E V k Hk. rewrite <- (V k Hk). unfold mbyte, mrestrict. rewrite (E k Hk). reflexivity. Qed.
Lemma apresent_vis_r : forall (H : word -> bool) (m : word -> option byte) a, apresent H m a -> aview tfibsegs H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.
Lemma vis_apresent_hi_r : forall (H : word -> bool) (m : word -> option byte) a, TFIB_IMG_END <= a < 2 ^ 64 ->
aview tfibsegs H m a <> None -> apresent H m a.
Proof.
intros H m a Ha Hv. unfold aview in Hv. destruct (mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:E; [|exfalso; exact (Hv eq_refl)].
exact (mbyte_high_apresent H m a b Ha E).
Qed.
Lemma same_io_wvb_r : forall md mat, same_io md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. destruct md. repeat split; reflexivity. Qed.
Lemma w64_unsigned_r : forall w : word, w64 (bv_unsigned w) = w.
Proof. intros w. unfold w64. apply Z_to_bv_bv_unsigned. Qed.
Lemma ap_get_r : forall (regs regs' : bvmap 5 word) (k : Z) (r : bv 5),
aregs_preserved regs regs' -> acallee_saved k -> bv_unsigned r = k -> getr regs' r = getr regs r.
Proof.
intros regs regs' k r P Hk Hr. replace r with (Z_to_bv 5 k) by (subst k; apply Z_to_bv_bv_unsigned). apply P. exact Hk.
Qed.
Lemma ap_mk_r : forall (regs regs' : bvmap 5 word),
(forall k (r : bv 5), acallee_saved k -> bv_unsigned r = k -> getr regs' r = getr regs r) -> aregs_preserved regs regs'.
Proof.
intros regs regs' Hm k Hk. apply (Hm k); [exact Hk|]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 5) with 32. apply Z.mod_small. unfold acallee_saved in Hk. lia.
Qed.
Lemma aview_mod_r : forall (H : word -> bool) m a, aview tfibsegs H m a = aview tfibsegs H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte, mrestrict.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma apresent_wview_r : forall (H : word -> bool) (m : word -> option byte) (x : word),
apresent H m (bv_unsigned x) -> wview tfibsegs m x <> None.
Proof.
intros H m x [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. unfold wview. rewrite Hb. discriminate.
Qed.
(* YAkMemnorm.memnorm_upd's argument (YAkMemnorm.v:85-101), for a write confined to two windows whose bytes are
   writable in the old memory. *)
Lemma memnorm_write_r : forall (m m' : word -> option byte) lo hi e,
YAkMemnorm.memnorm tfibsegs m ->
(forall x : word, ~ (lo <= bv_unsigned x < hi) -> ~ (e <= bv_unsigned x < e + 4) -> m' x = m x) ->
(forall x : word, lo <= bv_unsigned x < hi -> wview tfibsegs m x <> None) ->
(forall x : word, e <= bv_unsigned x < e + 4 -> wview tfibsegs m x <> None) ->
YAkMemnorm.memnorm tfibsegs m'.
Proof.
intros m m' lo hi e MN Hout H1 H2. pose proof MN as [Hi Ht].
assert (KEY : forall x : word, wview tfibsegs m x <> None ->
  YAkMemnorm.ro_addr tfibsegs x = false /\
  (find_segment tfibsegs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE)).
{ intros x W. unfold wview in W. revert W. destruct (m x) as [b0|] eqn:E; intros W; [exact (conj (Hi x b0 E) (Ht x b0 E))|].
  unfold YAkMemnorm.ro_addr. revert W.
  destruct (find_segment tfibsegs (bv_unsigned x) 1) as [seg|]; intros W; [|exfalso; exact (W eq_refl)].
  revert W. destruct (seg_writable seg); intros W; [|exfalso; exact (W eq_refl)].
  split; [reflexivity | left; discriminate]. }
assert (CASES : forall x : word, (lo <= bv_unsigned x < hi) \/ (e <= bv_unsigned x < e + 4) \/ m' x = m x).
{ intros x. destruct (Z_le_gt_dec lo (bv_unsigned x)) as [A1|A1]; [destruct (Z_lt_ge_dec (bv_unsigned x) hi) as [A2|A2]|].
  - left. split; assumption.
  - destruct (Z_le_gt_dec e (bv_unsigned x)) as [B1|B1]; [destruct (Z_lt_ge_dec (bv_unsigned x) (e + 4)) as [B2|B2]|].
    + right. left. split; assumption.
    + right. right. apply Hout; lia.
    + right. right. apply Hout; lia.
  - destruct (Z_le_gt_dec e (bv_unsigned x)) as [B1|B1]; [destruct (Z_lt_ge_dec (bv_unsigned x) (e + 4)) as [B2|B2]|].
    + right. left. split; assumption.
    + right. right. apply Hout; lia.
    + right. right. apply Hout; lia. }
split; intros x b E; destruct (CASES x) as [C|[C|C]].
- exact (proj1 (KEY x (H1 x C))).
- exact (proj1 (KEY x (H2 x C))).
- rewrite C in E. exact (Hi x b E).
- exact (proj2 (KEY x (H1 x C))).
- exact (proj2 (KEY x (H2 x C))).
- rewrite C in E. exact (Ht x b E).
Qed.
Lemma val_mem_rd32_r : forall (H : word -> bool) m a v, val_mem tfibsegs (mrestrict H m) a 4 v -> rd32 (aview tfibsegs H m) a v.
Proof.
intros H m a v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
apply unsigned_lit_small8. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

Section b.
Variable segs0 : list Segment.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (nmax al atp acf : Z).

(* errno is inside the image and not in Tfib_owned_static, so it is never owned (lib/Reusable/YFim.v:524's argument). *)
Lemma errno_not_owned_A : forall ly S Hp W mem md a,
ARcf tfibsegs B ly S Hp W mem md -> TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> ~ aowned B ly S a.
Proof.
intros ly S Hp W mem md a AR Ha O.
assert (IMGa : in_img tfibsegs a).
{ unfold in_img. rewrite AB13.tfib_segs_eq.
  eexists. split; [do 3 right; left; reflexivity|]. cbn. unfold TFIB_ERRNO in Ha. lia. }
apply (proj1 (AR_owned_image_law_ok_cf tfibsegs B ly S Hp W mem md a AR IMGa)) in O.
rewrite (ts_owned B TB) in O. unfold Tfib_owned_static in O. apply Exists_exists in O as (r & Hr & [X1 X2]).
cbn [In] in Hr. unfold TFIB_ERRNO in Ha.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [cbn [fst snd] in X1, X2; lia|] | False => destruct Hr end.
Qed.
End b.
End a.
