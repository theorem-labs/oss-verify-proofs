(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormG.v (a working branch 30a1993588f, c5 + memnorm; file sha256 b8514cd1dd81) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10: memnorm across the runs of the frozen Allocate / Deallocate chain, the shared base of the
   memnorm twins (task MEMNORM, c-asan; integrator ReallocPrimary).  Image-free.
   rule 24: no function proved (kind: generic run invariant + engine lemmas).

   WHY NOT ONE GENERIC LEMMA: `memnorm (mem c) -> amreal t W c Q -> amreal t W c (Q /\ memnorm)` is false.  Its IRet
   case is `SRr W c Q -> SRr W c (Q /\ memnorm)` (YG0d.v:75), and SRr is CPS (YA0n.v:36-39): the continuation may be
   called at a state the run never reaches (take Q0 := the one state c_h with AI, a read-only byte in its overlay and a
   next step to SError: SRr W c Q0 holds since srealizes c_h T is false for every T, but SRr W c (Q0 /\ memnorm) has an
   empty continuation and so needs srealizes c T for every T, false at T := fun _ => False by srealizes_nonempty).  So
   memnorm is carried through each run, the way YC80x.v's _inv runners carry an invariant P.

   WHAT:
   1. copies (byte-identical bodies, path and sha on each block): the invariant laws srr_inv_laws and the runners
      SRr_msteps_inv / SRr_step_inv; the memnorm instance srr_inv_laws_memnorm_k and the keep forms srr_inv_laws_imp /
      srr_inv_call / srr_inv_mn; the region_free facts down to region_free_reserved_off_segs_low.
   2. the two memory shapes a kernel answer makes: memnorm_zfill (a grant, by YAkMemnorm.memnorm_frame_off_segs),
      memnorm_unfill (an unmap, by YAkMemnorm.memnorm_sub), and memnorm_zfill_reserved (a grant clear of the reserved
      list, through region_free_reserved_off_segs_low).
   3. LPS's syscall effect (Run.v:175 apply_effect) directly: memnorm_apply_effect (no writes, no copies, every zero
      range below TASK_SIZE and clear of the segments; unmaps only drop bytes).
   4. the kernel-answer law over sstep_cfg: klaw P c := every sstep_cfg step from c keeps P.  klaw_instr (a machine
      step, from srr_inv_laws), klaw_syscall / klaw_syscall_memnorm (a syscall, from its effects), klaw_node /
      node_klaw (the law and node_ok's answers), klaw_call (a memnorm law lifts to any P closed under memnorm keeps).
      The per-request instances (KMapUser / KMapFreeArray / KMapPtrArray, KMmapSec, KMunmapSec) are in MemnormGk.v.
   5. node twins of YA0n.SRr_node / SRr_nodeI and YG0d.SRr_node_tnil that carry P across the node by klaw.
   6. amreal_m P t W c Q := P (mem c) -> amreal t W c (Q /\ P (mem c')), the invariant-carrying amreal, with its
      structural rules (ret, ibind, mbind, SRr_pre, world_le, mono, spin, fail) and the two IAsk rules (amreal_m_depot,
      amreal_m_node: the node's answers keep P by klaw at the ecall).  amreal_m_sound is the sound form of the
      withdrawn generic lemma.
   No arm is proved here.  The Require closure has no lib/Lib file and no lia redefinition. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Local Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1a. copy of proofs/omx-clap-core/fuzz_preset/lib/Reusable/YC80x.v:66-121 at 459129c18903 (sha256 c90a27017cc1),  *)
(*     byte-identical.                                                                                               *)
(* The three memory changes of one SRr_msteps run that P must survive. *)
Record srr_inv_laws (segs : list Segment) (P : (word -> option byte) -> Prop) : Prop := {
  sil_mrestrict : forall (H : word -> bool) (m : word -> option byte), P m -> P (YK04.mrestrict H m);
  sil_msteps : forall ms ms', YK0i.msteps segs ms ms' -> P (ms_mem ms) -> P (ms_mem ms');
  sil_munrestrict : forall (H : word -> bool) (full m' : word -> option byte),
    P full -> P m' -> P (YK04.munrestrict H full m') }.
(* The trivial invariant: Section e's runner lemmas are the _inv forms at it. *)
Lemma srr_inv_laws_true : forall segs : list Segment, srr_inv_laws segs (fun _ => True).
Proof.
intros segs. split; intros; exact I.
Qed.
Section s.
Variable segs : list Segment.
Hypothesis Hwx : wx_segs_nowrap segs.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
(* YA0n.SRr_msteps (:149) with P on the start memory and P on the end memory. *)
Lemma SRr_msteps_inv : forall W ms msr' model Q,
msteps segs (restrict (w_H W) ms) msr' ->
P (ms_mem ms) ->
(forall model', same_but_materialized model model' ->
hclean (w_H W) msr' ->
P (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) ->
SRr segs W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
SRr segs W (mkCfg ms model) Q.
Proof.
intros W ms msr' model Q Hms HPm Hk.
apply (SRr_msteps segs Hwx W ms msr' model Q Hms).
intros model' Hsame Hcl. apply (Hk model' Hsame Hcl).
change (P (YK04.munrestrict (w_H W) (ms_mem ms) (ms_mem msr'))).
apply (@sil_munrestrict segs P PLAW); [exact HPm|].
apply (@sil_msteps segs P PLAW (restrict (w_H W) ms) msr' Hms).
change (P (YK04.mrestrict (w_H W) (ms_mem ms))).
apply (@sil_mrestrict segs P PLAW). exact HPm.
Qed.
(* YA0n.SRr_step (:133), one hand step, with P on the start memory and P on the end memory. *)
Lemma SRr_step_inv : forall W ms msr' model Q,
ms_svc_pending ms = None ->
RiscvSemantics.step segs (restrict (w_H W) ms) = MachineOk msr' ->
P (ms_mem ms) ->
(forall model', same_but_materialized model model' ->
P (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) ->
SRr segs W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
SRr segs W (mkCfg ms model) Q.
Proof.
intros W ms msr' model Q Hsvc Hs HPm Hk.
apply (SRr_step segs Hwx W ms msr' model Q Hsvc Hs).
intros model' Hsame. apply (Hk model' Hsame).
change (P (YK04.munrestrict (w_H W) (ms_mem ms) (ms_mem msr'))).
apply (@sil_munrestrict segs P PLAW); [exact HPm|].
apply (@sil_msteps segs P PLAW (restrict (w_H W) ms) msr').
- apply (msteps_one segs (restrict (w_H W) ms) msr'); [exact Hsvc | exact Hs].
- change (P (YK04.mrestrict (w_H W) (ms_mem ms))).
  apply (@sil_mrestrict segs P PLAW). exact HPm.
Qed.
End s.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1b. copy of proofs/omx-clap-core/fuzz_preset/lib/Reusable/YSRrMemnorm.v:29-68 at 459129c18903 (sha256 74489f54fb24), *)
(*     byte-identical (over this lib's YAkMemnorm.v, the copy of the bytes sha256 b000fb9776e8).                      *)
(* The memnorm instance, from YAkMemnorm.v's own lemmas (YAkMemnorm requires no file that overrides lia). *)
Lemma srr_inv_laws_memnorm_k : forall segs : list Segment, srr_inv_laws segs (YAkMemnorm.memnorm segs).
Proof.
intros segs. split.
- exact (YAkMemnorm.memnorm_mrestrict segs).
- exact (YAkMemnorm.memnorm_msteps segs).
- exact (YAkMemnorm.memnorm_munrestrict segs).
Qed.

(* the laws survive an implication from a fixed memory: the keep `P mem0 -> P m` is itself an invariant
   (h-rw-pre-5's WalkS4, ruled into this file by h-hpreset-7 11:20Z) *)
Lemma srr_inv_laws_imp : forall (segs : list Segment) (P : (word -> option byte) -> Prop) (mem0 : word -> option byte),
  srr_inv_laws segs P -> srr_inv_laws segs (fun m => P mem0 -> P m).
Proof.
intros segs P mem0 [L1 L2 L3]. split.
- intros H m Hm H0. exact (L1 H m (Hm H0)).
- intros ms ms' Hs Hm H0. exact (L2 ms ms' Hs (Hm H0)).
- intros H full m' Hf Hm H0. exact (L3 H full m' (Hf H0) (Hm H0)).
Qed.

(* the CALL variant (h-hpreset-7 12:22Z, h-rw-pre-5's WalkS7a): a callee whose m-form post gives only the memnorm keep
   `memnorm m -> memnorm m'` carries P across the call when P is closed under that keep. A sibling definition, not a field
   of srr_inv_laws (it is true only at memnorm-derived P, e.g. the keep form below). *)
Definition srr_inv_call (segs : list Segment) (P : (word -> option byte) -> Prop) : Prop :=
  forall m m', (YAkMemnorm.memnorm segs m -> YAkMemnorm.memnorm segs m') -> P m -> P m'.

Lemma srr_inv_call_imp : forall (segs : list Segment) (mem0 : word -> option byte),
  srr_inv_call segs (fun m => YAkMemnorm.memnorm segs mem0 -> YAkMemnorm.memnorm segs m).
Proof. intros segs mem0 m m' Hk HP H0. exact (Hk (HP H0)). Qed.

(* the ENTRY variant (h-hpreset-7 12:23Z, h-rw-pre-5's WalkIval2): P hands memnorm to a callee that demands it at entry.
   Spelled over YAkMemnorm.memnorm (this file is override-free); YAjMemnorm.memnorm has the same body (mem_inv /\ task_mem),
   so a YAj-form consumer converts with `exact`. *)
Definition srr_inv_mn (segs : list Segment) (P : (word -> option byte) -> Prop) : Prop :=
  forall m, P m -> YAkMemnorm.memnorm segs m.

Lemma srr_inv_mn_imp : forall (segs : list Segment) (mem0 : word -> option byte),
  YAkMemnorm.memnorm segs mem0 ->
  srr_inv_mn segs (fun m => YAkMemnorm.memnorm segs mem0 -> YAkMemnorm.memnorm segs m).
Proof. intros segs mem0 HMN0 m H. exact (H HMN0). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1c. copy of proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallMxmn.v:737-795 at 459129c18903 (sha256 4a067e901e80; internal record), *)
(*     byte-identical (in_img is YG0d.v:482, kLowMemEnd YG0f.v:17, find_segment_some_spec YK04.v:265).              *)
(* LPS (State.v:4346 region_free, :4341 iv_overlap): a range region_free clears does not overlap a listed extent *)
Lemma region_free_iv_overlap : forall (l : list (word * word)) (lo n : word) p,
  region_free l lo n = true -> In p l -> iv_overlap lo n (fst p) (snd p) = false.
Proof.
induction l as [|[a0 s0] l IH]; intros lo n p Hf Hin; [destruct Hin|].
cbn [region_free] in Hf. apply andb_prop in Hf as [H1 H2]. destruct Hin as [Ep|Hin].
- subst p. cbn [fst snd]. apply negb_true_iff in H1. exact H1.
- exact (IH lo n p H2 Hin).
Qed.

(* the guard of a fresh grant clears its first list (Mmap.v:1566-1570: vm_reserved h ++ vm_maps h) *)
Lemma region_free_app_l : forall (l1 l2 : list (word * word)) (lo n : word),
  region_free (l1 ++ l2) lo n = true -> region_free l1 lo n = true.
Proof.
induction l1 as [|[a0 s0] l1 IH]; intros l2 lo n Hf; [reflexivity|].
cbn [region_free app] in Hf |- *. apply andb_prop in Hf as [H1 H2]. rewrite H1. exact (IH l2 lo n H2).
Qed.

(* the grant range of a region_free check against segments_reserved segs (Run.v:211-217) holds no segment byte *)
Lemma region_free_reserved_off_segs : forall (segs : list Segment) (a n x : word),
  (forall s, In s segs -> 0 < Z.of_N (seg_size s) -> Z.of_N (seg_base s) + Z.of_N (seg_size s) + page_size <= 2 ^ 64) ->
  region_free (segments_reserved segs) a n = true ->
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n ->
  find_segment segs (bv_unsigned x) 1 = None.
Proof.
intros segs a n x Hsz Hf Hx.
destruct (find_segment segs (bv_unsigned x) 1) as [s|] eqn:Ef; [exfalso | reflexivity].
destruct (find_segment_some_spec segs (bv_unsigned x) 1 s Ef) as (Hin & Hb & Ht).
pose proof (bv_unsigned_in_range _ x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
pose proof (N2Z.is_nonneg (seg_base s)) as Hb0. pose proof (N2Z.is_nonneg (seg_size s)) as Hs0.
specialize (Hsz s Hin ltac:(lia)). unfold page_size in Hsz.
pose proof (region_free_iv_overlap _ a n _ Hf (in_map segment_reservation segs s Hin)) as Hov.
unfold segment_reservation, page_round_down_Z, page_round_up_Z, page_size in Hov. cbn [fst snd] in Hov.
set (t := Z.of_N (seg_base s) + Z.of_N (seg_size s) + 4096 - 1) in Hov.
pose proof (Z.div_mod (Z.of_N (seg_base s)) 4096 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (Z.of_N (seg_base s)) 4096 ltac:(lia)) as M1.
pose proof (Z.div_mod t 4096 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound t 4096 ltac:(lia)) as M2.
assert (Et : t = Z.of_N (seg_base s) + Z.of_N (seg_size s) + 4096 - 1) by reflexivity. clearbody t.
unfold iv_overlap in Hov. rewrite !Z_to_bv_unsigned in Hov. unfold bv_wrap in Hov. change (bv_modulus 64) with (2 ^ 64) in Hov.
rewrite (Z.mod_small (Z.of_N (seg_base s) / 4096 * 4096)) in Hov by lia.
rewrite (Z.mod_small (t / 4096 * 4096 - Z.of_N (seg_base s) / 4096 * 4096)) in Hov by lia.
apply andb_false_iff in Hov as [Hv|Hv]; apply Z.ltb_ge in Hv; lia.
Qed.

(* the same at the engine's segs_low (the Section hypothesis of YCbqG.v / YGcallMx.v / YGcallSx.v): the last byte of a
   nonempty segment is in_img, hence below kLowMemEnd, far below 2 ^ 64 - page_size *)
Lemma region_free_reserved_off_segs_low : forall (segs : list Segment),
  (forall a, in_img segs a -> 0 <= a < kLowMemEnd) ->
  forall (a n x : word),
  region_free (segments_reserved segs) a n = true ->
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n ->
  find_segment segs (bv_unsigned x) 1 = None.
Proof.
intros segs Hlow a n x Hf Hx. apply (region_free_reserved_off_segs segs a n x); [|exact Hf | exact Hx].
intros s Hin Hsz.
assert (Hz : in_img segs (Z.of_N (seg_base s) + Z.of_N (seg_size s) - 1)) by (exists s; split; [exact Hin | lia]).
pose proof (Hlow _ Hz) as Hb. unfold page_size, kLowMemEnd in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The two memory shapes of a kernel answer.                                                                     *)
Section kn.
Variable segs : list Segment.

(* an unmap only drops overlay bytes (YK0v.v:503 unfill; YAkMemnorm.memnorm_sub) *)
Lemma memnorm_unfill : forall (a n : word) (m : word -> option byte),
  YAkMemnorm.memnorm segs m -> YAkMemnorm.memnorm segs (unfill a n m).
Proof.
intros a n m H. apply (YAkMemnorm.memnorm_sub segs m); [exact H|].
intros x b E. unfold unfill in E.
destruct (Z.leb (bv_unsigned a) (bv_unsigned x) && Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n))%bool;
[discriminate E | exact E].
Qed.

(* a grant below TASK_SIZE where no segment lies (YK0v.v:72 zfill; YAkMemnorm.memnorm_frame_off_segs) *)
Lemma memnorm_zfill : forall (a n : word) (m : word -> option byte),
  YAkMemnorm.memnorm segs m ->
  bv_unsigned a + bv_unsigned n <= TASK_SIZE ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n ->
    find_segment segs (bv_unsigned x) 1 = None) ->
  YAkMemnorm.memnorm segs (zfill a n m).
Proof.
intros a n m H Ht Hs.
apply (YAkMemnorm.memnorm_frame_off_segs segs m (zfill a n m) (bv_unsigned a) (bv_unsigned a + bv_unsigned n) H);
[| exact Ht | exact Hs].
intros x Hx. exact (zfill_out a n m x Hx).
Qed.

(* the same, for a grant clear of the reserved list (the guard of every grant the chain asks: YG0c.v:77-78,
   YK13.v:203-206), given segs_low (YG0d.v:482 in_img below YG0f.v:17 kLowMemEnd) *)
Lemma memnorm_zfill_reserved : forall (a n : word) (m : word -> option byte),
  (forall a0, in_img segs a0 -> 0 <= a0 < kLowMemEnd) ->
  YAkMemnorm.memnorm segs m ->
  region_free (segments_reserved segs) a n = true ->
  bv_unsigned a + bv_unsigned n <= TASK_SIZE ->
  YAkMemnorm.memnorm segs (zfill a n m).
Proof.
intros a n m Hlow H Hf Ht. apply memnorm_zfill; [exact H | exact Ht|].
intros x Hx. exact (region_free_reserved_off_segs_low segs Hlow a n x Hf Hx).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. LPS's syscall effect (Run.v:175 apply_effect), directly.                                                      *)

(* a zero range a grant may make: below TASK_SIZE and clear of every segment *)
Definition zero_ok (z : word * word) : Prop :=
  bv_unsigned (fst z) + bv_unsigned (snd z) <= TASK_SIZE /\
  forall x : word, bv_unsigned (fst z) <= bv_unsigned x < bv_unsigned (fst z) + bv_unsigned (snd z) ->
    find_segment segs (bv_unsigned x) 1 = None.

Lemma memnorm_apply_unmaps : forall (m : word -> option byte) us,
  YAkMemnorm.memnorm segs m -> YAkMemnorm.memnorm segs (apply_unmaps m us).
Proof.
intros m us H. apply (YAkMemnorm.memnorm_sub segs m); [exact H|].
intros x b E. unfold apply_unmaps in E. destruct us as [|u us]; [exact E|].
destruct (zeros_cover (u :: us) x); [discriminate E | exact E].
Qed.

Lemma memnorm_apply_zeros : forall (m : word -> option byte) zs,
  YAkMemnorm.memnorm segs m -> Forall zero_ok zs -> YAkMemnorm.memnorm segs (apply_zeros m zs).
Proof.
intros m zs [Hi Ht] HZ. destruct zs as [|z0 zs0]; [split; assumption|].
assert (C : forall x : word, zeros_cover (z0 :: zs0) x = true ->
  find_segment segs (bv_unsigned x) 1 = None /\ bv_unsigned x < TASK_SIZE).
{ intros x Hc. unfold zeros_cover in Hc. apply existsb_exists in Hc as (z & Hz & Hc).
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  destruct (proj1 (Forall_forall zero_ok (z0 :: zs0)) HZ z Hz) as [Hz1 Hz2].
  split; [apply Hz2; lia | lia]. }
split; intros a b E; unfold apply_zeros in E; cbv beta iota in E; revert E;
destruct (zeros_cover (z0 :: zs0) a) eqn:Ec; intros E.
- unfold YAkMemnorm.ro_addr. rewrite (proj1 (C a Ec)). reflexivity.
- exact (Hi a b E).
- right. exact (proj2 (C a Ec)).
- exact (Ht a b E).
Qed.

Lemma ms_mem_set_reg : forall ms r v, ms_mem (set_reg ms r v) = ms_mem ms.
Proof. intros ms r v. unfold set_reg. destruct (bv_eqb r 0); reflexivity. Qed.

(* LPS's effect keeps memnorm when it writes nothing, copies nothing, and zero-fills only below TASK_SIZE clear of the
   segments: the unmaps only drop bytes (Run.v:128), the zeros are grants (Run.v:113). *)
Lemma memnorm_apply_effect : forall ms eff,
  YAkMemnorm.memnorm segs (ms_mem ms) ->
  eff_writes eff = [] -> eff_copies eff = [] -> Forall zero_ok (eff_zeros eff) ->
  YAkMemnorm.memnorm segs (ms_mem (apply_effect ms eff)).
Proof.
intros ms [r ws zs us cs ci] H Hw Hc HZ. cbn [eff_writes eff_copies eff_zeros] in Hw, Hc, HZ. subst ws cs.
unfold apply_effect. cbn [ms_mem eff_writes eff_copies eff_zeros eff_unmaps eff_ret apply_writes apply_copies].
rewrite ms_mem_set_reg. apply memnorm_apply_zeros; [apply memnorm_apply_unmaps; exact H | exact HZ].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The kernel-answer law over sstep_cfg (LPS Run.v:1629): every step from c keeps P.                              *)
Definition klaw (P : (word -> option byte) -> Prop) (c : config) : Prop :=
  forall e c', sstep_cfg segs ACFG c e (SNext c') -> P (ms_mem (cfg_ms c)) -> P (ms_mem (cfg_ms c')).

(* a machine step (no syscall pending): the only SNext step is sstep_cfg_instr, an msteps run of length one *)
Lemma klaw_instr : forall P c, srr_inv_laws segs P -> ms_svc_pending (cfg_ms c) = None -> klaw P c.
Proof.
intros P c PL Hsvc e c' Hs HP. inversion Hs; subst; cbn [cfg_ms] in *; try congruence.
apply (@sil_msteps segs P PL ms ms'); [|exact HP].
apply (msteps_one segs ms ms'); [exact Hsvc|].
eapply mi_account_step_projects. eassumption.
Qed.

(* a syscall: every SNext step is an outcome's effect (sstep_cfg_syscall) or an exit / kill that keeps the memory *)
Lemma klaw_syscall : forall P c,
  ms_svc_pending (cfg_ms c) <> None ->
  (forall x8 eff model' evs, ms_svc_pending (cfg_ms c) = Some x8 ->
    syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) (Ok eff model' evs) ->
    P (ms_mem (cfg_ms c)) -> P (ms_mem (apply_effect (cfg_ms c) eff))) ->
  klaw P c.
Proof.
intros P c Hp Heff e c' Hs HP. inversion Hs; subst; cbn [cfg_ms cfg_model] in *.
- congruence.
- cbn [advance_past_svc ms_mem]. eapply Heff; eassumption.
- exact HP.
- exact HP.
Qed.

(* the memnorm instance: a syscall whose every outcome writes nothing, copies nothing and grants only good zeros *)
Lemma klaw_syscall_memnorm : forall c,
  ms_svc_pending (cfg_ms c) <> None ->
  (forall x8 eff model' evs, ms_svc_pending (cfg_ms c) = Some x8 ->
    syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) (Ok eff model' evs) ->
    eff_writes eff = [] /\ eff_copies eff = [] /\ Forall zero_ok (eff_zeros eff)) ->
  klaw (YAkMemnorm.memnorm segs) c.
Proof.
intros c Hp Hok. apply klaw_syscall; [exact Hp|].
intros x8 eff model' evs Hx Hspec HM. destruct (Hok x8 eff model' evs Hx Hspec) as (Hw & Hc & HZ).
exact (memnorm_apply_effect (cfg_ms c) eff HM Hw Hc HZ).
Qed.

(* the law at a node: from its answers (node_ok's second half), and back to its answers (node_ok's first half) *)
Lemma klaw_node : forall P c (I : Type) (evs : I -> list event) (nx : I -> config),
  node_ok segs c I evs nx ->
  (forall i, P (ms_mem (cfg_ms c)) -> P (ms_mem (cfg_ms (nx i)))) ->
  klaw P c.
Proof.
intros P c I evs nx [_ Hc] Hk e c' Hs HP. destruct (Hc e (SNext c') Hs) as (i & _ & E).
injection E as E. subst c'. exact (Hk i HP).
Qed.

Lemma node_klaw : forall P c (I : Type) (evs : I -> list event) (nx : I -> config),
  node_ok segs c I evs nx -> klaw P c ->
  forall i, P (ms_mem (cfg_ms c)) -> P (ms_mem (cfg_ms (nx i))).
Proof. intros P c I evs nx [Hs _] Hk i HP. exact (Hk (evs i) (nx i) (Hs i) HP). Qed.

(* a memnorm law lifts to any P closed under memnorm keeps (srr_inv_call, e.g. the keep form srr_inv_call_imp) *)
Lemma klaw_call : forall P c, srr_inv_call segs P -> klaw (YAkMemnorm.memnorm segs) c -> klaw P c.
Proof. intros P c HC Hk e c' Hs HP. exact (HC _ _ (Hk e c' Hs) HP). Qed.

(* the brief's statement form, at the memnorm law *)
Lemma sstep_cfg_memnorm : forall c e c',
  klaw (YAkMemnorm.memnorm segs) c ->
  sstep_cfg segs ACFG c e (SNext c') ->
  YAkMemnorm.memnorm segs (ms_mem (cfg_ms c)) -> YAkMemnorm.memnorm segs (ms_mem (cfg_ms c')).
Proof. intros c e c' Hk Hs HM. exact (Hk e c' Hs HM). Qed.
End kn.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. Node twins carrying P (YA0n.v:106 SRr_node, :120 SRr_nodeI; YG0d.v:44 SRr_node_tnil).                         *)
Section nd.
Variable segs : list Segment.
Variable P : (word -> option byte) -> Prop.

Lemma SRr_node_inv : forall (W : world segs) c (I : Type) (nx : I -> config) (i0 : I) Q,
  node_ok segs c I (fun _ => []) nx ->
  (forall i, AI segs (w_H W) (w_A W) (cfg_model c) -> AI segs (w_H W) (w_A W) (cfg_model (nx i))) ->
  klaw segs P c -> P (ms_mem (cfg_ms c)) ->
  (forall i, P (ms_mem (cfg_ms (nx i))) -> SRr segs W (nx i) Q) ->
  SRr segs W c Q.
Proof.
intros W c I nx i0 Q Hn HIt Hk HP H.
apply (SRr_node segs W c I nx i0 Q Hn HIt). intros i. apply H. exact (node_klaw segs P c I _ nx Hn Hk i HP).
Qed.

Lemma SRr_nodeI_inv : forall (W : world segs) c (I : Type) (nx : I -> config) (i0 : I) Q,
  (AI segs (w_H W) (w_A W) (cfg_model c) ->
    node_ok segs c I (fun _ => []) nx /\ (forall i, AI segs (w_H W) (w_A W) (cfg_model (nx i)))) ->
  klaw segs P c -> P (ms_mem (cfg_ms c)) ->
  (forall i, P (ms_mem (cfg_ms (nx i))) -> SRr segs W (nx i) Q) ->
  SRr segs W c Q.
Proof.
intros W c I nx i0 Q Hn Hk HP H. apply SRr_use_AI. intros HI. destruct (Hn HI) as [Hnode _].
apply (SRr_nodeI segs W c I nx i0 Q Hn). intros i. apply H. exact (node_klaw segs P c I _ nx Hnode Hk i HP).
Qed.

Lemma SRr_node_tnil_inv : forall (W : world segs) c (I : Type) (nx : I -> config) (sp : I -> bool) (i0 : I) Q,
  node_ok segs c I (fun _ => []) nx ->
  (forall i, AI segs (w_H W) (w_A W) (cfg_model c) -> AI segs (w_H W) (w_A W) (cfg_model (nx i))) ->
  sp i0 = false ->
  (forall i, sp i = true -> AI segs (w_H W) (w_A W) (cfg_model (nx i)) -> srealizes segs (nx i) t_nil) ->
  klaw segs P c -> P (ms_mem (cfg_ms c)) ->
  (forall i, sp i = false -> P (ms_mem (cfg_ms (nx i))) -> SRr segs W (nx i) Q) ->
  SRr segs W c Q.
Proof.
intros W c I nx sp i0 Q Hn HIt Hi0 Hspin Hk HP H.
apply (SRr_node_tnil segs W c I nx sp i0 Q Hn HIt Hi0 Hspin). intros i Hi. apply (H i Hi).
exact (node_klaw segs P c I _ nx Hn Hk i HP).
Qed.
End nd.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 6. amreal_m: the invariant-carrying amreal (YG0d.v:72).                                                          *)
Section am.
Variable segs : list Segment.
Variable P : (word -> option byte) -> Prop.

Definition amreal_m {R : Type} (t : itree astate R) (W : world segs) (c : config)
  (Q : R -> world segs -> config -> Prop) : Prop :=
  P (ms_mem (cfg_ms c)) -> amreal segs t W c (fun r W' c' => Q r W' c' /\ P (ms_mem (cfg_ms c'))).

(* the sound form of the withdrawn generic lemma: P at the start and amreal_m give P at every leaf *)
Lemma amreal_m_sound {R} : forall (t : itree astate R) W c Q,
  P (ms_mem (cfg_ms c)) -> amreal_m t W c Q ->
  amreal segs t W c (fun r W' c' => Q r W' c' /\ P (ms_mem (cfg_ms c'))).
Proof. intros t W c Q HP H. exact (H HP). Qed.

Lemma amreal_m_forget {R} : forall (t : itree astate R) W c Q,
  P (ms_mem (cfg_ms c)) -> amreal_m t W c Q -> amreal segs t W c Q.
Proof. intros t W c Q HP H. eapply amreal_mono; [| exact (H HP)]. intros r W' c' [HQ _]. exact HQ. Qed.

Lemma amreal_m_mono {R} : forall (t : itree astate R) W c (Q Q' : R -> world segs -> config -> Prop),
  (forall r W' c', Q r W' c' -> Q' r W' c') -> amreal_m t W c Q -> amreal_m t W c Q'.
Proof.
intros t W c Q Q' HQ H HP. eapply amreal_mono; [| exact (H HP)]. intros r W' c' [H1 H2]. exact (conj (HQ r W' c' H1) H2).
Qed.

Lemma amreal_m_ret {R} : forall (r : R) (s : astate) W c (Q : R * astate -> world segs -> config -> Prop),
  Q (r, s) W c -> amreal_m (ret r s) W c Q.
Proof. intros r s W c Q H HP. apply amreal_ret. exact (conj H HP). Qed.

Lemma amreal_m_ibind {A R} : forall (t : itree astate A) (f : A -> itree astate R) W c
  (P1 : A -> world segs -> config -> Prop) (Q : R -> world segs -> config -> Prop),
  amreal_m t W c P1 -> (forall a W' c', P1 a W' c' -> amreal_m (f a) W' c' Q) -> amreal_m (ibind t f) W c Q.
Proof.
intros t f W c P1 Q H Hf HP. eapply amreal_ibind; [exact (H HP)|].
intros a W' c' [H1 H2]. exact (Hf a W' c' H1 H2).
Qed.

Lemma amreal_m_mbind {A R} : forall (m : M A) (f : A -> M R) (s : astate) W c
  (P1 : A * astate -> world segs -> config -> Prop) (Q : R * astate -> world segs -> config -> Prop),
  amreal_m (m s) W c P1 -> (forall a s' W' c', P1 (a, s') W' c' -> amreal_m (f a s') W' c' Q) ->
  amreal_m (bind m f s) W c Q.
Proof.
intros m f s W c P1 Q H Hf HP. eapply amreal_mbind; [exact (H HP)|].
intros a s' W' c' [H1 H2]. exact (Hf a s' W' c' H1 H2).
Qed.

Lemma amreal_m_SRr_pre {R} : forall (t : itree astate R) W c Q (Rp : world segs -> config -> Prop),
  (P (ms_mem (cfg_ms c)) -> SRr segs W c (fun W' c' => Rp W' c' /\ P (ms_mem (cfg_ms c')))) ->
  (forall W' c', wle W W' -> Rp W' c' -> amreal_m t W' c' Q) -> amreal_m t W c Q.
Proof.
intros t W c Q Rp H Hk HP. eapply amreal_SRr_pre; [exact (H HP)|].
intros W' c' Hle [HR HP']. exact (Hk W' c' Hle HR HP').
Qed.

Lemma amreal_m_world_le {R} : forall (t : itree astate R) W W' c Q,
  wle W W' -> (AI segs (w_H W) (w_A W) (cfg_model c) -> AI segs (w_H W') (w_A W') (cfg_model c)) ->
  amreal_m t W' c Q -> amreal_m t W c Q.
Proof. intros t W W' c Q Hle Htr H HP. exact (amreal_world_le segs t W W' c _ Hle Htr (H HP)). Qed.

Lemma amreal_m_spin {R} : forall (pc : Z) W c (Q : R -> world segs -> config -> Prop),
  (AI segs (w_H W) (w_A W) (cfg_model c) -> srealizes segs c t_nil) -> amreal_m (ISpin pc) W c Q.
Proof. intros pc W c Q H _. exact H. Qed.

Lemma amreal_m_fail {R} : forall f W c (Q : R -> world segs -> config -> Prop), amreal_m (IFail f) W c Q.
Proof. intros f W c Q _. exact I. Qed.

(* IAsk at the depot: no kernel step, P rides the SRr *)
Lemma amreal_m_depot {R} : forall tr snap (k : Z -> itree astate R) W c Q,
  (P (ms_mem (cfg_ms c)) -> SRr segs W c (fun W1 c1 => P (ms_mem (cfg_ms c1)) /\
    exists z, aok snap (KDepot tr) z /\ amreal_m (k z) W1 c1 Q)) ->
  amreal_m (IAsk (KDepot tr) snap k) W c Q.
Proof.
intros tr snap k W c Q H HP. cbn [amreal]. eapply SRr_mono; [exact (H HP)|].
intros W1 c1 _ [HP1 (z & Hz & Hk)]. exists z. split; [exact Hz | exact (Hk HP1)].
Qed.

(* IAsk at a kernel request: the node's answers keep P by the law at the ecall c1 *)
Lemma amreal_m_node {R} : forall (q : kreq) snap (k : Z -> itree astate R) W c Q,
  (forall tr, q <> KDepot tr) ->
  (P (ms_mem (cfg_ms c)) -> SRr segs W c (fun W1 c1 => P (ms_mem (cfg_ms c1)) /\ klaw segs P c1 /\
    exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
    node_ok segs c1 I (fun _ => []) nx /\
    (forall i, AI segs (w_H W1) (w_A W1) (cfg_model c1) -> AI segs (w_H W1) (w_A W1) (cfg_model (nx i))) /\
    (forall i, aok snap q (bit i)) /\
    sp i0 = false /\ bit i0 = 1 /\
    (forall i, sp i = false -> bit i = 1) /\
    (forall i, sp i = true -> AI segs (w_H W1) (w_A W1) (cfg_model (nx i)) -> srealizes segs (nx i) t_nil) /\
    (forall i, sp i = false -> amreal_m (k (bit i)) W1 (nx i) Q))) ->
  amreal_m (IAsk q snap k) W c Q.
Proof.
intros q snap k W c Q Hq H HP. cbn [amreal]. eapply SRr_mono; [exact (H HP)|].
intros W1 c1 _ (HP1 & Hk & J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc).
assert (G : forall i, sp i = false ->
  amreal segs (k (bit i)) W1 (nx i) (fun r W' c' => Q r W' c' /\ P (ms_mem (cfg_ms c')))).
{ intros i Hi. apply (Hc i Hi). exact (node_klaw segs P c1 J _ nx Hn Hk i HP1). }
destruct q; try (exfalso; eapply Hq; reflexivity);
(exists J, nx, bit, sp, i0;
 split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|];
 split; [exact Hr|]; split; [exact Hz | exact G]).
Qed.
End am.

Arguments amreal_m segs P {R} t W c Q.
