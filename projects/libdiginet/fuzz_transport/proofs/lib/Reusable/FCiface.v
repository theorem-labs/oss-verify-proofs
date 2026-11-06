(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the frame-area interface of fuzz_preset's walks, image-free.
   The walks of __asan_stack_malloc_{0,1,3} and __asan_set_shadow_f5 are written over a relation
   ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop,
   whose third argument is the poisoned-head set Hp of the second allocator instance (YGcfNames.v).
   Every Hp runs unchanged from the pre to the post: a frame-area call neither poisons nor unpoisons a head.
   - ecall_pre_x              = YG0d.v ecall_pre (:278-284) with `AR segs B ly S W mem md` -> `ARx ly S Hp W mem md`.
   - astack_malloc_realizes_x = YG0d.v astack_malloc_realizes (:285-300), the same substitution, Hp quantified.
   - aset_shadow_realizes_x   = cgif_rgb_fuzzer lib/YG0e.v aset_shadow_realizes (:48-59), the same substitution.
   - fs_iface: exactly the facts the walks read from AR (cgif_file A/AF0s.v, cgif_rgb YF9q.v, YF8u.v).
     Each field is stated without Wf and without an event count; fs_iface_AR below proves every field for
     cgif's own AR (Hp ignored), so each one is a projection of a cgif AR piece. The instance owner of ARcf
     proves fs_iface for ARcf the same way, from ARmcf.
   No address and no image numeral appears in this file. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_preset/lib/Reusable/FCiface.v (sha256 72b16d2a0987aa9a1c38d37336da27698408f3ccb0cc1a72da073b2ab6835484) with only its module paths changed to plugin-hostd/fuzz_command's. *)
(* Modified by Theorem Labs, 2026-10: copied from plugin-hostd/fuzz_command at 781f46bc05cd for libdiginet/fuzz_transport by this unit's provenance/evidence/class5/copy.sh (image-free: module paths only). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0s YG0q YG0t YF0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.

(* YG0d.v:278-284 *)
Definition ecall_pre_x (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
ARx ly S Hp W mem md /\
YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + ESTACK <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B).

(* YG0d.v:285-300 *)
Definition astack_malloc_realizes_x (cid : Z) : Prop :=
forall ly S Hp W regs mem md pos S',
ecall_pre_x ly S Hp W regs mem md ->
count_cid cid (frames S) < fs_frames cid ->
apath (stack_malloc cid S) [] (PFake cid pos, S') ->
SRr segs W (cfg_at segs (pc_stack_malloc (as_code B) cid) regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S' Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (frame_addr ly cid pos) /\
zero_shadow (aview segs (w_H W) mem') SHADOW_OFF (frame_addr ly cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem') (frame_addr ly cid pos + fs_frame_bytes cid - 8) = Some (flag_addr ly cid pos) /\
(forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly S' a -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).

(* cgif_rgb_fuzzer lib/YG0e.v:48-59 *)
Definition aset_shadow_realizes_x (pc v : Z) : Prop :=
forall ly S Hp W regs mem md cid pos q n,
ecall_pre_x ly S Hp W regs mem md -> In (cid, pos) (frames S) ->
getr regs 10 = w64 q -> getr regs 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr ly cid pos) <= q -> q + n <= shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (q + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).

(* YG0t.v:577-589, the rebuild law of a malloc step; Hp unchanged. *)
Definition astack_malloc_law_x : Prop := forall ly S Hp W mem md mem' md' cid pos hint',
ARx ly S Hp W mem md -> 0 <= cid <= 10 ->
fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs S)) cid (znth 0 cid (fs_hint (st_fs S))) = Some (pos, hint') ->
let S' := set_fs (mkFS (zupd cid hint' (fs_hint (st_fs S))) ((cid, pos) :: fs_live (st_fs S))) S in
(forall k, (k < 8)%nat -> aview segs (w_H W) mem' (ly_F ly + 8 * cid + Z.of_nat k) = Some (le_byte hint' 8 k)) ->
aview segs (w_H W) mem' (flag_addr ly cid pos) = Some 1 ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> ~ (ly_F ly + 8 * cid <= a < ly_F ly + 8 * cid + 8) -> a <> flag_addr ly cid pos ->
~ in_zr a (frame_addr ly cid pos, fs_frame_bytes cid) -> ~ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
ARx ly S' Hp W mem' md'.

(* YG0d.v:468-470 *)
Definition AR_stack_law_x : Prop :=
forall ly S Hp W mem md a,
ARx ly S Hp W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ aowned B ly S a.

(* YG0d.v:439-446; Hp unchanged. *)
Definition AR_frame_law_x : Prop :=
forall ly S Hp W mem md mem' md',
ARx ly S Hp W mem md ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
ARx ly S Hp W mem' md'.

(* YG0d.v:447-455 *)
Definition AR_frames_law_x : Prop :=
forall ly S Hp W mem md cid pos,
ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos mod 32 = 0 /\ in_app (frame_addr ly cid pos) (fs_frame_bytes cid) /\
(forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
(forall i, 0 <= i < fs_frame_bytes cid / 8 ->
apresent (w_H W) mem (shadow_addr (frame_addr ly cid pos) + i) /\
~ aowned B ly S (shadow_addr (frame_addr ly cid pos) + i)).

(* What the walks read from AR. The comment on each field names the cgif AR piece it projects
   (YG0n.v:490 AR = ARm /\ ALedger /\ abudget_ok /\ amwf /\ ahs) and the donor line that reads it. *)
Record fs_iface : Prop := {
(* am_wf -> wf_fakestack -> wfs_hints (YG01.v:311); AF0s.v:57 *)
fi_hints : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
length (fs_hint (st_fs S)) = 11%nat /\ Forall (fun h => 0 <= h) (fs_hint (st_fs S));
(* am_layout (YG0n.v:209); AF0s.v:61, :87-101 *)
fi_layout : forall ly S Hp W mem md, ARx ly S Hp W mem md -> layout_ok ly;
(* ALedger -> al_img (YG0n.v:312); AF0x.img_cover_of_ledger, AF0s.v:62 *)
fi_img : forall ly S Hp W mem md sg, ARx ly S Hp W mem md -> In sg segs ->
fst (ly_img ly) <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= fst (ly_img ly) + snd (ly_img ly);
(* am_tsd (YG0n.v:223); AF0s.v:106 *)
fi_tsd : forall ly S Hp W mem md, ARx ly S Hp W mem md -> ly_tsd ly = as_tsd B;
(* am_const (YG0n.v:211); AF0x.tfib_const_lookup(_sym), AE2y.rodata_ok; AF0s.v:107-120, :166 *)
fi_const : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
Forall (cell_holds B ly (aview segs (w_H W) mem)) (as_const B ly);
(* am_cells restricted to fs_cells (YG0n.v:100-102, :213); AF0s.v:121-129 *)
fi_fs_cells : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
Forall (cell_holds B ly (aview segs (w_H W) mem)) (fs_cells S);
(* am_flags (YG0n.v:152-154, :215); AF0s.v:223-228 *)
fi_flags : forall ly S Hp W mem md, ARx ly S Hp W mem md -> fs_flags_ok ly (aview segs (w_H W) mem) S;
(* am_areas item (AF 0, kFakeStackSize) (YG0n.v:137, :220); AF0s.v:273-277 *)
fi_area_F : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
range_vis B ly (aview segs (w_H W) mem) (AF 0, kFakeStackSize);
(* am_areas item (ASh (AF kFakeFramesOff), ...) (YG0n.v:139, :220); AF0s.v:278-285 *)
fi_area_Fsh : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
range_vis B ly (aview segs (w_H W) mem) (ASh (AF kFakeFramesOff), (kFakeStackSize - kFakeFramesOff) / 8);
(* YF0v.own_free_frame from ARm (YF0v.v:37); AF0s.v:505 *)
fi_own_free_frame : forall ly S Hp W mem md cid pos a, ARx ly S Hp W mem md -> 0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
~ In (cid, pos) (frames S) ->
frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> aowned B ly S a;
(* YF0v.own_free_frame_shadow from ARm (YF0v.v:64); AF0s.v:503 *)
fi_own_free_frame_shadow : forall ly S Hp W mem md cid pos a, ARx ly S Hp W mem md -> 0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
~ In (cid, pos) (frames S) ->
shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 -> aowned B ly S a;
(* YG0q.own_F_low from ARm (YG0q.v:257); AF0s.v:507-508 *)
fi_own_F_low : forall ly S Hp W mem md a, ARx ly S Hp W mem md ->
ly_F ly <= a < ly_F ly + kFakeFramesOff -> aowned B ly S a;
(* YG0t.astack_malloc_law_ok (YG0t.v:662) over the whole AR; AF0s.v:467 *)
fi_malloc_law : astack_malloc_law_x;
(* AR_laws.al_stack (YG0d.v:504); AF0s.v:474 *)
fi_stack : AR_stack_law_x;
(* AR_laws.al_frame (YG0d.v:500); cgif_rgb YF8u.v:157 *)
fi_frame : AR_frame_law_x;
(* AR_laws.al_frames (YG0d.v:501); cgif_rgb YF8u.v:73 *)
fi_frames : AR_frames_law_x
}.
End b.

(* Every field of fs_iface is a projection of cgif's AR: cgif's AR, Hp ignored, satisfies fs_iface,
   and its _x contract is cgif's contract. *)
Section c.
Variable segs : list Segment.
Variable B : asyms.
Definition AR_nohp (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model) : Prop :=
AR segs B ly S W mem md.
Lemma fs_iface_AR : AR_laws segs B -> fs_iface segs B AR_nohp.
Proof.
intros LAWS. constructor; unfold AR_nohp.
- intros ly S Hp W mem md HAR. exact (wfs_hints _ (wf_fakestack _ _ _ _ _ (am_wf _ _ _ _ (proj1 HAR)))).
- intros ly S Hp W mem md HAR. exact (am_layout _ _ _ _ (proj1 HAR)).
- intros ly S Hp W mem md sg HAR Hsg. exact (al_img _ _ _ _ (proj1 (proj2 HAR)) sg Hsg).
- intros ly S Hp W mem md HAR. exact (am_tsd _ _ _ _ (proj1 HAR)).
- intros ly S Hp W mem md HAR. exact (am_const _ _ _ _ (proj1 HAR)).
- intros ly S Hp W mem md HAR. apply Forall_forall. intros c Hc.
apply (proj1 (Forall_forall _ _) (am_cells _ _ _ _ (proj1 HAR))).
unfold acells. rewrite !in_app_iff. right; right; right; right; right; left. exact Hc.
- intros ly S Hp W mem md HAR. exact (am_flags _ _ _ _ (proj1 HAR)).
- intros ly S Hp W mem md HAR. apply (proj1 (Forall_forall _ _) (am_areas _ _ _ _ (proj1 HAR))).
unfold aareas. rewrite !in_app_iff. right; right; right. cbn [In]. tauto.
- intros ly S Hp W mem md HAR. apply (proj1 (Forall_forall _ _) (am_areas _ _ _ _ (proj1 HAR))).
unfold aareas. rewrite !in_app_iff. right; right; right. cbn [In]. tauto.
- intros ly S Hp W mem md cid pos a HAR. exact (own_free_frame B ly S _ cid pos a (proj1 HAR)).
- intros ly S Hp W mem md cid pos a HAR. exact (own_free_frame_shadow B ly S _ cid pos a (proj1 HAR)).
- intros ly S Hp W mem md a HAR. exact (own_F_low B ly S _ a (proj1 HAR)).
- intros ly S Hp W mem md mem' md' cid pos hint'. exact (astack_malloc_law_ok segs B ly S W mem md mem' md' cid pos hint').
- intros ly S Hp W mem md a. exact (al_stack _ _ LAWS ly S W mem md a).
- intros ly S Hp W mem md mem' md'. exact (al_frame _ _ LAWS ly S W mem md mem' md').
- intros ly S Hp W mem md cid pos. exact (al_frames _ _ LAWS ly S W mem md cid pos).
Qed.
Lemma astack_malloc_realizes_of_x : forall cid,
astack_malloc_realizes_x segs B AR_nohp cid -> astack_malloc_realizes segs B cid.
Proof. intros cid H ly S W regs mem md pos S' HPRE. exact (H ly S [] W regs mem md pos S' HPRE). Qed.
End c.
End a.
