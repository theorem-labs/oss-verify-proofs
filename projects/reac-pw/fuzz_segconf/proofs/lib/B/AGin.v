(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGin.v (cold/c-asan-nmax-param 57e82b93d43, file sha256 5b0b49b0fc1b) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 29 image addresses moved by code-verified function pairs (32 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_state/lib/A/AGin.v (donor image sha256 64b53ff86172), with its module paths changed, names TfibSyms -> SegBSyms and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AGin.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* The k-path MISS arm of the frame-generic Allocate contract (AllocG.alloc_leaf), over the interface AGif0n.AIface
   and the miss fields AGif0n.AIfaceM (c5), the depot call at the post-refill state through the field [if_depot_miss].

   Generalized from the released malloc_missk (YFin): the run starts at Allocate's entry with an abstract caller
   frame and an abstract allocator relation ARX.  Case 0 <= n <= 48 (the k path), can_fill = 1, class cache empty.  Seed read
   through the miss view (AGja.SEEDM_ok); MISS1 (AGj8.miss1) reaches the refill call; the refill callee is [if_refill]
   whose post [rleaf] gives the post-refill state Sp (layout ly' >= ly) with a0 = 1 iff the class cache is non-empty.
   a0 = 1: the cache join as the hit-k arm (AGje / AGjd view facts at Sp via [if_view_m], AGj7.segJ, AGjg.tail_inner),
   the leaf from [if_post_miss] + [if_owned_m] / [if_mono_join] at Sp + rleaf's frame law.  a0 = 0: the OOM arm
   (AGj9.segN), the leaf from [if_oom].  The stack is never owned ([if_stack]), so the refill keeps the caller's frame. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YA0p YA0q YG0b.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG02 YG06 YG07 YG0k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YFl1.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d YG0s YG0q YG0h.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1w YE3d YFhy YFhm AGhy YFi1 AGhz AGi2 AGi4.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YFen.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import AGj6 YFi3.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YGAlloc AGif0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import AGif2cgif AGif0cgif AGjc AGjd AGje AGjb AGjg AGja AGj8 AGj7 AGj9 YB13.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import ErrnoG.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require ErrnoApart.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YA00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Ltac bvne := first [cbn; lia | vm_compute; congruence | intros X; vm_compute in X; discriminate X].
(* AGj6.memv (section-local there): a value chunk of region [i], chunk [j] of the symbolic state [HS]. *)
Local Ltac memv HS i j :=
lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
let nn := lazymatch n with 1%nat => constr:(1%N) | 2%nat => constr:(2%N) | 4%nat => constr:(4%N) | _ => constr:(8%N) end in
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
eapply (AGj6.chunk_val_at H E ss ms i j _ _ nn _ v a HS);
[ reflexivity | reflexivity | cbn [base_val YP09.r_base]
| | lazymatch goal with |- _ <= _ < ?p => let q := eval vm_compute in p in change p with q end
| cbn; lia ]
end
end.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Machine helper lemmas (generic), as in the released malloc_missk.                                                 *)
Lemma aview_eq_mbyte : forall (H H' : word -> bool) (m m' : word -> option byte) a,
aview tfibsegs H' m' a = aview tfibsegs H m a -> mbyte tfibsegs (mrestrict H' m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H' m') a) as [b'|], (mbyte tfibsegs (mrestrict H m) a) as [b|]; cbn in E; try discriminate E; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma val_mem_aview_xfer : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> aview tfibsegs H' m' (a + Z.of_nat k) = aview tfibsegs H m (a + Z.of_nat k)) ->
val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v.
Proof. intros H H' m m' a n v HA Hv. eapply val_mem_ext; [|exact Hv]. intros k Hk. apply aview_eq_mbyte. exact (HA k Hk). Qed.
Lemma apresent_aview_some : forall (H : word -> bool) m a, TFIB_IMG_END <= a < 2 ^ 64 -> apresent H m a -> aview tfibsegs H m a <> None.
Proof. intros H m a Ha Hp. destruct (apresent_mbyte H m a Hp) as [b Hb]. unfold aview. rewrite Hb. cbn. discriminate. Qed.
Lemma aview_some_apresent : forall (H : word -> bool) m a, TFIB_IMG_END <= a < 2 ^ 64 -> aview tfibsegs H m a <> None -> apresent H m a.
Proof.
intros H m a Ha Hv. destruct (mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:E.
- exact (mbyte_high_apresent H m a b Ha E).
- exfalso. apply Hv. unfold aview. rewrite E. reflexivity.
Qed.
Lemma apresent_xfer : forall (H H' : word -> bool) m m' a, TFIB_IMG_END <= a < 2 ^ 64 ->
aview tfibsegs H' m' a = aview tfibsegs H m a -> apresent H m a -> apresent H' m' a.
Proof. intros H H' m m' a Ha E Hp. apply aview_some_apresent; [exact Ha|]. rewrite E. exact (apresent_aview_some H m a Ha Hp). Qed.
Lemma val_mem_aview : forall (H : word -> bool) m a (w : nat) v k, val_mem tfibsegs (mrestrict H m) a w v -> (k < w)%nat ->
aview tfibsegs H m (a + Z.of_nat k) = Some (YG0f.le_byte v w k).
Proof.
intros H m a w v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. change (YG0f.le_byte v w k) with (YO0f.le_byte v w k). f_equal.
apply unsigned_lit_small8. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma region_kept_view : forall (H H' : word -> bool) (E : env) (m m' : word -> option byte) n lo hi wlo whi cs spv,
bv_unsigned (ew E n) = spv ->
(forall a, spv + lo <= a < spv + hi -> aview tfibsegs H' m' a = aview tfibsegs H m a) ->
TFIB_IMG_END <= spv + lo -> spv + hi <= 2 ^ 64 -> (forall a, spv + wlo <= a < spv + whi -> spv + lo <= a < spv + hi) ->
region_kept tfibsegs E (mrestrict H m) (mrestrict H' m') (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros H H' E m m' n lo hi wlo whi cs spv Hn HA Hlo Hhi Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply aview_eq_mbyte. apply HA. exact Ha.
- intros Hwr. pose proof (Hw a Ha) as Ha'. apply apresent_writable; [lia|]. apply (apresent_xfer H H' m m' a); [lia | apply HA; lia |].
apply writable_high_apresent; [lia | exact Hwr].
Qed.
Lemma extent_disjoint_sub : forall E r0 r r', YP09.r_base r' = YP09.r_base r0 -> YP09.r_lo r0 <= YP09.r_lo r' -> YP09.r_hi r' <= YP09.r_hi r0 ->
YP09.r_lo r' <= YP09.r_hi r' -> extent_disjoint E r0 r -> extent_disjoint E r' r.
Proof. intros E r0 r r' Hb Hlo Hhi Hwf H. unfold extent_disjoint in *. rewrite Hb. lia. Qed.
Lemma same_io_wvb : forall md mat, same_io md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. apply same_io_with_vm_backing. Qed.
Lemma E0_nondummy : forall ly regs0 n ch cl csz cnt v j0 jb j1 j2 j3 j4 cnt' v' j0' jb' j1' j2' j3' j4' k, (k < 64)%nat -> PND k = true ->
ew (AGj6.E0 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4) k = ew (AGj6.E0 ly regs0 n ch cl cnt' v' csz j0' jb' j1' j2' j3' j4') k.
Proof. intros until k. intros Hk HP. do 64 (destruct k as [|k]; [first [reflexivity | discriminate HP] |]). lia. Qed.
(* Across a layout_le grown layout (the refill), the non-dummy atoms of E0 agree: they read only ly_T, ly_C,
   ly_space and ly_top, all of which layout_le preserves. *)
Lemma E0_nondummy_ly : forall nsecs ly ly' regs0 n ch cl csz cnt v j0 jb j1 j2 j3 j4 cnt' v' j0' jb' j1' j2' j3' j4' k,
layout_le nsecs ly ly' -> (k < 64)%nat -> PND k = true ->
ew (AGj6.E0 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4) k = ew (AGj6.E0 ly' regs0 n ch cl cnt' v' csz j0' jb' j1' j2' j3' j4') k.
Proof.
intros nsecs ly ly' regs0 n ch cl csz cnt v j0 jb j1 j2 j3 j4 cnt' v' j0' jb' j1' j2' j3' j4' k Hly Hk HP.
destruct Hly as (_ & Hspace & _ & HT & HC & _ & _ & _ & Htop & _).
unfold AGj6.E0, AGj6.XW, AGj6.Pv, AGj6.SSLOTv. rewrite HT, HC, Hspace, Htop.
do 64 (destruct k as [|k]; [first [reflexivity | discriminate HP] |]). lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
Section b.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variables (nmax lmax : Z).
Variable lpost : astate -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variables (mtag stag : Z).
Hypothesis IF : AGif0n.AIface B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
Hypothesis TS : SegBSyms B.
Variable rtree : Z -> M unit.
Definition Finst := AGif0n.if_inst B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF.
Definition Fdepot := AGif0n.if_depot B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF.
Definition Fdaok := AGif0n.if_dpost_aok B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The miss fields: c5 AGif0n.AIfaceM (final revision, with the k twins if_post_miss_k / if_owned_m_k). *)
Hypothesis IFM : AGif0n.AIfaceM B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree.
Definition rleaf := AGif0n.rleaf.
Definition if_mview := AGif0n.if_mview B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM.
Definition if_view_m := AGif0n.if_view_m B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM.
Definition if_owned_m_k := AGif0n.if_owned_m_k B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM.
Definition if_shape_miss := AGif0n.if_shape_miss B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM.
Definition if_refill := AGif0n.if_refill B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM.
Definition if_post_miss_k := AGif0n.if_post_miss_k B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM.
Definition if_oom := AGif0n.if_oom B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM.
Definition if_stack := AGif0n.if_stack B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM.
Definition if_mono_join := AGif0n.if_mono_join B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM.
Definition if_depot_miss := AGif0n.if_depot_miss B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM.
(* ERRNO-KEPT add-ons (ErrnoG.AIfaceME): the refill with errno kept (rleaf_e). *)
Hypothesis IFME : ErrnoG.AIfaceME B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree.
Definition ame_refill := ErrnoG.ame_refill B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFME.
(* ERRNO-KEPT: errno's 4 bytes lie outside the frames the k walk excludes: at_RETkw's raw frame (the WIN windows, the
   depot zone, the new block and its shadow) and MISS1's (WINM), at any layout and stack pointer in that layout's stack.
   From h-decbox-a9's ErrnoApart image Props (discharged once per image in ErrnoApartcgif). *)
Hypothesis EAI : ErrnoApart.errno_in_img.
Hypothesis EAS : ErrnoApart.errno_apart_shadow_ag.
Hypothesis EAD : ErrnoApart.errno_apart_dzone_ag.
Lemma EA_K : forall (ly1 : alayout) (regs1 : bvmap 5 word) (n1 cl1 v1 : Z) (odd : bool) (i : Z),
  layout_ok ly1 -> img_cover ly1 -> ly_stk_lo ly1 + AFSTACK <= bv_unsigned (getr regs1 2) -> bv_unsigned (getr regs1 2) <= ly_stk_hi ly1 ->
  0 <= n1 <= 48 -> 1 <= cl1 <= 31 -> 0 <= v1 -> 0 <= i < 4 ->
  ~ AGj6.WIN ly1 regs1 n1 cl1 v1 odd (as_errno B + i) /\ ~ ImgBaseAG.ag_dzone ly1 (as_errno B + i) /\
  ~ (AGj6.Kv ly1 cl1 v1 + AGj6.RZ <= as_errno B + i < AGj6.Kv ly1 cl1 v1 + AGj6.RZ + AGj6.NPv n1) /\
  ~ (AGj6.SUv ly1 cl1 v1 <= as_errno B + i < AGj6.SUv ly1 cl1 v1 + AGj6.N8D n1 / 8).
Proof.
intros ly1 regs1 n1 cl1 v1 odd i LY1 IMG1 Lo1 Hi1 Nr Hc Hv Hi.
assert (Hk : 0 <= cl1 < kNumClasses) by (unfold kNumClasses; lia).
split; [intros X; apply (ErrnoApart.errno_apart_win_k EAI EAS B ly1 regs1 n1 cl1 v1 odd (as_errno B + i) TS LY1 IMG1
  ltac:(unfold ImgBaseAG.AFSTACK; unfold AFSTACK in Lo1; lia) Hk Hv X); lia|].
split; [intros X; apply (EAD B ly1 (as_errno B + i) TS LY1 IMG1 X); lia|].
split; [intros X; apply (ErrnoApart.errno_apart_blk_k EAI B ly1 n1 cl1 v1 (as_errno B + i) TS LY1 IMG1 ltac:(lia) Hv X); lia|].
intros X; apply (ErrnoApart.errno_apart_shd_k EAS B ly1 n1 cl1 v1 (as_errno B + i) TS LY1 ltac:(lia) Hv X); lia.
Qed.
Lemma EA_M : forall (ly1 : alayout) (regs1 : bvmap 5 word) (i : Z),
  layout_ok ly1 -> img_cover ly1 -> ly_stk_lo ly1 + AFSTACK <= bv_unsigned (getr regs1 2) -> bv_unsigned (getr regs1 2) <= ly_stk_hi ly1 ->
  0 <= i < 4 -> ~ AGj8.WINM ly1 regs1 (as_errno B + i).
Proof.
intros ly1 regs1 i LY1 IMG1 Lo1 Hi1 Hi X. unfold AGj8.WINM in X. destruct X as [X|X].
- assert (L1 : ly_stk_lo ly1 <= bv_unsigned (getr regs1 2) - AFSTACK) by lia.
  refine (ErrnoApart.errno_apart_stack EAI B ly1 _ _ (as_errno B + i) TS LY1 IMG1 L1 X _); lia.
- apply (ErrnoApart.errno_apart_unw EAI B ly1 (as_errno B + i) TS LY1 IMG1 X); lia.
Qed.

(* The virtual register file of the walk (as AGik). *)
Definition vregs (regs : bvmap 5 word) (n inst bp : Z) : bvmap 5 word :=
regupd (regupd (regupd regs 10%bv (w64 n)) 11%bv (w64 inst)) 12%bv (w64 bp).
Lemma vregs_other : forall regs n inst bp (r : bv 5), bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 ->
getr (vregs regs n inst bp) r = getr regs r.
Proof.
intros regs n inst bp r H10 H11 H12. unfold vregs.
rewrite getr_other by (intros ->; apply H12; reflexivity).
rewrite getr_other by (intros ->; apply H11; reflexivity).
rewrite getr_other by (intros ->; apply H10; reflexivity). reflexivity.
Qed.
Lemma vregs_10 : forall regs n inst bp, getr (vregs regs n inst bp) 10%bv = w64 n.
Proof.
intros regs n inst bp. unfold vregs. rewrite getr_other by (intros X; discriminate X). rewrite getr_other by (intros X; discriminate X). apply getr_same. intros X; discriminate X.
Qed.
Lemma vregs_11 : forall regs n inst bp, getr (vregs regs n inst bp) 11%bv = w64 inst.
Proof. intros regs n inst bp. unfold vregs. rewrite getr_other by (intros X; discriminate X). apply getr_same. intros X; discriminate X. Qed.
Lemma vregs_12 : forall regs n inst bp, getr (vregs regs n inst bp) 12%bv = w64 bp.
Proof. intros regs n inst bp. unfold vregs. apply getr_same. intros X; discriminate X. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
Section c.
Variables (inst : Z) (ly : alayout) (S : astate) (W : world tfibsegs).
Variables (regs0 regsU : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (tr : list Z).
Hypothesis HARX : ARX inst ly S W mem0 md0.
Hypothesis HRP : rpre S n.
Hypothesis Nrange : 0 <= n <= 48.
Hypothesis Hmiss : pc_chunks (cache S (chunk_class n)) = [].
Hypothesis Hnnmax : n < nmax.
Hypothesis HBB : blocks_bytes S + n <= lmax.
Hypothesis Htr : U tr S.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Hi11 : getr regs0 11 = w64 inst.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let BPv : Z := bv_unsigned (getr regs0 12).
Let T : Z := ly_T ly.
Let cl : Z := chunk_class n.
Let csz : Z := class_size cl.
Let S1 : astate := set_nev (st_nev S + 1) S.
Let md0' : list word -> Model := fun mat => with_vm_backing (m_vm_lazy md0) mat md0.
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Hso : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly /\ SOv mod 8 = 0.
Hypothesis Hbp : sp0 <= BPv /\ BPv + 8 * 30 <= ly_stk_hi ly /\ BPv mod 8 = 0.
Hypothesis Hcf1 : getr regs0 15 = w64 1.
Hypothesis Hpres0 : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis PSO : val_mem tfibsegs (mrestrict (w_H W) mem0) SOv 8 BPv.
Hypothesis PLEN : val_mem tfibsegs (mrestrict (w_H W) mem0) (SOv + 8) 8 (Z.of_nat (length tr)).
Hypothesis PBUF0 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem0) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).
Hypothesis HUo : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr regsU r = getr regs0 r.
Hypothesis HU10 : getr regsU 10%bv = getr regs0 11%bv.
Hypothesis HU11 : getr regsU 11%bv = getr regs0 10%bv.
Hypothesis HU12 : getr regsU 12%bv = w64 8.
Hypothesis HU14 : getr regsU 14%bv = w64 1.

Lemma HIO : inst_ok inst. Proof. exact (Finst inst ly S W mem0 md0 HARX). Qed.
Lemma Hn0 : 0 <= n. Proof. lia. Qed.
Lemma FP : from_primary n = true. Proof. pose proof (AGj6.case0_sizes n Nrange) as (_ & _ & _ & _ & FP' & _). exact FP'. Qed.
Lemma Hcl_class : cl = chunk_class n. Proof. reflexivity. Qed.
Lemma Hcl : 1 <= cl <= 31. Proof. pose proof (primary_geometry n Hn0 FP) as (G & _). unfold cl. lia. Qed.
Lemma Hcl_def : cl = class_id (AGj6.R8v n + AGj6.RZ).
Proof. pose proof (AGj6.case0_sizes n Nrange) as (_ & RS & _ & _ & _ & NS & _). subst cl. unfold chunk_class. rewrite NS, <- RS. reflexivity. Qed.
Lemma Hcsz_def : csz = class_size cl. Proof. reflexivity. Qed.
Lemma HMV0 : AGif0n.mview B W ly inst mem0 cl. Proof. exact (if_mview inst ly S W mem0 md0 n HARX Hn0 FP Hmiss). Qed.
Lemma HMV : AGif0n.mview B W ly inst mem0 cl. Proof. exact HMV0. Qed.
Lemma Hinst : TFIB_IMG_LO <= bv_unsigned (getr regs0 11) /\ bv_unsigned (getr regs0 11) + 0xe60 <= 0x17e688.
Proof.
pose proof HIO as (HIO1 & HIO2 & HIO3). assert (Hinst64 : 0 <= inst < 2 ^ 64) by lia.
rewrite Hi11, w64_unsigned by exact Hinst64. exact (inst_ok_img inst HIO).
Qed.
Lemma Hvd : 0 <= 0 /\ 16 * 0 + 2 ^ 16 <= 2 ^ 32. Proof. lia. Qed.
Lemma Hcntd : 1 <= 1 <= 16. Proof. lia. Qed.
Lemma Hjbd : 0 <= 0 <= 255. Proof. lia. Qed.
Lemma Hv2d : 0 mod 2 = 0. Proof. reflexivity. Qed.
Lemma LY : layout_ok ly. Proof. exact (AGif0n.mv_ly B W ly inst mem0 cl HMV). Qed.
Lemma IMG : img_cover ly. Proof. exact (AGif0n.mv_img B W ly inst mem0 cl HMV). Qed.
Lemma HTSD : ly_tsd ly = TFIB_TSD. Proof. exact (AGif0n.mv_tsd B W ly inst mem0 cl HMV). Qed.
Lemma STK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof. pose proof (lo_top ly LY) as (_ & _ & _ & H4 & _ & _ & H7). split; [exact H7 | exact H4]. Qed.
Lemma Usp : 0 <= sp0 < 2 ^ 64. Proof. unfold sp0. apply u64_range. Qed.
Let E0m : env := AGj6.E0 ly regs0 n tr cl 1 0 csz 0 0 0 0 0 0.
Let DPOSTm : Z -> (word -> option byte) -> Prop := fun z m => dpost inst ly S W tr z m.
Let mat0 : list word := m_vm_materialized md0.

Lemma SEEDM : st_ok tfibsegs E0m AGi4.MK_1 (restrict (w_H W) (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs))).
Proof.
exact (@AGja.SEEDM_ok _ _ W ly regs0 mem0 n tr cl 1 0 csz 0 0 0 0 0 0 Hcl Hvd Hcntd Hjbd Hv2d LY IMG Hn Htp Hsp Htrlen Hso Hbp (or_intror Hcf1) DPOSTm Nrange Hcl_def B inst TS Hi11 HIO (AGif0n.mv_tsd B W ly inst mem0 cl HMV) (AGif0n.mv_const B W ly inst mem0 cl HMV) (AGif0n.mv_inst B W ly inst mem0 cl HMV) (AGif0n.mv_cnt0 B W ly inst mem0 cl HMV) (AGif0n.mv_unw B W ly inst mem0 cl HMV) PSO PLEN Hpres0 regsU HUo HU10 HU11 HU12 HU14).
Qed.
Lemma MISS1 : SRr tfibsegs W (cfg_at tfibsegs A_Allocate regsU mem0 md0)
(AGj8.at_STM W ly regs0 mem0 md0 n tr cl 1 0 csz 0 0 0 0 0 0 AGi4.MK_CALL).
Proof.
replace (cfg_at tfibsegs A_Allocate regsU mem0 md0) with (mkCfg (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs)) (md0' mat0))
by (unfold cfg_at, md0', mat0; rewrite with_vm_backing_id; reflexivity).
exact (@AGj8.miss1 _ _ W ly regs0 mem0 md0 n tr cl 1 0 csz 0 0 0 0 0 0 Hcl Hvd Hcntd Hv2d LY IMG Hn Hsp Htrlen Hso Hbp DPOSTm Nrange Hcl_def mat0 regsU PBUF0 [] 0 Hpres0 SEEDM).
Qed.

Lemma rw_writable : forall (m : word -> option byte) a, 0xa1000 <= a < 0x602000 -> writable_at tfibsegs m a.
Proof. intros m a Ha. unfold writable_at. apply YB13.tfib_rw_window. rewrite unsigned_lit_small by lia. exact Ha. Qed.
Lemma aview_rw_some : forall (Hh : word -> bool) m a, 0xa1000 <= a < 0x602000 -> aview tfibsegs Hh m a <> None.
Proof.
intros Hh m a Ha. unfold aview, mbyte. destruct (mrestrict Hh m (Z_to_bv 64 a)); cbn; [discriminate|].
pose proof (YB13.tfib_rw_rom a Ha) as X. destruct (seg_rom tfibsegs (Z_to_bv 64 a)); [cbn; discriminate | exfalso; exact (X eq_refl)].
Qed.
(* The pre-leaf: the leaf given its granted path (supplied at the end by amreal_apath_gflag). *)
Definition PL (r : sptr * astate) (W' : world tfibsegs) (c' : config) : Prop :=
(exists trc, apath (mt n tr S) trc r /\ gflag trc = true) ->
alloc_leaf tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr r W' c'.
(* The pre-leaf with errno kept on the grant branch (ErrnoG.alloc_leaf_e). *)
Definition PL_e (r : sptr * astate) (W' : world tfibsegs) (c' : config) : Prop :=
(exists trc, apath (mt n tr S) trc r /\ gflag trc = true) ->
ErrnoG.alloc_leaf_e tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr r W' c'.
Lemma same_io_tr : forall m1 m2 m3, same_io m1 m2 -> same_io m2 m3 -> same_io m1 m3.
Proof. intros m1 m2 m3 (A1 & A2 & A3 & A4) (C1 & C2 & C3 & C4). unfold same_io. rewrite C1, C2, C3, C4. repeat split; assumption. Qed.
(* The callee-saved registers a post keeps from regs0 are the entry regsU's. *)
Lemma CS_leaf : forall regs' : bvmap 5 word,
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) ->
aregs_preserved regsU regs'.
Proof.
intros regs' RCS r Hr. assert (HrZ : bv_unsigned (Z_to_bv 5 r) = r).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32. unfold acallee_saved in Hr. apply Z.mod_small. lia. }
rewrite (HUo (Z_to_bv 5 r)) by (rewrite HrZ; unfold acallee_saved in Hr; lia).
apply RCS. unfold acallee_saved in Hr.
assert (H18 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear - H18.
assert (E5 : forall k : Z, 0 <= k < 32 -> forall b : bv 5, bv_unsigned b = k -> Z_to_bv 5 k = b) by (intros k Hk b Hb; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 5) with 32; rewrite Z.mod_small by lia; symmetry; exact Hb).
destruct H18 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
[ rewrite (E5 2 ltac:(lia) 2%bv eq_refl) | rewrite (E5 3 ltac:(lia) 3%bv eq_refl) | rewrite (E5 4 ltac:(lia) 4%bv eq_refl)
| rewrite (E5 8 ltac:(lia) 8%bv eq_refl) | rewrite (E5 9 ltac:(lia) 9%bv eq_refl) | rewrite (E5 18 ltac:(lia) 18%bv eq_refl)
| rewrite (E5 19 ltac:(lia) 19%bv eq_refl) | rewrite (E5 20 ltac:(lia) 20%bv eq_refl) | rewrite (E5 21 ltac:(lia) 21%bv eq_refl)
| rewrite (E5 22 ltac:(lia) 22%bv eq_refl) | rewrite (E5 23 ltac:(lia) 23%bv eq_refl) | rewrite (E5 24 ltac:(lia) 24%bv eq_refl)
| rewrite (E5 25 ltac:(lia) 25%bv eq_refl) | rewrite (E5 26 ltac:(lia) 26%bv eq_refl) | rewrite (E5 27 ltac:(lia) 27%bv eq_refl) ];
cbn [In]; tauto.
Qed.
Lemma CFG_leaf : forall regs' mem' md', mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) md' = cfg_at tfibsegs (raZ regsU) regs' mem' md'.
Proof. intros regs' mem' md'. unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. rewrite (HUo 1%bv) by bvne. reflexivity. Qed.
Lemma SP_U : bv_unsigned (getr regsU 2) = sp0. Proof. rewrite (HUo 2%bv) by bvne. reflexivity. Qed.


(* --- The refill-call machine state. --- *)
Section f.
Variables (ms1 : machine_state) (mat1 : list word) (Em : env).
Hypothesis HEm : forall k, (k < aHAV)%nat -> ew Em k = ew E0m k.
Hypothesis HSC : st_ok tfibsegs Em AGi4.MK_CALL (restrict (w_H W) ms1).
Hypothesis MEQW : forall x : word, ~ AGj8.WINM ly regs0 (bv_unsigned x) -> (ms_mem ms1) x = mem0 x.
Hypothesis PRESW : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a.
Hypothesis BUFW : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).
Lemma ms1_shape : ms1 = mkst (ms_regs ms1) (w64 0x37e68) (ms_mem ms1) (seg_rom tfibsegs).
Proof. exact (st_ok_restrict_mkst tfibsegs (w_H W) Em _ _ HSC eq_refl). Qed.
Lemma Em2 : ew Em 2 = getr regs0 2. Proof. rewrite (HEm 2%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma Em3 : ew Em 3 = getr regs0 3. Proof. rewrite (HEm 3%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma Em11 : ew Em 11 = getr regs0 11. Proof. rewrite (HEm 11%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma Em13 : bv_unsigned (ew Em 13) = SOv. Proof. rewrite (HEm 13%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma Em32 : ew Em 32 = w64 T. Proof. rewrite (HEm 32%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma Em39 : ew Em 39 = w64 cl. Proof. rewrite (HEm 39%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma Em40 : ew Em 40 = w64 (AGj6.Pv ly cl). Proof. rewrite (HEm 40%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma T_range : zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL.
Proof. pose proof (@AGj6.high_facts _ ly regs0 mem0 n tr 0 Hvd LY IMG Htrlen DPOSTm) as (F1 & F2 & _). split; assumption. Qed.
Lemma R_ra : getr (ms_regs ms1) 1 = w64 0x379c8. Proof. rreg HSC (1%bv : bv 5) R. exact R. Qed.
Lemma R_sp : getr (ms_regs ms1) 2 = w64 (sp0 - 176).
Proof. rreg HSC (2%bv : bv 5) R. rewrite R, Em2. unfold w64, sp0. f_equal; lia. Qed.
Lemma R_gp : getr (ms_regs ms1) 3 = getr regs0 3. Proof. rreg HSC (3%bv : bv 5) R. rewrite R, Em3. reflexivity. Qed.
Lemma R_tp : getr (ms_regs ms1) 4 = w64 TFIB_TP. Proof. rreg HSC (4%bv : bv 5) R. exact R. Qed.
Lemma R_a0 : getr (ms_regs ms1) 10 = w64 (T + t_cache).
Proof. rreg HSC (10%bv : bv 5) R. rewrite R, Em32. unfold w64, t_cache. rewrite Zbv_add_unsigned. reflexivity. Qed.
Lemma R_a1 : getr (ms_regs ms1) 11 = w64 (T + t_cache + 80 * cl). Proof. rreg HSC (11%bv : bv 5) R. rewrite R, Em40. reflexivity. Qed.
Lemma R_a2 : getr (ms_regs ms1) 12 = w64 inst. Proof. rreg HSC (12%bv : bv 5) R. rewrite R, Em11, Hi11. reflexivity. Qed.
Lemma R_a3 : getr (ms_regs ms1) 13 = w64 cl. Proof. rreg HSC (13%bv : bv 5) R. rewrite R, Em39. reflexivity. Qed.
Lemma SP1 : spZ (ms_regs ms1) = sp0 - 176.
Proof. unfold spZ. rewrite R_sp. unfold w64. apply unsigned_lit_small. pose proof Usp. pose proof Hsp. pose proof STK. unfold AFSTACK, kHighMemBeg in *. lia. Qed.
Lemma UNW1 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (T + t_unwinding) 1 0.
Proof.
pose proof T_range as [T1 T2].
memv HSC 41%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite Em32; unfold w64, t_unwinding; rewrite unsigned_lit_small by (ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia); reflexivity
| reflexivity | cbn; lia].
Qed.
Lemma UNW0 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + t_unwinding) 1 0. Proof. exact (AGif0n.mv_unw B W ly inst mem0 cl HMV). Qed.
Lemma AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem0 a.
Proof.
intros a Ha Hs. destruct (Z.eq_dec a (T + t_unwinding)) as [->|Hne].
- pose proof (val_mem_aview (w_H W) (ms_mem ms1) (T + t_unwinding) 1 0 0 UNW1 ltac:(lia)) as X1.
  pose proof (val_mem_aview (w_H W) mem0 (T + t_unwinding) 1 0 0 UNW0 ltac:(lia)) as X0.
  rewrite Z.add_0_r in X1, X0. rewrite X1, X0. reflexivity.
- apply aview_same. apply MEQW. rewrite unsigned_lit_small by exact Ha. unfold AGj8.WINM. fold sp0. unfold T in Hne. clear - Hs Hne. lia.
Qed.
(* The refill call: [if_refill] at the call state reached by MISS1. *)
Lemma REFILL : amreal tfibsegs (rtree cl S1) W (cfg_at tfibsegs A_Refill (ms_regs ms1) (ms_mem ms1) (md0' mat1))
  (rleaf ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1)).
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal).
assert (RAW : forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) ->
  ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) -> ms_mem ms1 x = mem0 x).
{ intros x N1 N2. apply MEQW. unfold AGj8.WINM. intros [X|X]; [exact (N1 X) | exact (N2 X)]. }
exact (if_refill inst ly S W mem0 md0 n sp0 (ms_regs ms1) (ms_mem ms1) mat1 HARX HRP Hn0 FP Hmiss Hlo Hbot Hhi Hal AG1 RAW PRESW
  SP1 R_ra (eq_trans R_gp Hgp) R_tp R_a0 R_a1 R_a2 R_a3).
Qed.
Lemma RAZ1 : raZ (ms_regs ms1) = 0x379c8.
Proof. unfold raZ. rewrite R_ra. unfold w64. apply unsigned_lit_small. lia. Qed.
(* The refill call with errno kept (ErrnoG.ame_refill). *)
Lemma REFILL_e : amreal tfibsegs (rtree cl S1) W (cfg_at tfibsegs A_Refill (ms_regs ms1) (ms_mem ms1) (md0' mat1))
  (ErrnoG.rleaf_e B ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1)).
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal).
assert (RAW : forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) ->
  ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) -> ms_mem ms1 x = mem0 x).
{ intros x N1 N2. apply MEQW. unfold AGj8.WINM. intros [X|X]; [exact (N1 X) | exact (N2 X)]. }
exact (ame_refill inst ly S W mem0 md0 n sp0 (ms_regs ms1) (ms_mem ms1) mat1 HARX HRP Hn0 FP Hmiss Hlo Hbot Hhi Hal AG1 RAW PRESW
  SP1 R_ra (eq_trans R_gp Hgp) R_tp R_a0 R_a1 R_a2 R_a3).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* After the refill: post-refill state S' at layout ly' (>= ly), registers regsR, memory memR.                       *)
Section g0.
Variables (S' : astate) (ly' : alayout) (W' : world tfibsegs) (regsR : bvmap 5 word) (memR : word -> option byte) (mdR : Model).
Hypothesis HARXp : ARX inst ly' S' W' memR mdR.
Hypothesis HLPp : lpost S'.
Hypothesis CIp : st_cache_inited S' = true.
Hypothesis HBBp : blocks_bytes S' = blocks_bytes S.
Hypothesis Hly : layout_le (length (st_secs S)) ly ly'.
Hypothesis HWLE : wle W W'.
Hypothesis HAREGS : aregs_preserved (ms_regs ms1) regsR.
Hypothesis HSIO : same_io (md0' mat1) mdR.
Hypothesis HFRA : forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly' S' a -> ~ (spZ (ms_regs ms1) - RSTACK <= a < spZ (ms_regs ms1)) ->
  aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) (ms_mem ms1) a.
Hypothesis HFRR : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' S' (bv_unsigned x) ->
  ~ (spZ (ms_regs ms1) - RSTACK <= bv_unsigned x < spZ (ms_regs ms1)) -> memR x = (ms_mem ms1) x.
Hypothesis HPRR : forall a, spZ (ms_regs ms1) - RSTACK <= a < spZ (ms_regs ms1) -> apresent (w_H W') memR a.
(* ERRNO-KEPT: the refill keeps errno (ErrnoG.rleaf_e); used only by the _e lemmas. *)
Hypothesis HERRp : ErrnoG.errno_kept B (ms_mem ms1) memR.
Let msR : machine_state := mkst regsR (w64 0x379c8) memR (seg_rom tfibsegs).
Let cR : config := mkCfg msR (with_vm_backing (m_vm_lazy mdR) (m_vm_materialized mdR) mdR).
Let ms3 : machine_state := mkst regsR (w64 0x379c8) (mrestrict (w_H W') memR) (seg_rom tfibsegs).
Let E1 : env := havoc Em hRFk (map (getr regsR) CLOB).

Lemma LyEq : ly_stk_lo ly' = ly_stk_lo ly /\ ly_stk_hi ly' = ly_stk_hi ly /\ ly_top ly' = ly_top ly /\ ly_T ly' = ly_T ly.
Proof. destruct Hly as (_ & _ & _ & HT & _ & _ & _ & _ & Htop & Hlo & Hhi & _). repeat split; assumption. Qed.
Lemma Hsp' : ly_stk_lo ly' + AFSTACK <= sp0 /\ ly_bot ly' < sp0 /\ sp0 <= ly_stk_hi ly' /\ sp0 mod 16 = 0.
Proof. pose proof LyEq as (E1' & E2' & E3' & _). pose proof Hsp as H. unfold ly_bot in *. rewrite E1', E2', E3'. exact H. Qed.
Lemma Hso' : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly' /\ SOv mod 8 = 0. Proof. pose proof LyEq as (_ & E2' & _). rewrite E2'. exact Hso. Qed.
Lemma Hbp' : sp0 <= BPv /\ BPv + 8 * 30 <= ly_stk_hi ly' /\ BPv mod 8 = 0. Proof. pose proof LyEq as (_ & E2' & _). rewrite E2'. exact Hbp. Qed.
(* A stack address is owned neither at S (layout ly) nor at S' (layout ly'). *)
Lemma NOWN : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX ly S a /\ ~ AOX ly' S' a.
Proof.
intros a Ha. pose proof LyEq as (E1' & E2' & _). split.
- exact (if_stack inst ly S W mem0 md0 a HARX Ha).
- apply (if_stack inst ly' S' W' memR mdR a HARXp). rewrite E1', E2'. exact Ha.
Qed.
(* The refill keeps the caller's stack: any address in the stack, outside the callee window. *)
Lemma STKkept : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp0 - 176 - RSTACK <= a < sp0 - 176) ->
  aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) (ms_mem ms1) a.
Proof.
intros a Ha Hnw. pose proof STK as [K1 K2]. destruct (NOWN a Ha) as [N1 N2].
apply (HFRA a); [clear - Ha K1 K2; unfold kHighMemBeg, kHighMemEnd in *; lia | exact N1 | exact N2 | rewrite SP1; exact Hnw].
Qed.
(* Above the entry sp (the caller's frame): the refill and MISS1 keep the bytes of the entry memory. *)
Lemma ABOVE : forall a, sp0 <= a < ly_stk_hi ly -> aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) mem0 a.
Proof.
intros a Ha. pose proof Hsp as (S1' & _ & S3' & _). pose proof STK as [K1 K2].
rewrite (STKkept a ltac:(clear - Ha S1'; unfold AFSTACK in *; lia) ltac:(clear - Ha; lia)).
apply AG1; [clear - Ha S1' K1 K2; unfold kHighMemBeg, kHighMemEnd, AFSTACK in *; lia | clear - Ha; lia].
Qed.
Lemma PRES' : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W') memR a.
Proof.
intros a Ha. pose proof Hsp as (S1' & S2' & S3' & S4'). pose proof STK as [K1 K2]. pose proof Usp as Us.
assert (Hhi' : TFIB_IMG_END <= a < 2 ^ 64) by (clear - Ha S1' K1 Us; unfold TFIB_IMG_END, AFSTACK, kHighMemBeg in *; unfold sp0 in *; lia).
assert (Hst : ly_stk_lo ly <= a < ly_stk_hi ly) by (clear - Ha S1' S3'; unfold AFSTACK, sp0 in *; lia).
destruct (Z_lt_le_dec a (sp0 - 176 - RSTACK)) as [H1|H1]; [|destruct (Z_lt_le_dec a (sp0 - 176)) as [H2|H2]].
- apply (apresent_xfer (w_H W) (w_H W') (ms_mem ms1) memR a Hhi'); [apply STKkept; [exact Hst | lia] | exact (PRESW a Ha)].
- apply HPRR. rewrite SP1. lia.
- apply (apresent_xfer (w_H W) (w_H W') (ms_mem ms1) memR a Hhi'); [apply STKkept; [exact Hst | lia] | exact (PRESW a Ha)].
Qed.
Lemma Em2u : bv_unsigned (ew Em 2) = sp0. Proof. rewrite Em2. reflexivity. Qed.
Lemma KEPT3 : Forall (region_kept tfibsegs Em (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W') memR)) AGi4.RSK3.
Proof.
pose proof Hsp as (S1' & S2' & S3' & S4'). pose proof STK as [K1 K2]. pose proof Usp as Us. pose proof Hso as (O1 & O2 & O3).
assert (A : forall a, sp0 - 176 <= a < sp0 -> aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) (ms_mem ms1) a)
by (intros a Ha; apply STKkept; [clear - Ha S1' S3'; unfold AFSTACK, sp0 in *; lia | clear - Ha; unfold RSTACK; lia]).
assert (ASO : forall a, SOv <= a < SOv + 16 -> aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) (ms_mem ms1) a)
by (intros a Ha; apply STKkept; [clear - Ha O1 O2 S1'; unfold AFSTACK, SOv, sp0 in *; lia | clear - Ha O1; unfold RSTACK, SOv, sp0 in *; lia]).
unfold AGi4.RSK3. cbn [AGi4.K3bst AGi4.K3scr AGi4.K3top]. cbv [trim_lo].
apply Forall_cons. { eapply (region_kept_view (w_H W) (w_H W') Em (ms_mem ms1) memR 13 _ _ _ _ _ SOv Em13);
  [intros a Ha; apply ASO; clear - Ha; unfold SOv in *; lia | clear - O1 S1' K1; unfold TFIB_IMG_END, kHighMemBeg, AFSTACK, SOv, sp0 in *; lia | clear - O2 K2; unfold kHighMemEnd, SOv in *; lia | clear; intros a Ha; lia]. }
apply Forall_cons. { eapply (region_kept_view (w_H W) (w_H W') Em (ms_mem ms1) memR 2 _ _ _ _ _ sp0 Em2u);
  [intros a Ha; apply A; clear - Ha; lia | clear - S1' K1; unfold TFIB_IMG_END, AFSTACK, kHighMemBeg in *; unfold sp0 in *; lia | clear - Us; unfold sp0 in *; lia | clear; intros a Ha; lia]. }
apply Forall_cons. { eapply (region_kept_view (w_H W) (w_H W') Em (ms_mem ms1) memR 2 _ _ _ _ _ sp0 Em2u);
  [intros a Ha; apply A; clear - Ha; lia | clear - S1' K1; unfold TFIB_IMG_END, AFSTACK, kHighMemBeg in *; unfold sp0 in *; lia | clear - Us; unfold sp0 in *; lia | clear; intros a Ha; lia]. }
apply Forall_nil.
Qed.
Lemma HS3 : st_ok tfibsegs E1 AGi4.SSK3 ms3.
Proof.
rewrite AGi4.SSK3_eq. pose proof (AGi4.MK_CALL_facts) as (F1 & F2 & F3 & F4 & F5 & F6). destruct AGi4.MK_CALL_mem3 as [rest ER].
apply (st_ok_after_call tfibsegs hRFk Em AGi4.MK_CALL (mkst (ms_regs ms1) (w64 0x37e68) (mrestrict (w_H W) (ms_mem ms1)) (seg_rom tfibsegs))
regsR (mrestrict (w_H W') memR) AGi4.RSK3 0x379c8).
- pose proof HSC as H. rewrite ms1_shape in H. exact H.
- exact F6.
- exact F1.
- exact F2.
- exact F3.
- exact F4.
- rewrite ER. change AGi4.RSK3 with [AGi4.K3bst; trim_lo AGi4.K3scr (-176); AGi4.K3top].
  apply submem_keep; [apply subregion_refl|]. apply submem_keep; [apply subregion_trim_lo|]. apply submem_keep; [apply subregion_refl|]. apply submem_nil.
- exact F5.
- exact HAREGS.
- exact KEPT3.
Qed.
Lemma E1_2 : bv_unsigned (ew E1 2) = sp0.
Proof. unfold E1. rewrite ew_havoc_old by (unfold hRFk; lia). exact Em2u. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The a0 = 1 cache join, at the post-refill layout ly'.                                                            *)
Section g.
Variables (l : list Z) (off : Z).
Hypothesis Hcache' : pc_chunks (cache S' cl) = l ++ [off].
Hypothesis HA1 : getr regsR 10 = w64 1.
Let cnt' : Z := Z.of_nat (length (l ++ [off])).
Let v' : Z := off / 16.
Let DPOST' : Z -> (word -> option byte) -> Prop := fun z m => dpost inst ly' S' W' tr z m.
Lemma HVW : off mod 32 = 0 /\ AGif0n.hview B W' ly' inst memR cl cnt' v'.
Proof. exact (if_view_m inst ly' S' W' memR mdR n l off HARXp Hn0 FP CIp Hcache'). Qed.
Lemma HVn' : AGif0n.hview B W' ly' inst memR cl cnt' v'. Proof. exact (proj2 HVW). Qed.
Lemma HV' : AGif0cgif.hview B W' ly' inst memR cl cnt' v'. Proof. exact (hview_cgif B W' ly' inst memR cl cnt' v' HVn'). Qed.
Lemma LY' : layout_ok ly'. Proof. exact (AGif0cgif.hv_ly B W' ly' inst memR cl cnt' v' HV'). Qed.
Lemma IMG' : img_cover ly'. Proof. exact (AGif0cgif.hv_img B W' ly' inst memR cl cnt' v' HV'). Qed.
Lemma HTSD' : ly_tsd ly' = TFIB_TSD. Proof. exact (AGif0cgif.hv_tsd B W' ly' inst memR cl cnt' v' HV'). Qed.
Lemma Hoff_def' : off = 16 * v'.
Proof.
pose proof (proj1 HVW) as H32. unfold v'. clear - H32. apply Z.mod_divide in H32 as [q Hq]; [|lia]. rewrite Hq.
replace (q * 32) with ((2 * q) * 16) by lia. rewrite Z.div_mul by lia. lia.
Qed.
Lemma Hv' : 0 <= v' /\ 16 * v' + 2 ^ 16 <= 2 ^ 32. Proof. exact (@AGjd.vw_Hv _ _ B W' ly' inst memR n cl cnt' v' TS HV' Nrange Hcl_class). Qed.
Lemma Hv2' : v' mod 2 = 0. Proof. exact (@AGjd.vw_Hv2 _ _ B W' ly' inst memR n cl cnt' v' TS HV' Nrange Hcl_class). Qed.
Lemma Hcnt' : 1 <= cnt' <= 16. Proof. exact (@AGjd.vw_Hcnt _ _ B W' ly' inst memR n cl cnt' v' TS HV' Nrange Hcl_class). Qed.
Lemma HKpres' : forall a, AGj6.Kv ly' cl v' <= a < AGj6.Kv ly' cl v' + AGj6.RZ + AGj6.R8v n -> apresent (w_H W') memR a.
Proof. exact (@AGjd.vw_KPRES _ _ B W' ly' inst memR n cl cnt' v' TS HV' Nrange Hcl_class). Qed.
Lemma HSKpres' : forall a, AGj6.SKv ly' cl v' <= a < AGj6.SKv ly' cl v' + (AGj6.RZ + AGj6.R8v n) / 8 -> apresent (w_H W') memR a.
Proof. exact (@AGjd.vw_SKPRES _ _ B W' ly' inst memR n cl cnt' v' TS HV' Nrange Hcl_class). Qed.
Lemma HPB250' : AGj6.NPv n mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W') memR) (AGj6.PBv ly' n cl v') 1 250.
Proof. exact (@AGjd.vw_PB250 _ _ B W' ly' inst memR n cl cnt' v' TS HV' Nrange Hcl_class). Qed.
Lemma PSO' : val_mem tfibsegs (mrestrict (w_H W') memR) SOv 8 BPv.
Proof.
pose proof Hso as (O1 & O2 & O3). eapply val_mem_aview_xfer; [|exact PSO].
intros k Hk. apply ABOVE. clear - Hk O1 O2. lia.
Qed.
Lemma PLEN' : val_mem tfibsegs (mrestrict (w_H W') memR) (SOv + 8) 8 (Z.of_nat (length tr)).
Proof.
pose proof Hso as (O1 & O2 & O3). eapply val_mem_aview_xfer; [|exact PLEN].
intros k Hk. apply ABOVE. clear - Hk O1 O2. lia.
Qed.
Lemma BUF' : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W') memR) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).
Proof.
intros i Hi. pose proof Hbp as (O1 & O2 & O3). pose proof Hsp as (S1' & _ & S3' & _). eapply val_mem_aview_xfer; [|exact (BUFW i Hi)].
intros k Hk. apply STKkept; clear - Hi Hk O1 O2 Htrlen S1'; unfold AFSTACK, RSTACK, BPv, sp0 in *; lia.
Qed.

Section gj.
Variables (j0 jb j1 j2 j3 j4 : Z).
Hypothesis Hj0 : val_mem tfibsegs (mrestrict (w_H W') memR) (ly_T ly' + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfibsegs (mrestrict (w_H W') memR) (ly_T ly' + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfibsegs (mrestrict (w_H W') memR) (ly_T ly' + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfibsegs (mrestrict (w_H W') memR) (ly_T ly' + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfibsegs (mrestrict (w_H W') memR) (AGj6.SSLOTv ly' cl) 8 j4.
Hypothesis Hjb : 0 <= jb <= 255.
Hypothesis Hjb_def : val_mem tfibsegs (mrestrict (w_H W') memR) (AGj6.Kv ly' cl v' + AGj6.RZ - 15) 1 jb.
Let E0' : env := AGj6.E0 ly' regs0 n tr cl cnt' v' csz j0 jb j1 j2 j3 j4.
Let Es : env := env_merge PND E1 E0'.
Lemma HEs : forall k, (k < aHAV)%nat -> ew Es k = ew E0' k.
Proof.
intros k Hk. unfold aHAV in Hk. destruct (PND k) eqn:HP.
- unfold Es. rewrite (ew_merge_in PND E1 E0' k HP). unfold E1. rewrite ew_havoc_old by (unfold hRFk; lia).
  rewrite (HEm k Hk). unfold E0m, E0'. exact (E0_nondummy_ly _ ly ly' regs0 n tr cl csz 1 0 0 0 0 0 0 0 cnt' v' j0 jb j1 j2 j3 j4 k Hly Hk HP).
- unfold Es. apply ew_merge_out. exact HP.
Qed.
Lemma AGs : env_agree 64 E0' Es. Proof. split; [exact HEs | reflexivity]. Qed.
Lemma Es2 : bv_unsigned (ew Es 2) = sp0.
Proof. rewrite (HEs 2%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma FACTS' : atoms_ok E0' (f_atoms FKG).
Proof. exact (proj1 (@AGje.FACTS_ok _ _ W' ly' regs0 memR n tr cl cnt' v' csz j0 jb j1 j2 j3 j4 Hcl Hv' Hcnt' Hjb Hv2' LY' IMG' Hn Hsp' Htrlen Hso' Hbp' (or_intror Hcf1) DPOST' Nrange B inst TS HV' Hi11 HIO Hcl_class)). Qed.
Lemma REG0' : Forall (region_ok tfibsegs E0' (mrestrict (w_H W') memR)) REG0KG.
Proof. exact (@AGjd.REG0K_ok _ _ W' ly' regs0 memR n tr cl cnt' v' csz j0 jb j1 j2 j3 j4 Hcl Hv' Hcnt' Hjb Hv2' LY' IMG' Hsp' Htrlen Hso' Hbp' DPOST' Nrange B inst TS HV' Hi11 HIO PSO' PLEN' PRES' Hcl_class Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def). Qed.
Lemma PAIRS' : pairwise_disjoint E0' REG0KG.
Proof. exact (@AGje.PAIRS_ok _ W' ly' regs0 memR n tr cl cnt' v' csz j0 jb j1 j2 j3 j4 Hcl Hv' Hcnt' Hv2' LY' IMG' Hsp' Htrlen Hso' Hbp' DPOST' Nrange inst Hi11 HIO). Qed.
Lemma HS5 : st_ok tfibsegs Es (mkSS (ss_pc AGi4.SSK3) (sr_set (ss_regs AGi4.SSK3) 10%bv (SLit 1)) (ss_mem AGi4.SSK3) (ss_resv AGi4.SSK3) (ss_facts AGi4.SSK3)) ms3.
Proof.
assert (HS4 : st_ok tfibsegs Es AGi4.SSK3 ms3).
{ pose proof AGi4.SSK3_atoms as (A1 & A2 & A3 & A4 & A5). pose proof AGi4.tlREG0K_facts as (_ & _ & T3).
  apply (st_ok_agree_on2 tfibsegs PND E1 Es AGi4.SSK3 ms3 HS3 (env_merge_on PND E1 E0') A1 A2 A3 A4).
  rewrite A5. exact (atoms_ok_agree 64 E0' Es _ AGs T3 FACTS'). }
apply (st_ok_pin_regU Es AGi4.SSK3 ms3 10%bv (SLit 1) HS4); [intros X; discriminate X|].
pose proof (st_ok_reg tfibsegs Es AGi4.SSK3 ms3 10%bv HS4) as R. unfold YP0e.U. rewrite <- R. unfold ms3. cbn [ms_regs mkst]. rewrite HA1. reflexivity.
Qed.
Lemma region_ok_agree_on_lt : forall r, In r TAIL0KG -> region_ok tfibsegs E0' (mrestrict (w_H W') memR) r -> region_ok tfibsegs Es (ms_mem ms3) r.
Proof.
intros r Hr H. pose proof AGi4.tlREG0K_facts as (T1 & _). unfold ms3. cbn [ms_mem mkst].
apply (region_ok_agree tfibsegs 64 E0' Es _ r AGs); [|exact H]. exact (proj1 (forallb_forall _ _) T1 r Hr).
Qed.
Lemma HS6 : st_ok tfibsegs Es (mkSS 0x379c8 (sr_set (ss_regs AGi4.SSK3) 10%bv (SLit 1)) [AGi4.K3bst; AGi4.K3scr; AGi4.K3top] None (ss_facts AGi4.SSK3)) ms3.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U_. pose proof Hso as (O1 & O2 & O3).
pose proof (st_ok_mem_surgery Es _ ms3 [AGi4.K3bst; AGi4.K3scr; AGi4.K3top] HS5) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. apply X. clear X.
intros (HW & HF & HP). unfold ms3 in *. cbn [ms_mem mkst] in *.
assert (BV : base_val Es (Some 2%nat) = sp0) by (cbn [base_val]; exact Es2).
assert (BV13 : base_val Es (Some 13%nat) = SOv) by (cbn [base_val]; rewrite (HEs 13%nat ltac:(cbv; lia)); reflexivity).
split; [reflexivity|]. split.
- apply Forall_cons; [exact (Forall_inv HF)|]. apply Forall_cons; [|exact (Forall_inv_tail (Forall_inv_tail HF))].
pose proof (Forall_inv (Forall_inv_tail HF)) as (R1 & R2 & R3 & R4). cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in R1, R2, R3, R4.
rewrite BV in R1, R2, R3, R4.
unfold region_ok, AGi4.K3scr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV.
split; [clear - Hlo K1; unfold AFSTACK, kHighMemBeg in *; unfold sp0 in *; lia|]. split; [clear - U_; unfold sp0 in *; lia|]. split; [|exact R4].
intros o Ho. apply apresent_writable; [clear - Ho Hlo K1 U_; unfold TFIB_IMG_END, AFSTACK, kHighMemBeg in *; unfold sp0 in *; lia|]. apply PRES'. clear - Ho; unfold AFSTACK; lia.
- unfold AGi4.K3bst, AGi4.K3scr, AGi4.K3top. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite BV, BV13. repeat split; unfold sp0, SOv in *; lia.
Qed.
Lemma HS7 : st_ok tfibsegs Es AGi4.MK_AFTER ms3.
Proof.
rewrite AGi4.MK_AFTER_eq3. pose proof AGi4.tlREG0K_facts as (T1 & T2 & T3).
pose proof (st_ok_mem_surgery Es _ ms3 ([AGi4.K3bst; AGi4.K3scr; AGi4.K3top] ++ TAIL0KG) HS6) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. apply X. clear X.
intros HM. pose proof PAIRS' as PP. unfold REG0KG in PP. cbn [pairwise_disjoint] in PP. destruct PP as (A0 & A1 & A2 & PT).
pose proof REG0' as RR. unfold REG0KG in RR. apply Forall_inv_tail, Forall_inv_tail, Forall_inv_tail in RR.
apply mem_ok_app; [exact HM | exact T2 | | |].
- apply Forall_forall. intros r Hr. apply (region_ok_agree_on_lt r); [exact Hr|]. exact (proj1 (Forall_forall _ _) RR r Hr).
- exact (pairwise_disjoint_agree 64 E0' Es TAIL0KG AGs T1 PT).
- intros r Hr.
  assert (Hb : obase_lt 64 (YP09.r_base r) = true).
  { pose proof (proj1 (forallb_forall _ _) T1 r Hr) as Ha. unfold region_atoms_lt in Ha. apply andb_prop in Ha as [Ha _]. exact Ha. }
  assert (D0 : extent_disjoint Es R_soG r) by (apply (extent_disjoint_agree 64 E0' Es R_soG r AGs eq_refl Hb); apply (all_disjoint_In E0' _ _ r A0); right; right; exact Hr).
  assert (D1 : extent_disjoint Es R_scrG r) by (apply (extent_disjoint_agree 64 E0' Es R_scrG r AGs eq_refl Hb); apply (all_disjoint_In E0' _ _ r A1); right; exact Hr).
  assert (D2 : extent_disjoint Es R_slotG r) by (apply (extent_disjoint_agree 64 E0' Es R_slotG r AGs eq_refl Hb); apply (all_disjoint_In E0' _ _ r A2); exact Hr).
  cbn [all_disjoint]. split; [|split; [|split; [|exact I]]].
  + exact (YFhm.extent_disjoint_ext3 Es r R_soG AGi4.K3bst eq_refl (YFhm.extent_disjoint_sym Es R_soG r D0)).
  + exact (YFhm.extent_disjoint_ext3 Es r R_scrG AGi4.K3scr eq_refl (YFhm.extent_disjoint_sym Es R_scrG r D1)).
  + exact (YFhm.extent_disjoint_ext3 Es r R_slotG AGi4.K3top eq_refl (YFhm.extent_disjoint_sym Es R_slotG r D2)).
Qed.
Lemma ATJ : AGj6.at_ST W' ly' regs0 memR mdR n tr cl cnt' v' csz j0 jb j1 j2 j3 j4 AGi4.MK_AFTER W' cR.
Proof.
split; [reflexivity|]. exists msR, (m_vm_materialized mdR), Es. split; [reflexivity|]. split; [exact HEs|].
split; [unfold msR; rewrite restrict_mkst_fx; exact HS7|].
split; [intros x _; reflexivity|]. split; [exact PRES' | exact BUF'].
Qed.
Lemma HDAOK : forall z m, DPOST' z m -> aok S' (KDepot tr) z.
Proof. intros z m H. exact (Fdaok inst ly' S' W' tr z m H). Qed.
Lemma HDEP : forall (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) (buf : Z),
(forall x : word, AGj6.DZONE ly' (bv_unsigned x) \/ CZONE ly' (bv_unsigned x) -> mem1 x = memR x) ->
getr regs1 10 = Z_to_bv 64 buf -> getr regs1 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs1 3 = Z_to_bv 64 (as_gp B) -> getr regs1 4 = Z_to_bv 64 TFIB_TP -> YK0s.ret_ok (getr regs1 1) ->
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W') mem1) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly' <= buf -> buf + 8 * 30 <= ly_stk_hi ly' ->
buf + 8 * 30 <= bv_unsigned (getr regs1 2) - DEP_STK \/ bv_unsigned (getr regs1 2) <= buf ->
bv_unsigned (getr regs1 2) mod 16 = 0 -> ly_stk_lo ly' <= bv_unsigned (getr regs1 2) - DEP_STK ->
bv_unsigned (getr regs1 2) <= ly_stk_hi ly' ->
(forall a, bv_unsigned (getr regs1 2) - DEP_STK <= a < bv_unsigned (getr regs1 2) -> apresent (w_H W') mem1 a) ->
SRr tfibsegs W' (mkCfg (mkst regs1 (Z_to_bv 64 A_StackDepotPut) mem1 (seg_rom tfibsegs)) md1)
(fun W'' c' => W'' = W' /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs1 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md1) mat md1) /\
regs_preserved regs1 regs' /\
(forall x : word, ~ (bv_unsigned (getr regs1 2) - DEP_STK <= bv_unsigned x < bv_unsigned (getr regs1 2)) ->
~ AGj6.DZONE ly' (bv_unsigned x) -> mem' x = mem1 x) /\
(forall a, apresent (w_H W') mem1 a -> apresent (w_H W') mem' a) /\
DPOST' z mem').
Proof. intros regs1 mem1 md1 buf. exact (if_depot_miss inst ly' ly S S' W mem0 md0 W' memR mdR tr regs1 mem1 md1 buf HARX Htr HARXp). Qed.
Lemma TAILJ : amreal tfibsegs (malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs 0x379c8 regsR memR mdR)
(fun r W'' c'' => exists odd z, r = (ck_user (new_chunk cl off n), st_final S' cl l off n tr z) /\
(odd = true <-> AGj6.NPv n mod 8 <> 0) /\
AGif0n.at_RETkw W' ly' regs0 memR mdR n cl cnt' v' jb DPOST' odd z W'' c'').
Proof.
replace (cfg_at tfibsegs 0x379c8 regsR memR mdR) with cR by (unfold cfg_at, cR, msR; rewrite with_vm_backing_id; reflexivity).
eapply amreal_SRr_pre.
{ exact (@AGj7.segJ _ _ W' ly' regs0 memR mdR n tr cl cnt' v' csz j0 jb j1 j2 j3 j4 Hcl Hv' Hcnt' Hv2' LY' IMG' Hsp' Htrlen Hbp' DPOST' Nrange l off W' cR ATJ). }
intros W2 c2 _ HJ. pose proof (proj1 HJ) as EW. subst W2.
exact (@AGjg.tail_inner _ _ W' ly' regs0 memR mdR n tr cl cnt' v' csz j0 jb j1 j2 j3 j4 Hcl Hv' Hcnt' Hjb Hv2' LY' IMG' Hn Htp (or_intror Hcf1) Hra Hsp' Htrlen Hso' Hbp' Hinst DPOST' HKpres' HSKpres' HPB250' Nrange Hcl_def B S' l off stag Hgp Hcache' HDEP HDAOK c2 HJ).
Qed.
(* The join leaf, given its granted path. *)
Lemma LEAFJ : forall r W'' c'',
(exists odd z, r = (ck_user (new_chunk cl off n), st_final S' cl l off n tr z) /\ (odd = true <-> AGj6.NPv n mod 8 <> 0) /\
  AGif0n.at_RETkw W' ly' regs0 memR mdR n cl cnt' v' jb DPOST' odd z W'' c'') -> PL r W'' c''.
Proof.
intros r W'' c'' (odd & z & -> & Hodd & HR) HPATH.
pose proof HR as HR0.
destruct HR as (-> & regs' & mem' & mat & -> & R10 & RCS & (memD & DP & PRD & EQD) & MEQF & PRS & PRW & VALS).
pose proof (AGj6.case0_sizes n Nrange) as (L & RS & R8 & NP & FP' & NSz & RQ).
assert (WF : wframe W' ly' regs0 memR tr) by (split; [exact Hsp'|]; split; [exact Htrlen|]; split; [exact Hso'|]; split; [exact Hbp' | exact PRES']).
destruct (if_post_miss_k inst ly' ly S S' W mem0 md0 W' memR mdR n tr l off regs0 jb odd z regs' mem' mat HARX HRP HBB HARXp Hnnmax
  ltac:(rewrite HBBp; exact HBB) Htr Nrange CIp Hcache' WF Hjb Hjb_def HR0 Hodd HPATH) as [HARXf HLPf].
assert (KU : sptr_addr B ly' (ck_user (new_chunk cl off n)) = AGj6.Kv ly' cl v' + AGj6.RZ).
{ unfold new_chunk, ck_user, ck_rz. cbn [ck_beg ck_req padd]. rewrite RS.
  rewrite (AGj6.Kv_is_sptr ly' cl v' Hcl B off Hoff_def'). unfold sptr_addr. cbn. lia. }
exists ly', regs', mem', (with_vm_backing (m_vm_lazy mdR) mat mdR).
split; [exact (CFG_leaf regs' mem' _)|].
split.
{ split; [exact HARXf|]. split; [exact Hly|]. split; [exact HWLE|]. split; [exact (CS_leaf regs' RCS)|].
  split; [exact (same_io_tr _ _ _ (same_io_tr _ _ _ (same_io_wvb md0 mat1) HSIO) (same_io_wvb mdR mat))|].
  split.
  { intros a Ra NO NO' NS NE.
    assert (NBLK : ~ (sptr_addr B ly' (ck_user (new_chunk cl off n)) <= a < sptr_addr B ly' (ck_user (new_chunk cl off n)) + req_size n)).
    { intros H. apply NE. cbn [fst]. split; [unfold new_chunk, ck_user, padd; cbn; discriminate | exact H]. }
    assert (OWN : AGif0n.hit_writes_k ly' n cl v' odd a -> False).
    { intros HW. apply NO'. apply (if_mono_join inst ly' S' W' memR mdR n l off tr z a HARXp Hcache' NBLK).
      exact (if_owned_m_k inst ly' S' W' memR mdR n l off odd a HARXp Nrange CIp Hcache' Ra (proj1 Hodd) HW). }
    assert (NST : ~ (sp0 - AFSTACK <= a < sp0)).
    { intros X. apply NS. unfold ascratch, spZ, AFSTACK_G. left. rewrite SP_U. unfold AFSTACK in X. exact X. }
    transitivity (aview tfibsegs (w_H W') memR a).
    { apply aview_same. apply MEQF; rewrite unsigned_lit_small by exact Ra.
      - intros Hw. unfold AGj6.WIN in Hw. destruct Hw as [Hs|Hw]; [exact (NST Hs)|].
        apply OWN. unfold AGif0n.hit_writes_k. destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw | right; left; exact Hw | right; right; left; exact Hw].
      - intros Hd. apply OWN. unfold AGif0n.hit_writes_k. right; right; right; left; exact Hd.
      - intros Hu. apply NE. cbn [fst]. split; [unfold new_chunk, ck_user, padd; cbn; discriminate|]. rewrite KU, RQ. exact Hu.
      - intros Hs. apply OWN. unfold AGif0n.hit_writes_k. right; right; right; right; exact Hs. }
    transitivity (aview tfibsegs (w_H W) (ms_mem ms1) a).
    { apply (HFRA a); [exact Ra | exact NO | intros O; apply NO'; exact (if_mono_join inst ly' S' W' memR mdR n l off tr z a HARXp Hcache' NBLK O) | rewrite SP1; intros X; apply NST; unfold RSTACK, AFSTACK in *; lia]. }
    exact (AG1 a Ra NST). }
  split.
  { (* the raw frame: the same three steps on the raw memory *)
    intros x NO NO' NS NE. pose proof (u64_range x) as Ra.
    assert (NBLK : ~ (sptr_addr B ly' (ck_user (new_chunk cl off n)) <= bv_unsigned x < sptr_addr B ly' (ck_user (new_chunk cl off n)) + req_size n)).
    { intros H. apply NE. cbn [fst]. split; [unfold new_chunk, ck_user, padd; cbn; discriminate | exact H]. }
    assert (OWN : AGif0n.hit_writes_k ly' n cl v' odd (bv_unsigned x) -> False).
    { intros HW. apply NO'. apply (if_mono_join inst ly' S' W' memR mdR n l off tr z (bv_unsigned x) HARXp Hcache' NBLK).
      exact (if_owned_m_k inst ly' S' W' memR mdR n l off odd (bv_unsigned x) HARXp Nrange CIp Hcache' Ra (proj1 Hodd) HW). }
    assert (NST : ~ (sp0 - AFSTACK <= bv_unsigned x < sp0)).
    { intros X. apply NS. unfold ascratch, spZ, AFSTACK_G. left. rewrite SP_U. unfold AFSTACK in X. exact X. }
    transitivity (memR x).
    { apply MEQF.
      - intros Hw. unfold AGj6.WIN in Hw. destruct Hw as [Hs|Hw]; [exact (NST Hs)|].
        apply OWN. unfold AGif0n.hit_writes_k. destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw | right; left; exact Hw | right; right; left; exact Hw].
      - intros Hd. apply OWN. unfold AGif0n.hit_writes_k. right; right; right; left; exact Hd.
      - intros Hu. apply NE. cbn [fst]. split; [unfold new_chunk, ck_user, padd; cbn; discriminate|]. rewrite KU, RQ. exact Hu.
      - intros Hs. apply OWN. unfold AGif0n.hit_writes_k. right; right; right; right; exact Hs. }
    transitivity (ms_mem ms1 x).
    { apply HFRR; [exact NO | intros O; apply NO'; exact (if_mono_join inst ly' S' W' memR mdR n l off tr z (bv_unsigned x) HARXp Hcache' NBLK O) | rewrite SP1; intros X; apply NST; unfold RSTACK, AFSTACK in *; lia]. }
    apply MEQW. unfold AGj8.WINM. intros [Hs|Hu]; [exact (NST Hs)|].
    apply OWN. unfold AGif0n.hit_writes_k. left. unfold AGj6.WINT. right; right; right.
    pose proof Hly as (_ & _ & _ & HT & _). first [rewrite HT | rewrite <- HT]; unfold T in Hu; exact Hu. }
  intros a Ha. unfold spZ, AFSTACK_G in Ha. rewrite SP_U in Ha. unfold AFSTACK in PRS. exact (PRS a Ha). }
split; [cbn [fst]; rewrite R10, KU; reflexivity|].
split; [exact HLPf|].
split; [exact HPATH|].
cbn [fst]. unfold new_chunk, ck_user, padd. cbn. intros X; discriminate X.
Qed.
(* The join leaf with errno kept: LEAFJ, plus errno from at_RETkw's raw frame (MEQF), the refill (HERRp) and MISS1 (MEQW). *)
Lemma LEAFJ_e : forall r W'' c'',
(exists odd z, r = (ck_user (new_chunk cl off n), st_final S' cl l off n tr z) /\ (odd = true <-> AGj6.NPv n mod 8 <> 0) /\
  AGif0n.at_RETkw W' ly' regs0 memR mdR n cl cnt' v' jb DPOST' odd z W'' c'') -> PL_e r W'' c''.
Proof.
intros r W'' c'' H HPATH.
pose proof (LEAFJ r W'' c'' H HPATH) as AL.
destruct H as (odd & z & -> & Hodd & HR).
destruct HR as (-> & regs' & mem' & mat & -> & R10 & RCS & DPP & MEQF & PRS & PRW & VALS).
destruct AL as (ly2 & regs2 & mem2 & md2 & Hc & HP & HR2 & HL & HT & HO).
assert (EM : mem2 = mem') by (unfold cfg_at in Hc; injection Hc; intros; subst; reflexivity). subst mem2.
exists ly2, regs2, mem', md2. split; [exact Hc|]. split; [exact HP|].
split; [| split; [exact HR2|]; split; [exact HL|]; split; [exact HT | exact HO]].
intros _ i Hi.
pose proof Hsp' as (Lo' & _ & Hi' & _). pose proof Hsp as (Lo0 & _ & Hi0 & _).
pose proof (EA_K ly' regs0 n cl v' odd i LY' IMG' Lo' Hi' Nrange Hcl (proj1 Hv') Hi) as (N1 & N2 & N3 & N4).
pose proof (EA_M ly regs0 i LY IMG Lo0 Hi0 Hi) as N5.
assert (RE : 0 <= as_errno B + i < 2 ^ 64) by (rewrite (ts_errno B TS); unfold TFIB_ERRNO; lia).
assert (UX : bv_unsigned (w64 (as_errno B + i)) = as_errno B + i) by (unfold w64; apply unsigned_lit_small; exact RE).
transitivity (memR (w64 (as_errno B + i))).
{ apply MEQF; rewrite UX; assumption. }
transitivity (ms_mem ms1 (w64 (as_errno B + i))); [exact (HERRp i Hi)|].
apply MEQW. rewrite UX. exact N5.
Qed.
End gj.
Lemma JOIN : amreal tfibsegs (malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs 0x379c8 regsR memR mdR) PL.
Proof.
destruct (@AGjd.vw_junk_values _ _ B W' ly' inst memR n cl cnt' v' TS HV' Nrange Hcl_class)
  as (j0 & j1 & j2 & j3 & j4 & jb & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hjb & Hjb_def).
eapply amreal_mono; [| eapply TAILJ; eassumption].
intros r W'' c'' H. eapply LEAFJ; eassumption.
Qed.
Lemma JOIN_e : amreal tfibsegs (malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs 0x379c8 regsR memR mdR) PL_e.
Proof.
destruct (@AGjd.vw_junk_values _ _ B W' ly' inst memR n cl cnt' v' TS HV' Nrange Hcl_class)
  as (j0 & j1 & j2 & j3 & j4 & jb & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hjb & Hjb_def).
eapply amreal_mono; [| eapply TAILJ; eassumption].
intros r W'' c'' H. eapply LEAFJ_e; eassumption.
Qed.
End g.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The a0 = 0 class-full OOM arm, at the post-refill layout ly' (the final state is S' itself).                     *)
Section h.
Hypothesis Hc0 : pc_chunks (cache S' cl) = [].
Hypothesis HA0 : getr regsR 10 = w64 0.
Lemma HE1 : forall k, (k < aHAV)%nat -> ew E1 k = ew E0m k.
Proof. intros k Hk. unfold E1. unfold aHAV in Hk. rewrite ew_havoc_old by (unfold hRFk; lia). apply HEm. exact Hk. Qed.
Lemma HSN : st_ok tfibsegs E1 AGi4.MK_N0 ms3.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as Us. pose proof Hso as (O1 & O2 & O3).
assert (H4 : st_ok tfibsegs E1 (mkSS (ss_pc AGi4.SSK3) (sr_set (ss_regs AGi4.SSK3) 10%bv (SLit 0)) (ss_mem AGi4.SSK3) (ss_resv AGi4.SSK3) (ss_facts AGi4.SSK3)) ms3).
{ apply (st_ok_pin_regU E1 AGi4.SSK3 ms3 10%bv (SLit 0) HS3); [intros X; discriminate X|].
  pose proof (st_ok_reg tfibsegs E1 AGi4.SSK3 ms3 10%bv HS3) as R. unfold YP0e.U. rewrite <- R. unfold ms3. cbn [ms_regs mkst]. rewrite HA0. reflexivity. }
rewrite AGi4.MK_N0_eq. pose proof (st_ok_mem_surgery E1 _ ms3 ([AGi4.K3bst; AGi4.K3scr; AGi4.K3top] ++ AGi4.NREGS) H4) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. apply X. clear X H4.
intros (HW & HF & HP). unfold ms3 in *. cbn [ms_mem mkst] in *.
assert (BV : base_val E1 (Some 2%nat) = sp0) by (cbn [base_val]; exact E1_2).
assert (BV13 : base_val E1 (Some 13%nat) = SOv) by (cbn [base_val]; rewrite (HE1 13%nat ltac:(cbv; lia)); reflexivity).
assert (OOM1 : val_mem tfibsegs (mrestrict (w_H W') memR) (TFIB_OOM + 1) 1 1).
{ pose proof (if_mview inst ly' S' W' memR mdR n HARXp Hn0 FP Hc0) as HMVp.
  pose proof (proj1 (Forall_forall _ _) (AGif0n.mv_const B W' ly' inst memR cl HMVp) (z1 (ANum (TFIB_OOM + 1)) 1)) as C.
  rewrite (ts_const B TS ly') in C. specialize (C ltac:(unfold Tfib_const; apply in_app_iff; right; apply in_app_iff; left; apply (nth_error_In _ 60); reflexivity)).
  exact (cell_holds_val_mem B ly' (w_H W') memR (ANum (TFIB_OOM + 1)) 1 (ANum 1) C). }
split; [reflexivity|]. split.
- apply Forall_cons; [exact (Forall_inv HF)|]. apply Forall_cons.
  { pose proof (Forall_inv (Forall_inv_tail HF)) as (R1 & R2 & R3 & R4). cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in R1, R2, R3, R4.
    rewrite BV in R1, R2, R3, R4.
    unfold region_ok, AGi4.K3scr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV.
    split; [clear - Hlo K1; unfold AFSTACK, kHighMemBeg in *; unfold sp0 in *; lia|]. split; [clear - Us; unfold sp0 in *; lia|]. split; [|exact R4].
    intros o Ho. apply apresent_writable; [clear - Ho Hlo K1 Us; unfold TFIB_IMG_END, AFSTACK, kHighMemBeg in *; unfold sp0 in *; lia|]. apply PRES'. clear - Ho; unfold AFSTACK; lia. }
  apply Forall_cons; [exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HF)))|].
  unfold AGi4.NREGS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + unfold region_ok, lit1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold TFIB_OOM; lia|]. split; [unfold TFIB_OOM; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia |]. rewrite Z.add_0_l. exact OOM1.
  + unfold region_ok, AGi4.oomR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold TFIB_OOM; lia|]. split; [unfold TFIB_OOM; lia|]. split; [|apply Forall_nil]. intros o Ho. rewrite Z.add_0_l. apply rw_writable. unfold TFIB_OOM in *. lia.
  + unfold region_ok, AGi4.errR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold TFIB_ERRNO; lia|]. split; [unfold TFIB_ERRNO; lia|]. split; [|apply Forall_nil]. intros o Ho. rewrite Z.add_0_l. apply rw_writable. unfold TFIB_ERRNO in *. lia.
- unfold AGi4.K3bst, AGi4.K3scr, AGi4.K3top, AGi4.NREGS, lit1, AGi4.oomR, AGi4.errR. cbn [pairwise_disjoint all_disjoint app]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !BV, BV13. cbn [base_val].
  clear - Hlo Hhi K1 K2 Us O1 O2. unfold TFIB_OOM, TFIB_ERRNO, AFSTACK, kHighMemBeg, kHighMemEnd in *. unfold sp0, SOv in *. repeat split; lia.
Qed.
Lemma ATN : AGj9.at_STN W' ly regs0 memR mdR n tr cl 1 0 csz 0 0 0 0 0 0 AGi4.MK_N0 W' cR.
Proof.
split; [reflexivity|]. exists msR, (m_vm_materialized mdR), E1. split; [reflexivity|]. split; [exact HE1|].
split; [unfold msR; rewrite restrict_mkst_fx; exact HSN|]. split; [reflexivity | exact PRES'].
Qed.
Lemma segN_run : SRr tfibsegs W' cR (AGj9.at_RETN W' regs0 memR mdR).
Proof. exact (@AGj9.segN _ _ W' ly regs0 memR mdR n tr cl 1 0 csz 0 0 0 0 0 0 Hvd LY IMG Htp Hra Hsp Htrlen DPOSTm [] 0 W' cR ATN). Qed.
(* The OOM leaf, given its granted path. *)
Lemma LEAFN : forall W'' c'', AGj9.at_RETN W' regs0 memR mdR W'' c'' -> PL (PNull, S') W'' c''.
Proof.
intros W'' c'' HR HPATH.
pose proof Hsp' as (Hlo' & Hbot' & Hhi' & Hal').
destruct HR as (-> & regs' & mem' & mat & -> & A0 & CS' & MEQ' & PRS' & VOOM).
assert (AVR : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> a <> TFIB_OOM -> ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4) ->
  aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W') memR a).
{ intros a Ra N1 N2 N3. apply aview_same. apply MEQ'. rewrite unsigned_lit_small by exact Ra. unfold AGj9.WINN. fold sp0. lia. }
assert (RAWN : forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) -> bv_unsigned x <> TFIB_OOM ->
  ~ (TFIB_ERRNO <= bv_unsigned x < TFIB_ERRNO + 4) -> mem' x = memR x).
{ intros x N1 N2 N3. apply MEQ'. unfold AGj9.WINN. fold sp0. lia. }
destruct (if_oom inst ly' S S' W' memR mdR n tr sp0 mem' (with_vm_backing (m_vm_lazy mdR) mat mdR) HARXp HLPp Hc0 AVR RAWN PRES' PRS'
  Hlo' Hhi' VOOM (same_io_wvb mdR mat) ltac:(apply m_vmmaps_wvb) ltac:(apply m_vm_lazy_wvb) HPATH) as (HARXf & HLPf & HOOM & HUNWA).
exists ly', regs', mem', (with_vm_backing (m_vm_lazy mdR) mat mdR).
split; [exact (CFG_leaf regs' mem' _)|].
split.
{ split; [exact HARXf|]. split; [exact Hly|]. split; [exact HWLE|]. split; [exact (CS_leaf regs' CS')|].
  split; [exact (same_io_tr _ _ _ (same_io_tr _ _ _ (same_io_wvb md0 mat1) HSIO) (same_io_wvb mdR mat))|].
  split.
  { intros a Ra NO NO' NS NE.
    assert (NOO : a <> TFIB_OOM) by (intros ->; exact (NO' HOOM)).
    assert (NER : ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4)) by (intros X; apply NS; unfold ascratch; right; rewrite (ts_errno B TS); exact X).
    assert (NST : ~ (sp0 - AFSTACK <= a < sp0)) by (intros X; apply NS; unfold ascratch, spZ, AFSTACK_G; left; rewrite SP_U; unfold AFSTACK in X; exact X).
    transitivity (aview tfibsegs (w_H W') memR a); [exact (AVR a Ra NST NOO NER)|].
    transitivity (aview tfibsegs (w_H W) (ms_mem ms1) a).
    { apply (HFRA a); [exact Ra | exact NO | exact NO' | rewrite SP1; intros X; apply NST; unfold RSTACK, AFSTACK in *; lia]. }
    exact (AG1 a Ra NST). }
  split.
  { (* the raw frame *)
    intros x NO NO' NS NE.
    assert (NOO : bv_unsigned x <> TFIB_OOM) by (intros X; apply NO'; rewrite X; exact HOOM).
    assert (NER : ~ (TFIB_ERRNO <= bv_unsigned x < TFIB_ERRNO + 4)) by (intros X; apply NS; unfold ascratch; right; rewrite (ts_errno B TS); exact X).
    assert (NST : ~ (sp0 - AFSTACK <= bv_unsigned x < sp0)) by (intros X; apply NS; unfold ascratch, spZ, AFSTACK_G; left; rewrite SP_U; unfold AFSTACK in X; exact X).
    transitivity (memR x); [exact (RAWN x NST NOO NER)|].
    transitivity (ms_mem ms1 x).
    { apply HFRR; [exact NO | exact NO' | rewrite SP1; intros X; apply NST; unfold RSTACK, AFSTACK in *; lia]. }
    apply MEQW. unfold AGj8.WINM. intros [Hs|Hu]; [exact (NST Hs)|].
    apply NO'. replace (bv_unsigned x) with (ly_T ly' + t_unwinding); [exact HUNWA|].
    pose proof Hly as (_ & _ & _ & HT & _). unfold T in Hu. first [rewrite HT | rewrite <- HT]; lia. }
  intros a Ha. unfold spZ, AFSTACK_G in Ha. rewrite SP_U in Ha. unfold AFSTACK in PRS'. exact (PRS' a Ha). }
split; [cbn [fst]; rewrite A0; cbn [sptr_addr sptr_exp aeval]; reflexivity|].
split; [exact HLPf|].
split; [exact HPATH|].
intros _. exact VOOM.
Qed.
Lemma OOMJ : amreal tfibsegs (malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs 0x379c8 regsR memR mdR) PL.
Proof.
unfold malloc_join_t. rewrite bind_assoc_eq. eapply amreal_pure; [exact (pop_miss S' cl Hc0)|]. eapply amreal_pure; [reflexivity|].
unfold malloc_K_t. cbn [amreal].
replace (cfg_at tfibsegs 0x379c8 regsR memR mdR) with cR by (unfold cfg_at, cR, msR; rewrite with_vm_backing_id; reflexivity).
eapply SRr_mono; [exact segN_run|]. intros W6 c6 _ HR. exact (LEAFN W6 c6 HR).
Qed.
(* The OOM arm returns PNull, so the errno clause of alloc_leaf_e is vacuous there. *)
Lemma OOMJ_e : amreal tfibsegs (malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs 0x379c8 regsR memR mdR) PL_e.
Proof.
unfold malloc_join_t. rewrite bind_assoc_eq. eapply amreal_pure; [exact (pop_miss S' cl Hc0)|]. eapply amreal_pure; [reflexivity|].
unfold malloc_K_t. cbn [amreal].
replace (cfg_at tfibsegs 0x379c8 regsR memR mdR) with cR by (unfold cfg_at, cR, msR; rewrite with_vm_backing_id; reflexivity).
eapply SRr_mono; [exact segN_run|]. intros W6 c6 _ HR HPATH.
destruct (LEAFN W6 c6 HR HPATH) as (ly2 & regs2 & mem2 & md2 & Hc & HP & HR2 & HL & HT & HO).
exists ly2, regs2, mem2, md2. split; [exact Hc|]. split; [exact HP|].
split; [intros X; exfalso; apply X; reflexivity|]. split; [exact HR2|]. split; [exact HL|]. split; [exact HT | exact HO].
Qed.
End h.
End g0.
End f.

(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma missk_core : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0)
(alloc_leaf tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr).
Proof.
assert (CORE : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0) PL).
{
rewrite (if_shape_miss n tr S Hn0 FP Hmiss). fold cl.
eapply amreal_pure; [reflexivity|].
eapply amreal_pure; [unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage; lia); reflexivity|].
change (set_nev (st_nev S + 1) S) with S1.
eapply (YG0d.amreal_mbind tfibsegs (rtree cl) (fun _ : unit => malloc_join_t stag n tr cl) S1 W _
(fun r W1 c1 => exists ms1 mat1 Em,
  ((forall k, (k < aHAV)%nat -> ew Em k = ew E0m k) /\ st_ok tfibsegs Em AGi4.MK_CALL (restrict (w_H W) ms1) /\
   (forall x : word, ~ AGj8.WINM ly regs0 (bv_unsigned x) -> ms_mem ms1 x = mem0 x) /\
   (forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a) /\
   (forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0))) /\
  rleaf ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1) r W1 c1)).
- (* MISS1, then the refill callee *)
  eapply amreal_SRr_pre; [exact MISS1|]. intros W1 c1 _ HC.
  destruct HC as (-> & ms1 & mat1 & Em & -> & HEm & HSC & MEQW & PRESW & BUFW).
  assert (SHAPE : ms1 = mkst (ms_regs ms1) (w64 0x37e68) (ms_mem ms1) (seg_rom tfibsegs)) by (eapply ms1_shape; eassumption).
  assert (RR : amreal tfibsegs (rtree cl S1) W (cfg_at tfibsegs A_Refill (ms_regs ms1) (ms_mem ms1) (md0' mat1))
    (rleaf ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1))) by (eapply REFILL; eassumption).
  unfold cfg_at, A_Refill in RR. rewrite SHAPE at 1.
  eapply amreal_mono; [| exact RR]. intros r W2 c2 HRL. exists ms1, mat1, Em. split; [|exact HRL]. repeat (split; [assumption|]). exact BUFW.
- (* the post-refill branch on the class cache *)
  intros [] Sp W1 c1 (ms1 & mat1 & Em & (HEm & HSC & MEQW & PRESW & BUFW) & HRL).
  destruct HRL as (ly' & regsR & memR & mdR & -> & HARXp & HLPp & CIp & HBBp & Hly & HWLE & HAREGS & HSIO & HFRA & HFRR & HPRR & HA0e).
  cbn [snd] in *.
  assert (RA : raZ (ms_regs ms1) = 0x379c8) by (eapply RAZ1; eassumption). rewrite RA.
  destruct (pc_chunks (cache Sp cl)) as [|x t] eqn:El.
  + assert (HA0 : getr regsR 10 = w64 0) by (rewrite HA0e; try rewrite El; reflexivity).
    eapply OOMJ; eassumption.
  + assert (LX : exists l off, x :: t = l ++ [off]) by (exists (List.removelast (x :: t)), (List.last (x :: t) 0); apply List.app_removelast_last; discriminate).
    destruct LX as (l & off & LX). rewrite LX in El.
    assert (HA1 : getr regsR 10 = w64 1) by (rewrite HA0e; try rewrite El; destruct l; reflexivity).
    eapply JOIN; eassumption.
}
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0) PL CORE)].
intros r W' c' [HL HP]. exact (HL HP).
Qed.
(* ERRNO-KEPT twin of missk_core (ErrnoG.alloc_leaf_e): the same composition over REFILL_e / JOIN_e / OOMJ_e. *)
Lemma missk_core_e : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0)
(ErrnoG.alloc_leaf_e tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr).
Proof.
assert (CORE : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0) PL_e).
{
rewrite (if_shape_miss n tr S Hn0 FP Hmiss). fold cl.
eapply amreal_pure; [reflexivity|].
eapply amreal_pure; [unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage; lia); reflexivity|].
change (set_nev (st_nev S + 1) S) with S1.
eapply (YG0d.amreal_mbind tfibsegs (rtree cl) (fun _ : unit => malloc_join_t stag n tr cl) S1 W _
(fun r W1 c1 => exists ms1 mat1 Em,
  ((forall k, (k < aHAV)%nat -> ew Em k = ew E0m k) /\ st_ok tfibsegs Em AGi4.MK_CALL (restrict (w_H W) ms1) /\
   (forall x : word, ~ AGj8.WINM ly regs0 (bv_unsigned x) -> ms_mem ms1 x = mem0 x) /\
   (forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a) /\
   (forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0))) /\
  ErrnoG.rleaf_e B ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1) r W1 c1)).
- (* MISS1, then the refill callee *)
  eapply amreal_SRr_pre; [exact MISS1|]. intros W1 c1 _ HC.
  destruct HC as (-> & ms1 & mat1 & Em & -> & HEm & HSC & MEQW & PRESW & BUFW).
  assert (SHAPE : ms1 = mkst (ms_regs ms1) (w64 0x37e68) (ms_mem ms1) (seg_rom tfibsegs)) by (eapply ms1_shape; eassumption).
  assert (RR : amreal tfibsegs (rtree cl S1) W (cfg_at tfibsegs A_Refill (ms_regs ms1) (ms_mem ms1) (md0' mat1))
    (ErrnoG.rleaf_e B ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1))) by (eapply REFILL_e; eassumption).
  unfold cfg_at, A_Refill in RR. rewrite SHAPE at 1.
  eapply amreal_mono; [| exact RR]. intros r W2 c2 HRL. exists ms1, mat1, Em. split; [|exact HRL]. repeat (split; [assumption|]). exact BUFW.
- (* the post-refill branch on the class cache *)
  intros [] Sp W1 c1 (ms1 & mat1 & Em & (HEm & HSC & MEQW & PRESW & BUFW) & HRL).
  destruct HRL as (ly' & regsR & memR & mdR & -> & HARXp & HLPp & CIp & HBBp & Hly & HWLE & HAREGS & HSIO & HFRA & HFRR & HERRp & HPRR & HA0e).
  cbn [snd] in *.
  assert (RA : raZ (ms_regs ms1) = 0x379c8) by (eapply RAZ1; eassumption). rewrite RA.
  destruct (pc_chunks (cache Sp cl)) as [|x t] eqn:El.
  + assert (HA0 : getr regsR 10 = w64 0) by (rewrite HA0e; try rewrite El; reflexivity).
    eapply OOMJ_e; eassumption.
  + assert (LX : exists l off, x :: t = l ++ [off]) by (exists (List.removelast (x :: t)), (List.last (x :: t) 0); apply List.app_removelast_last; discriminate).
    destruct LX as (l & off & LX). rewrite LX in El.
    assert (HA1 : getr regsR 10 = w64 1) by (rewrite HA0e; try rewrite El; destruct l; reflexivity).
    eapply JOIN_e; eassumption.
}
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0) PL_e CORE)].
intros r W' c' [HL HP]. exact (HL HP).
Qed.
End c.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The theorem: from alloc_pre at Allocate's entry, the virtual register file regs0 := vregs regs n inst bp.         *)
Theorem alloc_missk : forall inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 1 inst so bp ly S W regs mem md n tr ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x331a4 regs mem md)
(alloc_leaf tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Proof.
intros inst so bp ly S W regs mem md n tr PRE Nrange Hmiss.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres0 & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hn0 & Hlive).
unfold spZ, raZ, AFSTACK_G in *. rewrite (ts_tp B TS) in Htp.
pose proof (Finst inst ly S W mem md HARX) as HIO. pose proof HIO as (HIO1 & HIO2 & HIO3).
assert (Hnn : n < nmax) by lia.
assert (FP0 : from_primary n = true) by (eapply FP; eassumption).
pose proof (if_mview inst ly S W mem md n HARX ltac:(lia) FP0 Hmiss) as HMV0.
pose proof (lo_top ly (AGif0n.mv_ly B W ly inst mem (chunk_class n) HMV0)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
set (regs0 := vregs regs n inst bp).
assert (Hso64 : 0 <= so < 2 ^ 64) by (unfold kHighMemEnd, kHighMemBeg in T4, T7; lia).
assert (Hbp64 : 0 <= bp < 2 ^ 64) by (unfold kHighMemEnd, kHighMemBeg in T4, T7; lia).
assert (Hinst64 : 0 <= inst < 2 ^ 64) by lia.
assert (HUo : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr regs r = getr regs0 r)
by (intros r H10 H11 H12; unfold regs0; symmetry; exact (vregs_other regs n inst bp r H10 H11 H12)).
assert (HU10 : getr regs 10%bv = getr regs0 11%bv) by (unfold regs0; rewrite Hr10, vregs_11; reflexivity).
assert (HU11 : getr regs 11%bv = getr regs0 10%bv) by (unfold regs0; rewrite Hr11, vregs_10; reflexivity).
assert (HU12 : getr regs 12%bv = w64 8) by exact Hr12.
assert (HU14 : getr regs 14%bv = w64 1) by exact Hr14.
assert (Hn : getr regs0 10 = w64 n) by (unfold regs0; apply vregs_10).
assert (Hi11 : getr regs0 11 = w64 inst) by (unfold regs0; apply vregs_11).
assert (R2 : getr regs0 2 = getr regs 2) by (unfold regs0; apply vregs_other; bvne).
assert (R1 : getr regs0 1 = getr regs 1) by (unfold regs0; apply vregs_other; bvne).
assert (R12 : bv_unsigned (getr regs0 12) = bp) by (unfold regs0; rewrite vregs_12; apply w64_unsigned; exact Hbp64).
assert (R13 : bv_unsigned (getr regs0 13) = so)
by (unfold regs0; rewrite (vregs_other regs n inst bp 13%bv) by bvne; rewrite Hr13; apply w64_unsigned; exact Hso64).
assert (Htp0 : getr regs0 4 = w64 TFIB_TP) by (unfold regs0; rewrite (vregs_other regs n inst bp 4%bv) by bvne; exact Htp).
assert (Hgp0 : getr regs0 3 = w64 (as_gp B)) by (unfold regs0; rewrite (vregs_other regs n inst bp 3%bv) by bvne; exact Hgp).
assert (Hcf1 : getr regs0 15 = w64 1) by (unfold regs0; rewrite (vregs_other regs n inst bp 15%bv) by bvne; exact Hr15).
assert (Hra0 : YK0s.ret_ok (getr regs0 1)) by (rewrite R1; exact Hra).
assert (Hra40 : 4096 <= bv_unsigned (getr regs0 1)) by (rewrite R1; exact Hra4096).
assert (Hsp : ly_stk_lo ly + AFSTACK <= bv_unsigned (getr regs0 2) /\ ly_bot ly < bv_unsigned (getr regs0 2) /\
bv_unsigned (getr regs0 2) <= ly_stk_hi ly /\ bv_unsigned (getr regs0 2) mod 16 = 0) by (rewrite R2; unfold AFSTACK; repeat split; assumption).
assert (Hso : bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 13) /\ bv_unsigned (getr regs0 13) + 16 <= ly_stk_hi ly /\
bv_unsigned (getr regs0 13) mod 8 = 0) by (rewrite R2, R13; repeat split; assumption).
assert (Hbp : bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 12) /\ bv_unsigned (getr regs0 12) + 8 * 30 <= ly_stk_hi ly /\
bv_unsigned (getr regs0 12) mod 8 = 0) by (rewrite R2, R12; repeat split; assumption).
assert (Hpres00 : forall a, bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W) mem a)
by (rewrite R2; unfold AFSTACK; exact Hpres0).
assert (PSO0 : val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 13)) 8 (bv_unsigned (getr regs0 12))) by (rewrite R13, R12; exact PSO).
assert (PLEN0 : val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 13) + 8) 8 (Z.of_nat (length tr))) by (rewrite R13; exact PLEN).
assert (PBUF0 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 12) + 8 * Z.of_nat i) 8 (nth i tr 0))
by (rewrite R12; exact PBUF).
change (cfg_at tfibsegs 0x331a4 regs mem md) with (cfg_at tfibsegs A_Allocate regs mem md).
eapply (missk_core inst ly S W regs0 regs mem md n tr); eassumption.
Qed.
(* ERRNO-KEPT twin of alloc_missk: errno's bytes kept on the grant branch (ErrnoG.alloc_leaf_e). *)
Theorem alloc_missk_e : forall inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 1 inst so bp ly S W regs mem md n tr ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x331a4 regs mem md)
(ErrnoG.alloc_leaf_e tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Proof.
intros inst so bp ly S W regs mem md n tr PRE Nrange Hmiss.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres0 & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hn0 & Hlive).
unfold spZ, raZ, AFSTACK_G in *. rewrite (ts_tp B TS) in Htp.
pose proof (Finst inst ly S W mem md HARX) as HIO. pose proof HIO as (HIO1 & HIO2 & HIO3).
assert (Hnn : n < nmax) by lia.
assert (FP0 : from_primary n = true) by (eapply FP; eassumption).
pose proof (if_mview inst ly S W mem md n HARX ltac:(lia) FP0 Hmiss) as HMV0.
pose proof (lo_top ly (AGif0n.mv_ly B W ly inst mem (chunk_class n) HMV0)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
set (regs0 := vregs regs n inst bp).
assert (Hso64 : 0 <= so < 2 ^ 64) by (unfold kHighMemEnd, kHighMemBeg in T4, T7; lia).
assert (Hbp64 : 0 <= bp < 2 ^ 64) by (unfold kHighMemEnd, kHighMemBeg in T4, T7; lia).
assert (Hinst64 : 0 <= inst < 2 ^ 64) by lia.
assert (HUo : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr regs r = getr regs0 r)
by (intros r H10 H11 H12; unfold regs0; symmetry; exact (vregs_other regs n inst bp r H10 H11 H12)).
assert (HU10 : getr regs 10%bv = getr regs0 11%bv) by (unfold regs0; rewrite Hr10, vregs_11; reflexivity).
assert (HU11 : getr regs 11%bv = getr regs0 10%bv) by (unfold regs0; rewrite Hr11, vregs_10; reflexivity).
assert (HU12 : getr regs 12%bv = w64 8) by exact Hr12.
assert (HU14 : getr regs 14%bv = w64 1) by exact Hr14.
assert (Hn : getr regs0 10 = w64 n) by (unfold regs0; apply vregs_10).
assert (Hi11 : getr regs0 11 = w64 inst) by (unfold regs0; apply vregs_11).
assert (R2 : getr regs0 2 = getr regs 2) by (unfold regs0; apply vregs_other; bvne).
assert (R1 : getr regs0 1 = getr regs 1) by (unfold regs0; apply vregs_other; bvne).
assert (R12 : bv_unsigned (getr regs0 12) = bp) by (unfold regs0; rewrite vregs_12; apply w64_unsigned; exact Hbp64).
assert (R13 : bv_unsigned (getr regs0 13) = so)
by (unfold regs0; rewrite (vregs_other regs n inst bp 13%bv) by bvne; rewrite Hr13; apply w64_unsigned; exact Hso64).
assert (Htp0 : getr regs0 4 = w64 TFIB_TP) by (unfold regs0; rewrite (vregs_other regs n inst bp 4%bv) by bvne; exact Htp).
assert (Hgp0 : getr regs0 3 = w64 (as_gp B)) by (unfold regs0; rewrite (vregs_other regs n inst bp 3%bv) by bvne; exact Hgp).
assert (Hcf1 : getr regs0 15 = w64 1) by (unfold regs0; rewrite (vregs_other regs n inst bp 15%bv) by bvne; exact Hr15).
assert (Hra0 : YK0s.ret_ok (getr regs0 1)) by (rewrite R1; exact Hra).
assert (Hra40 : 4096 <= bv_unsigned (getr regs0 1)) by (rewrite R1; exact Hra4096).
assert (Hsp : ly_stk_lo ly + AFSTACK <= bv_unsigned (getr regs0 2) /\ ly_bot ly < bv_unsigned (getr regs0 2) /\
bv_unsigned (getr regs0 2) <= ly_stk_hi ly /\ bv_unsigned (getr regs0 2) mod 16 = 0) by (rewrite R2; unfold AFSTACK; repeat split; assumption).
assert (Hso : bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 13) /\ bv_unsigned (getr regs0 13) + 16 <= ly_stk_hi ly /\
bv_unsigned (getr regs0 13) mod 8 = 0) by (rewrite R2, R13; repeat split; assumption).
assert (Hbp : bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 12) /\ bv_unsigned (getr regs0 12) + 8 * 30 <= ly_stk_hi ly /\
bv_unsigned (getr regs0 12) mod 8 = 0) by (rewrite R2, R12; repeat split; assumption).
assert (Hpres00 : forall a, bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W) mem a)
by (rewrite R2; unfold AFSTACK; exact Hpres0).
assert (PSO0 : val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 13)) 8 (bv_unsigned (getr regs0 12))) by (rewrite R13, R12; exact PSO).
assert (PLEN0 : val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 13) + 8) 8 (Z.of_nat (length tr))) by (rewrite R13; exact PLEN).
assert (PBUF0 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 12) + 8 * Z.of_nat i) 8 (nth i tr 0))
by (rewrite R12; exact PBUF).
change (cfg_at tfibsegs 0x331a4 regs mem md) with (cfg_at tfibsegs A_Allocate regs mem md).
eapply (missk_core_e inst ly S W regs0 regs mem md n tr); eassumption.
Qed.
End b.
End a.
