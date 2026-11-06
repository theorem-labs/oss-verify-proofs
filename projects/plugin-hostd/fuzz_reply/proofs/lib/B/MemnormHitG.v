(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormHitG.v (commit 30a1993588f, c5 + memnorm; file sha256 ae14e070a8c8) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 3 image addresses moved by code-verified function pairs (5 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/MemnormHitG.v (commit d2dafa219c1, file sha256 b89d8ee844ff) (its comment at :19-20 re-flowed first so that the range [0x9f000, 0x5fb000) sits on one line) (comment numerals that the A text still had at cgif_file's values are stated at image B here) onto plugin-hostd/fuzz_reply's asan-ubsan image (unstripped fuzz_reply.asan-ubsan, sha256 3389287e1d61; pin 10ffb5f9202a) by alreloc ced0368250cb6538 (A -> B, direct map 541d2a13b9d2): 8 numerals moved; module paths lib.A -> lib.B and the image twins A<r> -> Y<r>. *)
(* PILOT (task MEMNORM): the hit-g arm of AGikE.v with memnorm kept.  [ARM_HITG_em] is AGikE.ARM_HITG_e with
   MemnormT.alloc_leaf_em (ErrnoG.alloc_leaf_e plus `memnorm mem -> memnorm mem'`) in place of ErrnoG.alloc_leaf_e.
   rule 24: no function proved (kind: arm twin, frame corollary).

   WHY THE ARM AND NOT THE TOP: the top post's raw frame (AllocG.v:99-100) leaves the owned set AOX free, and at cgif
   aowned meets the read-only segment [0x10000, 0x30000) (YF0m.v:279-285 Tfib_owned_static holds (0x102e8, 8) ...
   (0x20e62, 0x1e)), so the top post admits a ROM byte copied into the overlay.  The arm's own raw frame is tighter:
   at_RETw's MEQF (AGif0n.v:90-92) keeps every byte outside ImgBaseAG.WIN, ag_dzone, the new block and its shadow,
   and none of those zones holds a read-only byte or reaches TASK_SIZE ([memnorm_at_RETw]):
   - high zones (the stack window, the class span Kv / Uv, the block, PBW and the shadow) lie at or above kImgEnd,
     where tfibsegs has no segment (YF0x.v:257 tfib_find_segment_none_high, TFIB_IMG_END = 0x5fc000 <= kImgEnd), and
     below TASK_SIZE (layout_ok's lo_top / lo_space_in / lo_high, YG0f.v:312-326);
   - the thread object's cells (WINT) and the depot's node and store blocks are owned extents, off the layout's image
     window (lo_disj) and in_app (lo_app), so off every segment ([tfib_seg_range]: a segment byte lies in
     [TFIB_IMG_LO, TFIB_IMG_END), inside the window by img_cover, YF0x.v:53);
   - the depot zone's static part [0x178508, 0x5c8c90) (AGis.v:230) lies in the read-write segment
     [0x9f000, 0x5fc000) ([tfib_seg_rw]).
   The proof of ARM_HITG_em is AGikE.v:93-286 (the block marked as a copy) plus the memnorm conjunct from the same
   MEQF; no runner is swapped and no walk is touched.  AGikE.v is unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG07.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YE3d YFhy AGhy.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGis AGhz YFi3 AllocG AGif0reply AGiz AGj0 AGj2.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif0n AGif2reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG ErrnoApart ErrnoApartreply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGik AGikE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require MemnormT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* tfibsegs: where a segment byte can be, and which segments are writable.                                         *)

(* a segment byte lies in the image [TFIB_IMG_LO, TFIB_IMG_END) (YF0x.v:249, :257) *)
Lemma tfib_seg_range : forall x seg, find_segment tfibsegs x 1 = Some seg -> TFIB_IMG_LO <= x < TFIB_IMG_END.
Proof.
intros x seg F. destruct (Z_lt_le_dec x TFIB_IMG_LO) as [L|L].
- rewrite (tfib_find_segment_none_low x L) in F. discriminate F.
- destruct (Z_lt_le_dec x TFIB_IMG_END) as [H|H]; [lia|].
  rewrite (tfib_find_segment_none_high x H) in F. discriminate F.
Qed.

(* every segment at or above 0x9d000 is writable (tfibsegs: [0x9d000, 0x9f000) and [0x9f000, 0x5fc000) are RW) *)
Lemma tfib_seg_rw : forall x seg, 0x9d000 <= x -> find_segment tfibsegs x 1 = Some seg -> seg_writable seg = true.
Proof.
intros x seg Hx F. destruct (find_segment_some_spec tfibsegs x 1 seg F) as (Hin & Hb & Ht).
assert (E : tfibsegs = [AsanUbsan_segment_000; AsanUbsan_segment_001;
AsanUbsan_segment_002; AsanUbsan_segment_003]) by reflexivity.
rewrite E in Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Ht |- *; try reflexivity; lia.
Qed.

(* off the layout's image window and below TASK_SIZE: mn_safe *)
Lemma mn_safe_off : forall ly (x : word), img_cover ly ->
  ~ (fst (ly_img ly) <= bv_unsigned x < fst (ly_img ly) + snd (ly_img ly)) -> bv_unsigned x < TASK_SIZE ->
  MemnormT.mn_safe tfibsegs x.
Proof.
intros ly x [C1 C2] Hoff Hlt. split; [|exact Hlt].
unfold YAkMemnorm.ro_addr. destruct (find_segment tfibsegs (bv_unsigned x) 1) as [seg|] eqn:F; [|reflexivity].
exfalso. pose proof (tfib_seg_range _ _ F) as R. apply Hoff. unfold TFIB_IMG_LO, TFIB_IMG_END in *. lia.
Qed.

(* at or above kImgEnd and below TASK_SIZE: mn_safe *)
Lemma mn_safe_high : forall (x : word), kImgEnd <= bv_unsigned x < TASK_SIZE -> MemnormT.mn_safe tfibsegs x.
Proof.
intros x [H1 H2]. split; [|exact H2]. unfold YAkMemnorm.ro_addr.
rewrite (tfib_find_segment_none_high (bv_unsigned x)) by (unfold TFIB_IMG_END, kImgEnd in *; lia). reflexivity.
Qed.

(* an owned extent's byte (off the image window by lo_disj, in_app by lo_app): mn_safe *)
Lemma mn_safe_owned : forall ly e (x : word), layout_ok ly -> img_cover ly -> In e (owned_extents ly) ->
  fst e <= bv_unsigned x < fst e + snd e -> MemnormT.mn_safe tfibsegs x.
Proof.
intros ly e x LY IMG He Hx.
pose proof (pairwise_In zdisjoint (static_extents ly) e (ly_img ly) (owned_extents ly) [_; _] eq_refl (lo_disj _ LY) He
  (or_intror (or_introl eq_refl))) as D.
pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) _ He) as A. cbv beta in A.
pose proof (ASAN_CEIL_range) as [CR _].
apply (mn_safe_off ly x IMG).
- unfold zdisjoint in D. lia.
- unfold in_app, kLowShadowBeg, kHighMemBeg in A. unfold TASK_SIZE. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* memnorm is kept by a memory that equals [mem] outside at_RETw's raw frame zones (AGif0n.v:90-92, the clause in
   the form at_RETw states it, as AGikE.errno_kept_at_RETw reads it). *)
Lemma memnorm_at_RETw : forall B ly (regs0 : bvmap 5 word) n cl v kz odd (mem mem' : word -> option byte),
TfibSyms B -> layout_ok ly -> ImgBase.im_img_cover ly ->
ly_stk_lo ly + ImgBaseAG.AFSTACK <= bv_unsigned (getr regs0 2) -> bv_unsigned (getr regs0 2) <= ly_stk_hi ly ->
0 <= cl < kNumClasses -> 0 <= v -> 16 * v + 2 ^ 16 <= 2 ^ 32 -> 0 <= n <= 64512 -> 1 <= kz <= 6 ->
(forall x : word, ~ ImgBaseAG.WIN ly regs0 n cl v kz odd (bv_unsigned x) -> ~ ImgBaseAG.ag_dzone ly (bv_unsigned x) ->
 ~ (ImgBaseAG.Kv ly cl v + ImgBaseAG.RZ kz <= bv_unsigned x < ImgBaseAG.Kv ly cl v + ImgBaseAG.RZ kz + n) ->
 ~ (ImgBaseAG.SUv ly cl v kz <= bv_unsigned x < ImgBaseAG.SUv ly cl v kz + ImgBaseAG.N8D n / 8) -> mem' x = mem x) ->
MemnormT.memnorm_keep tfibsegs mem mem'.
Proof.
intros B ly regs0 n cl v kz odd mem mem' TS LY IMG HSP HSH Hcl Hv Hv2 Hn Hkz MEQ.
change (img_cover ly) in IMG.
pose proof (ErrnoApart.ly_space_high ly LY) as SH. pose proof (lo_space_in ly LY) as [S1 S2]. pose proof (lo_high ly LY) as [P1 P2].
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). pose proof (ASAN_CEIL_range) as [CR _].
assert (C0 : 0 <= cl * 2 ^ 32 <= 31 * 2 ^ 32) by (unfold kNumClasses in Hcl; nia).
assert (R0 : 16 <= ImgBaseAG.RZ kz <= 1024).
{ unfold ImgBaseAG.RZ, ImgBaseAG.rz_of.
  assert (2 ^ 1 <= 2 ^ kz <= 2 ^ 6) by (split; apply Z.pow_le_mono_r; lia). change (2 ^ 1) with 2 in *. change (2 ^ 6) with 64 in *. lia. }
assert (KU : kImgEnd <= ImgBaseAG.Kv ly cl v /\ ImgBaseAG.Kv ly cl v + ImgBaseAG.RZ kz + 65536 <= ASAN_CEIL).
{ unfold ImgBaseAG.Kv. unfold in_high, kSpaceSize, kPrimResvSize, kImgEnd in *. lia. }
assert (UE : ImgBaseAG.Uv ly cl v kz = ImgBaseAG.Kv ly cl v + ImgBaseAG.RZ kz) by reflexivity.
assert (UU0 : 0 <= ImgBaseAG.Uv ly cl v kz <= ASAN_CEIL) by (rewrite UE; unfold kImgEnd in KU; lia).
assert (UU : 0 <= ImgBaseAG.Uv ly cl v kz / 8 <= ASAN_CEIL / 8)
  by (split; [apply Z.div_pos | apply Z.div_le_mono]; lia).
assert (N0 : 0 <= ImgBaseAG.N8D n <= 64512).
{ unfold ImgBaseAG.N8D. pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le n 8 ltac:(lia)). lia. }
assert (SHB : ImgBaseAG.SHBv = 0x7fff8000) by reflexivity.
apply (MemnormT.memnorm_frame4 tfibsegs (ImgBaseAG.WIN ly regs0 n cl v kz odd) (ImgBaseAG.ag_dzone ly)
  (fun a => ImgBaseAG.Kv ly cl v + ImgBaseAG.RZ kz <= a < ImgBaseAG.Kv ly cl v + ImgBaseAG.RZ kz + n)
  (fun a => ImgBaseAG.SUv ly cl v kz <= a < ImgBaseAG.SUv ly cl v kz + ImgBaseAG.N8D n / 8) mem mem').
- intros x Hw. unfold ImgBaseAG.WIN in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
  + apply mn_safe_high. unfold ImgBaseAG.AFSTACK, kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
  + apply (mn_safe_owned ly (ly_T ly, kThreadObjSize) x LY IMG ltac:(unfold owned_extents; right; right; left; reflexivity)).
    cbn [fst snd]. unfold ImgBaseAG.WINT, ImgBaseAG.Pv, ImgBaseAG.SSLOTv in Hw.
    unfold kThreadObjSize, t_cache, t_stats, t_unwinding, kNumClasses in *. lia.
  + apply mn_safe_high. rewrite UE in Hw. unfold TASK_SIZE. lia.
  + destruct Hw as [_ Hw]. apply mn_safe_high. unfold ImgBaseAG.PBv in Hw. rewrite SHB in Hw.
    assert (0 <= (ImgBaseAG.Kv ly cl v + ImgBaseAG.RZ kz + ImgBaseAG.N8D n) / 8 <= ASAN_CEIL / 8).
    { split; [apply Z.div_pos; lia|]. apply Z.div_le_mono; lia. }
    unfold kImgEnd, TASK_SIZE in *. lia.
- intros x Hd. change (AGis.DZONE ly (bv_unsigned x)) in Hd. destruct Hd as [Hd|[Hd|Hd]].
  + split; [|unfold TASK_SIZE; lia]. unfold YAkMemnorm.ro_addr.
    destruct (find_segment tfibsegs (bv_unsigned x) 1) as [seg|] eqn:F; [|reflexivity].
    rewrite (tfib_seg_rw (bv_unsigned x) seg ltac:(lia) F). reflexivity.
  + apply (mn_safe_owned ly (ly_NB ly, kNodesBlockSize) x LY IMG
      ltac:(unfold owned_extents; right; right; right; right; left; reflexivity)). exact Hd.
  + apply (mn_safe_owned ly (ly_SB ly, kStoreBlockSize) x LY IMG
      ltac:(unfold owned_extents; right; right; right; right; right; left; reflexivity)). exact Hd.
- intros x Hb. apply mn_safe_high. unfold TASK_SIZE. lia.
- intros x Hs. apply mn_safe_high. unfold ImgBaseAG.SUv in Hs. rewrite SHB in Hs.
  assert (0 <= ImgBaseAG.N8D n / 8 <= 8064) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  unfold kImgEnd, TASK_SIZE in *. lia.
- exact MEQ.
Qed.

(* copy of AGikE.v:64-86 (the section header), unchanged *)
Section b.
Variable B : asyms.
(* The trace premise (C5): a predicate on the trace and the state (cgif: In tr (as_universe B)). *)
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variables (nmax lmax : Z).
Variable lpost : astate -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variables (mtag stag : Z).
Hypothesis IF : AIface B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
Hypothesis TS : TfibSyms B.
(* copy of AGik.v:50 *)
Local Ltac bvne := first [cbn; lia | vm_compute; congruence | intros X; vm_compute in X; discriminate X].
(* can_fill of the caller's call site: 1 (malloc, realloc) or 0 (calloc). *)
Variable cf : Z.
Hypothesis Hcf01 : cf = 0 \/ cf = 1.
(* The image facts errno_kept_at_RETw reads (cgif_file: ErrnoApartcgif.v). *)
Hypothesis Hei : ErrnoApart.errno_in_img (IM := AImg_reply).
Hypothesis Hesh : ErrnoApart.errno_apart_shadow_ag (AG := AGImg_reply).
Hypothesis Hedz : ErrnoApart.errno_apart_dzone_ag (AG := AGImg_reply).
Theorem ARM_HITG_em : forall inst so bp ly S W regs mem md n tr l off,
alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 cf inst so bp ly S W regs mem md n tr ->
49 <= n <= 64512 -> st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x31c30 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Proof.
(* copy of AGikE.v:93-248, unchanged *)
(* copy of AGik.v:87-272, + errno *)
intros inst so bp ly S W regs mem md n tr l off PRE Nrange0 Hinited Hcache.
destruct IF as [Finst Fview Fshape Fdepot Fdaok Fpost Fowned Funinit].
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres0 & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hn0 & Hlive).
unfold spZ, raZ, AFSTACK_G in *. rewrite (ts_tp B TS) in Htp.
pose proof (Finst _ _ _ _ _ _ HARX) as HIO. pose proof HIO as (HIO1 & HIO2 & HIO3).
(* The class and the redzone log. *)
set (kz := rz_log n).
assert (Hkz : 1 <= kz <= 6 /\ rz_lo kz <= n <= rz_hi kz).
{ subst kz. unfold rz_log. clear - Nrange0.
destruct (Z.leb_spec n 48); [lia|]. destruct (Z.leb_spec n 96); [cbn; lia|]. destruct (Z.leb_spec n 448); [cbn; lia|].
destruct (Z.leb_spec n 3968); [cbn; lia|]. destruct (Z.leb_spec n 16128); [cbn; lia|]. destruct (Z.leb_spec n 32256); [cbn; lia|].
destruct (Z.leb_spec n 64512); [cbn; lia|]. lia. }
destruct Hkz as [Hkz Nrange].
pose proof (AGis.casek_sizes n kz Hkz Nrange) as (L & RS & R8 & NP & FP & NS & RQ).
destruct (Fview inst ly S W mem md n l off HARX HRP ltac:(lia) FP Hinited Hcache) as (Hoff32 & HV).
apply hview_reply in HV.
set (cl := chunk_class n) in *. set (cnt := Z.of_nat (length (l ++ [off]))) in *. set (v := off / 16) in *. set (csz := class_size cl).
assert (Hcl_class : cl = chunk_class n) by reflexivity.
assert (Hcnt_def : cnt = Z.of_nat (length (l ++ [off]))) by reflexivity.
assert (Hcsz_def : csz = class_size cl) by reflexivity.
assert (Hoff_def : off = 16 * v).
{ subst v. pose proof Hoff32 as H32. apply Z.mod_divide in H32 as [q Hq]; [|lia]. rewrite Hq.
  replace (q * 32) with ((2 * q) * 16) by lia. rewrite Z.div_mul by lia. lia. }
pose proof HV as [HLY HIMG HTSD Hcnt Hvv Hconst Hinstc Hcachec Hunw Hjunk Hchunk Hshadow].
destruct Hvv as (Hv0 & Hv2 & Hvcl).
assert (Hcl_def : cl = class_id (R8v n + AGis.RZ kz)) by (subst cl; unfold chunk_class; rewrite NS, <- RS; reflexivity).
(* The view's consequences (AGiz). *)
assert (Hcl : 1 <= cl <= 31) by (assert (1 <= cl <= 30) by (eapply vw_cl_range; eassumption); lia).
assert (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32) by (eapply vw_Hv; eassumption).
assert (HKpres : forall a, Kv ly cl v <= a < Kv ly cl v + AGis.RZ kz + R8v n -> apresent (w_H W) mem a) by (eapply vw_KPRES; eassumption).
assert (HSKpres : forall a, SKv ly cl v <= a < SKv ly cl v + (AGis.RZ kz + R8v n) / 8 -> apresent (w_H W) mem a) by (eapply vw_SKPRES; eassumption).
assert (HPB250 : n mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W) mem) (PBv ly n cl v kz) 1 250) by (eapply vw_PB250; eassumption).
assert (JV : exists j0 j1 j2 j3 j4 jb,
val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + 2784) 8 j0 /\ val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + 2800) 8 j1 /\
val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + 2808) 8 j2 /\ val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + 2816) 8 j3 /\
val_mem tfibsegs (mrestrict (w_H W) mem) (SSLOTv ly cl) 8 j4 /\ 0 <= jb <= 255 /\
val_mem tfibsegs (mrestrict (w_H W) mem) (Kv ly cl v + AGis.RZ kz - 15) 1 jb) by (eapply vw_junk_values; eassumption).
destruct JV as (j0 & j1 & j2 & j3 & j4 & jb & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hjb & Hjb_def).
(* The walk's virtual register file. *)
set (regs0 := vregs regs n inst bp).
pose proof (lo_top ly HLY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
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
assert (Hcf : getr regs0 15 = w64 0 \/ getr regs0 15 = w64 1)
by (unfold regs0; rewrite (vregs_other regs n inst bp 15%bv) by bvne; rewrite Hr15; destruct Hcf01 as [E|E]; rewrite E; [left | right]; reflexivity).
assert (Hra0 : YK0s.ret_ok (getr regs0 1)) by (rewrite R1; exact Hra).
assert (Hra40 : 4096 <= bv_unsigned (getr regs0 1)) by (rewrite R1; exact Hra4096).
assert (Hsp : ly_stk_lo ly + AFSTACK <= bv_unsigned (getr regs0 2) /\ ly_bot ly < bv_unsigned (getr regs0 2) /\
bv_unsigned (getr regs0 2) <= ly_stk_hi ly /\ bv_unsigned (getr regs0 2) mod 16 = 0) by (rewrite R2; unfold AFSTACK; repeat split; assumption).
assert (Hso : bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 13) /\ bv_unsigned (getr regs0 13) + 16 <= ly_stk_hi ly /\
bv_unsigned (getr regs0 13) mod 8 = 0) by (rewrite R2, R13; repeat split; assumption).
assert (Hbp : bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 12) /\ bv_unsigned (getr regs0 12) + 8 * 30 <= ly_stk_hi ly /\
bv_unsigned (getr regs0 12) mod 8 = 0) by (rewrite R2, R12; repeat split; assumption).
assert (Hinst : TFIB_IMG_LO <= bv_unsigned (getr regs0 11) /\ bv_unsigned (getr regs0 11) + 0xe60 <= 0x178508)
by (rewrite Hi11, w64_unsigned by exact Hinst64; exact (inst_ok_img inst HIO)).
assert (Hpres00 : forall a, bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W) mem a)
by (rewrite R2; unfold AFSTACK; exact Hpres0).
assert (PSO0 : val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 13)) 8 (bv_unsigned (getr regs0 12))) by (rewrite R13, R12; exact PSO).
assert (PLEN0 : val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 13) + 8) 8 (Z.of_nat (length tr))) by (rewrite R13; exact PLEN).
assert (PBUF0 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 12) + 8 * Z.of_nat i) 8 (nth i tr 0))
by (rewrite R12; exact PBUF).
(* The seed at Allocate's entry (AGj0). *)
assert (SEED : st_ok tfibsegs (AGis.E0 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz) SS_1
(restrict (w_H W) (mkst regs (w64 A_Allocate) mem (seg_rom tfibsegs)))).
{ exact (@SEED_ok _ _ W ly regs0 mem n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 HLY HIMG Hn Htp0 Hsp Htrlen Hso Hbp Hcf
  (fun (_ : Z) (_ : word -> option byte) => True) Hkz Nrange B inst TS HV Hi11 HIO PSO0 PLEN0 Hpres00 Hcl_class Hcsz_def
  Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def regs HUo HU10 HU11 HU12 HU14). }
(* The model state at the pop: the tick. *)
set (S1 := set_nev (st_nev S + 1) S).
assert (Hcache1 : pc_chunks (cache S1 cl) = l ++ [off]) by exact Hcache.
(* The depot callee, at this allocator. *)
assert (HDEP : forall (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) (buf : Z),
(forall x : word, DZONE ly (bv_unsigned x) \/ CZONE ly (bv_unsigned x) -> mem1 x = mem x) ->
getr regs1 10 = Z_to_bv 64 buf -> getr regs1 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs1 3 = Z_to_bv 64 (as_gp B) -> getr regs1 4 = Z_to_bv 64 TFIB_TP -> YK0s.ret_ok (getr regs1 1) ->
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem1) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
buf + 8 * 30 <= bv_unsigned (getr regs1 2) - DEP_STK \/ bv_unsigned (getr regs1 2) <= buf ->
bv_unsigned (getr regs1 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs1 2) - DEP_STK ->
bv_unsigned (getr regs1 2) <= ly_stk_hi ly ->
(forall a, bv_unsigned (getr regs1 2) - DEP_STK <= a < bv_unsigned (getr regs1 2) -> apresent (w_H W) mem1 a) ->
SRr tfibsegs W (mkCfg (mkst regs1 (Z_to_bv 64 A_StackDepotPut) mem1 (seg_rom tfibsegs)) md1)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs1 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md1) mat md1) /\
regs_preserved regs1 regs' /\
(forall x : word, ~ (bv_unsigned (getr regs1 2) - DEP_STK <= bv_unsigned x < bv_unsigned (getr regs1 2)) ->
~ DZONE ly (bv_unsigned x) -> mem' x = mem1 x) /\
(forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem' a) /\
dpost inst ly S W tr z mem')).
{ intros regs1 mem1 md1 buf. exact (Fdepot inst ly S W mem md tr regs1 mem1 md1 buf HARX Htr). }
assert (HDAOK : forall z m, dpost inst ly S W tr z m -> aok S1 (KDepot tr) z) by (intros z m H; exact (Fdaok _ _ _ _ _ _ _ H)).
assert (Hmat0 : m_vm_materialized md = m_vm_materialized md) by reflexivity.
(* The walk (AGj2). *)
assert (MAIN : amreal tfibsegs (malloc_join_t stag n tr cl S1) W (cfg_at tfibsegs A_Allocate regs mem md)
(fun r W' c' => exists odd z, r = (ck_user (new_chunk cl off n), st_final S1 cl l off n tr z) /\
(odd = true <-> n mod 8 <> 0) /\
at_RETw W ly regs0 mem md n cl cnt v jb kz (fun z m => dpost inst ly S W tr z m) odd z W' c')).
{ eapply hitg_inner; try first [exact SEED | exact HDEP | exact HDAOK | exact Hmat0 | eassumption].
  Unshelve. all: try first [exact (m_vm_materialized md) | exact B]. }
(* The model's steps before the pop (shape (b)). *)
assert (MAIN' : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x31c30 regs mem md)
(fun r W' c' => exists odd z, r = (ck_user (new_chunk cl off n), st_final S1 cl l off n tr z) /\
(odd = true <-> n mod 8 <> 0) /\
at_RETw W ly regs0 mem md n cl cnt v jb kz (fun z m => dpost inst ly S W tr z m) odd z W' c')).
{ rewrite (Fshape n tr S l off ltac:(lia) FP Hinited Hcache).
  eapply amreal_pure; [reflexivity|].
  eapply amreal_pure; [unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage; lia); reflexivity|].
  exact MAIN. }
(* The leaf. *)
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs _ _ _ _ MAIN')].
intros r W' c' [(odd & z & -> & Hodd & HR) HPATH].
pose proof HR as HR0.
destruct HR as (-> & regs' & mem' & mat & -> & R10 & RCS & (memD & DP & PRD & EQD) & MEQF & PRS & PRW & VALS).
assert (WF : wframe W ly regs0 mem tr) by (split; [exact Hsp|]; split; [exact Htrlen|]; split; [exact Hso|]; split; [exact Hbp | exact Hpres00]).
destruct (Fpost inst ly S W mem md n tr l off regs0 jb odd z regs' mem' mat HARX HRP ltac:(lia) Hlive Htr Nrange0 Hinited Hcache WF Hjb Hjb_def
  HR0 Hodd HPATH)
as [HARX' HLP].
assert (KU : sptr_addr B ly (ck_user (new_chunk cl off n)) = Kv ly cl v + AGis.RZ kz).
{ unfold new_chunk, ck_user, ck_rz. cbn [ck_beg ck_req padd]. rewrite RS.
  rewrite (AGis.Kv_is_sptr ly cl v Hcl B off Hoff_def). unfold sptr_addr. cbn. lia. }
(* The raw frame (at_RETw's raw MEQF); the aview frame follows from it. *)
assert (RAWF : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ ascratch B AFSTACK_G regs (bv_unsigned x) ->
  ~ (Kv ly cl v + AGis.RZ kz <= bv_unsigned x < Kv ly cl v + AGis.RZ kz + n) -> mem' x = mem x).
{ intros x NO NSc NE. pose proof (u64_range x) as Ra.
  assert (OWN : hit_writes ly n cl v kz odd (bv_unsigned x) -> False).
  { intros HW. apply NO. exact (Fowned inst ly S W mem md n l off odd (bv_unsigned x) HARX HRP Nrange0 Hinited Hcache Ra (proj1 Hodd) HW). }
  apply MEQF.
  - intros Hw. unfold ImgBaseAG.WIN in Hw. destruct Hw as [Hs|Hw].
    + apply NSc. unfold ascratch. left. unfold spZ, AFSTACK_G. rewrite <- R2. unfold ImgBaseAG.AFSTACK in Hs. exact Hs.
    + apply OWN. unfold hit_writes. destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw | right; left; exact Hw | right; right; left; exact Hw].
  - intros Hd. apply OWN. unfold hit_writes. right; right; right; left; exact Hd.
  - exact NE.
  - intros Hs. apply OWN. unfold hit_writes. right; right; right; right; exact Hs. }
(* errno: the same raw MEQF keeps it (errno_kept_at_RETw). *)
assert (ERRNO : ErrnoG.errno_kept B mem mem').
{ refine (errno_kept_at_RETw Hei Hesh Hedz B ly regs0 n cl v kz odd mem mem' TS HLY HIMG (proj1 Hsp) _ (proj1 Hv) _ MEQF).
  - clear - Hcl. unfold kNumClasses. lia.
  - clear - Nrange0. lia. }
(* memnorm: the same raw MEQF keeps it (memnorm_at_RETw). *)
assert (MNK : MemnormT.memnorm_keep tfibsegs mem mem').
{ refine (memnorm_at_RETw B ly regs0 n cl v kz odd mem mem' TS HLY HIMG (proj1 Hsp) (proj1 (proj2 (proj2 Hsp))) _
    (proj1 Hv) (proj2 Hv) _ Hkz MEQF).
  - clear - Hcl. unfold kNumClasses. lia.
  - clear - Nrange0. lia. }
(* copy of AGikE.v:249-281, unchanged *)
assert (NEu : forall a, ~ (fst (ck_user (new_chunk cl off n), st_final S1 cl l off n tr z) <> PNull /\
  sptr_addr B ly (fst (ck_user (new_chunk cl off n), st_final S1 cl l off n tr z)) <= a <
  sptr_addr B ly (fst (ck_user (new_chunk cl off n), st_final S1 cl l off n tr z)) + req_size n) ->
  ~ (Kv ly cl v + AGis.RZ kz <= a < Kv ly cl v + AGis.RZ kz + n)).
{ intros a NE Hu. apply NE. cbn [fst]. split; [unfold new_chunk, ck_user, padd; cbn; discriminate|]. rewrite KU, RQ. exact Hu. }
exists ly, regs', mem', (with_vm_backing (m_vm_lazy md) mat md).
split. { unfold cfg_at, raZ, w64. rewrite R1, Z_to_bv_bv_unsigned. reflexivity. }
split.
{ split; [exact HARX'|]. split; [apply layout_le_refl|]. split; [apply wle_refl|].
split.
{ intros r Hr. assert (HrZ : bv_unsigned (Z_to_bv 5 r) = r).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32. unfold acallee_saved in Hr. apply Z.mod_small. lia. }
  rewrite <- (vregs_other regs n inst bp (Z_to_bv 5 r)) by (rewrite HrZ; unfold acallee_saved in Hr; lia). fold regs0.
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
  cbn [In]; tauto. }
split. { unfold same_io. destruct md; cbn; repeat split; reflexivity. }
split.
{ intros a Ra NO NO' NSc NE.
  apply aview_same. pose proof (RAWF (Z_to_bv 64 a)) as RW. rewrite unsigned_lit_small in RW by exact Ra.
  exact (RW NO NSc (NEu a NE)). }
split.
{ intros x NO NO' NSc NE. exact (RAWF x NO NSc (NEu _ NE)). }
intros a Ha. unfold spZ, AFSTACK_G in Ha. rewrite <- R2 in Ha. unfold ImgBaseAG.AFSTACK in PRS. exact (PRS a Ha). }
split. { intros _. exact ERRNO. }
split; [exact MNK|].
(* copy of AGikE.v:282-288, unchanged *)
split. { cbn [fst]. rewrite R10, KU. reflexivity. }
split; [exact HLP|].
split; [exact HPATH|].
cbn [fst]. unfold new_chunk, ck_user, padd. cbn. intros X; discriminate X.
Qed.
End b.
End a.
