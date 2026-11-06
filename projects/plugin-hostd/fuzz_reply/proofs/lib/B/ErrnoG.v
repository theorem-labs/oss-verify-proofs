(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/ErrnoG.v (commit 30a1993588f, c5 + memnorm; file sha256 a021f133aa77) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/ErrnoG.v (commit d2dafa219c1, file sha256 b723a96c354e) onto plugin-hostd/fuzz_reply's asan-ubsan image (unstripped fuzz_reply.asan-ubsan, sha256 3389287e1d61; pin 10ffb5f9202a) by alreloc ced0368250cb6538 (A -> B, direct map 541d2a13b9d2): 0 numerals moved; module paths lib.A -> lib.B and the image twins A<r> -> Y<r>. *)
(* Errno-kept twins of the frame-generic Allocate / Deallocate contracts, and the callee add-ons their proofs read.

   Every frame clause of AllocG.alloc_post and DeallocG.dealloc_post / dealloc_post_raw excludes [ascratch B stk regs],
   and [ascratch] holds the stack window AND errno's 4 bytes (YG0d.v:219-220), so a caller of Allocate or Deallocate
   cannot conclude that errno is unchanged.  Measured on the cgif_file walk files: errno enters Allocate's frames only
   on the failure arms (the OOM tails AGj9 / AGk1 / AGim / AGin, the secondary refusal AGif5 / AGjj / AGjn, the refill
   refusal AGif1m), where the frame leaves errno to the caller's SetErrnoOnNull; every errno mention on the Deallocate
   side proves that a stack byte is not errno.  So Allocate's grant paths and every Deallocate path keep errno.

   This file states that, additively (AllocG, DeallocG and the interface records are unchanged):
   - [errno_kept B mem mem'] (raw bytes) and [errno_kept_v segs B W W' mem mem'] (the view, in the aview form of
     DeallocG.dealloc_post's frame): errno's 4 bytes after are those before;
   - [alloc_leaf_e] = AllocG.alloc_leaf plus errno_kept on the grant branch (fst r <> PNull), and its contracts
     [aalloc_prim_realizes_e] / [aalloc_realizes_e];
   - [dealloc_leaf_e] = DeallocG.dealloc_leaf plus errno_kept_v on every branch, and [adealloc_realizes_e] (the view
     form, the one the closed cgif Deallocate top proves); [dealloc_leaf_raw_e] = DeallocG.dealloc_leaf_raw plus
     errno_kept on every branch, and [adealloc_realizes_raw_e];
   - the bridges back to the released forms (drop the conjunct; the contracts by amreal_mono);
   - the callee add-ons: one named Prop per callee and form ([*_t]), so that an arm takes only the contract it uses,
     and records beside the interface records, over their parameters, that bundle them for an instance:
     [DIfaceE] (view forms, beside DGif0.DIface), [DIfaceRE] (raw forms, beside DIfaceR.DIfaceR), [AIfaceE]
     (AGif0n.AIface), [AIfaceME] (AGif0n.AIfaceM).  Each restates a field's contract with errno kept between the
     memory at the call and the memory at the return; a callee whose post frames both the view and the raw memory gets
     both forms.
   No arm is proved here.  The consumers (h-decbox-a5, h-rw-dec-3, h-aag-7) thread the conjunct through the arms in
   step 2.

   Moved to ErrnoGS.v, names and statements unchanged: the secondary path's add-ons aes_depot_t, aes_post_grant_v_t,
   aes_post_grant_t and the record AIfaceSE (beside AGif4.AIfaceS).  They name AGif4's sfin / skern / CZS, and AGif4's
   Require closure reaches YA08 / YA09 / YA0e, whose non-local Zify flag setting escapes Require (ErrnoGS.v's header
   gives the consumer's fix).  This file's Require closure reaches none of AGif4, YA08, YA09, YA0e.

   The file is image-free: the interface part takes the image classes as AGif0n / DGif0 do
   ([Context {IM : AImg} {AG : AGImg}], [{IM : AImg} {DI : DImg}]).  ImgBaseAG and ImgBaseAGS both define DEP_STK /
   AFSTACK, so the restated fields name them qualified, as the field they accompany reads them. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AllocG DeallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif0n DGif0 DIfaceR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* errno's 4 bytes (at [as_errno B], the address ascratch excludes) are the same in [mem'] as in [mem]: on the raw
   memory (the form of alloc_post's and dealloc_post_raw's raw frames) and on the view (the form of dealloc_post's
   frame). *)
Definition errno_kept (B : asyms) (mem mem' : word -> option byte) : Prop :=
forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i)).
Definition errno_kept_v (segs : list Segment) (B : asyms) (W W' : world segs) (mem mem' : word -> option byte) : Prop :=
forall a, as_errno B <= a < as_errno B + 4 -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Allocate: AllocG's section variables, in AllocG's order, so that the twins take AllocG's arguments.              *)
Section al.
Variable segs : list Segment.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable nmax : Z.
Variable lmax : Z.
Variable lpost : astate -> Prop.
Variable pcA : Z.
Variable oomb : Z.
Variable al : Z.
Variable atp : Z.
Variable cf : Z.

(* AllocG.alloc_leaf, with errno kept on the grant branch (next to alloc_post's memory facts). *)
Definition alloc_leaf_e (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z) (tr : list Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
alloc_post segs B ARX AOX inst ly S W regs mem md
(fun a => fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
ly' (snd r) W' regs' mem' md' /\
(fst r <> PNull -> errno_kept B mem mem') /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
lpost (snd r) /\
(exists trc, apath (mt n tr S) trc r /\ gflag trc = true) /\
(fst r = PNull -> val_mem segs (mrestrict (w_H W') mem') oomb 1 1).

(* AllocG.aalloc_prim_realizes over alloc_leaf_e. *)
Definition aalloc_prim_realizes_e : Prop :=
forall inst so bp ly S W regs mem md n tr,
alloc_pre segs B U ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr -> n <= 64512 ->
amreal segs (mt n tr S) W (cfg_at segs pcA regs mem md)
(alloc_leaf_e inst ly S W regs mem md n tr).

(* AllocG.aalloc_realizes over alloc_leaf_e. *)
Definition aalloc_realizes_e : Prop :=
forall inst so bp ly S W regs mem md n tr,
alloc_pre segs B U ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr ->
amreal segs (mt n tr S) W (cfg_at segs pcA regs mem md)
(alloc_leaf_e inst ly S W regs mem md n tr).

Lemma alloc_leaf_e_alloc_leaf : forall inst ly S W regs mem md n tr r W' c',
alloc_leaf_e inst ly S W regs mem md n tr r W' c' ->
alloc_leaf segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c'.
Proof.
intros inst ly S W regs mem md n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & _ & HR & HL & HT & HO).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HR|]. split; [exact HL|].
split; [exact HT | exact HO].
Qed.

Lemma aalloc_prim_realizes_e_aalloc_prim_realizes : aalloc_prim_realizes_e ->
aalloc_prim_realizes segs B U mt ARX AOX rpre nmax lmax lpost pcA oomb al atp cf.
Proof.
intros H inst so bp ly S W regs mem md n tr P N.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md n tr P N)]; exact (alloc_leaf_e_alloc_leaf inst ly S W regs mem md n tr).
Qed.

Lemma aalloc_realizes_e_aalloc_realizes : aalloc_realizes_e ->
aalloc_realizes segs B U mt ARX AOX rpre nmax lmax lpost pcA oomb al atp cf.
Proof.
intros H inst so bp ly S W regs mem md n tr P.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md n tr P)]; exact (alloc_leaf_e_alloc_leaf inst ly S W regs mem md n tr).
Qed.
End al.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Deallocate: DeallocG's section variables, in DeallocG's order.                                                   *)
Section dl.
Variable segs : list Segment.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable nmax : Z.
Variable lmax : Z.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world segs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable pcD : Z.
Variable atp : Z.
Variable MP : (word -> option byte) -> Prop.

(* DeallocG.dealloc_leaf (the view form), with errno kept on the view (every branch: NULL and live block). *)
Definition dealloc_leaf_e (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
dealloc_post segs B ARX AOX inst ly S W regs mem md
(fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
ly' (snd r) W' regs' mem' md' /\
errno_kept_v segs B W W' mem mem' /\
lpost (snd r) /\
(exists trc, apath (ft p tr S) trc r /\ gflag trc = true).

(* DeallocG.adealloc_realizes over dealloc_leaf_e. *)
Definition adealloc_realizes_e : Prop :=
forall inst so bp ly S W regs mem md p n tr,
dealloc_pre segs B U ARX rpre fpre atp inst so bp ly S W regs mem md p n tr -> MP mem ->
amreal segs (ft p tr S) W (cfg_at segs pcD regs mem md)
(dealloc_leaf_e inst ly S W regs mem md p n tr).

(* DeallocG.dealloc_leaf_raw, with errno kept on the raw memory (every branch: NULL and live block). *)
Definition dealloc_leaf_raw_e (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
dealloc_post_raw segs B ARX AOX inst ly S W regs mem md
(fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
ly' (snd r) W' regs' mem' md' /\
errno_kept B mem mem' /\
lpost (snd r) /\
(exists trc, apath (ft p tr S) trc r /\ gflag trc = true).

(* DeallocG.adealloc_realizes_raw over dealloc_leaf_raw_e. *)
Definition adealloc_realizes_raw_e : Prop :=
forall inst so bp ly S W regs mem md p n tr,
dealloc_pre segs B U ARX rpre fpre atp inst so bp ly S W regs mem md p n tr -> MP mem ->
amreal segs (ft p tr S) W (cfg_at segs pcD regs mem md)
(dealloc_leaf_raw_e inst ly S W regs mem md p n tr).

Lemma dealloc_leaf_e_dealloc_leaf : forall inst ly S W regs mem md p n tr r W' c',
dealloc_leaf_e inst ly S W regs mem md p n tr r W' c' ->
dealloc_leaf segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & _ & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HL | exact HT].
Qed.

Lemma adealloc_realizes_e_adealloc_realizes : adealloc_realizes_e ->
adealloc_realizes segs B U ft ARX AOX rpre lpost fpre pcD atp MP.
Proof.
intros H inst so bp ly S W regs mem md p n tr P HMP.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md p n tr P HMP)]; exact (dealloc_leaf_e_dealloc_leaf inst ly S W regs mem md p n tr).
Qed.

Lemma dealloc_leaf_raw_e_raw : forall inst ly S W regs mem md p n tr r W' c',
dealloc_leaf_raw_e inst ly S W regs mem md p n tr r W' c' ->
dealloc_leaf_raw segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & _ & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HL | exact HT].
Qed.

Lemma adealloc_realizes_raw_e_raw : adealloc_realizes_raw_e ->
adealloc_realizes_raw segs B U ft ARX AOX rpre lpost fpre pcD atp MP.
Proof.
intros H inst so bp ly S W regs mem md p n tr P HMP.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md p n tr P HMP)]; exact (dealloc_leaf_raw_e_raw inst ly S W regs mem md p n tr).
Qed.
End dl.
End a.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The Deallocate callees (DGif0.DIface's parameters).                                                              *)
(* Callee posts with a frame that does not conclude errno, each with its add-on:                                   *)
(* - StackDepotPut (DIface.di_depot, DGif0.v:284-302): the post frames the raw memory only (DGif0.v:299-300), outside *)
(*   the depot's stack window and [dg_dzone], which DImg does not keep apart from errno; one form, [de_depot_t];    *)
(* - Enqueue / Drain / Recycle / CacheDealloc: acall_post_x's view frame excludes ascratch (DMspec.v:109), and so    *)
(*   does DIfaceR's raw frame (DIfaceR.v:56); two forms each: the view form (DIface's contract, DGif0.v:307-331 /    *)
(*   326 and DMiface.v:232-255, plus errno_kept_v) and the raw form (DIfaceR's contract, DIfaceR.v:143-179, plus      *)
(*   errno_kept).  amreal has no conjunction rule (an IAsk node is an existential over the kernel's answers,         *)
(*   YG0d.v:72-91), so the raw form carries the raw frame and errno together: an errno-only contract could not be    *)
(*   joined to DIfaceR's in a proof of adealloc_realizes_raw_e.                                                      *)
(* DIface's other fields state no callee post with a memory frame (di_post_c / di_post_n conclude ARX and lpost).    *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.

(* The extra conjunct of the Enqueue and Drain contracts (DIfaceR.fxrel's arguments; [mem] is the memory at the
   call, [mem'] the memory at the return): errno kept on the view (the view form), and DIfaceR.acall_raw_x with errno
   kept on the raw memory (the raw form). *)
Definition acall_errno_v_x (B : asyms) : fxrel :=
fun inst stk ly S W regs mem md E ly' S' W' regs' mem' md' => errno_kept_v im_segs B W W' mem mem'.
Definition acall_raw_e_x (B : asyms) (AOX : alayout -> astate -> Z -> Prop) : fxrel :=
fun inst stk ly S W regs mem md E ly' S' W' regs' mem' md' =>
acall_raw_x B AOX inst stk ly S W regs mem md E ly' S' W' regs' mem' md' /\ errno_kept B mem mem'.

(* Recycle / CacheDealloc: DMiface.di_rchunk_t / di_cdealloc_t plus errno_kept_v (view form), DIfaceR.dr_rchunk_t /
   dr_cdealloc_t plus errno_kept (raw form). *)
Section rc.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Definition de_rchunk_v_t : Prop :=
forall inst ly X k ks zs cbp W regs mem md,
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs ->
amreal im_segs (recycle_chunk k X) W (cfg_at im_segs dg_rchunk regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  errno_kept_v im_segs B W W' mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq (snd r) ks zs /\ st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a)).
Definition de_rchunk_t : Prop :=
forall inst ly X k ks zs cbp W regs mem md,
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs ->
amreal im_segs (recycle_chunk k X) W (cfg_at im_segs dg_rchunk regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  errno_kept B mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq (snd r) ks zs /\ st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a)).
Definition de_cdealloc_v_t : Prop :=
forall inst ly X its z zs W regs mem md,
cd_pre_x B ARXr inst ly X z W regs mem md -> DRq X its (z :: zs) ->
amreal im_segs (cache_dealloc kBatchClass z X) W (cfg_at im_segs dg_cdealloc regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  errno_kept_v im_segs B W W' mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq (snd r) its zs /\ st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a)).
Definition de_cdealloc_t : Prop :=
forall inst ly X its z zs W regs mem md,
cd_pre_x B ARXr inst ly X z W regs mem md -> DRq X its (z :: zs) ->
amreal im_segs (cache_dealloc kBatchClass z X) W (cfg_at im_segs dg_cdealloc regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  errno_kept B mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq (snd r) its zs /\ st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a)).
End rc.

(* The depot, Enqueue and Drain add-ons, and the records, over DIfaceR's parameters (DIface's without the unused
   [ft]).  [DIfaceE] bundles the depot and the view forms (what an instance with DIface alone can give: the closed
   cgif Deallocate top has no DIfaceR instance), [DIfaceRE] the raw forms. *)
Section b.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world im_segs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
(* DGif0.DIface's memory predicate at Put's call of Enqueue (DIfaceR.enq_spec_g's premise). *)
Variable MP : (word -> option byte) -> Prop.

(* StackDepotPut at QuarantineChunk's call: DIface.di_depot with errno kept *)
Definition de_depot_t : Prop :=
forall inst ly S W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
ARX inst ly S W mem0 md0 -> U tr S ->
(forall x : word, dg_dzone ly (bv_unsigned x) \/ (dg_czone ly (bv_unsigned x) /\ ~ dg_izone (bv_unsigned x)) -> mem x = mem0 x) ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 im_tp -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem im_segs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
buf + 8 * 30 <= bv_unsigned (getr regs 2) - YFl0C.DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - YFl0C.DEP_STK ->
bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
(forall a, bv_unsigned (getr regs 2) - YFl0C.DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
SRr im_segs W (mkCfg (mkst regs (Z_to_bv 64 dg_depot) mem (seg_rom im_segs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
  regs_preserved regs regs' /\
  (forall x : word, ~ (bv_unsigned (getr regs 2) - YFl0C.DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
     ~ dg_dzone ly (bv_unsigned x) -> mem' x = mem x) /\
  errno_kept B mem mem' /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
  dpost inst ly S W tr z mem').
(* QuarantineCache::Enqueue at Put's call: DIface.di_enqueue with errno kept on the view, DIfaceR.dr_enqueue with
   errno kept on the raw memory *)
Definition de_enqueue_v_t : Prop := enq_spec_g B U ARX AOX rpre lpost fpre dpost L24 QB MP (acall_errno_v_x B).
Definition de_enqueue_t : Prop := enq_spec_g B U ARX AOX rpre lpost fpre dpost L24 QB MP (acall_raw_e_x B AOX).
(* Quarantine::Drain at Put's call: DIface.di_drain with errno kept on the view, DIfaceR.dr_drain with errno kept on
   the raw memory *)
Definition de_drain_v_t : Prop := drain_spec_g B ARX AOX dbody L24 QB (acall_errno_v_x B).
Definition de_drain_t : Prop := drain_spec_g B ARX AOX dbody L24 QB (acall_raw_e_x B AOX).

Record DIfaceE : Prop := {
  de_depot : de_depot_t;
  de_enqueue_v : de_enqueue_v_t;
  de_drain_v : de_drain_v_t;
  de_rchunk_v : de_rchunk_v_t B ARXr AOX DRq;
  de_cdealloc_v : de_cdealloc_v_t B ARXr AOX DRq
}.
Record DIfaceRE : Prop := {
  de_enqueue : de_enqueue_t;
  de_drain : de_drain_t;
  de_rchunk : de_rchunk_t B ARXr AOX DRq;
  de_cdealloc : de_cdealloc_t B ARXr AOX DRq
}.
End b.
End d.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The Allocate callees, primary path (AGif0n.AIface / AIfaceK / AIfaceM's parameters).                             *)
(* Fields of AIface / AIfaceK / AIfaceM with a memory frame that does not conclude errno, each with its add-on:     *)
(* - if_depot (AGif0n.v:178-196) and if_depot_miss (AGif0n.v:334-353): the post frames the raw memory only           *)
(*   (AGif0n.v:193-194, 350-351), outside the depot's stack window and [ag_dzone], which AGImg does not keep apart  *)
(*   from errno; one form each;                                                                                      *)
(* - if_refill (AGif0n.v:285-300): its PREMISE's raw frame (AGif0n.v:292-293) excludes only Allocate's stack window *)
(*   and the unwinding byte, but its POST [rleaf] frames the view and the raw memory outside the owned sets           *)
(*   AOX ly S0 and AOX ly' (snd r) and the refill's stack window (AGif0n.v:264-268), and no AIface / AIfaceM field   *)
(*   says that errno is unowned (if_stack, AGif0n.v:369, covers the stack only); so errno is not concluded either;  *)
(*   two forms (rleaf has both frames).  cgif's instance has errno unowned (AGif1m.v:105-107), from which both      *)
(*   follow by amreal_mono.                                                                                          *)
(* No add-on: if_post / if_post_k / if_post_miss / if_post_miss_k conclude ARX and lpost only (their memory facts   *)
(* at_RETw / at_RETkw are premises); if_oom (AGif0n.v:355-366) is the refusal arm (a0 = PNull), where alloc_leaf_e  *)
(* asks nothing of errno; the other fields state no memory frame.                                                  *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {AG : AGImg}.
Local Open Scope am_scope.

(* AGif0n.rleaf, with errno kept on the view (rleaf_ev) or on the raw memory (rleaf_e), next to the frame of the
   same form. *)
Definition rleaf_ev (B : asyms) (ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (lpost : astate -> Prop)
(inst : Z) (ly : alayout) (S0 : astate) (n cl : Z) (W : world im_segs) (regs : bvmap 5 word) (mem : word -> option byte)
(md : Model) (r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
ARX inst ly' (snd r) W' mem' md' /\ lpost (snd r) /\ st_cache_inited (snd r) = true /\
blocks_bytes (snd r) = blocks_bytes S0 /\ layout_le (length (st_secs S0)) ly ly' /\
wle W W' /\ aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S0 a -> ~ AOX ly' (snd r) a -> ~ (spZ regs - ImgBaseAG.RSTACK <= a < spZ regs) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
errno_kept_v im_segs B W W' mem mem' /\
(forall x : word, ~ AOX ly S0 (bv_unsigned x) -> ~ AOX ly' (snd r) (bv_unsigned x) ->
   ~ (spZ regs - ImgBaseAG.RSTACK <= bv_unsigned x < spZ regs) -> mem' x = mem x) /\
(forall a, spZ regs - ImgBaseAG.RSTACK <= a < spZ regs -> apresent (w_H W') mem' a) /\
getr regs' 10 = w64 (match pc_chunks (cache (snd r) cl) with [] => 0 | _ => 1 end).
Definition rleaf_e (B : asyms) (ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (lpost : astate -> Prop)
(inst : Z) (ly : alayout) (S0 : astate) (n cl : Z) (W : world im_segs) (regs : bvmap 5 word) (mem : word -> option byte)
(md : Model) (r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
ARX inst ly' (snd r) W' mem' md' /\ lpost (snd r) /\ st_cache_inited (snd r) = true /\
blocks_bytes (snd r) = blocks_bytes S0 /\ layout_le (length (st_secs S0)) ly ly' /\
wle W W' /\ aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S0 a -> ~ AOX ly' (snd r) a -> ~ (spZ regs - ImgBaseAG.RSTACK <= a < spZ regs) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
(forall x : word, ~ AOX ly S0 (bv_unsigned x) -> ~ AOX ly' (snd r) (bv_unsigned x) ->
   ~ (spZ regs - ImgBaseAG.RSTACK <= bv_unsigned x < spZ regs) -> mem' x = mem x) /\
errno_kept B mem mem' /\
(forall a, spZ regs - ImgBaseAG.RSTACK <= a < spZ regs -> apresent (w_H W') mem' a) /\
getr regs' 10 = w64 (match pc_chunks (cache (snd r) cl) with [] => 0 | _ => 1 end).

(* The add-ons, over the variables they use (AIfaceM's, in AIfaceM's order). *)
Section v.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable rtree : Z -> M unit.

(* AIface.if_depot with errno kept *)
Definition ae_depot_t : Prop :=
forall inst ly S W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
ARX inst ly S W mem0 md0 -> U tr S ->
(forall x : word, ag_dzone ly (bv_unsigned x) \/ ag_czone ly (bv_unsigned x) -> mem x = mem0 x) ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 im_tp -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem im_segs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
buf + 8 * 30 <= bv_unsigned (getr regs 2) - ImgBaseAG.DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - ImgBaseAG.DEP_STK ->
bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
(forall a, bv_unsigned (getr regs 2) - ImgBaseAG.DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
SRr im_segs W (mkCfg (mkst regs (Z_to_bv 64 ag_depot_put) mem (seg_rom im_segs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
  regs_preserved regs regs' /\
  (forall x : word, ~ (bv_unsigned (getr regs 2) - ImgBaseAG.DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
     ~ ag_dzone ly (bv_unsigned x) -> mem' x = mem x) /\
  errno_kept B mem mem' /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
  dpost inst ly S W tr z mem').

(* AIfaceM.if_refill over rleaf_ev (view form) and over rleaf_e (raw form) *)
Definition ame_refill_v_t : Prop :=
forall inst ly S0 W mem0 md0 n (sp0 : Z) (regs : bvmap 5 word) (mem : word -> option byte) (mat : list word),
ARX inst ly S0 W mem0 md0 -> rpre S0 n -> 0 <= n -> from_primary n = true ->
pc_chunks (cache S0 (chunk_class n)) = [] ->
ly_stk_lo ly + ImgBaseAG.AFSTACK <= sp0 -> ly_bot ly < sp0 -> sp0 <= ly_stk_hi ly -> sp0 mod 16 = 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ImgBaseAG.AFSTACK <= a < sp0) -> aview im_segs (w_H W) mem a = aview im_segs (w_H W) mem0 a) ->
(forall x : word, ~ (sp0 - ImgBaseAG.AFSTACK <= bv_unsigned x < sp0) -> ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) ->
   mem x = mem0 x) ->
(forall a, sp0 - ImgBaseAG.AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
spZ regs = sp0 - 176 -> getr regs 1 = w64 ag_refill_ret -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 im_tp ->
getr regs 10 = w64 (ly_T ly + t_cache) -> getr regs 11 = w64 (ly_T ly + t_cache + 80 * chunk_class n) ->
getr regs 12 = w64 inst -> getr regs 13 = w64 (chunk_class n) ->
amreal im_segs (rtree (chunk_class n) (set_nev (st_nev S0 + 1) S0)) W
  (cfg_at im_segs ag_refill regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
  (rleaf_ev B ARX AOX lpost inst ly S0 n (chunk_class n) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0)).
Definition ame_refill_t : Prop :=
forall inst ly S0 W mem0 md0 n (sp0 : Z) (regs : bvmap 5 word) (mem : word -> option byte) (mat : list word),
ARX inst ly S0 W mem0 md0 -> rpre S0 n -> 0 <= n -> from_primary n = true ->
pc_chunks (cache S0 (chunk_class n)) = [] ->
ly_stk_lo ly + ImgBaseAG.AFSTACK <= sp0 -> ly_bot ly < sp0 -> sp0 <= ly_stk_hi ly -> sp0 mod 16 = 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ImgBaseAG.AFSTACK <= a < sp0) -> aview im_segs (w_H W) mem a = aview im_segs (w_H W) mem0 a) ->
(forall x : word, ~ (sp0 - ImgBaseAG.AFSTACK <= bv_unsigned x < sp0) -> ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) ->
   mem x = mem0 x) ->
(forall a, sp0 - ImgBaseAG.AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
spZ regs = sp0 - 176 -> getr regs 1 = w64 ag_refill_ret -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 im_tp ->
getr regs 10 = w64 (ly_T ly + t_cache) -> getr regs 11 = w64 (ly_T ly + t_cache + 80 * chunk_class n) ->
getr regs 12 = w64 inst -> getr regs 13 = w64 (chunk_class n) ->
amreal im_segs (rtree (chunk_class n) (set_nev (st_nev S0 + 1) S0)) W
  (cfg_at im_segs ag_refill regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
  (rleaf_e B ARX AOX lpost inst ly S0 n (chunk_class n) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0)).

(* AIfaceM.if_depot_miss with errno kept *)
Definition ame_depot_miss_t : Prop :=
forall inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
ARX inst ly0 S0 W0 mem00 md00 -> U tr S0 ->
ARX inst ly Sp W mem0 md0 ->
(forall x : word, ag_dzone ly (bv_unsigned x) \/ ag_czone ly (bv_unsigned x) -> mem x = mem0 x) ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 im_tp -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem im_segs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
buf + 8 * 30 <= bv_unsigned (getr regs 2) - ImgBaseAG.DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - ImgBaseAG.DEP_STK ->
bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
(forall a, bv_unsigned (getr regs 2) - ImgBaseAG.DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
SRr im_segs W (mkCfg (mkst regs (Z_to_bv 64 ag_depot_put) mem (seg_rom im_segs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
  regs_preserved regs regs' /\
  (forall x : word, ~ (bv_unsigned (getr regs 2) - ImgBaseAG.DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
     ~ ag_dzone ly (bv_unsigned x) -> mem' x = mem x) /\
  errno_kept B mem mem' /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
  dpost inst ly Sp W tr z mem').
End v.

(* AIface's add-on (AIface's parameters). *)
Record AIfaceE (B : asyms) (U : list Z -> astate -> Prop) (mt : Z -> list Z -> M sptr)
(ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (rpre : astate -> Z -> Prop) (nmax lmax : Z) (lpost : astate -> Prop)
(dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop) (mtag stag : Z) : Prop := {
  ae_depot : ae_depot_t B U ARX dpost
}.

(* AIfaceM's add-ons (AIfaceM's parameters). *)
Record AIfaceME (B : asyms) (U : list Z -> astate -> Prop) (mt : Z -> list Z -> M sptr)
(ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (rpre : astate -> Z -> Prop) (nmax lmax : Z) (lpost : astate -> Prop)
(dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop) (mtag stag : Z) (rtree : Z -> M unit) : Prop := {
  ame_refill_v : ame_refill_v_t B ARX AOX rpre lpost rtree;
  ame_refill : ame_refill_t B ARX AOX rpre lpost rtree;
  ame_depot_miss : ame_depot_miss_t B U ARX dpost
}.
End g.
