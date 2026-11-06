(* copied from proofs/cgif/cgif_file_fuzzer/lib/DMspec.v @ 95e6f1d72b6 (c-asan, frozen), module paths changed only. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The contract of Quarantine::Drain (0x32f58) with the REAL MergeBatches, for the shared (reply / preset)
   allocator instance, in the form of cgif_file's released tfib_drain_spec (YFeu.v:190-208).

   What changes from the released form:
   - the allocator relation is a parameter [ARX inst] over the instance at [inst] (cgif: inst = TFIB_INST /\ AR),
     and a0 is [inst + o_quar] (inst + 0x2d8), the instance atom as the generic Deallocate passes it
     (DeallocG.v; DEALLOCG-FILES.md, the drain field);
   - the owned set of the frame clause is a parameter [AOX] (cgif: aowned B);
   - the model tree is a parameter [dbody] (run as [dbody X X], as the released [drain_body X X]); the shared
     instance's tree is [drain_body_cf] below, the drain sub-tree of free_cf: maybe_drain_cf's branch after the
     thread-cache test ([maybe_drain_cf_drain]);
   - the class-24 batch bound is a parameter [L24], with the premise that the number of batch objects of the
     quarantine is at most [L24] (all_batches = thread list ++ global list, YG01.v:153; the shared instance takes
     L24 := L24MAX_cf, h-mani-a8's YGcfBatch.v). No fixed window;
   - cgif's byte bounds [qloose X] (thread bytes <= 2^29, false on the shared instance) become a parameter
     [QB : astate -> Prop] on the entry state (cgif: qloose; preset / reply: their cf bounds). The proof reads the
     byte bound it uses through ARX (DMiface.qview).
   The post is acall_post (YG0d.v:234-242) with ARX for AR and AOX for aowned B, field for field.
   The model is h-mani-a8's YG00cf.v (the shared tree; read-only mirror in this lib).
   Non-vacuity of the merge arm: witnessed for the model by h-w6-2's dm_merge_witness_cf (h-mani-a8 branch, YGcfDmWit.v: Wf_cf state with 16384 < |all_batches| <= L24MAX_cf, the recycle test and merge_split_cf's merge test true); the machine part rests on ARcf being realisable at such a model state, not proved.
   The file is image-free: the binary's segments and Drain's entry pc are the fields of ImgBase.AImg and
   ImgBaseDG.DImg ([Context {IM : AImg} {DI : DImg}]; cgif_file's instances AGif2cgif.AImg_cgif and
   DGif0cgif.DImg_cgif); transfer_g and DSTACK are ImgBaseDG's copies of YFeu's.  The contract is [drain_spec_cf]
   (released name tfib_drain_spec_cf; DGif0cgif keeps the old name as an abbreviation). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG06 YG03 YG0f YG0v YG0n YG0d YG0k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YGcfNames YG00cf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import ImgBase ImgBaseDG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The shared instance's drain tree: maybe_drain_cf's branch after the thread-cache test, split as the released     *)
(* drain_body / recycle_body (YFeu.v:156-166). transfer_g is YFeu's (thread list appended to the global list).     *)
(* [merge_split_cf g] is the kept quarantine and the extracted (emptied) batches: MergeBatches runs when            *)
(* kBatchBytes * L < bytes < 2 * kBatchBytes * L (Recycle's test, 0x3316c / 0x33180), else nothing is extracted.   *)
Definition merge_split_cf (g : qcache) : qcache * list batch :=
let L := Z.of_nat (length (qc_list g)) in
if (kBatchBytes * L <? qc_bytes g) && (qc_bytes g <? 2 * (kBatchBytes * L))
then let '(l', ex) := merge_batches_cf (length (qc_list g)) (qc_list g) in
(mkQC l' (qc_bytes g - kBatchBytes * Z.of_nat (length ex)), ex)
else (g, []).
Definition recycle_body_cf (g : qcache) : M unit :=
let '(gm, ex) := merge_split_cf g in
let '(g', popped) := pop_batches (S (length (qc_list gm))) gm [] in
modify (set_qglobal g') ;;
do_recycle (length (ex ++ popped)) (ex ++ popped).
Definition drain_body_cf (X : astate) : M unit :=
let g := YFeuC.transfer_g X in
put (set_qglobal g (set_qthread qc0 X)) ;;
(if qc_bytes g <=? kQuarantineMax then ret tt else recycle_body_cf g).

Lemma maybe_drain_cf_eq : forall X,
maybe_drain_cf X = if qc_bytes (st_qthread X) <=? kQuarantineCacheMax then ret tt X else drain_body_cf X X.
Proof.
intros X. unfold maybe_drain_cf, drain_body_cf, recycle_body_cf, merge_split_cf, YFeuC.transfer_g.
unfold bind at 1. unfold get. cbn [ibind].
destruct (qc_bytes (st_qthread X) <=? kQuarantineCacheMax); reflexivity.
Qed.
Lemma maybe_drain_cf_drain : forall X,
kQuarantineCacheMax < qc_bytes (st_qthread X) -> maybe_drain_cf X = drain_body_cf X X.
Proof.
intros X H. rewrite maybe_drain_cf_eq.
destruct (Z.leb_spec (qc_bytes (st_qthread X)) kQuarantineCacheMax); [lia | reflexivity].
Qed.

Section e.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.

(* YFeu.drain_pre with ARX inst for AR, a0 = inst + o_quar, QB for qloose, and the batch bound. *)
Definition drain_pre_cf (inst : Z) (ly : alayout) (X : astate) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
ARX inst ly X W mem md /\
kQuarantineCacheMax < qc_bytes (st_qthread X) /\ QB X /\
Z.of_nat (length (all_batches X)) <= L24 /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + YFeuC.DSTACK <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - YFeuC.DSTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 (inst + o_quar) /\ getr regs 11 = w64 (ly_T ly + t_qc) /\ getr regs 12 = w64 (ly_T ly + t_cache).

(* acall_post (YG0d.v:234-242) with ARX inst for AR and AOX for aowned B: the frame on the view only, as the released
   post states it.  The same frame on the raw memory is DIfaceR.acall_raw_x (the DIfaceR contracts add it). *)
Definition acall_post_x (inst stk : Z) (ly : alayout) (S : astate) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world im_segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
ARX inst ly' S' W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ wle W W' /\
aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly' S' a -> ~ ascratch B stk regs a -> ~ E a ->
aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W') mem' a).

(* YFeu.drain_leaf over acall_post_x. *)
Definition drain_leaf_cf (inst : Z) (ly : alayout) (X : astate) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model)
(r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
acall_post_x inst YFeuC.DSTACK ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md'.

Definition drain_spec_cf : Prop :=
forall inst ly X W regs mem md,
drain_pre_cf inst ly X W regs mem md ->
amreal im_segs (dbody X X) W (cfg_at im_segs dg_drain regs mem md) (drain_leaf_cf inst ly X W regs mem md).
End e.

(* The shared instance's contract: the tree is free_cf's drain sub-tree. *)
Definition drain_spec_cf_free (B : asyms)
(ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (L24 : Z) (QB : astate -> Prop) : Prop :=
drain_spec_cf B ARX AOX drain_body_cf L24 QB.
End d.
