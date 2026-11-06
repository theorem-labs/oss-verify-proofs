(* copy of proofs/cgif/cgif_file_fuzzer/lib/CLdepot.v@1470d2b40a0e; do not edit. Only this line is added, and the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib is this unit's OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (ReallocPrimary.TkSecLink), 2026-10-30: P'' trace premise: the released contract YFl0.tfib_depot_spec admits a trace by `admits (as_universe B) tr S` (YG01.v:157), so this file states it the same way; an In-form caller converts with admits_fix (YG01.v:184). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* The depot callee's contract over a generic allocator relation [ARX], image-free.

   The interfaces' depot fields (AGif0n.if_depot for Allocate, DGif0.di_depot for Deallocate) state
   StackDepotPut's contract at the walk's call site: entered with the depot zone and the constant cells as at the
   relation's memory [mem0], the call returns an answer [z], keeps the registers and the memory outside the walk's
   stack window and the depot zone, and gives the post [dpost_x].  That field is not a new walk: it follows from
   the released machine-level depot contract ([depot_spec_x] below; cgif_file: YFl0.tfib_depot_spec) plus the four
   facts of [DepotSub], which an instance proves once from its own relation.

   The model-level names ([depot_after], [depot_footprint], [depot_mem_ok], [DEP_STK]) are YFl0.v:58-66 verbatim;
   they name no image, so a consumer that relocates the core relocates them with it.  The image enters only
   through the section variables [segs] (the segments), [A_DEP] (StackDepotPut's entry pc), [TPv] (the thread
   pointer the callee is entered with) and [IMGC] (the layout's image-cover premise).

   The caller's side of the field, which this file does NOT need: after the call the caller restores its relation
   from the post's [depot_mem_ok (depot_after z tr S)] and [Forall (cell_holds ...) (as_const B ly)] (YFl0.v:85-86),
   which is why [dpost_x] carries exactly those two facts beside the answer. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The model-level names of the depot call (YFl0.v:58-66), image-free.                                              *)

(* StackDepotPut's stack need below the caller's sp. *)
Definition DEP_STK : Z := 512.
(* The model state after the put: a granted answer appends the trace to the depot, a refused one changes nothing. *)
Definition depot_after (z : Z) (tr : list Z) (S : astate) : astate :=
if z =? 0 then S else set_depot (st_depot S ++ [tr]) S.
(* The addresses StackDepotPut may write. *)
Definition depot_footprint (B : asyms) (ly : alayout) (a : Z) : Prop :=
(as_depot B <= a < as_depot B + d_map1 + 8 * 32768) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/
(ly_SB ly <= a < ly_SB ly + kStoreBlockSize) \/ (as_store B <= a < as_store B + 64).
(* The depot's memory facts: its cells, its table invariant and the ranges it reads. *)
Definition depot_mem_ok (B : asyms) (ly : alayout) (S : astate) (rd : reader) : Prop :=
Forall (cell_holds B ly rd) (depot_cells ly S) /\ depot_ok B ly rd S /\
Forall (range_vis B ly rd) [(ADepot (d_nuniq + 4), 12); (AStore 8, 8); (AStore 24, 8); (ANB 0, kNodesBlockSize); (ASB 0, kStoreBlockSize)].

Section b.
(* The image: the segments, StackDepotPut's entry pc, the thread pointer, the image-cover premise. *)
Variable segs : list Segment.
Variable A_DEP : Z.
Variable TPv : Z.
Variable IMGC : alayout -> Prop.
Variable B : asyms.
(* The allocator relation and the trace premise of the consumer (AllocG / DeallocG's [ARX] and [U]). *)
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable U : list Z -> astate -> Prop.
(* [DZ]: the zone the caller frames out of the post (the walk's DZONE).  [KEEP]: the zone the caller keeps as at
   the relation's memory (AGif0n: DZONE or CZONE; DGif0: DZONE, or CZONE outside the internal allocator). *)
Variable DZ : alayout -> Z -> Prop.
Variable KEEP : alayout -> Z -> Prop.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The sub-interface: what an instance proves once.                                                                 *)
Record DepotSub : Prop := {
  (* the layout premises and the model's well-formedness *)
  ds_view : forall inst ly S W mem md, ARX inst ly S W mem md -> layout_ok ly /\ IMGC ly /\ Wf (as_universe B) S;
  (* the trace premise of the consumer bridges to the released spec's [admits (as_universe B) tr S] *)
  ds_univ : forall inst ly S W mem md tr, ARX inst ly S W mem md -> U tr S -> admits (as_universe B) tr S;
  (* the constant cells and the depot's memory facts hold at any memory that keeps [KEEP] as at [mem0] *)
  ds_keep : forall inst ly S W mem0 md0 (mem : word -> option byte),
    ARX inst ly S W mem0 md0 -> (forall x : word, KEEP ly (bv_unsigned x) -> mem x = mem0 x) ->
    Forall (cell_holds B ly (aview segs (w_H W) mem)) (as_const B ly) /\
    depot_mem_ok B ly S (aview segs (w_H W) mem);
  (* what StackDepotPut may write lies in the zone the caller frames out *)
  ds_fp : forall inst ly S W mem md a, ARX inst ly S W mem md -> depot_footprint B ly a -> DZ ly a
}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The depot post the field gives: the model's answer, and the two facts the caller restores [ARX] from.            *)
Definition dpost_x (inst : Z) (ly : alayout) (S : astate) (W : world segs) (tr : list Z) (z : Z)
(m : word -> option byte) : Prop :=
aok S (KDepot tr) z /\ depot_mem_ok B ly (depot_after z tr S) (aview segs (w_H W) m) /\
Forall (cell_holds B ly (aview segs (w_H W) m)) (as_const B ly).

(* The released machine-level contract (YFl0.v:67-86 over [segs] / [A_DEP] / [TPv] / [IMGC]). *)
Definition depot_spec_x : Prop :=
forall (W : world segs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (buf : Z) (tr : list Z),
let H := w_H W in let rd := aview segs H mem in let sp := bv_unsigned (getr regs 2) in
layout_ok ly -> IMGC ly -> Wf (as_universe B) S -> admits (as_universe B) tr S ->
Forall (cell_holds B ly rd) (as_const B ly) -> depot_mem_ok B ly S rd ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 TPv -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem segs (mrestrict H mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly -> buf + 8 * 30 <= sp - DEP_STK \/ sp <= buf ->
sp mod 16 = 0 -> ly_stk_lo ly <= sp - DEP_STK -> sp <= ly_stk_hi ly -> (forall a, sp - DEP_STK <= a < sp -> apresent H mem a) ->
SRr segs W (mkCfg (mkst regs (Z_to_bv 64 A_DEP) mem (seg_rom segs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
aok S (KDepot tr) z /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp - DEP_STK <= bv_unsigned x < sp) -> ~ depot_footprint B ly (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent H mem a -> apresent H mem' a) /\
depot_mem_ok B ly (depot_after z tr S) (aview segs H mem') /\
Forall (cell_holds B ly (aview segs H mem')) (as_const B ly)).

(* The interfaces' depot field (AGif0n.if_depot / DGif0.di_depot, with [DZ] / [KEEP] for the walk's zones). *)
Definition depot_field : Prop :=
forall inst ly S W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
ARX inst ly S W mem0 md0 -> U tr S ->
(forall x : word, KEEP ly (bv_unsigned x) -> mem x = mem0 x) ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 TPv -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem segs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
buf + 8 * 30 <= bv_unsigned (getr regs 2) - DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - DEP_STK ->
bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
(forall a, bv_unsigned (getr regs 2) - DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
SRr segs W (mkCfg (mkst regs (Z_to_bv 64 A_DEP) mem (seg_rom segs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (bv_unsigned (getr regs 2) - DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
~ DZ ly (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
dpost_x inst ly S W tr z mem').

(* The field follows from the released contract and the sub-interface (AGix.depot_call's script, with the
   instance's facts taken from [DepotSub] instead of from AR). *)
Theorem depot_field_ok : DepotSub -> depot_spec_x -> depot_field.
Proof.
intros SUB HD1 inst ly S W mem0 md0 tr regs mem md buf HARX HU MEQ R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES.
destruct (ds_view SUB inst ly S W mem0 md0 HARX) as (LY & IMG & WF).
pose proof (ds_univ SUB inst ly S W mem0 md0 tr HARX HU) as Htr.
destruct (ds_keep SUB inst ly S W mem0 md0 mem HARX MEQ) as [CST DEP].
eapply SRr_mono.
{ exact (HD1 W ly S regs mem md buf tr LY IMG WF Htr CST DEP R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES). }
intros W' c' Hle (-> & z & regs' & mem' & mat & -> & AOK & RP & FR & PR' & DEP' & CST'). split; [reflexivity|].
exists z, regs', mem', mat. split; [reflexivity|]. split; [exact RP|].
split; [|split; [exact PR' | exact (conj AOK (conj DEP' CST'))]].
intros x N1 N2. apply FR; [exact N1|].
intros FP. apply N2. exact (ds_fp SUB inst ly S W mem0 md0 (bv_unsigned x) HARX FP).
Qed.
End b.
End a.
