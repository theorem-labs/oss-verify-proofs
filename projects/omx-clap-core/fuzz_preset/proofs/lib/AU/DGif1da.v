(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGif1da.v (cold/c-asan-realloc-c5 ced28ed2383, file sha256 921e43ac5e57) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53); module paths changed; its 5 image addresses moved by code-verified function pairs (5 port_addr_check 0767e70e074a MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: the states of cgif_file's released DoRecycle walk (YFhd.v) restated for the
   recycle callees' contracts of DGif0.DIface (di_rchunk / di_cdealloc: stack window KSTACK_CF = 2048 below the callee's
   sp, and a raw-memory frame): the stack window below DoRecycle's entry sp grows from DRSTACK = 2048 to DRSTACK_X =
   2176 (DoRecycle's frame 112 plus the callee's 2048), and the accumulated frame [acc] gets a raw-memory clause. *)
(* DoRecycle (0x347c4) with a raw frame, for the drain of cgif_file's DIface instance (DGif1d.v (removed in this series)).

   The contract: [dr_pre_x] is the released YFeu.dr_pre plus the larger stack window; [dr_leaf_x] is the released
   dr_leaf over DMspec.acall_post_x (ARX_cgif, aowned, the raw frame clause) with the larger window.  The recycle callees
   are taken in the types of DMiface.di_rchunk_t / di_cdealloc_t at the cgif instantiation ([rch_cgif], [cdh_cgif]). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YP09 YN3v YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YF0x YFl1 YFeq YFeu YFf2 YFh9 YFhd.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AllocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* DoRecycle's frame (112) plus the recycle callees' window KSTACK_CF (2048), rounded up to 16. *)
Definition DRSTACK_X : Z := 2176.

(* The cgif recycle invariant (DGif1d.DRq_cgif (removed in this series)) and the callees' contracts at the cgif instantiation. *)
Definition rch_cgif (B : asyms) : Prop :=
dr_rchunk_t B (ARX_cgif B) (aowned B) (fun S its zs => RIx (as_universe B) 0 0 0 S its [] zs).
Definition cdh_cgif (B : asyms) : Prop :=
dr_cdealloc_t B (ARX_cgif B) (aowned B) (fun S its zs => RIx (as_universe B) 0 0 0 S its [] zs).

Section c.
Variable B : asyms.
Definition dr_pre_x (ly : alayout) (X : astate) (P : list batch) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
dr_pre B ly X P W regs mem md /\ ly_stk_lo ly + DRSTACK_X <= spZ regs /\
(forall a, spZ regs - DRSTACK_X <= a < spZ regs -> apresent (w_H W) mem a).
Definition dr_leaf_x (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model)
(r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
acall_post_x B (ARX_cgif B) (aowned B) TFIB_INST DRSTACK_X ly X W regs mem md (fun a => spZ regs <= a < spZ regs + 32) ly (snd r) W' regs' mem' md' /\
acall_raw_x B (aowned B) TFIB_INST DRSTACK_X ly X W regs mem md (fun a => spZ regs <= a < spZ regs + 32) ly (snd r) W' regs' mem' md' /\
(forall a, spZ regs <= a < spZ regs + 32 -> apresent (w_H W') mem' a).
Definition tfib_dorecycle_spec_x : Prop :=
forall ly X P W regs mem md,
dr_pre_x ly X P W regs mem md ->
amreal tfibsegs (do_recycle 100000%nat P X) W (cfg_at tfibsegs A_DoRecycle regs mem md) (dr_leaf_x ly X W regs mem md).
End c.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The walk's states (YFhd.v), over the larger window and with the raw frame.                                      *)
Section e.
Variable B : asyms.
Variables (ly : alayout) (X0 : astate) (W0 : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Local Notation sp0 := (YFhd.sp0 regs0).
Local Notation sp1 := (YFhd.sp1 regs0).
Local Notation U := (as_universe B).
Definition SY (a : Z) : Prop := sp0 - DRSTACK_X <= a < sp0 + 32.
Record acc (X : astate) (W : world tfibsegs) (mem : word -> option byte) (md : Model) : Prop := {
acc_AR : AR tfibsegs B ly X W mem md;
acc_wle : wle W0 W;
acc_io : same_io md0 md;
acc_own : forall a, aowned B ly X a -> aowned B ly X0 a;
acc_frame : forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly X0 a -> ~ aowned B ly X a -> ~ ascratch B DRSTACK_X regs0 a -> ~ (sp0 <= a < sp0 + 32) ->
aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W0) mem0 a;
acc_pres : forall a, SY a -> apresent (w_H W) mem a;
acc_inited : st_cache_inited X = true;
acc_raw : forall x : word, ~ aowned B ly X0 (bv_unsigned x) -> ~ aowned B ly X (bv_unsigned x) -> ~ ascratch B DRSTACK_X regs0 (bv_unsigned x) ->
~ (sp0 <= bv_unsigned x < sp0 + 32) -> mem x = mem0 x
}.
Local Notation common_regs := (YFhd.common_regs regs0).
Local Notation loop_regs := (YFhd.loop_regs regs0).
Local Notation frame_cells := (YFhd.frame_cells ly regs0).
Local Notation tmp_cells := (YFhd.tmp_cells ly regs0).
Local Notation batch_regs := (YFhd.batch_regs ly).
Local Notation zlen := (@YFhd.zlen _).
Local Notation hdra := (YFhd.hdra B ly).
Record ost (X : astate) (rest : list batch) (lz qb : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
o_acc : acc X W mem md;
o_rix : RIx U 0 0 0 X [] rest [];
o_ne : rest <> [];
o_len : zlen rest < 100000;
o_cregs : common_regs regs;
o_lregs : loop_regs regs;
o_a0 : getr regs 10 = w64 (zlen rest);
o_frame : frame_cells W mem;
o_tmp : tmp_cells W mem rest lz qb;
o_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells rest)
}.
Record rcst (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
rc_acc : acc X W mem md;
rc_rix : RIx U 0 0 0 X its t [b_self b];
rc_items : exists done, b_items b = done ++ its /\ length done = i;
rc_ne : its <> [];
rc_blen : (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat;
rc_len : zlen t < 100000;
rc_cregs : common_regs regs;
rc_lregs : loop_regs regs;
rc_bregs : batch_regs regs b;
rc_ra : getr regs 1 = w64 0x34888;
rc_a0 : getr regs 10 = w64 (sp1 + 8);
rc_a1 : forall k ks, its = k :: ks -> getr regs 11 = w64 (hdra k);
rc_s7 : getr regs 23 = w64 (ly_space ly + b_self b + 152 + 8 * Z.of_nat i);
rc_s9 : getr regs 25 = w64 (16 + Z.of_nat i);
rc_frame : frame_cells W mem;
rc_tmp : tmp_cells W mem t lz qb;
rc_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells (b :: t))
}.
Record rst (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
r_acc : acc X W mem md;
r_rix : RIx U 0 0 0 X its t [b_self b];
r_items : exists done, b_items b = done ++ its /\ length done = i;
r_i : (1 <= i)%nat;
r_blen : (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat;
r_len : zlen t < 100000;
r_cregs : common_regs regs;
r_lregs : loop_regs regs;
r_bregs : batch_regs regs b;
r_s7 : getr regs 23 = w64 (ly_space ly + b_self b + 144 + 8 * Z.of_nat i);
r_s9 : getr regs 25 = w64 (15 + Z.of_nat i);
r_frame : frame_cells W mem;
r_tmp : tmp_cells W mem t lz qb;
r_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells (b :: t))
}.
Record cdst (X : astate) (b : batch) (t : list batch) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
cd_acc : acc X W mem md;
cd_rix : RIx U 0 0 0 X [] t [b_self b];
cd_len : zlen t < 100000;
cd_cregs : common_regs regs;
cd_lregs : loop_regs regs;
cd_ra : getr regs 1 = w64 0x348c0;
cd_a0 : getr regs 10 = w64 (ly_T ly + t_cache);
cd_a1 : getr regs 11 = w64 A_ALLOCATOR;
cd_a2 : getr regs 12 = w64 kBatchClass;
cd_a3 : getr regs 13 = w64 (ly_space ly + b_self b);
cd_frame : frame_cells W mem;
cd_tmp : tmp_cells W mem t lz qb;
cd_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells t)
}.
Record qst (X : astate) (t : list batch) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
q_acc : acc X W mem md;
q_rix : RIx U 0 0 0 X [] t [];
q_len : zlen t < 100000;
q_cregs : common_regs regs;
q_lregs : loop_regs regs;
q_frame : frame_cells W mem;
q_tmp : tmp_cells W mem t lz qb;
q_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells t)
}.
Definition OST (X : astate) (rest : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x3483c regs mem md /\ ost X rest lz qb W regs mem md.
Definition RCST (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs A_RChunk regs mem md /\ rcst X b t its i lz qb W regs mem md.
Definition RST (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x34888 regs mem md /\ rst X b t its i lz qb W regs mem md.
Definition CDST (X : astate) (b : batch) (t : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs A_CDealloc regs mem md /\ cdst X b t lz qb W regs mem md.
Definition QST (X : astate) (t : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x348c0 regs mem md /\ qst X t lz qb W regs mem md.
Lemma SY_not_owned : forall X W mem md a, AR tfibsegs B ly X W mem md ->
ly_stk_lo ly + DRSTACK_X <= sp0 -> sp0 + 32 <= ly_stk_hi ly -> SY a -> ~ aowned B ly X a.
Proof. intros X W mem md a HA H1 H2 Ha. apply (AR_stack_law_ok tfibsegs B ly X W mem md a HA). unfold SY in Ha. lia. Qed.
End e.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The recycle invariant with the remaining batches folded into the chunk and object lists (DRq's form).           *)
Lemma RIx_fold : forall U s its P sel, RIx U 0 0 0 s its P sel -> RIx U 0 0 0 s (its ++ flat_map b_items P) [] (sel ++ map b_self P).
Proof.
intros U s its P sel (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold RIx. cbn [flat_map map]. rewrite !app_nil_r.
refine (conj A1 (conj A2 (conj A3 (conj (Forall_nil _) (conj A5 (conj A6 A7)))))).
Qed.
Lemma RIx_unfold : forall U s its P sel, RIx U 0 0 0 s (its ++ flat_map b_items P) [] (sel ++ map b_self P) ->
Forall (fun b => (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat) P -> RIx U 0 0 0 s its P sel.
Proof.
intros U s its P sel (A1 & A2 & A3 & A4 & A5 & A6 & A7) BL. unfold RIx. cbn [flat_map map] in *. rewrite !app_nil_r in *.
refine (conj A1 (conj A2 (conj A3 (conj BL (conj A5 (conj A6 A7)))))).
Qed.
End d.
