(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMrecL.v (commit 67deba317dfb, blob 279fef9968c9) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 5 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YP09 YN3v YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AF0x AFl1 AFeq AFeu AFf2 AFh9 AFhd.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMwalkIFA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG MemnormT.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variables (ly : alayout) (X0 : astate) (W0 : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Local Notation sp0 := (AFhd.sp0 regs0).
Local Notation sp1 := (AFhd.sp1 regs0).
Local Notation DRSTACK_X := DMwalkIFA.DRSTACK_X.

Definition SYr (a : Z) : Prop := sp0 - DRSTACK_X <= a < sp0 + 32.

Record accr (X : astate) (W : world tfibsegs) (mem : word -> option byte) (md : Model) : Prop := {
ar_AR : ARXr (as_inst B) ly X W mem md;
ar_wle : wle W0 W;
ar_io : same_io md0 md;
ar_own : forall a, AOX ly X a -> AOX ly X0 a;
ar_frame : forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly X0 a -> ~ AOX ly X a -> ~ ascratch B DRSTACK_X regs0 a -> ~ (sp0 <= a < sp0 + 32) ->
  aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W0) mem0 a;
ar_pres : forall a, SYr a -> apresent (w_H W) mem a;
ar_inited : st_cache_inited X = true;
ar_raw : forall x : word, ~ AOX ly X0 (bv_unsigned x) -> ~ AOX ly X (bv_unsigned x) -> ~ ascratch B DRSTACK_X regs0 (bv_unsigned x) ->
  ~ (sp0 <= bv_unsigned x < sp0 + 32) -> mem x = mem0 x;
ar_ek : ErrnoG.errno_kept B mem0 mem;
ar_mk : MemnormT.memnorm_keep tfibsegs mem0 mem
}.
Local Notation common_regs := (AFhd.common_regs regs0).
Local Notation loop_regs := (AFhd.loop_regs regs0).
Local Notation frame_cells := (AFhd.frame_cells ly regs0).
Local Notation tmp_cells := (AFhd.tmp_cells ly regs0).
Local Notation batch_regs := (AFhd.batch_regs ly).
Local Notation zlen := (@AFhd.zlen _).
Local Notation hdra := (AFhd.hdra B ly).

Definition blen_ok (P : list batch) : Prop := Forall (fun b => (length (b_items b) <= Z.to_nat kBatchSlots)%nat) P.

Record ostr (X : astate) (rest : list batch) (lz qb : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
o_acc : accr X W mem md;
o_drq : DRq X (flat_map b_items rest) (map b_self rest);
o_bl : blen_ok rest;
o_ne : rest <> [];
o_len : zlen rest < 2 ^ 40;
o_cregs : common_regs regs;
o_lregs : loop_regs regs;
o_a0 : getr regs 10 = w64 (zlen rest);
o_frame : frame_cells W mem;
o_tmp : tmp_cells W mem rest lz qb;
o_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells rest)
}.

Record rcstr (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
rc_acc : accr X W mem md;
rc_drq : DRq X (its ++ flat_map b_items t) (b_self b :: map b_self t);
rc_bl : blen_ok t;
rc_items : exists done, b_items b = done ++ its /\ length done = i;
rc_ne : its <> [];
rc_blen : (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat;
rc_len : zlen t < 2 ^ 40;
rc_cregs : common_regs regs;
rc_lregs : loop_regs regs;
rc_bregs : batch_regs regs b;
rc_ra : getr regs 1 = w64 0x3479c;
rc_a0 : getr regs 10 = w64 (sp1 + 8);
rc_a1 : forall k ks, its = k :: ks -> getr regs 11 = w64 (hdra k);
rc_s7 : getr regs 23 = w64 (ly_space ly + b_self b + 152 + 8 * Z.of_nat i);
rc_s9 : getr regs 25 = w64 (16 + Z.of_nat i);
rc_frame : frame_cells W mem;
rc_tmp : tmp_cells W mem t lz qb;
rc_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells (b :: t))
}.

Record rstr (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
r_acc : accr X W mem md;
r_drq : DRq X (its ++ flat_map b_items t) (b_self b :: map b_self t);
r_bl : blen_ok t;
r_items : exists done, b_items b = done ++ its /\ length done = i;
r_i : (1 <= i)%nat;
r_blen : (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat;
r_len : zlen t < 2 ^ 40;
r_cregs : common_regs regs;
r_lregs : loop_regs regs;
r_bregs : batch_regs regs b;
r_s7 : getr regs 23 = w64 (ly_space ly + b_self b + 144 + 8 * Z.of_nat i);
r_s9 : getr regs 25 = w64 (15 + Z.of_nat i);
r_frame : frame_cells W mem;
r_tmp : tmp_cells W mem t lz qb;
r_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells (b :: t))
}.

Record cdstr (X : astate) (b : batch) (t : list batch) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
cd_acc : accr X W mem md;
cd_drq : DRq X (flat_map b_items t) (b_self b :: map b_self t);
cd_bl : blen_ok t;
cd_len : zlen t < 2 ^ 40;
cd_cregs : common_regs regs;
cd_lregs : loop_regs regs;
cd_ra : getr regs 1 = w64 0x347d4;
cd_a0 : getr regs 10 = w64 (ly_T ly + t_cache);
cd_a1 : getr regs 11 = w64 A_ALLOCATOR;
cd_a2 : getr regs 12 = w64 kBatchClass;
cd_a3 : getr regs 13 = w64 (ly_space ly + b_self b);
cd_frame : frame_cells W mem;
cd_tmp : tmp_cells W mem t lz qb;
cd_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells t)
}.

Record qstr (X : astate) (t : list batch) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
q_acc : accr X W mem md;
q_drq : DRq X (flat_map b_items t) (map b_self t);
q_bl : blen_ok t;
q_len : zlen t < 2 ^ 40;
q_cregs : common_regs regs;
q_lregs : loop_regs regs;
q_frame : frame_cells W mem;
q_tmp : tmp_cells W mem t lz qb;
q_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells t)
}.
Definition OSTr (X : astate) (rest : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x34750 regs mem md /\ ostr X rest lz qb W regs mem md.
Definition RCSTr (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs A_RChunk regs mem md /\ rcstr X b t its i lz qb W regs mem md.
Definition RSTr (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x3479c regs mem md /\ rstr X b t its i lz qb W regs mem md.
Definition CDSTr (X : astate) (b : batch) (t : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs A_CDealloc regs mem md /\ cdstr X b t lz qb W regs mem md.
Definition QSTr (X : astate) (t : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x347d4 regs mem md /\ qstr X t lz qb W regs mem md.
End e.

Lemma blen_ok_cons : forall b P, blen_ok (b :: P) <-> (length (b_items b) <= Z.to_nat kBatchSlots)%nat /\ blen_ok P.
Proof. intros b P. unfold blen_ok. rewrite Forall_cons_iff. tauto. Qed.
End d.
