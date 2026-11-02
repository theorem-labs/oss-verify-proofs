(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN25.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition NT_FRAME : Z := 96.
Definition used_metasX (X : list sptr) (s : astate) : list (sptr * ameta) :=
List.filter (fun gm => negb (memb (fst gm) X)) (used_metas s).
Definition imageX (X : list sptr) (s : astate) : list mcell :=
ctx_cells s ++ areas_cells s (st_areas s)
++ flat_map (fun gm : sptr * ameta => group_cells (fst gm) (snd gm)) (used_metasX X s).
Definition tail_cellsX (X : list sptr) (s : astate) : list mcell :=
flat_map (fun gm : sptr * ameta => group_tail_cells (snd gm)) (used_metasX X s).
Section d.
Variable B : malloc_syms.
Definition memrepX (X : list sptr) (L : layout) (A : astate) (mem : word -> option byte) : Prop :=
Forall (cell_mem B L mem) (imageX X A) /\
Forall (cell_mem B L mem) (tail_cellsX X A) /\
Forall (foot_ok L mem) (footprint A).
Lemma filter_all {T} (f : T -> bool) (l : list T) : (forall x, f x = true) -> List.filter f l = l.
Proof. intros Hf. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite Hf. f_equal. exact IH. Qed.
Lemma used_metasX_nil s : used_metasX [] s = used_metas s.
Proof. unfold used_metasX. apply filter_all. intros x. reflexivity. Qed.
Lemma memrepX_nil L A mem : memrepX [] L A mem <-> memrep B L A mem.
Proof. unfold memrepX, memrep, imageX, tail_cellsX, image, tail_cells. rewrite used_metasX_nil. tauto. Qed.
End d.
Section e.
Variable B : malloc_syms.
Let segs := ms_segs B.
Definition nt_pre (X : list sptr) (fuel : nat) (L : layout) (A : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (g : sptr) (i : Z) : Prop :=
syms_ok B /\ layout_ok L A /\ ly_ctx L = ms_ctx B /\ 0 <= ly_sec L < 2 ^ 64   /\
memrepX B X L A mem /\ statics_ok B mem /\ ledger_ok B L A md /\
m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [] /\
getr regs 10 = Z_to_bv 64 (ptr_addr L g) /\ getr regs 11 = Z_to_bv 64 i /\
YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ alloc_ceiling + NT_FRAME * Z.of_nat fuel <= spZ regs /\ spZ regs < 2 ^ 63 /\
(forall a, spZ regs - NT_FRAME * Z.of_nat fuel <= a < spZ regs -> writable_at segs mem a) /\
getr regs 4 = Z_to_bv 64 (ms_tp B).
Definition nt_post (X : list sptr) (fuel : nat) (L : layout) (A : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model)
(r : option (nat * Z) * astate) (c' : config) : Prop :=
exists regs' mem',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md /\
memrepX B X L (snd r) mem' /\ statics_ok B mem' /\
regs_preserved regs regs' /\
getr regs' 10 = Z_to_bv 64 (match fst r with Some (k, _) => ly_reg L k | None => 0 end) /\
getr regs' 11 = Z_to_bv 64 (match fst r with Some (_, len) => len | None => 0 end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ alloc_owned L A a -> ~ (spZ regs - NT_FRAME * Z.of_nat fuel <= a < spZ regs) ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall a, spZ regs - NT_FRAME * Z.of_nat fuel <= a < spZ regs -> writable_at segs mem' a).
Definition ntfree_hyp : Prop :=
forall (fuel : nat) X U L A g i am regs mem md,
Inv X (Some (g, i)) U A -> usedX X A g am -> (forall c, 0 <= U c) ->
((am_prev am, am_next am) <> (None, None) -> active_hd A (am_sc am) <> Some g -> am_freed am <> 0) ->
(fneed (am_sc am) <= fuel)%nat -> bounded A ->
nt_pre X fuel L A regs mem md g i ->
mreal segs (mkCfg (mkst regs (Z_to_bv 64 (pc_nontrivial_free (ms_pcs B))) mem (seg_rom segs)) md)
(nontrivial_free fuel g i A)
(nt_post X fuel L A regs mem md).
End e.
End b.
