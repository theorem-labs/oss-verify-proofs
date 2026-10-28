(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK0i YP09 YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AF0x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition A_UnwindImpl : Z := 0x5a384.
Definition UNW_STK : Z := 144.
Definition BST_SIZE : Z := 2064.
Definition tfib_unwind_spec : Prop :=
forall (W : world tfibsegs) (ly : alayout) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(this pc0 bp ra0 nfp0 : Z) (ch : list (Z * Z * Z)),
let H := w_H W in let m := mrestrict H mem in
let sp := bv_unsigned (getr regs 2) in let T := ly_T ly in
layout_ok ly -> img_cover ly ->
getr regs 10 = Z_to_bv 64 this -> getr regs 11 = Z_to_bv 64 pc0 -> getr regs 12 = Z_to_bv 64 bp ->
getr regs 13 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 30 ->
getr regs 4 = Z_to_bv 64 TFIB_TP -> YK0s.ret_ok (getr regs 1) -> 0 <= pc0 < 2 ^ 64 ->
val_mem tfibsegs m 0xa6cd8 1 1 -> val_mem tfibsegs m 0xa5860 1 1 -> val_mem tfibsegs m 0xa5864 4 0 ->
val_mem tfibsegs m (TFIB_TP - 88) 8 TFIB_TSD -> val_mem tfibsegs m TFIB_TSD 8 (ly_C ly) ->
val_mem tfibsegs m (ly_C ly + 152) 8 T -> val_mem tfibsegs m (T + 40) 1 0 ->
val_mem tfibsegs m (T + 8) 8 (ly_top ly) -> val_mem tfibsegs m (T + 16) 8 (ly_bot ly) ->
val_mem tfibsegs m (T + t_unwinding) 1 0 -> apresent H mem (T + t_unwinding) ->
val_mem tfibsegs m 0x9df78 8 0x135aa0 -> val_mem tfibsegs m 0x135aa0 8 4096 ->
sp mod 16 = 0 -> ly_stk_lo ly <= sp - UNW_STK -> (forall a, sp - UNW_STK <= a < sp -> apresent H mem a) ->
this mod 8 = 0 -> ly_stk_lo ly <= this -> this + BST_SIZE <= sp - UNW_STK \/ sp <= this ->
(forall a, this <= a < this + BST_SIZE -> apresent H mem a) ->
this + BST_SIZE <= bp - 16 -> sp <= bp - 16 -> ly_bot ly < bp -> bp <= ly_stk_hi ly -> bp mod 8 = 0 ->
rdword (aview tfibsegs H mem) (bp - 8) = Some ra0 -> rdword (aview tfibsegs H mem) (bp - 16) = Some nfp0 -> 4096 <= ra0 ->
(if bp + 16 <? ly_top ly
then (if bad_next bp (ly_top ly) nfp0 then ch = [] else bp + 16 <= nfp0 /\ fpchain (rdword (aview tfibsegs H mem)) nfp0 (ly_top ly) ch)
else ch = []) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_UnwindImpl) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp - UNW_STK <= bv_unsigned x < sp) -> ~ (this + 8 <= bv_unsigned x < this + 12) ->
~ (this + 16 <= bv_unsigned x < this + 16 + 8 * 30) -> ~ (this + 2056 <= bv_unsigned x < this + BST_SIZE) ->
mem' x = mem x) /\
(forall a, apresent H mem a -> apresent H mem' a) /\
let tr := if bp + 16 <? ly_top ly then unwind_of_chain pc0 ((bp, ra0, nfp0) :: ch) else [pc0] in
val_mem tfibsegs (mrestrict H mem') (this + 8) 4 (Z.of_nat (length tr)) /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict H mem') (this + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
val_mem tfibsegs (mrestrict H mem') (this + 2056) 8 bp).
Definition A_StackDepotPut : Z := 0x724b0.
Definition DEP_STK : Z := 512.
Definition depot_after (z : Z) (tr : list Z) (S : astate) : astate :=
if z =? 0 then S else set_depot (st_depot S ++ [tr]) S.
Definition depot_footprint (B : asyms) (ly : alayout) (a : Z) : Prop :=
(as_depot B <= a < as_depot B + d_map1 + 8 * 32768) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/
(ly_SB ly <= a < ly_SB ly + kStoreBlockSize) \/ (as_store B <= a < as_store B + 64).
Definition depot_mem_ok (B : asyms) (ly : alayout) (S : astate) (rd : reader) : Prop :=
Forall (cell_holds B ly rd) (depot_cells ly S) /\ depot_ok B ly rd S /\
Forall (range_vis B ly rd) [(ADepot (d_nuniq + 4), 12); (AStore 8, 8); (AStore 24, 8); (ANB 0, kNodesBlockSize); (ASB 0, kStoreBlockSize)].
Definition tfib_depot_spec (B : asyms) : Prop :=
forall (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (buf : Z) (tr : list Z),
let H := w_H W in let rd := aview tfibsegs H mem in let sp := bv_unsigned (getr regs 2) in
layout_ok ly -> img_cover ly   -> Wf (as_universe B) S -> In tr (as_universe B) ->
Forall (cell_holds B ly rd) (as_const B ly) -> depot_mem_ok B ly S rd ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 TFIB_TP -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict H mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly -> buf + 8 * 30 <= sp - DEP_STK \/ sp <= buf ->
sp mod 16 = 0 -> ly_stk_lo ly <= sp - DEP_STK -> sp <= ly_stk_hi ly -> (forall a, sp - DEP_STK <= a < sp -> apresent H mem a) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
aok S (KDepot tr) z /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp - DEP_STK <= bv_unsigned x < sp) -> ~ depot_footprint B ly (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent H mem a -> apresent H mem' a) /\
depot_mem_ok B ly (depot_after z tr S) (aview tfibsegs H mem') /\
Forall (cell_holds B ly (aview tfibsegs H mem')) (as_const B ly)).
End b.
