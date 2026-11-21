(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (2 recorded proofs replaced by written proofs (meta_word_upd_af, decay_bounces_eq)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A3 ASlot_W1.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_W3 () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_wordC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3lebK47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc:set_bounceC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01".
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.

Section CANSEC1. Context {rc : runConstT}.
Lemma meta_word_upd_af mr a f' : meta_word (m_set_avail a (m_set_freed f' mr)) = meta_word mr.
Proof. reflexivity. Qed.

Lemma decay_bounces_eq sc st :
  decay_bounces sc st =
  if ((7 <=? sc) && (sc <? 39)) && negb (bounces st (sc - 7) =? 0) then set_bounce (sc - 7) (bounces st (sc - 7) - 1) st else st.
Proof. reflexivity. Qed.

Section AVZ.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Let ai := g_active_idx gh.
Let act := mask_upto ai.
Let mask := Z.land f act.
Let st4 := upd_meta g (fun r => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) st.
Let st5 := decay_bounces (m_sizeclass mr) st4.
Hypothesis MSL : meta_slot st g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI : 0 <= ai <= 31.
Hypothesis FR32 : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.
Hypothesis MASK : mask <> 0.
Hypothesis BNC : forall i, 0 <= bounces st i < 256.
End AVZ.


End CANSEC1.
