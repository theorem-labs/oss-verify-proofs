(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AFeu.v, with its module paths changed; 74 of its 98 lines of code are new or changed and 258 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/ImgBaseDG.v (commit 30a1993588f, c5 + memnorm; file sha256 9ec73d89c58a) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/ImgBaseDG.v (commit d2dafa219c1, file sha256 43a67585007e) onto plugin-hostd/fuzz_reply's asan-ubsan image (unstripped fuzz_reply.asan-ubsan, sha256 3389287e1d61; pin 10ffb5f9202a) by alreloc ced0368250cb6538 (A -> B, direct map 541d2a13b9d2): 0 numerals moved; module paths lib.A -> lib.B and the image twins A<r> -> Y<r>. *)
(* The image-free base of the Deallocate interface DGif0.DIface and its drain contract (DMspec / DMiface), beside
   ImgBase.

   - [DImg]: the facts about the binary's image that these files name and ImgBase.AImg does not hold.  They take it
     as [Context {IM : AImg} {DI : DImg}], so a consumer's explicit arguments do not move; the image file of a binary
     declares the instance (cgif_file: DGif0cgif.DImg_cgif).
   - copies of the image-free names they borrow from image files (DGgi / DGgm geometry, the stack sizes, the depot
     answer, the drain tree and the drain's cell / region names).  Each copy is byte-identical to its original, in a
     module named after the original's file (DGgiC.Bv is the copy of DGgi.Bv), so a copy and its original are
     convertible and the walk files and their proofs are untouched. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG06 YG03 YG0f YG0v YG0n YG0d YG0k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The image facts of the Deallocate interface.                                                                     *)
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg}.
Class DImg : Type := MkDImg {
  (* the constant cells' zone: the cells of [as_const] lie here (cgif: AGif0cgif.CZONE) *)
  dg_czone : alayout -> Z -> Prop;
  (* the allocator instance object lies in the image's data (cgif: AGif0cgif.inst_ok) *)
  dg_inst_ok : Z -> Prop;
  (* the depot's zone: its static data, the nodes block and the store block (cgif: DGgi.DZONE) *)
  dg_dzone : alayout -> Z -> Prop;
  (* the internal allocator's zone (cgif: DGgi.IZONE) *)
  dg_izone : Z -> Prop;
  (* the internal allocator is initialized (cgif: DGgi.IAL_POST) *)
  dg_ial_post : world im_segs -> (word -> option byte) -> Prop;
  (* [sz] bytes at [x] lie in an application zone off the image (cgif: YF0x.zone3) *)
  dg_zone3 : Z -> Z -> Prop;
  (* the entry pcs of StackDepotPut and QuarantineCache::Enqueue (cgif: YFl0.A_StackDepotPut, YFew.A_Enqueue) *)
  dg_depot : Z;
  dg_enqueue : Z;
  (* the entry pcs of Quarantine::Drain, QuarantineCallback::Recycle and CacheDealloc, which the drain contract
     DMspec / DMiface names (cgif: YFeu.A_Drain, A_RChunk, A_CDealloc) *)
  dg_drain : Z;
  dg_rchunk : Z;
  dg_cdealloc : Z
}.
End i.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Copies of image-free names from image files.                                                                     *)
Module DGbaseC.
(* copy of DGbase.v:26, remove when DGbase.v is ported *)
Definition DFSTACK : Z := 8192.
End DGbaseC.

Module YFewC.
(* copy of YFew.v:22, remove when YFew.v is ported *)
Definition QSTACK : Z := 1088.
End YFewC.

Module YFl0C.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* copy of YFl0.v:58, remove when YFl0.v is ported *)
Definition DEP_STK : Z := 512.
(* copy of YFl0.v:59, remove when YFl0.v is ported *)
Definition depot_after (z : Z) (tr : list Z) (S : astate) : astate :=
if z =? 0 then S else set_depot (st_depot S ++ [tr]) S.
End b.
End YFl0C.

Module YFeuC.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
(* copy of YFeu.v:155, remove when YFeu.v is ported *)
Definition DSTACK : Z := 4096.
(* copy of YFeu.v:156, remove when YFeu.v is ported *)
Definition transfer_g (X : astate) : qcache :=
mkQC (qc_list (st_qglobal X) ++ qc_list (st_qthread X)) (qc_bytes (st_qglobal X) + qc_bytes (st_qthread X)).
(* copy of YFeu.v:158, remove when YFeu.v is ported *)
Definition recycle_body (g : qcache) : M unit :=
mcheck (2 * (kBatchBytes * Z.of_nat (length (qc_list g))) <=? qc_bytes g) 209280 ;;
let '(g', popped) := pop_batches 100000%nat g [] in
modify (set_qglobal g') ;;
do_recycle 100000%nat popped.
(* copy of YFeu.v:163, remove when YFeu.v is ported *)
Definition drain_body (X : astate) : M unit :=
let g := transfer_g X in
put (set_qglobal g (set_qthread qc0 X)) ;;
(if qc_bytes g <=? kQuarantineMax then ret tt else recycle_body g).
(* copy of YFeu.v:211, remove when YFeu.v is ported *)
Definition plist_cells (tmp : Z) (P : list batch) : list acell :=
qc_cells (ANum tmp) (mkQC P (sum_bytes P)).
(* copy of YFeu.v:247, remove when YFeu.v is ported *)
Definition puser (ly : alayout) (X : astate) (a : Z) : Prop :=
exists c, 1 <= c <= 31 /\ region_base ly c <= a < region_base ly c + rg_alloc_user (reg X c).
End d.
End YFeuC.

(* The geometry of the Deallocate arm whose last batch has room, over DGgi's section variables (in DGgi's order). *)
Module DGgiC.
Section WF.
Variables (ly : alayout).
Variables (p nn : Z) (q : qcache) (lastb : batch).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
(* copy of DGgi.v:63, remove when DGgi.v is ported *)
Definition SPv : Z := SHADOW_OFF + p / 8.
(* copy of DGgi.v:64, remove when DGgi.v is ported *)
Definition N8v : Z := (nn + 7) / 8 * 8.
(* copy of DGgi.v:65, remove when DGgi.v is ported *)
Definition CNT8v : Z := N8v / 8.
(* copy of DGgi.v:66, remove when DGgi.v is ported *)
Definition Bv : Z := SB + b_self lastb.
(* copy of DGgi.v:67, remove when DGgi.v is ported *)
Definition BBv : Z := b_bytes lastb.
(* copy of DGgi.v:68, remove when DGgi.v is ported *)
Definition BCv : Z := Z.of_nat (length (b_items lastb)).
(* copy of DGgi.v:69, remove when DGgi.v is ported *)
Definition SLOTv : Z := Bv + 24 + 8 * BCv.
(* copy of DGgi.v:70, remove when DGgi.v is ported *)
Definition QSv : Z := Z.of_nat (length (qc_list q)).
(* copy of DGgi.v:71, remove when DGgi.v is ported *)
Definition QFv : Z := match qc_list q with [] => 0 | b :: _ => SB + b_self b end.
(* copy of DGgi.v:72, remove when DGgi.v is ported *)
Definition QBv : Z := qc_bytes q.
(* copy of DGgi.v:113, remove when DGgi.v is ported *)
Definition PSTATIC : Prop := forall a, p - 16 <= a < p + N8v ->
~ (ly_stk_lo ly <= a < ly_stk_hi ly) /\ ~ (T <= a < T + kThreadObjSize) /\ ~ (ly_C ly <= a < ly_C ly + 256) /\
~ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) /\ ~ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) /\
~ (ly_D ly <= a < ly_D ly + 4096)  .
(* copy of DGgi.v:117, remove when DGgi.v is ported *)
Definition PBDISJ : Prop := Bv + kBatchBytes <= p - 16 \/ p + N8v <= Bv.
(* copy of DGgi.v:344, remove when DGgi.v is ported *)
Definition WINT (a : Z) : Prop :=
(T + t_qc <= a < T + t_qc + 32) \/ (T + t_unwinding <= a < T + t_unwinding + 1) \/ (T + t_stats + 24 <= a < T + t_stats + 40).
(* copy of DGgi.v:346, remove when DGgi.v is ported *)
Definition WINB (a : Z) : Prop := (p - 16 <= a < p - 8) \/ (p <= a < p + 8) \/ (Bv + 8 <= a < Bv + 24) \/ (SLOTv <= a < SLOTv + 8).
End WF.
End DGgiC.

(* The windows of the Deallocate arms that open a new batch or drain, over DGgm's section variables. *)
Module DGgmC.
Section WF.
Variables (ly : alayout).
Variables (p : Z).
Let T : Z := ly_T ly.
(* copy of DGgm.v:331, remove when DGgm.v is ported *)
Definition WINT (a : Z) : Prop := (T + t_unwinding <= a < T + t_unwinding + 1) \/ (T + t_stats + 24 <= a < T + t_stats + 40).
(* copy of DGgm.v:332, remove when DGgm.v is ported *)
Definition WINB (a : Z) : Prop := (p - 16 <= a < p - 8) \/ (p <= a < p + 8).
End WF.
End DGgmC.
