(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep MallocTree MallocFacts_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocNat.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MallocFacts_AS () : Init.string Init.list := ["Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Heap.MallocTree.mem"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "Corelib.Init.Datatypes.nat"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "IST"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "req_ok"; "OSSVerify.KrLib.Heap.MallocTree.leaf_of"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.Malloc.alloc_slot"; "OSSVerify.KrLib.Heap.Malloc.full_lay"; "OSSVerify.KrLib.Heap.MallocNat.kS"; "OSSVerify.KrLib.Heap.MallocNat.bS"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.m_mem"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "OSSVerify.KrLib.Heap.Malloc.m_next"; "OSSVerify.KrLib.Heap.Malloc.m_prev"; "OSSVerify.KrLib.Heap.Malloc.active"; "lmem"; "OSSVerify.KrLib.Heap.Malloc.m_sizeclass"; "OSSVerify.KrLib.Heap.Malloc.c_free_meta_head"; "OSSVerify.KrLib.Heap.Malloc.ctx"; "OSSVerify.KrLib.Heap.MallocRep.meta_slot"; "OSSVerify.KrLib.Heap.Malloc.m_last_idx"; "OSSVerify.KrLib.Heap.Malloc.m_freeable"; "OSSVerify.KrLib.Heap.Malloc.m_maplen"; "Stdlib.ZArith.BinInt.Z.pow"; "mw_ok"; "OSSVerify.KrLib.Heap.Malloc.m_avail"; "OSSVerify.KrLib.Heap.Malloc.m_freed"; "OSSVerify.KrLib.Heap.Malloc.get_stride"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.UNIT"; "OSSVerify.KrLib.Heap.Malloc.size_class"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "OSSVerify.KrLib.Heap.Malloc.g_active_idx"; "OSSVerify.KrLib.Heap.Malloc.cellval"; "OSSVerify.KrLib.Heap.Malloc.cell_read"; "OSSVerify.KrLib.Heap.Malloc.get_shadow"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.snd"; "OSSVerify.KrLib.Heap.Malloc.Unknown"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.orb"; "Stdlib.ZArith.BinInt.Z.testbit"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Heap.Malloc.meta"; "OSSVerify.KrLib.Heap.Malloc.meta0"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Heap.MallocBlocks.block"; "OSSVerify.KrLib.Heap.MallocBlocks.AREACH_from"; "ta_fail"].


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ta_fail (sc : Z) (st st1 : mstate) : Prop :=
  try_avail sc st kS bS = SRet (Some (st1, 0)).

(* [comment removed for export] *)
Definition req_ok (sc req : Z) : Prop := 0 <= req /\ req + IB <= UNIT * size_class sc.

(* [comment removed for export] *)
Inductive IST (st0 : mstate) : mstate -> Prop :=
| ist_top : forall t, (s_tick st0 < t)%N -> IST st0 (set_tick t st0)
| ist_am : forall o st sc st1 st2 m,
    IST st0 st -> 0 <= sc < 48 -> ta_fail sc st st1 ->
    leaf_of o (alloc_meta st1 kS bS) (Some (st2, Some m)) ->
    IST st0 st2.

(* [comment removed for export] *)
Definition ISTR (st0 st3 : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_AS ()) "(0.$1.Lo,$1.(0.$2.Lst,$2.(0.$3.Lf,$3.(0.$4.Lsc,$4.(0.$4.Lreq,$4.(0.$4.Lidx,$4.(5.(6.O2.R5.)(5.(5.(7.=R3.)(8.R3.+30.))(5.(9.R3.R2.)(:.(;.(<.$2.$4.))R6.(=.(;.(<.$2.$4.))$>.R4.R5.R3.R2.(?.$2.$4.)(10.(<.$2.$4.)))(11.(<.$2.$4.)(12.$2.$4.O1.R1.))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lmem (cs : mstate) (g : aptr) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_AS ()) "(5.(13.(14.$15.(16.(17.O2.O1.))(18.$19.)))(5.(13.(14.$15.(1:.(17.O2.O1.))(18.$19.)))(13.(14.$15.(1;.(17.O2.O1.))(18.$19.)))))")
(* [comment removed for export] *).

Definition fact_lists (cs : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_AS ()) "(5.Psc,$4.Pg,$19.P,(14.$15.(1<.O1.R2.)(11.$19.R1.))(1=.O1.R2.)(5.Pg,$19.Pn,$19.P,(13.(14.$15.(16.(17.O1.R2.))(18.$19.)))P,(14.$15.(1:.(17.O1.R3.))(11.$19.R2.))(5.(1=.O1.R3.)(14.$4.(1>.(17.O1.R3.))(1>.(17.O1.R4.))))Pg,$19.Pp,$19.P,(13.(14.$15.(16.(17.O1.R2.))(18.$19.)))P,(14.$15.(1;.(17.O1.R3.))(11.$19.R2.))(5.(1=.O1.R3.)(14.$4.(1>.(17.O1.R3.))(1>.(17.O1.R4.))))))")
(* [comment removed for export] *).

Definition fact_freelist (cs : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_AS ()) "Ph,$19.P,(14.$15.(1?.(20.O1.))(11.$19.R1.))(5.(21.O1.R2.)(5.(14.$15.(16.(17.O1.R2.))(18.$19.))(5.(13.(14.$15.(1:.(17.O1.R2.))(18.$19.)))(0.$19.Lp,$19.(5.(14.$15.(1;.(17.O1.R3.))(11.$19.R1.))(5.(21.O1.R1.)(5.(14.$15.(16.(17.O1.R1.))(18.$19.))(13.(14.$15.(1:.(17.O1.R1.))(18.$19.))))))))))")
(* [comment removed for export] *).

Definition mw_ok (mr : meta) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_AS ()) "(5.(5.(7.=(22.O1.))(7.(22.O1.)+1?.))(5.(5.(7.=(23.O1.))(7.(23.O1.)+1.))(5.(5.(7.=(1>.O1.))(7.(1>.O1.)+3?.))(5.(7.=(24.O1.))(8.(24.O1.)(25.+2.+34.))))))")
(* [comment removed for export] *).

Definition fact_mw (cs : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_AS ()) "Pg,$19.(5.(26.(17.O1.R1.))(5.(5.(7.=(27.(17.O1.R1.)))(8.(27.(17.O1.R1.))(25.+2.+20.)))(5.(7.=(28.(17.O1.R1.)))(8.(28.(17.O1.R1.))(25.+2.+20.)))))")
(* [comment removed for export] *).

Definition fact_host_stride (cs : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_AS ()) "Pg,$19.Pb,$19.P,(14.$15.(16.(17.O1.R2.))(11.$19.R1.))P,(5.(7.=(1>.(17.O1.R3.)))(7.(1>.(17.O1.R3.))+1;.))(14.$4.(29.(17.O1.R4.))(2:.$2;.(2<.(1>.(17.O1.R4.)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fact_links (cs : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_AS ()) "Pg,$19.P,(1=.O1.R1.)(5.Pn,$19.P,(14.$15.(1:.(17.O1.R3.))(11.$19.R1.))(14.$15.(1;.(17.O1.R2.))(11.$19.R4.))Pp,$19.P,(14.$15.(1;.(17.O1.R3.))(11.$19.R1.))(14.$15.(1:.(17.O1.R2.))(11.$19.R4.)))")
(* [comment removed for export] *).

Definition fact_sc0_full (cs : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_AS ()) "Pg,$19.Pb,$19.Pgh,$2=.P,(14.$15.(16.(17.O1.R3.))(11.$19.R2.))P,(14.(;.$2=.)(2>.$19.$2=.(2?.$19.(30.$31.$32.$4.$33.)(34.$31.$32.$35.$4.$33.$36.)$2=.)(37.$19.(30.$31.$32.$4.$33.)(34.$31.$32.$35.$4.$33.$36.)$2=.)R3.(38.O1.))(11.$2=.R2.))P,(14.$4.(1>.(17.O1.R5.))=)(14.$4.(39.R4.)(22.(17.O1.R6.)))")
(* [comment removed for export] *).

Definition fact_ghdr_unk (st : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_AS ()) "Pb,(<.$31.$4.)Pgh,$2=.Po,$4.P,(14.(;.$2=.)(2>.(<.$31.$4.)$2=.(2?.$19.(30.$31.$32.$4.$33.)(34.$31.$32.$35.$4.$33.$36.)$2=.)(37.$19.(30.$31.$32.$4.$33.)(34.$31.$32.$35.$4.$33.$36.)$2=.)R3.(38.O1.))(11.$2=.R2.))P,(5.(7.=R2.)(8.R2.+9.))(0.$4.Lh,$4.(14.$3:.(3;.(3<.O1.(3=.$31.$4.R6.))(3>.(3?.$31.$4.R6.)R4.))(40.R1.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fact_bit_stride (cs : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_AS ()) "Pg,$19.Pb,$19.Pi,$4.P,(14.$15.(16.(17.O1.R3.))(11.$19.R2.))P,(7.=R2.)P,(14.$41.(42.(43.(27.(17.O1.R5.))R3.)(43.(28.(17.O1.R5.))R3.))$44.)P,(8.(1>.(17.O1.R6.))+30.)(7.(2:.$2;.(2<.(1>.(17.O1.R7.))))(29.(17.O1.R7.)))")
(* [comment removed for export] *).

Record LFACTS (cs : mstate) : Prop := mkLF {
  lf_lists : fact_lists cs;
  lf_freelist : fact_freelist cs;
  lf_mw : fact_mw cs;
  lf_host_stride : fact_host_stride cs;
  lf_links : fact_links cs;
  lf_sc0_full : fact_sc0_full cs;
  lf_bit_stride : fact_bit_stride cs
}.

(* [comment removed for export] *)
Record ISTF_g {resv : list (Z * Z)} (st : mstate) (LB : list block) : Prop := mkISTF {
  isf_mf : @MFACTS_g resv st LB;
  isf_lf : LFACTS (strip st);
  isf_ghdr : fact_ghdr_unk st
}.

(* [comment removed for export] *)
Notation ISTF := (@ISTF_g agent_reserved).


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nest_ok (m : aptr) (st3 : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_AS ()) "(5.(14.$45.(17.O1.O2.)$46.)Ph,$19.P,(14.$15.(1?.(20.O1.))(11.$19.R1.))(5.(13.(14.$19.R2.O2.))(13.(14.$15.(1;.(17.O1.R2.))(11.$19.O2.)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AMP_AS_g (resv : list (Z * Z)) (am_pre : mstate -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_AS ()) "Pst0,$2.PLB,(47.$48.)Pst,$2.Psc,$4.Pst1,$2.P,(49.O2.R5.R4.)P,(6.R6.R4.)P,(5.(7.=R4.)(8.R4.+30.))P,(4:.R5.R6.R4.)A1.O1.R5.")
(* [comment removed for export] *).
Notation AMP_AS := (AMP_AS_g agent_reserved).

