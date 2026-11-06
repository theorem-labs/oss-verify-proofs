(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc.
(* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_VirginDefs () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.N"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.r_cells"; "OSSVerify.KrLib.Heap.Malloc.get_shadow"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.list"; "Stdlib.ZArith.BinInt.Z.div"; "OSSVerify.KrLib.Heap.Malloc.r_hav"; "OSSVerify.KrLib.Heap.Malloc.r_havp"; "undersized"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "span_virgin"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.get_stride"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.m_mem"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc.m_sizeclass"; "OSSVerify.KrLib.Heap.Malloc.UNIT"; "OSSVerify.KrLib.Heap.Malloc.size_class"; "OSSVerify.KrLib.Heap.Malloc.m_avail"; "OSSVerify.KrLib.Heap.Malloc.m_freed"].


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition undersized (mr : meta) : Prop :=
  m_sizeclass mr < 48 -> get_stride mr < UNIT * size_class (m_sizeclass mr).

(* [comment removed for export] *)
Definition span_virgin (st : mstate) (rid : N) (S len : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_VirginDefs ()) "Po,$0.P,(1.(2.O2.R1.)(3.R1.(4.O2.O1.)))(1.(5.(6.(7.$0.$8.))(9.$0.(7.$0.$8.)(:.$0.$;.$<.(7.$0.$8.))(=.$0.$;.$<.(7.$0.$8.))R2.(>.(?.O4.O3.)))(10.(7.$0.$8.)))(1.(5.(6.(11.(7.$0.$8.)))(9.$0.(11.(7.$0.$8.))(:.$0.$;.$<.(11.(7.$0.$8.)))(=.$0.$;.$<.(11.(7.$0.$8.)))(12.R2.+10.)(13.(?.O4.O3.)))(10.(11.(7.$0.$8.))))(5.(6.$8.)(9.$0.$8.(:.$0.$;.$<.$8.)(=.$0.$;.$<.$8.)(12.R2.+1000.)(14.(?.O4.O3.)))(10.$8.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition under_virgin (st : mstate) (g b : aptr) (idx : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_VirginDefs ()) "P,(15.(16.O4.O3.))(17.O4.(18.$8.$0.O2.)(4.(4.(19.$8.$0.O2.)+10.)(1:.(1;.(16.O4.O3.))O1.))(1<.(1;.(16.O4.O3.))+4.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fact_under (cs : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_VirginDefs ()) "Pg,$1=.Pb,$1=.P,(5.$1>.(1?.(16.O1.R2.))(20.$1=.R1.))P,(3.(21.(16.O1.R3.))+30.)P,(3.(1;.(16.O1.R4.))(1:.$22.(23.(21.(16.O1.R4.)))))(1.(5.$0.(24.(16.O1.R5.))=)(5.$0.(25.(16.O1.R5.))=))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma span_virgin_read st rid S len o :
  span_virgin st rid S len -> S <= o < S + len -> cell_read (get_shadow st rid) o = Known 0.
Proof.
  intros V Ho. ddestruct (V o Ho) as (C & H & P). unfold cell_read. rewrite C, H, P. cbn. reflexivity.
Qed.

Lemma span_virgin_sub st rid S len S' len' :
  span_virgin st rid S len -> S <= S' -> S' + len' <= S + len -> span_virgin st rid S' len'.
Proof. intros V H1 H2 o Ho. apply V. lia. Qed.

