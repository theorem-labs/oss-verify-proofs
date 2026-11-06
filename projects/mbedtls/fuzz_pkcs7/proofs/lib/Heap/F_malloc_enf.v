(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_F_malloc_enf () : Init.string Init.list := ["Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.get_stride"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "Corelib.Init.Datatypes.pair"; "Corelib.Numbers.BinNums.N"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "OSSVerify.KrLib.Heap.Malloc.havoc"; "OSSVerify.KrLib.Heap.Malloc.enframe_at"; "OSSVerify.KrLib.Heap.Malloc.fold_off"; "enf_off0"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.sub"].



(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition enf_off0 (o : mem) (st1 : mstate) (b : aptr) (stride idx : Z) : Z :=
  let q := snd b + (16 + stride * idx) in
  if rdv pans_mem o st1 (fst b, q + -3) =? 0 then Z.land (c_mmap_counter (ctx st1)) 255
  else Z.land (rdv pans_mem o st1 (fst b, q + -2) + 256 * rdv pans_mem o st1 (fst b, q + -2 + 1) + 1) 255.

Definition enf_leaf (o : mem) (st1 : mstate) (g b : aptr) (idx n : Z) (st' : mstate) (p : aptr) : Prop := ltac2:(CDefT.buildp (gd_tbl_F_malloc_enf ()) "(0.$1.Loff,$1.(2.(3.=R1.)(2.(3.(4.(4.(5.+10.R1.)O3.)+4.)(6.(7.O7.O6.)))(2.(8.$9.O1.(:.$;.$1.(<.$;.$1.O5.)(4.(4.(4.(=.$;.$1.O5.)+10.)(5.(6.(7.O7.O6.))O4.))(5.+10.R1.))))(2.(8.$>.O2.(?.O1.O3.(<.$>.$9.(10.O7.O6.O4.O3.R1.))))(2.(8.$9.O1.(=.$>.$9.(10.O7.O6.O4.O3.R1.)))(8.$1.R1.(11.(12.O8.O7.O5.(6.(7.O7.O6.))O4.)(13.(14.(14.(6.(7.O7.O6.))+4.)O3.)+10.)))))))))")
(* [comment removed for export] *).


Lemma surj_pair_let {A B C'} (e : A * B) (f : A -> B -> C') : (let '(x, y) := e in f x y) = f (fst e) (snd e).
Proof. destruct e; reflexivity. Qed.

