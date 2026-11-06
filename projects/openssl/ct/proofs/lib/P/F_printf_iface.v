(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel PrintfModelX.
From OSSVerify.Proofs.openssl.ct.lib.P Require Import Printf_lib F_memset F_memcpy F_fwritex F_pop_arg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition OUT_DEPTH : Z := 1024.        (* [comment removed for export] *)
Definition FMT_FP_DEPTH : Z := 4640.     (* [comment removed for export] *)
Definition PC_DEPTH : Z := 5184.         (* [comment removed for export] *)
Definition VF_DEPTH : Z := 5552.         (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SFILE_LO : Z := 0x2d7af8.      Definition SFILE_HI : Z := 0x2ebf38.
(* [comment removed for export] *)
Definition SBUF_LO : Z := 0x2ebf40.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sink.
  Context {St : Type}.
  Variables (Fp B BS : Z).
  Variable SINK : mem -> St -> Prop.
  Variable TOPOK : Z -> Prop.
  Variable OUT : list Z -> M St unit.
  Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.

  (* [comment removed for export] *)
  Definition SR : list (Z * Z) := [(Fp, Fp + 232); (B, B + BS)].
(* [comment removed for export] *)

(* [comment removed for export] *)


  Definition topok_stmt : Prop := forall a b, a <= b -> TOPOK b -> TOPOK a.
(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)

  Definition hd_cov (covs : list (option Z)) : option Z := match covs with [] => None | c :: _ => c end.




(* [comment removed for export] *)
(* [comment removed for export] *)

End Sink.
(* [comment removed for export] *)



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section SnSink.
  (* [comment removed for export] *)
  Variables (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (frest : list cell) (B TOP : Z).
  Definition SN_CAP : Z := 80.

  Definition TOPOK_sn (sp : Z) : Prop := sp <= TOP.

  Definition OUT_sn (bs : list Z) : M (list Z) unit :=
    o <- mget ;; if zlength o + zlength bs <=? SN_CAP then mput (o ++ bs) else munr.

  (* [comment removed for export] *)
  Definition OUTFP_sn (y w p fl t : Z) : M (list Z) Z := munr.
End SnSink.

(* [comment removed for export] *)
Definition TOPOK_none (sp : Z) : Prop := True.

