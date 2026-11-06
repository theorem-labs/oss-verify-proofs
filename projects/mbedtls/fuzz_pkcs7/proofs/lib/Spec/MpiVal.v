(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MpiVal () : Init.string Init.list := ["Corelib.Init.Logic.and"; "OSSVerify.KrLib.Spec.Rep.mpi_at"; "md_addr"; "stdpp.bitvector.definitions.Z_to_bv"; "md_sg"; "md_n"; "md_p"; "md_limbs"; "md_pad"; "md_own"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Stdlib.Lists.List.In"; "mpd_blk"; "Corelib.Init.Datatypes.list"].


Record mpd := mkMPD {
  md_addr : Z;            (* [comment removed for export] *)
  md_sg : Z;              (* [comment removed for export] *)
  md_n : Z;               (* [comment removed for export] *)
  md_p : Z;               (* [comment removed for export] *)
  md_limbs : list word;
  md_pad : word;
  md_own : limb_own }.

Definition mpd_at (segs : list Segment) (m : mem) (LB : list blk) (d : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_MpiVal ()) "(0.(1.O4.O3.O2.(2.O1.)(3.&40.(4.O1.))(5.O1.)(6.O1.)(7.O1.)(8.O1.)(9.O1.))(:.(;.$<.(4.O1.)+1.)(;.$<.(4.O1.)-1.)))")
(* [comment removed for export] *).

Definition mpd_abs (d : mpd) : Z := limbs_val (md_limbs d).
Definition mpd_val (d : mpd) : Z := md_sg d * limbs_val (md_limbs d).

(* [comment removed for export] *)
Definition mpd_ivs (d : mpd) : list (Z * Z) :=
  (md_addr d, md_addr d + 16) :: match md_own d with LNull => [] | _ => [(md_p d, md_p d + 4 * md_n d)] end.

(* [comment removed for export] *)
Definition mpd_blk (d : mpd) : list blk :=
  match md_own d with LHeap => [(md_p d, 4 * md_n d)] | _ => [] end.

(* [comment removed for export] *)
Definition mpd_sep (d1 d2 : mpd) : Prop :=
  d1 = d2 \/ md_addr d1 + 16 <= md_addr d2 \/ md_addr d2 + 16 <= md_addr d1.

(* [comment removed for export] *)
Definition mpd_out (LB : list blk) (dX : mpd) (LB' : list blk) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_MpiVal ()) "(0.(;.$<.(2.O1.)(2.O3.))(0.(=.(;.$>.(9.O1.)$?.))(0.Pb,$10.P,(11.$10.R1.O2.)(:.(11.$10.R2.O4.)(11.$10.R2.(12.O1.)))(0.Pb,$10.P,(11.$10.R1.O4.)P,(=.(11.$10.R2.(12.O3.)))(11.$10.R3.O2.)Pb,$10.P,(11.$10.R1.(12.O3.))P,(11.$10.R2.O2.)(;.(13.$10.)(12.O1.)(12.O3.))))))")
(* [comment removed for export] *).

Lemma limbs_val_nonneg : forall ws, 0 <= limbs_val ws.
Proof. induction ws as [|w ws IH]; cbn; [lia|]. pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(lia)). lia. Qed.

Lemma mpd_abs_nonneg d : 0 <= mpd_abs d.
Proof. apply limbs_val_nonneg. Qed.

Lemma mpd_val_abs d : md_sg d = 1 \/ md_sg d = -1 -> Z.abs (mpd_val d) = mpd_abs d.
Proof. intros [E|E]; unfold mpd_val, mpd_abs; rewrite E; pose proof (limbs_val_nonneg (md_limbs d)); lia. Qed.
