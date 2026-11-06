(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr Frame TacX Bytes.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXRep AXRep2 AXPRep AXPRep2 N8Kit N8Kit2 N8Kit3 X8Kit X8LeafKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac win_loadH WIN q :=
  lazymatch type of WIN with bytes_at _ ?mx ?it0 ?bs =>
    let b := fresh "b" in let N := fresh "N" in let RD := fresh "RD" in let BR := fresh "BR" in
    destruct (win_byte _ _ _ q WIN ltac:(lia)) as [b N];
    pose proof (zb_range b) as BR; unfold zb in BR;
    pose proof (u8ro_read asegs _ it0 bs (q - it0) b (Z_to_bv 64 q) WIN N ltac:(lia) ltac:(symmetry; apply wa_of_Z_to_bv; lia)) as RD;
    step; clear RD; change (zxb b) with (Z_to_bv 64 (zb b)); fold (zb b) in BR
  end.

Ltac list_eq_lia := repeat first [ reflexivity | lia | progress f_equal ].
Ltac close_cells OBJ :=
  first [ exact OBJ
        | lazymatch goal with |- rw_cells _ _ _ ?cs2 =>
            lazymatch type of OBJ with rw_cells _ _ _ ?cs1 =>
              replace cs2 with cs1; [exact OBJ | unfold wz; list_eq_lia ] end end ].
