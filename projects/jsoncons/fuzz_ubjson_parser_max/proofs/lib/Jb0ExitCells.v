(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StepTac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0ExitCells () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0ExitCells."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1option"; "2and"; "2eq"; "3Z"; "0M"; "0M'"; "4AXHI"; "4AXLO"; "4atexit_cellsA"; "5le"; "5lt"; "0a"; "0ax"; "6Z_to_bv"; "6bv"]]).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Definition AXLO : Z := 0x690b10.
Definition AXHI : Z := 0x690d30.
Definition AX_CELLS_A : list (Z * Z * Z) :=
[(0x690b14, 4, 0); (0x690b18, 4, 2); (0x690b20, 8, 0x690b28); (0x690b28, 8, 0); (0x690b30, 8, 0x115708); (0x690c30, 8, 0x96edc); (0x690b38, 8, 0x115708); (0x690c38, 8, 0xa78a4)].
Definition AX_CELLS_B : list (Z * Z * Z) :=
[(0x690b14, 4, 0); (0x690b18, 4, 4); (0x690b20, 8, 0x690b28); (0x690b28, 8, 0); (0x690b30, 8, 0x115708); (0x690c30, 8, 0x96edc); (0x690b38, 8, 0x115708); (0x690c38, 8, 0xa78a4);
(0x690b40, 8, 0xd2008); (0x690b48, 8, 0x6d414); (0x690c40, 8, 0x138ad8); (0x690c48, 8, 0)].
Definition ax_cell (MV : word -> option byte) (c : Z * Z * Z) : Prop :=
rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (Z.to_nat (snd (fst c))) = Some (word_to_le_bytes (Z.to_nat (snd (fst c))) (Z_to_bv 64 (snd c))).
Definition atexit_cellsA (MV : word -> option byte) (ax : bool) : Prop :=
Forall (ax_cell MV) (if ax then AX_CELLS_B else AX_CELLS_A).
Lemma ax_cells_in : forall (ax : bool) (c : Z * Z * Z), In c (if ax then AX_CELLS_B else AX_CELLS_A) -> AXLO <= fst (fst c) /\ fst (fst c) + snd (fst c) <= AXHI /\ 0 <= snd (fst c) <= 8.
Proof.
intros ax c Hc. unfold AXLO, AXHI. destruct ax; cbn [In AX_CELLS_A AX_CELLS_B] in Hc;
repeat (destruct Hc as [<-|Hc]; [cbn [fst snd]; lia|]); destruct Hc.
Qed.
Lemma atexit_cellsA_frame : ltac2:(TCodec.tc2 tcn__Jb0ExitCells "Q7'?yR0%211'1y8%511%311p051'0'4'2&:&8r1%3221&;&7%2241%8241'3r4&>r2%22F1%411r5%113%83E31p0:1pJD1&9%12;9r3%32=1p031p061pLL1p>N1p<O1").
Proof.
intros M M' ax AG H. unfold atexit_cellsA in *. rewrite Forall_forall in *. intros c Hc.
pose proof (ax_cells_in ax c Hc) as (B1 & B2 & B3). specialize (H c Hc). unfold ax_cell in *.
rewrite <- H. apply rdn_ext; [rewrite u_Z2bv by (unfold AXLO, AXHI in *; lia); rewrite Z2Nat.id by lia; unfold AXHI in *; lia|].
intros x Hx. rewrite u_Z2bv in Hx by (unfold AXLO, AXHI in *; lia). rewrite Z2Nat.id in Hx by lia.
rewrite <- (Z_to_bv_bv_unsigned 64 x). apply AG. lia.
Qed.
Lemma atexit_cellsA_at : forall (MV : word -> option byte) (ax : bool) a n v,
atexit_cellsA MV ax -> In (a, n, v) (if ax then AX_CELLS_B else AX_CELLS_A) ->
rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
Proof. intros MV ax a n v H Hin. unfold atexit_cellsA in H. rewrite Forall_forall in H. exact (H (a, n, v) Hin). Qed.
