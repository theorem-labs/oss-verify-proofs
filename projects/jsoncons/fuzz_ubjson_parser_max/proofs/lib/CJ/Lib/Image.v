(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import PropExec MState Mem Cells Step.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Lib_Image () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Image.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1Some"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2eq"; "3Z"; "4CB"; "4cell"; "5image_bytes"; "5ro_bytes_b"]; ["6mem_inv"; "6ro_bytes"; "7ro_cells"; "8add"; "8le"; "8of_nat"; "8pow"; "0bs"; "0m"; "0n"; "0segs"; "9bv"]]).
Section WithSegs.
Variable segs : list Segment.
Fixpoint ro_bytes_b (A : Z) (bs : list byte) : bool :=
match bs with
| [] => true
| b :: bs' =>
match seg_rom segs (wa A) with
| Some b' => bv_eqb b b' && ro_addr segs (wa A) && ro_bytes_b (A + 1) bs'
| None => false
end
end.
Lemma ro_bytes_b_sound : ltac2:(TCodec.tc2 tcn__CJ_Lib_Image "E'5'Ky8%211%411';':'2&?r1r2%3221(9%73621&AvJr3%33271p051p2>1pQ@@1").
Proof.
induction bs as [|b bs IH]; intros A H; cbn in *; [exact I|].
destruct (seg_rom segs (wa A)) as [b'|] eqn:E; [|discriminate].
apply andb_prop in H. destruct H as [H1 H3]. apply andb_prop in H1. destruct H1 as [H1 H2].
unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b'.
split; [split; [exact E| exact H2]|]. apply IH. exact H3.
Qed.
Lemma ro_cells_image : ltac2:(TCodec.tc2 tcn__CJ_Lib_Image "QI'KyR0%211'8y8%511%311p051';'5%115&@vJr3%3221':'2&?r2%2261(9%63521&Dzr4%3221&Cr5&E&4%12I6%311%6251&F+2+R0%3221%?251&Br7r6(3'=(<%?2Q7A%221B(7%115%73631%;4Q5:91p0=1p0J1p0O1p0Q71pQ@Q<1p2Q?1pQBQA1").
Proof.
intros m A bs Hinv Hb HA Hl. split.
- cbn. split; [reflexivity|exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. apply ro_bytes_at; try assumption.
apply ro_bytes_b_sound. exact Hb.
Qed.
Fixpoint image_bytes (A : Z) (n : nat) : option (list byte) :=
match n with
| O => Some []
| S n' => match seg_rom segs (wa A), image_bytes (A + 1) n' with
| Some b, Some bs => Some (b :: bs)
| _, _ => None
end
end.
Lemma image_bytes_length : ltac2:(TCodec.tc2 tcn__CJ_Lib_Image "J'6';'5'Ky8%211%411':'8%113&>r2r3%3221(1r1%22:1%:3841&4%12>8r4%>3E21p051pQ@A1p2G1pQDI1").
Proof.
induction n as [|n IH]; intros A bs H; cbn in H.
- inversion H. reflexivity.
- destruct (seg_rom segs (wa A)); [|discriminate]. destruct (image_bytes (A + 1) n) eqn:E; [|discriminate].
inversion H. cbn. f_equal. eapply IH. exact E.
Qed.
End WithSegs.
