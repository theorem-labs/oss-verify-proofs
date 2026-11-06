(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtRegs ArtAtomics ArtTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatRzLog () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRzLog."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2eq"; "3Z"; "4bvmap"; "0M"; "5Wn"; "5apart"; "5wr"; "6msteps"; "7ret_ok"; "8art_rz_rodata"; "9getr"; "9mkst"; "9regupd"; ":loaded_segments"]; [";le"; ";lt"; ";pow"; ";sub"; "0fx"; "0raw"; "0regs"; "0rom"; "0sp"; "<BV"; "<Z_to_bv"; "<bv"; "<bv_unsigned"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_rz_rodata (M : word -> option byte) : Prop :=
cellA M 0x10418 8 0x218a392cd3d5dbf /\ cellA M 0x10598 1 4 /\ cellA M 0x105c1 1 11.
Definition art_rz_kept (r : reg) : Prop := r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.
Section FPX. Context {fx : PropExec.FPState}.
#[local] Ltac post_kept := intros r Hr; unfold art_rz_kept in Hr; destruct Hr as (?&?&?&?&?); kept_solve.
Ltac zlbu F D a HYP :=
chain_step; [reflexivity | eapply step_lbu; [exact F | reflexivity | exact D | zaddr a; exact HYP ] | step_simpl; vnorm].
Section SE.
Local Abbreviation SEC_T_art_rz2log_16_fn := (ltac2:(TCodec.tc2 tcn__JatRzLog "SC&4y5'KyR0%211%5241'0y8%611%311p061'3'2&<r5(I+:(1%33A21%6251&J+@%22C1%;3C41r6+2%;3I19%>231r3%92J1%B3J31r7+1%B3Q01@%E231%G3O17&:r4%211&@%12C@&A&B+R0%22C1%42>1&8&?r:&Cr8%221N%64541O&;r;%211&7%829Q4+RPP0+U\P0%443Q721'9&=vDr>+Zl`4%QC3QO1QA/01QOr=r<%8576321&>%138Q7H%QE2R6C%332Q@1z%QH2R91%633QK1+;%R03R>1QN%93314+<%R33RA1R1+4%R02RA1%>3531+=%R83RF1R6%A331R2+>%R;3RI1R9%D331R5&6u8+8%Q>2Q91&L%12RNQA%645N31%Q55Q48QC1N%Q73QEN1p0Q91p0Q?1p0QC1p0QK1p0R11p0R41p0R81p0R>1p0RF1pQ<S:1pQBS41pQ@S61p<S71pQ>S=1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_rz2log_16_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_rz2log_16_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_rz2log_16_fn) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_rz2log_16_fn) 3%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_rz2log_16_fn) 4%nat 0%nat).
Lemma art_rz2log_16_fn : ltac:(sec_stmt2 constr:(SEC_T_art_rz2log_16_fn) 5%nat 0%nat).
Proof using Type regs M rom sp raw.
intros H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
zstep (ltac:(oF' 0x57204%Z)) (ltac:(oD' 0x57204%Z)).
zsd (ltac:(oF' 0x57208%Z)) (ltac:(oD' 0x57208%Z)) (sp - 8) (U raw) ltac:(rewok W).
assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10418 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10598 1 4) by (unfold apart in *; recell R2).
zstep (ltac:(oF' 0x5720c%Z)) (ltac:(oD' 0x5720c%Z)). zstep (ltac:(oF' 0x57210%Z)) (ltac:(oD' 0x57210%Z)). zstep (ltac:(oF' 0x57214%Z)) (ltac:(oD' 0x57214%Z)).
zbft (ltac:(oF' 0x57218%Z)) (ltac:(oD' 0x57218%Z)).
zstep (ltac:(oF' 0x5721c%Z)) (ltac:(oD' 0x5721c%Z)). zstep (ltac:(oF' 0x57220%Z)) (ltac:(oD' 0x57220%Z)).
zbft (ltac:(oF' 0x57224%Z)) (ltac:(oD' 0x57224%Z)).
zstep (ltac:(oF' 0x57228%Z)) (ltac:(oD' 0x57228%Z)). zstep (ltac:(oF' 0x5722c%Z)) (ltac:(oD' 0x5722c%Z)).
zbft (ltac:(oF' 0x57230%Z)) (ltac:(oD' 0x57230%Z)).
zstep (ltac:(oF' 0x57234%Z)) (ltac:(oD' 0x57234%Z)). zstep (ltac:(oF' 0x57238%Z)) (ltac:(oD' 0x57238%Z)).
zld (ltac:(oF' 0x5723c%Z)) (ltac:(oD' 0x5723c%Z)) 0x10418 C1.
zstep (ltac:(oF' 0x57240%Z)) (ltac:(oD' 0x57240%Z)). zstep (ltac:(oF' 0x57244%Z)) (ltac:(oD' 0x57244%Z)). zstep (ltac:(oF' 0x57248%Z)) (ltac:(oD' 0x57248%Z)). zstep (ltac:(oF' 0x5724c%Z)) (ltac:(oD' 0x5724c%Z)). zstep (ltac:(oF' 0x57250%Z)) (ltac:(oD' 0x57250%Z)). zstep (ltac:(oF' 0x57254%Z)) (ltac:(oD' 0x57254%Z)).
zlbu (ltac:(oF' 0x57258%Z)) (ltac:(oD' 0x57258%Z)) 0x10598 C2.
zstep (ltac:(oF' 0x5725c%Z)) (ltac:(oD' 0x5725c%Z)). zstep (ltac:(oF' 0x57260%Z)) (ltac:(oD' 0x57260%Z)).
zbft (ltac:(oF' 0x57264%Z)) (ltac:(oD' 0x57264%Z)).
zstep (ltac:(oF' 0x57268%Z)) (ltac:(oD' 0x57268%Z)). zstep (ltac:(oF' 0x5726c%Z)) (ltac:(oD' 0x5726c%Z)).
zbft (ltac:(oF' 0x57270%Z)) (ltac:(oD' 0x57270%Z)).
zstep (ltac:(oF' 0x57274%Z)) (ltac:(oD' 0x57274%Z)).
assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
zld (ltac:(oF' 0x57278%Z)) (ltac:(oD' 0x57278%Z)) (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x5727c%Z)) (ltac:(oD' 0x5727c%Z)).
stepret (ltac:(oF' 0x57280%Z)) (ltac:(oD' 0x57280%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_rz2log_2048_fn := (ltac2:(TCodec.tc2 tcn__JatRzLog "SC&4y5'KyR0%211%5241'0y8%611%311p061'3'2&<r5(I+:(1%33A21%6251&J+RP0%22C1%;3C41r6+2%;3I19%>231r3%92J1%B3J31r7+1%B3Q01@%E231%G3O17&:r4%211&@+@%221A&A&B+R0%22D1%42?1&8&?r:&Cr8%221<%64541=&;r;%211&7%829B+RPP0+U\P0%443E21'9&=vDr>+Zl`4%QD3R01QB/01R0r=r<%8576321&>%138Q8H%QF2R7C%332QA1+7%QI2R:1%633QL1+;%R13R?1QO%93314+<%R43RB1R2%R02RA5%=3421+=%R83RF1R6%@331R2+>%R;3RI1R9%C331R5&6u8+8%Q=2Q81&L%12RNQ@%645M31%Q45Q38QB1M%Q63QDM1p0Q81p0Q>1p0QB1p0QJ1p0R01p0R41p0R81p0R>1p0RF1pQ<S:1pQBS41pQ@S61p<S71pQ>S=1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_rz2log_2048_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_rz2log_2048_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_rz2log_2048_fn) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_rz2log_2048_fn) 3%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_rz2log_2048_fn) 4%nat 0%nat).
Lemma art_rz2log_2048_fn : ltac:(sec_stmt2 constr:(SEC_T_art_rz2log_2048_fn) 5%nat 0%nat).
Proof using Type regs M rom sp raw.
intros H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
zstep (ltac:(oF' 0x57204%Z)) (ltac:(oD' 0x57204%Z)).
zsd (ltac:(oF' 0x57208%Z)) (ltac:(oD' 0x57208%Z)) (sp - 8) (U raw) ltac:(rewok W).
assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10418 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x105c1 1 11) by (unfold apart in *; recell R3).
zstep (ltac:(oF' 0x5720c%Z)) (ltac:(oD' 0x5720c%Z)). zstep (ltac:(oF' 0x57210%Z)) (ltac:(oD' 0x57210%Z)). zstep (ltac:(oF' 0x57214%Z)) (ltac:(oD' 0x57214%Z)).
zbft (ltac:(oF' 0x57218%Z)) (ltac:(oD' 0x57218%Z)).
zstep (ltac:(oF' 0x5721c%Z)) (ltac:(oD' 0x5721c%Z)). zstep (ltac:(oF' 0x57220%Z)) (ltac:(oD' 0x57220%Z)).
zbft (ltac:(oF' 0x57224%Z)) (ltac:(oD' 0x57224%Z)).
zstep (ltac:(oF' 0x57228%Z)) (ltac:(oD' 0x57228%Z)). zstep (ltac:(oF' 0x5722c%Z)) (ltac:(oD' 0x5722c%Z)).
zbft (ltac:(oF' 0x57230%Z)) (ltac:(oD' 0x57230%Z)).
zstep (ltac:(oF' 0x57234%Z)) (ltac:(oD' 0x57234%Z)). zstep (ltac:(oF' 0x57238%Z)) (ltac:(oD' 0x57238%Z)).
zld (ltac:(oF' 0x5723c%Z)) (ltac:(oD' 0x5723c%Z)) 0x10418 C1.
zstep (ltac:(oF' 0x57240%Z)) (ltac:(oD' 0x57240%Z)). zstep (ltac:(oF' 0x57244%Z)) (ltac:(oD' 0x57244%Z)). zstep (ltac:(oF' 0x57248%Z)) (ltac:(oD' 0x57248%Z)). zstep (ltac:(oF' 0x5724c%Z)) (ltac:(oD' 0x5724c%Z)). zstep (ltac:(oF' 0x57250%Z)) (ltac:(oD' 0x57250%Z)). zstep (ltac:(oF' 0x57254%Z)) (ltac:(oD' 0x57254%Z)).
zlbu (ltac:(oF' 0x57258%Z)) (ltac:(oD' 0x57258%Z)) 0x105c1 C2.
zstep (ltac:(oF' 0x5725c%Z)) (ltac:(oD' 0x5725c%Z)). zstep (ltac:(oF' 0x57260%Z)) (ltac:(oD' 0x57260%Z)).
zbft (ltac:(oF' 0x57264%Z)) (ltac:(oD' 0x57264%Z)).
zstep (ltac:(oF' 0x57268%Z)) (ltac:(oD' 0x57268%Z)). zstep (ltac:(oF' 0x5726c%Z)) (ltac:(oD' 0x5726c%Z)).
zbft (ltac:(oF' 0x57270%Z)) (ltac:(oD' 0x57270%Z)).
zstep (ltac:(oF' 0x57274%Z)) (ltac:(oD' 0x57274%Z)).
assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
zld (ltac:(oF' 0x57278%Z)) (ltac:(oD' 0x57278%Z)) (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x5727c%Z)) (ltac:(oD' 0x5727c%Z)).
stepret (ltac:(oF' 0x57280%Z)) (ltac:(oD' 0x57280%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
End FPX.
