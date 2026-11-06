(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk SeqExec Hoare StreamSim
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__LibSym () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3Sound.AX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymRun3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibSym.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibSym.FPX.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1false"; "1list"; "1nat"; "1prod"; "1true"; "2and"; "2eq"; "3le"; "3lt"; "4Z"; "0E"; "0E'"; "5instr"; "6bvmap"; "0R"]; ["0R'"; "7PTLeaf"; "7env"; "7ev"; "7expr"; "7itab"; "7itab_sound"; "7ridx"; "7sr_id"; "8regs_ok"; "9env_agree"; ":EnvR"; ";itab_of"; ";itab_of_ranges"; ":pres_check"; "<getr"]; ["=eqb"; ">existsb"; "?le"; "?lt"; "?of_nat"; "?pow"; "0b"; "0exc"; "0n"; "0r"; "0rs"; "0segs"; "0sr'"; "@Z_to_bv"; "@bv"; "@bv_unsigned"]; ["0t"; "0z"]]).
Section FPX. Context {fx : PropExec.FPState}.
Section WithSegs.
Variable segs : list Segment.
Fixpoint itab_of_ranges (rs : list (Z * nat)) (t : itab) : itab :=
match rs with
| [] => t
| (lo, n) :: rs' => itab_of_ranges rs' (mk_itab_fuel segs n lo t)
end.
Lemma itab_of_ranges_sound : ltac2:(TCodec.tc2 tcn__LibSym "C'2'4':'3%3221%511&E&FvQ;r1%3221&Mr3r2%3221%8271p061pS2;1pRF=1").
Proof. induction rs as [|[lo n] rs IH]; intros t Ht; cbn; [exact Ht|]. apply IH. apply mk_itab_fuel_sound. exact Ht. Qed.
Lemma itab_leaf_sound : ltac2:(TCodec.tc2 tcn__LibSym "6&FvQ;(A'=%211%5241").
Proof. intros pc i. unfold itab_lookup. destruct pc; try discriminate. rewrite pt_get_leaf. discriminate. Qed.
Definition itab_of (rs : list (Z * nat)) : itab := itab_of_ranges rs PTLeaf.
Lemma itab_of_sound : ltac2:(TCodec.tc2 tcn__LibSym "='2'4':'3%3221%511&FvQ;&Lr1%211%5241pRF71").
Proof. intros rs. apply itab_of_ranges_sound, itab_leaf_sound. Qed.
End WithSegs.
Definition EnvR (R : bvmap 5 word) : env := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => []).
Lemma EnvR_regs_ok : ltac2:(TCodec.tc2 tcn__LibSym "=&>y5'Q>yR0%211%5241&I&Kr1%211&H%53213pQ071").
Proof. intros R. apply regs_ok_id. Qed.
Lemma EnvR_ev : ltac2:(TCodec.tc2 tcn__LibSym "L&>y5'Q>yR0%211%5241'3&9r1uQ0%3221'7&C&Kr3%211r2%5221&O&Q=&Q4%115%32E1%5291%=3D71p0?1pRBD1pQ0F1").
Proof. intros R n Hn. cbn [ev EnvR]. unfold reg_ev. apply Nat.ltb_lt in Hn. rewrite Hn. reflexivity. Qed.
Lemma u64_of_Z : ltac2:(TCodec.tc2 tcn__LibSym "G':'6&Q2zr1%3221&Q3&Q5+2+R0%3221%5271%;271'7&Q?yR0&Q=r2%2231%5241%73D13p091pS4F1").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.
Definition pres_check (sr' : list expr) (exc : list nat) : bool :=
forallb (fun i => expr_eqb (nth i sr' (ELit 0)) (EVar i) || existsb (Nat.eqb i) exc)%bool (seq 0 32).
Lemma pres_check_sound : ltac2:(TCodec.tc2 tcn__LibSym "R0'2'D%211'3%411'B&>y5'Q>yR0%211%5241'7'0&Nr7r6%3221(5%73621&I&Hr4%33721r9%53913&Jr8%2361='8uQ0r5%3221%I1J&Q1&Q0&Gr1%211%411r<%73Q621(1%O3N21&Or2%22F1r:%4213%Q53Q731p071pRDB1p0D1p0I1p0M1p0Q01p0Q51pR>QF1pQ2Q?1pQ0Q@1pJQG1pHQH1pR@QJ1pRJQM1").
Proof.
intros sr' exc E E' R R' b Hc HR HR' Hag Hb r Hr.
rewrite (HR' r), (HR r). unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
pose proof (ridx_range r) as Hlt.
unfold pres_check in Hc. rewrite forallb_forall in Hc.
specialize (Hc (ridx r)). rewrite Hr, orb_false_r in Hc.
assert (Hin : In (ridx r) (seq 0 32)) by (apply in_seq; lia).
specialize (Hc Hin). apply expr_eqb_eq in Hc. rewrite Hc.
assert (Hid : nth (ridx r) sr_id (ELit 0) = EVar (ridx r)).
{ set (n := ridx r) in *. clearbody n. do 32 (destruct n as [|n]; [reflexivity|]). exfalso; lia. }
rewrite Hid. cbn [edenot]. symmetry. apply (proj1 Hag). lia.
Qed.
End FPX.
