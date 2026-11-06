(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nat"; "bool"; "fst"; "list"; "pair"; "prod"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "ss_pc"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "add"; "@Corelib.Init.Nat"; "add"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "lf_reason"; "lf_state"; "list_set"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "callee_saved"; "pre_reg"; "@Stdlib.Lists.List"; "fold_left"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition NF : positive := 100%positive.
Definition NPOST : positive := 140%positive.

Definition pre_reg (r : nat) : sv := ltac2:(tb__ "0|1|
S0S7Lr;Vr;S8SaScU14Vr;A2A1A1M0S0S0S7Ln;R1S8PbA1S0S0S7Ln0;R1S8PaA1S0S0S7Ln1;R1G0S0S0S7Ln2;R1G0S0S0S7Ln3;R1G0S0S0S7Ln4;R1G0S0S0S7Ln5;R1G0S0S0S7Ln6;R1G0S0S0S7Ln7;R1G0S0S0S7Ln8;R1S8PcA1S0S0S7Ln9;R1S8PdA1S0S0S7Ln10;R1S8PeA1S0G0Ln11;X0x2Ln10;X0x2Ln9;X0x2Ln8;X0x2Ln7;X0x2Ln6;X0x2Ln5;X0x2Ln4;X0x2Ln3;X0x2Ln2;X0x2Ln1;X0x2Ln0;X0x2Ln;X0x2").
Definition pre_regs : list sv := map pre_reg (seq 0 32).
Definition pre_fregs : list sv := ltac2:(tb__ "0|0|
SdS0S7S0S8SaScU3cR1A2A1A1Lr;SeU0U20A2A4").

Definition callee_saved (r : nat) : bool :=
  match r with
  | 1 | 2 | 3 | 4 | 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true
  | _ => false
  end%nat.

Definition cut_regs (base : positive) : list sv := ltac2:(tb__ "0|0|
SdS0S7S0S1S7L_;S14R1A1S15R1A1S8SbVbase;SaR1A1A2A1X1x2Lr;SeU0U20A2A4").
Definition post_regs (base : positive) : list sv := cut_regs base.

Definition setregs (rs : list sv) (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|2|
S16S3S7A1M0S5S0S7A2M1G0G1S12S7R2S2S0S7R1A3S6S0S7R1A3A4Lp;Lacc;Vl;Vrs;A5").

Definition two62 : Z := 2 ^ 62.

Definition show_leaf (L : leaf) : Z * stop_reason := ltac2:(tb__ "0|0|
S4SfS13S9S11VL;A1A1S10VL;A1A4").
