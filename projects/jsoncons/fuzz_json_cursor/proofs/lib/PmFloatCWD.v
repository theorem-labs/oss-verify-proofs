(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibDefsA PmCurDefs PmLibSpecsA PmFloatCSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeapA CutL5A.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMFCW.
Section SpecsW.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.

Definition write_double_specW (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (wd o dp sp r : Z),
    PMSA.cps_asan L ar HI pc r sp PMFCA.WD_SCR_A LB FF LK cr A PMFCA.WD_D
      (fun R M => PMSA.a0 R wd /\ PMSA.a1 R o /\ PMSA.u8 L M wd 0 /\ PMSA.u32 L M (wd + 4) 0 /\ PMSA.u8 L M (wd + 8) dp /\ (sp <= wd /\ wd + 12 <= ar_sptop ar) /\
                  PMLA.str_at (hl_segs L) M o (PML.SShort []) /\ L5.defined M o 24 /\ PMLA.fobj M FF o 24 /\ PMLA.apart wd 12 o 24 /\
                  PMSA.stksh ar M sp PMFCA.WD_SCR_A /\ PMLA.img_ro IC M /\ acredit_ok L cr 48 /\ sp mod 32 = 16)
      (fun R M R' M' LB' cr' LBk W => PMSA.a0 R' 0 /\ (exists s', 1 <= Z.of_nat (length s') <= 47 /\ PMFCA.sso_grownA L ar LB FF cr M' o s' LB' cr') /\ LBk = LB /\
                                      W = [(o, 24); (hl_tp L - 164, 4)]).

End SpecsW.
End PMFCW.
