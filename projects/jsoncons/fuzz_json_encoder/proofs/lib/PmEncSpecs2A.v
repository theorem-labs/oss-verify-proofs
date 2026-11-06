(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutL5A.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMES2A.
Import PML. Import PMES.

Definition PC_PUSH_SLOW_ROOT : Z := 0xca1ac.      (* [comment removed for export] *)
Definition PC_PUSH_SLOW_NESTED : Z := 0xca6bc.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition PC_PUSH_FAST_ROOT_xboth : Z := 0xce8f4.    Definition PC_PUSH_SLOW_ROOT_xboth : Z := 0xce9ec.
Definition PC_PUSH_FAST_NESTED_xboth : Z := 0xcdd60.  Definition PC_PUSH_SLOW_NESTED_xboth : Z := 0xcde58.
Definition PC_ANNOT_SHRINK_CTX_xboth : Z := 0xbbf80.
(* [comment removed for export] *)
Definition PUSH_SCRA : Z := 192 + PMSA.AINC_SCR.
Definition PUSH_DA : Z := 0.

Section Specs2A.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable onmax : Z.                 (* [comment removed for export] *)
Let mem := PMSA.mem.
Let u8 := PMSA.u8 L.   Let u32 := PMSA.u32 L.   Let u64 := PMSA.u64 L.
Let a0 := PMSA.a0.     Let a1 := PMSA.a1.       Let a2 := PMSA.a2.       Let a3 := PMSA.a3.

(* [comment removed for export] *)
Definition push_argsA (M : mem) (R : bvmap 5 word) (sp V : Z) (arr : bool) (ib : Z) : Prop :=
  exists pty psp pib ppos pos col,
    a1 R pty /\ a2 R psp /\ a3 R pib /\ getr R 14%bv = Z_to_bv 64 (V + O_COLUMN) /\ getr R 15%bv = Z_to_bv 64 ppos /\
    u32 M pty (b2z arr) /\ u8 M psp 0 /\ u8 M pib ib /\ 0 <= ib <= 1 /\ u64 M ppos pos /\ u64 M (V + O_COLUMN) col /\
    L5.defined M pty 4 /\ L5.defined M psp 1 /\ L5.defined M pib 1 /\ L5.defined M ppos 8 /\
    sp <= pty /\ pty + 4 <= sp + 64 /\ sp <= psp /\ psp + 1 <= sp + 64 /\ sp <= pib /\ pib + 1 <= sp + 64 /\ sp <= ppos /\ ppos + 8 <= sp + 64 /\
    sp + 64 <= ar_sptop ar.

(* [comment removed for export] *)
Definition push_slow_specA (pc : Z) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r V : Z) (es : estate) (b capb : Z) (arr : bool) (ib : Z),
    PMSA.cps_asan L ar HI pc r sp PUSH_SCRA (LBo ++ stack_blocks b capb) FF LK cr A PUSH_DA
      (fun R M => a0 R (V + O_STACK) /\ push_argsA M R sp V arr ib /\
                  PMESA.stack_at L M V es b capb /\ PMESA.stack_sh M es b capb /\ 32 * depth es = capb /\ depth es < MAX_DEPTH /\
                  PMSA.fobj M FF V ENC_SIZE /\ PMSA.stksh ar M sp PUSH_SCRA /\
                  acredit_ok L cr (Z.max 32 (2 * capb)) /\ Z.max 32 (2 * capb) <= onmax)
      (fun R M R' M' LB' cr' LBk W => exists (b' capb' : Z),
          a0 R' (b' + 32 * depth es) /\ capb' = Z.max 32 (2 * capb) /\
          PMESA.stack_at L M' V (ECtx arr 0 false :: es) b' capb' /\ PMESA.stack_sh M' (ECtx arr 0 false :: es) b' capb' /\
          ablock_range L ar b' capb' /\ blocks_apart b' capb' LBo /\ fframes_apart b' capb' FF /\ L5.defined M' b' capb' /\
          LB' = LBo ++ [(b', capb')] /\ LBk = LBo /\ W = [(V + O_STACK, 24)] /\ cr' = adebit L cr capb').
Definition push_slow_root_specA : Prop := push_slow_specA PC_PUSH_SLOW_ROOT.        (* [comment removed for export] *)
Definition push_slow_nested_specA : Prop := push_slow_specA PC_PUSH_SLOW_NESTED.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition push_fast_specA (pc : Z) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r V : Z) (es : estate) (b capb : Z) (arr : bool) (ib : Z),
    PMSA.cps_asan L ar HI pc r sp PUSH_SCRA (LBo ++ stack_blocks b capb) FF LK cr A PUSH_DA
      (fun R M => a0 R (V + O_STACK) /\ push_argsA M R sp V arr ib /\
                  PMESA.stack_at L M V es b capb /\ PMESA.stack_sh M es b capb /\ 32 * depth es < capb /\ depth es < MAX_DEPTH /\
                  PMSA.fobj M FF V ENC_SIZE /\ PMSA.stksh ar M sp PUSH_SCRA)
      (fun R M R' M' LB' cr' LBk W =>
          a0 R' (b + 32 * depth es) /\
          PMESA.stack_at L M' V (ECtx arr 0 false :: es) b capb /\ PMESA.stack_sh M' (ECtx arr 0 false :: es) b capb /\
          LB' = LBo ++ stack_blocks b capb /\ LBk = LBo ++ stack_blocks b capb /\ W = [(V + O_STACK, 24); (b + 32 * depth es, 32); (S b, (capb + 7) / 8)] /\ cr' = cr).
Definition push_fast_root_specA : Prop := push_fast_specA PC_PUSH_SLOW_ROOT.
Definition push_fast_nested_specA : Prop := push_fast_specA PC_PUSH_SLOW_NESTED.

(* [comment removed for export] *)
Definition PC_ANNOT_INC_CTX : Z := 0xcabcc.   Definition PC_ANNOT_SHRINK_CTX : Z := 0xba5a0.
Definition annotate_increase_ctx_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o b mid capb n sp r : Z),
    PMSA.cps_asan L ar HI pc r sp PMSA.AINC_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R o /\ PMSA.a1 R n /\ PMSA.u64 L M o b /\ PMSA.u64 L M (o + 8) (b + mid) /\ PMSA.u64 L M (o + 16) (b + capb) /\ L5.defined M o 24 /\
                  CL5A.ainfr FF o 24 /\ o mod 8 = 0 /\ shadow_zero M o 3 /\
                  In (b, capb) LB /\ 0 <= mid /\ 0 < n /\ mid + 32 * n <= capb /\ shadow_cont M b capb mid /\ b <> 0 /\ capb <= 32768)
      (fun R M R' M' LB' cr' LBk W => shadow_cont M' b capb (mid + 32 * n) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(S b, (capb + 7) / 8)]).
Definition annotate_shrink_ctx_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o b mid old capb sp r : Z),
    PMSA.cps_asan L ar HI pc r sp PMSA.AINC_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R o /\ PMSA.a1 R old /\ PMSA.u64 L M o b /\ PMSA.u64 L M (o + 8) (b + mid) /\ PMSA.u64 L M (o + 16) (b + capb) /\ L5.defined M o 24 /\
                  CL5A.ainfr FF o 24 /\ o mod 8 = 0 /\ shadow_zero M o 3 /\
                  In (b, capb) LB /\ 0 <= mid <= 32 * old /\ 32 * old <= capb /\ shadow_cont M b capb (32 * old) /\ b <> 0 /\ capb <= 32768)
      (fun R M R' M' LB' cr' LBk W => shadow_cont M' b capb mid /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(S b, (capb + 7) / 8)]).
(* [comment removed for export] *)
Definition push_slow_specXB (pc : Z) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r V : Z) (es : estate) (b capb : Z) (arr : bool) (ib : Z),
    PMSA.cps_asan L ar HI pc r sp PUSH_SCRA (LBo ++ stack_blocks b capb) FF LK cr A PUSH_DA
      (fun R M => a0 R (V + O_STACK) /\ push_argsA M R sp V arr ib /\
                  PMESA.stack_at L M V es b capb /\ PMESA.stack_sh M es b capb /\ 32 * depth es = capb /\ depth es < MAX_DEPTH /\
                  PMSA.fobj M FF V ENC_SIZE /\ PMSA.stksh ar M sp PUSH_SCRA /\
                  acredit_ok L cr (Z.max 32 (2 * capb)) /\ Z.max 32 (2 * capb) <= onmax)
      (fun R M R' M' LB' cr' LBk W => exists (b' capb' : Z),
          a0 R' (b' + 32 * depth es + 32) /\ capb' = Z.max 32 (2 * capb) /\
          PMESA.stack_at L M' V (ECtx arr 0 false :: es) b' capb' /\ PMESA.stack_sh M' (ECtx arr 0 false :: es) b' capb' /\
          ablock_range L ar b' capb' /\ blocks_apart b' capb' LBo /\ fframes_apart b' capb' FF /\ L5.defined M' b' capb' /\
          LB' = LBo ++ [(b', capb')] /\ LBk = LBo /\ W = [(V + O_STACK, 24)] /\ cr' = adebit L cr capb').
Definition push_fast_specXB (pc : Z) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r V : Z) (es : estate) (b capb : Z) (arr : bool) (ib : Z),
    PMSA.cps_asan L ar HI pc r sp PUSH_SCRA (LBo ++ stack_blocks b capb) FF LK cr A PUSH_DA
      (fun R M => a0 R (V + O_STACK) /\ push_argsA M R sp V arr ib /\
                  PMESA.stack_at L M V es b capb /\ PMESA.stack_sh M es b capb /\ 32 * depth es < capb /\ depth es < MAX_DEPTH /\
                  PMSA.fobj M FF V ENC_SIZE /\ PMSA.stksh ar M sp PUSH_SCRA)
      (fun R M R' M' LB' cr' LBk W =>
          PMESA.stack_at L M' V (ECtx arr 0 false :: es) b capb /\ PMESA.stack_sh M' (ECtx arr 0 false :: es) b capb /\
          LB' = LBo ++ stack_blocks b capb /\ LBk = LBo ++ stack_blocks b capb /\ W = [(V + O_STACK, 24); (b + 32 * depth es, 32); (S b, (capb + 7) / 8)] /\ cr' = cr).
Definition push_slow_root_specXB : Prop := push_slow_specXB PC_PUSH_SLOW_ROOT_xboth.
Definition push_slow_nested_specXB : Prop := push_slow_specXB PC_PUSH_SLOW_NESTED_xboth.
Definition push_fast_root_specXB : Prop := push_fast_specXB PC_PUSH_FAST_ROOT_xboth.
Definition push_fast_nested_specXB : Prop := push_fast_specXB PC_PUSH_FAST_NESTED_xboth.
End Specs2A.
End PMES2A.
