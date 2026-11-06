(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutL5A.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMSB.
Section SpecsB.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.

(* [comment removed for export] *)
Definition AINC_SCR : Z := 4128.
Definition annotate_increase_spec (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o b len cap n sp r : Z),
    PMSA.cps_asan L ar HI pc r sp AINC_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R o /\ PMSA.a1 R n /\ PMSA.vec_at L M o b len cap /\ PMSA.ainfr FF o 24 /\ o mod 8 = 0 /\ shadow_zero M o 3 /\
                  In (b, cap) LB /\ 0 <= len /\ 0 < n /\ len + n <= cap /\ shadow_cont M b cap len /\ b <> 0 /\ cap <= 4096)
      (fun R M R' M' LB' cr' LBk W => shadow_cont M' b cap (len + n) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(S b, (cap + 7) / 8)]).
Definition annotate_shrink_spec (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o b len old cap sp r : Z),
    PMSA.cps_asan L ar HI pc r sp AINC_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R o /\ PMSA.a1 R old /\ PMSA.vec_at L M o b len cap /\ PMSA.ainfr FF o 24 /\ o mod 8 = 0 /\ shadow_zero M o 3 /\
                  In (b, cap) LB /\ 0 <= len <= old /\ old <= cap /\ shadow_cont M b cap old /\ b <> 0 /\ cap <= 4096)
      (fun R M R' M' LB' cr' LBk W => shadow_cont M' b cap len /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(S b, (cap + 7) / 8)]).

(* [comment removed for export] *)
Definition annotate_delete_null_spec (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r : Z),
    PMSA.cps_asan L ar HI pc r sp PMSA.ANEW_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R o /\ PMSA.u64 L M o 0 /\ PMSA.u64 L M (o + 8) 0 /\ PMSA.u64 L M (o + 16) 0 /\ PMSA.acobj ar FF sp o 24 /\ o mod 8 = 0 /\ shadow_zero M o 3)
      (fun R M R' M' LB' cr' LBk W => LB' = LB /\ cr' = cr /\ LBk = LB /\ W = []).

(* [comment removed for export] *)
Definition POP_SCR : Z := 96 + 32 + AINC_SCR.
Definition pop_state_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (P b cap x sp r : Z) (rest : list Z),
    PMSA.cps_asan L ar HI pc r sp POP_SCR LB FF LK cr A 2
      (fun R M => PMSA.a0 R P /\ sp mod 32 = 0 /\ PMSA.vec_ok L M LB FF (P + 248) b (Z.of_nat (length rest) + 1) cap /\ L5.bytes_at (hl_segs L) M b (rest ++ [x]) /\ 0 <= x < 256)
      (fun R M R' M' LB' cr' LBk W => PMSA.a0 R' x /\ PMSA.vec_at L M' (P + 248) b (Z.of_nat (length rest)) cap /\ shadow_cont M' b cap (Z.of_nat (length rest)) /\
          LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(P + 256, 8); (S b, (cap + 7) / 8)]).
(* [comment removed for export] *)
Definition ESV_SCR : Z := 256 + POP_SCR.
Definition end_string_value_specA (pc : Z) : Prop :=
  PMSA.ptrans_staleA L ar HI IC pc ESV_SCR 3 true
         (fun R M LBo P V E ps => PMSA.a0 R P /\ PMSA.a3 R V /\ PMSA.a4 R E /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_STRING /\
                              exists s len, PMSA.a1 R s /\ PMSA.a2 R len /\ 0 <= len < 2 ^ 26 /\ L5.defined M s len /\
                                            PMSA.text_inA M (PML.ps_blocks ps ++ LBo) s len)
         (fun ps ps' code R' =>
            (code = 0 /\ PML.ps_more ps' = true /\ PML.ps_level ps' = PML.ps_level ps /\
             In (PML.ps_st ps') [PML.ST_EXPECT_COLON; PML.ST_EXPECT_COMMA_OR_END; PML.ST_ACCEPT])
            \/ In code [25; 26; 27; 28; 29]).
(* [comment removed for export] *)
Definition convert_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o cap p cpa cp sp r kx bx : Z) (s : list Z),
    PMSA.cps_asan L ar HI pc r sp PMSA.CONVERT_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R cpa /\ PMSA.a1 R 1 /\ PMSA.a2 R o /\ PMSA.a3 R 0 /\
                  PMSA.u32 L M cpa cp /\ 0 <= cp < 2 ^ 32 /\ PMSA.ainfr FF cpa 4 /\ cpa mod 4 = 0 /\ PMLA.img_ro IC M /\ ((cpa mod 8 = 0 /\ byte_at M (S cpa) 4) \/ byte_at M (S cpa) 0) /\
                  PMSA.str_at L M o (PML.SLong cap p s) /\ 24 <= cap /\ In (p, cap) LB /\ shadow_blk M p cap /\ PMSA.fobj M FF o 24 /\
                  PMSA.stksh ar M sp PMSA.CONVERT_SCR /\ Z.of_nat (length s) + 4 < 2 ^ 26 /\ PMSA.bufcredA L cr cap kx bx)
      (fun R M R' M' LB' cr' LBk W => exists cap' p' s',
          PMSA.str_at L M' o (PML.SLong cap' p' s') /\ shadow_blk M' p' cap' /\ cap <= cap' /\
          Z.of_nat (length s) <= Z.of_nat (length s') <= Z.of_nat (length s) + 4 /\
          LB' = (p', cap') :: lb_remove p LB /\ LBk = lb_remove p LB /\ W = [(o, 24)] /\ PMSA.bufcredA L cr' cap' kx bx).
(* [comment removed for export] *)
Definition parser_check_done_specB16 (pc : Z) : Prop :=
  PMSA.ptransA L ar HI IC pc PMSA.PF_SCR 2 false (fun R M LBo P V E ps => PMSA.a0 R P /\ PMSA.a1 R E /\ bv_unsigned (getr R 2%bv) mod 32 = 16)
         (fun ps ps' code R' => (code = 0 /\ PMSA.win_exhausted ps' /\ PML.ps_more ps' = PML.ps_more ps /\ PML.ps_st ps' = PML.ps_st ps /\ PML.ps_stack ps' = PML.ps_stack ps /\ PML.ps_level ps' = PML.ps_level ps) \/ code = 4).
End SpecsB.
End PMSB.
