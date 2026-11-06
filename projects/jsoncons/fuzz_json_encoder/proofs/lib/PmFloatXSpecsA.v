(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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

Module PMFXA.
(* [comment removed for export] *)
Definition TXT_INF : list Z := [105; 110; 102].       Definition TXT_NAN : list Z := [110; 97; 110].
Definition gtext (txt : list Z) : Prop := PML.num_final txt \/ In txt [TXT_INF; 45 :: TXT_INF; TXT_NAN; 45 :: TXT_NAN].
(* [comment removed for export] *)
Definition txt_home (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (sp s n : Z) : Prop :=
  (exists b, In b LB /\ fst b <= s /\ s + n <= fst b + snd b) \/ CL5A.acobj ar FF sp s n.

(* [comment removed for export] *)
Definition PC_SNPRINTF_xasan : Z := 0x6b96c.     (* [comment removed for export] *)
Definition FMT_G_xasan : Z := 0x25b80.           (* [comment removed for export] *)
Definition PC_STRTOD_xasan : Z := 0x151d48.      Definition PC_DECSTR_DOUBLE_xasan : Z := 0xc9558.     Definition PC_FLOATSCAN_xasan : Z := 0x14d930.
Definition PC_WRITE_DOUBLE_xasan : Z := 0xbc830. Definition PC_DTOA_TRUE_xasan : Z := 0xc9900.         Definition PC_DTOA_FALSE_xasan : Z := 0xc9cd8.
Definition PC_DUMP_BUFFER_xasan : Z := 0xc70f4.  Definition PC_PRETTIFY_xasan : Z := 0xc7f44.          Definition PC_FILL_EXP_xasan : Z := 0xc8ca8.
Definition PC_GRISU3_xasan : Z := 0xc7be0.       Definition PC_DIGIT_GEN_xasan : Z := 0xc87ac.
Definition PC_FROM_INT_U64_xasan : Z := 0xbb0cc. Definition PC_FROM_INT_I64_xasan : Z := 0xbb72c.      Definition PC_VISIT_DOUBLE_xasan : Z := 0xb4a8c.
Definition FMT_G_xboth : Z := 0x25d20.           (* [comment removed for export] *)

Section SpecsA.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition strtod_g_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (s endp sp r : Z) (txt : list Z),
    PMSA.cps_asan L ar HI pc r sp PMSA.STRTOD_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R s /\ PMSA.a1 R endp /\ PMLA.img_ro IC M /\
                  L5.bytes_at (hl_segs L) M s txt /\ PMSA.u8 L M (s + Z.of_nat (length txt)) 0 /\ gtext txt /\ Z.of_nat (length txt) < 2 ^ 26 /\
                  L5.defined M endp 8 /\ PMSA.acobj ar FF sp endp 8 /\
                  (s + Z.of_nat (length txt) + 1 <= sp - PMSA.STRTOD_SCR \/ sp <= s) /\
                  (s + Z.of_nat (length txt) + 1 <= endp \/ endp + 8 <= s) /\
                  (s + Z.of_nat (length txt) + 1 <= hl_tp L - 164 \/ hl_tp L - 160 <= s) /\
                  L5.defined M s (Z.of_nat (length txt) + 1) /\
                  txt_home ar LB FF sp s (Z.of_nat (length txt) + 1))
      (fun R M R' M' LB' cr' LBk W => PMSA.u64 L M' endp (s + Z.of_nat (length txt)) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(endp, 8); (hl_tp L - 164, 4)]).

(* [comment removed for export] *)
Definition decstr_to_double_g_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (s dp sp r : Z) (txt : list Z),
    PMSA.cps_asan L ar HI pc r sp PMSA.DECSTR_SCR LB FF LK cr A 2
      (fun R M => PMSA.a0 R s /\ PMSA.a1 R (Z.of_nat (length txt)) /\ PMSA.a2 R dp /\ sp mod 32 = 0 /\ PMLA.img_ro IC M /\ PMSA.stksh ar M sp PMSA.DECSTR_SCR /\
                  L5.bytes_at (hl_segs L) M s txt /\ PMSA.u8 L M (s + Z.of_nat (length txt)) 0 /\ gtext txt /\ Z.of_nat (length txt) < 2 ^ 26 /\
                  L5.defined M s (Z.of_nat (length txt) + 1) /\
                  txt_home ar LB FF sp s (Z.of_nat (length txt) + 1) /\ (s + Z.of_nat (length txt) + 1 <= dp \/ dp + 8 <= s) /\
                  L5.defined M dp 8 /\ PMSA.acobj ar FF sp dp 8 /\ dp mod 8 = 0 /\ shadow_zero M dp 1)
      (fun R M R' M' LB' cr' LBk W => PMSA.a0 R' (s + Z.of_nat (length txt)) /\ (exists c, getr R' 11%bv = Z_to_bv 64 c /\ In c [0; 34]) /\
                                      LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(dp, 8); (hl_tp L - 164, 4)]).

(* [comment removed for export] *)
Definition SNPRINTF_SCR_A : Z := 12288.    (* [comment removed for export] *)
Definition snprintf_g_specA (pc fmt : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (buf p v sp r : Z),
    PMSA.cps_asan L ar HI pc r sp SNPRINTF_SCR_A LB FF LK cr A 0
      (fun R M => PMSA.a0 R buf /\ PMSA.a1 R 100 /\ PMSA.a2 R fmt /\ PMSA.a3 R p /\ (p = 15 \/ p = 17) /\
                  getr R 14%bv = Z_to_bv 64 v /\ 0 <= v < 2 ^ 64 /\ PMLA.img_ro IC M /\ PMSA.stksh ar M sp SNPRINTF_SCR_A /\
                  L5.defined M buf 100 /\ PMSA.ainfr FF buf 100 /\ aacc M buf 100)
      (fun R M R' M' LB' cr' LBk W => (exists txt, gtext txt /\ 1 <= Z.of_nat (length txt) <= 25 /\ PMSA.a0 R' (Z.of_nat (length txt)) /\
                                                 L5.bytes_at (hl_segs L) M' buf txt /\ PMSA.u8 L M' (buf + Z.of_nat (length txt)) 0 /\ L5.defined M' buf 100) /\
                                      LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(buf, 100)]).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STRX_SCR_A : Z := PMSA.STR_SCR.                                              (* [comment removed for export] *)
Definition DB_SCR_A : Z := 112 + STRX_SCR_A.
Definition PR_SCR_A : Z := 96 + 48 + STRX_SCR_A.
Definition DF_SCR_A : Z := 128 + Z.max SNPRINTF_SCR_A (Z.max PMSA.DECSTR_SCR DB_SCR_A).
Definition DT_SCR_A : Z := 128 + Z.max DF_SCR_A (Z.max (80 + 80) PR_SCR_A).
Definition WD_SCR_A : Z := 96 + DT_SCR_A.                                               (* [comment removed for export] *)
Definition WD_SCR_XA : Z := 12800.          (* [comment removed for export] *)
Definition WD_D_XA : Z := 4.                (* [comment removed for export] *)
End SpecsA.
Lemma WD_SCR_A_val : WD_SCR_A = 12640. Proof. vm_compute. reflexivity. Qed.
Lemma WD_SCR_A_le : WD_SCR_A <= WD_SCR_XA. Proof. vm_compute. discriminate. Qed.
End PMFXA.
