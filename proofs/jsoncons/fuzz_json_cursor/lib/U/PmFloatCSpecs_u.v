(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmLibSpecs_u.
Import ListNotations.
Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMFC.

Definition PC_FROM_INT_U64 : Z := 0x431b0.   Definition PC_FROM_INT_I64 : Z := 0x432fc.   Definition PC_WRITE_DOUBLE : Z := 0x43520.
Definition PC_DUMP_BUFFER : Z := 0x43d90.    Definition PC_GRISU3 : Z := 0x44178.         Definition PC_PRETTIFY : Z := 0x44530.
Definition PC_DIGIT_GEN : Z := 0x44940.      Definition PC_FILL_EXP : Z := 0x44d84.       Definition PC_DTOA_TRUE : Z := 0x450a8.
Definition PC_DTOA_FALSE : Z := 0x4517c.     Definition PC_SNPRINTF : Z := 0xacd08.

Section Specs.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable STRTOD_SCR : Z.

Definition STR_SCR : Z := PMS.STR_SCR.
Definition FROMINT_SCR : Z := 320 + STR_SCR.
Definition SNPRINTF_SCR : Z := 6144.
Definition DTOA_FALSE_SCR : Z := 160 + Z.max SNPRINTF_SCR (Z.max (96 + STRTOD_SCR) (96 + STR_SCR)).
Definition DTOA_TRUE_SCR : Z := 144 + Z.max DTOA_FALSE_SCR (Z.max (80 + 80) (64 + 32 + Z.max 464 STR_SCR)).
Definition WD_SCR : Z := 256 + DTOA_TRUE_SCR.

Definition sso_grown (LB : list (Z * Z)) (cr : credit) (M' : mem) (o : Z) (s' : list Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
     (Z.of_nat (length s') <= 22 /\ str_at M' o (SShort s') /\ L5.defined M' o 24 /\ LB' = LB /\ cr' = cr)
  \/ (exists p, 23 <= Z.of_nat (length s') < 48 /\ str_at M' o (SLong 48 p s') /\ L5.defined M' o 24 /\ L5C.fresh_block L LB M' p 48 /\
                LB' = (p, 48) :: LB /\ cr' = debit L cr 48).

Definition str_push_back_sso_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (o c sp r : Z) (s : list Z),
    cps_heap L HI PC_STR_PUSH_BACK r sp STR_SCR LB cr
      (fun R M => entry L R M sp r STR_SCR /\ a0 R o /\ a1 R c /\ 0 <= c < 256 /\ str_at M o (SShort s) /\ Z.of_nat (length s) <= 22 /\
                  L5.defined M o 24 /\ obj_on_stack L sp o 24 /\ (Z.of_nat (length s) = 22 -> credit_ok L cr 48))
      (fun R M R' M' LB' cr' LBk W => sso_grown LB cr M' o (s ++ [c]) LB' cr' /\ LBk = LB /\ W = [(o, 24)]).

Definition num_str (LB : list (Z * Z)) (cr : credit) (M' : mem) (o : Z) (s' : list Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  sso_grown LB cr M' o s' LB' cr'.

Definition from_integer_spec (pc : Z) (vrange : Z -> Prop) : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (o v sp r : Z),
    cps_heap L HI pc r sp FROMINT_SCR LB cr
      (fun R M => entry L R M sp r FROMINT_SCR /\ a0 R v /\ vrange v /\ a1 R o /\ str_at M o (SShort []) /\ L5.defined M o 24 /\
                  obj_on_stack L sp o 24 /\ img_ro M)
      (fun R M R' M' LB' cr' LBk W => exists d, 1 <= Z.of_nat (length d) <= 20 /\ str_at M' o (SShort d) /\ a0 R' (Z.of_nat (length d)) /\
                                              LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(o, 24)]).
Definition from_integer_u64_spec : Prop := from_integer_spec PC_FROM_INT_U64 (fun v => 0 <= v < 2 ^ 64).

Definition from_integer_i64_spec : Prop := from_integer_spec PC_FROM_INT_I64 (fun v => 0 <= v < 2 ^ 64).

Definition write_double_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (wd o dp sp r : Z),
    cps_heap L HI PC_WRITE_DOUBLE r sp WD_SCR LB cr
      (fun R M => entry L R M sp r WD_SCR /\ a0 R wd /\ a1 R o /\ sp <= wd /\ wd + 9 <= hl_sptop L /\ u8 M wd 0 /\ u32 M (wd + 4) 0 /\ u8 M (wd + 8) dp /\
                  str_at M o (SShort []) /\ L5.defined M o 24 /\ obj_on_stack L sp o 24 /\ img_ro M /\ credit_ok L cr 48)
      (fun R M R' M' LB' cr' LBk W => a0 R' 0 /\ (exists s', 1 <= Z.of_nat (length s') <= 47 /\ num_str LB cr M' o s' LB' cr') /\ LBk = LB /\ W = [(o, 24)]).

Definition FMT_G : Z := 0x130d8.

Definition TXT_INF : list Z := [105; 110; 102].       Definition TXT_NAN : list Z := [110; 97; 110].
Definition gtext (txt : list Z) : Prop := num_final txt \/ In txt [TXT_INF; 45 :: TXT_INF; TXT_NAN; 45 :: TXT_NAN].

Definition snprintf_g_spec : Prop :=
  forall (buf p v sp r : Z),
    cps_pure PC_SNPRINTF r sp SNPRINTF_SCR [(buf, 100)]
      (fun R M => entry L R M sp r SNPRINTF_SCR /\ a0 R buf /\ a1 R 100 /\ a2 R FMT_G /\ a3 R p /\ (p = 15 \/ p = 17) /\
                  getr R 14%bv = Z_to_bv 64 v /\ 0 <= v < 2 ^ 64 /\ img_ro M /\
                  L5.defined M buf 100 /\ sp <= buf /\ buf + 100 <= hl_sptop L)
      (fun R M R' M' => exists txt, gtext txt /\ 1 <= Z.of_nat (length txt) <= 25 /\ a0 R' (Z.of_nat (length txt)) /\
                                    L5.bytes_at RSEGS M' buf txt /\ u8 M' (buf + Z.of_nat (length txt)) 0 /\ L5.defined M' buf 100).

Definition decstr_to_double_g_spec : Prop :=
  forall (s dp sp r : Z) (txt : list Z),
    cps_pure PC_DECSTR_DOUBLE r sp (96 + STRTOD_SCR) [(dp, 8); (TP - 164, 4)]
      (fun R M => entry L R M sp r (96 + STRTOD_SCR) /\ a0 R s /\ a1 R (Z.of_nat (length txt)) /\ a2 R dp /\ img_ro M /\
                  L5.bytes_at RSEGS M s txt /\ u8 M (s + Z.of_nat (length txt)) 0 /\ gtext txt /\ Z.of_nat (length txt) < 2 ^ 26 /\
                  L5.defined M dp 8 /\ sp <= dp /\ dp + 8 <= hl_sptop L /\
                  L5.defined M s (Z.of_nat (length txt) + 1) /\ 4096 <= s /\ s + Z.of_nat (length txt) < 2 ^ 47 /\
                  (s + Z.of_nat (length txt) + 1 <= sp - (96 + STRTOD_SCR) \/ sp <= s) /\
                  (s + Z.of_nat (length txt) + 1 <= TP - 164 \/ TP - 160 <= s))
      (fun R M R' M' => a0 R' (s + Z.of_nat (length txt)) /\ exists c, getr R' 11%bv = Z_to_bv 64 c /\ In c [0; 34]).

End Specs.
End PMFC.
