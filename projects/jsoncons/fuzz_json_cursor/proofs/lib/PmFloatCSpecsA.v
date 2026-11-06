(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibDefsA PmCurDefs PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeapA CutL5A.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMFCA.

Definition TXT_INF : list Z := [105; 110; 102].       Definition TXT_NAN : list Z := [110; 97; 110].
Definition gtext (txt : list Z) : Prop := PML.num_final txt \/ In txt [TXT_INF; 45 :: TXT_INF; TXT_NAN; 45 :: TXT_NAN].

Definition txt_home (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (sp s n : Z) : Prop :=
  (exists b, In b LB /\ fst b <= s /\ s + n <= fst b + snd b) \/ CL5A.acobj ar FF sp s n.

Definition PC_SNPRINTF_casan : Z := 0x6a5a0.

Section SpecsA.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.

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

Definition SNPRINTF_SCR_A : Z := 12288.
Definition snprintf_g_specA (pc fmt : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (buf p v sp r : Z),
    PMSA.cps_asan L ar HI pc r sp SNPRINTF_SCR_A LB FF LK cr A 0
      (fun R M => PMSA.a0 R buf /\ PMSA.a1 R 100 /\ PMSA.a2 R fmt /\ PMSA.a3 R p /\ (p = 15 \/ p = 17) /\
                  getr R 14%bv = Z_to_bv 64 v /\ 0 <= v < 2 ^ 64 /\ PMLA.img_ro IC M /\ PMSA.stksh ar M sp SNPRINTF_SCR_A /\
                  L5.defined M buf 100 /\ PMSA.ainfr FF buf 100 /\ aacc M buf 100)
      (fun R M R' M' LB' cr' LBk W => (exists txt, gtext txt /\ 1 <= Z.of_nat (length txt) <= 25 /\ PMSA.a0 R' (Z.of_nat (length txt)) /\
                                                 L5.bytes_at (hl_segs L) M' buf txt /\ PMSA.u8 L M' (buf + Z.of_nat (length txt)) 0 /\ L5.defined M' buf 100) /\
                                      LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(buf, 100)]).

Definition FROMINT_SCR_A : Z := 512 + PMSA.STR_SCR.
Definition FROMINT_D : Z := 2.
Definition WD_SCR_A : Z := 2048 + Z.max SNPRINTF_SCR_A (Z.max PMSA.DECSTR_SCR PMSA.STR_SCR).
Definition WD_D : Z := 5.

Definition sso_grownA (LB : list (Z * Z)) (FF : list fframe) (cr : credit) (M' : word -> option byte) (o : Z) (s' : list Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
     (Z.of_nat (length s') <= 22 /\ PMLA.str_at (hl_segs L) M' o (PML.SShort s') /\ L5.defined M' o 24 /\ LB' = LB /\ cr' = cr)
  \/ (exists p, 23 <= Z.of_nat (length s') < 48 /\ PMLA.str_at (hl_segs L) M' o (PML.SLong 48 p s') /\ L5.defined M' o 24 /\
                PMLA.afresh L ar LB FF M' p 48 /\ LB' = (p, 48) :: LB /\ cr' = adebit L cr 48).

Definition from_integer_specA (pc : Z) (vrange : Z -> Prop) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o v sp r : Z),
    PMSA.cps_asan L ar HI pc r sp FROMINT_SCR_A LB FF LK cr A FROMINT_D
      (fun R M => PMSA.a0 R v /\ vrange v /\ PMSA.a1 R o /\ PMLA.str_at (hl_segs L) M o (PML.SShort []) /\ L5.defined M o 24 /\
                  PMLA.fobj M FF o 24 /\ PMSA.stksh ar M sp FROMINT_SCR_A /\ PMLA.img_ro IC M /\ sp mod 32 = 16)
      (fun R M R' M' LB' cr' LBk W => exists d, 1 <= Z.of_nat (length d) <= 20 /\ PMLA.str_at (hl_segs L) M' o (PML.SShort d) /\
                                              PMSA.a0 R' (Z.of_nat (length d)) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(o, 24)]).
Definition PC_FROM_INT_U64_casan : Z := 0xccf40.   Definition PC_FROM_INT_I64_casan : Z := 0xcd580.   Definition PC_WRITE_DOUBLE_casan : Z := 0xcdc30.
Definition from_integer_u64_specA (pc : Z) : Prop := from_integer_specA pc (fun v => 0 <= v < 2 ^ 64).
Definition from_integer_i64_specA (pc : Z) : Prop := from_integer_specA pc (fun v => 0 <= v < 2 ^ 64).

Definition write_double_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (wd o dp sp r : Z),
    PMSA.cps_asan L ar HI pc r sp WD_SCR_A LB FF LK cr A WD_D
      (fun R M => PMSA.a0 R wd /\ PMSA.a1 R o /\ PMSA.u8 L M wd 0 /\ PMSA.u32 L M (wd + 4) 0 /\ PMSA.u8 L M (wd + 8) dp /\ PMSA.acobj ar FF sp wd 12 /\
                  PMLA.str_at (hl_segs L) M o (PML.SShort []) /\ L5.defined M o 24 /\ PMLA.fobj M FF o 24 /\ PMLA.apart wd 12 o 24 /\
                  PMSA.stksh ar M sp WD_SCR_A /\ PMLA.img_ro IC M /\ acredit_ok L cr 48 /\ sp mod 32 = 16)
      (fun R M R' M' LB' cr' LBk W => PMSA.a0 R' 0 /\ (exists s', 1 <= Z.of_nat (length s') <= 47 /\ sso_grownA LB FF cr M' o s' LB' cr') /\ LBk = LB /\
                                      W = [(o, 24); (hl_tp L - 164, 4)]).

Definition PR_SCR : Z := 128 + PMSA.STR_SCR.
Definition DB_SCR : Z := 128 + PMSA.STR_SCR.
Definition DF_SCR : Z := 256 + Z.max SNPRINTF_SCR_A (Z.max PMSA.DECSTR_SCR DB_SCR).
Definition DT_SCR : Z := 256 + Z.max DF_SCR (Z.max PR_SCR 512).
Definition DF_D : Z := 3.
Definition DT_D : Z := 4.
Definition PC_DTOA_TRUE_casan : Z := 0xd0f74.   Definition PC_DTOA_FALSE_casan : Z := 0xd12f4.   Definition PC_PRETTIFY_casan : Z := 0xcfbb0.
Definition PC_DUMP_BUFFER_casan : Z := 0xcee28.

Definition sso_nonul (M : word -> option byte) (o : Z) (s : list Z) : Prop :=
  (length s <= 22)%nat /\ L5.u8_at (hl_segs L) M o (2 * Z.of_nat (length s)) /\ L5.bytes_at (hl_segs L) M (o + 1) s.
Definition l48_nonul (M : word -> option byte) (o p : Z) (s : list Z) : Prop :=
  L5.u64_at (hl_segs L) M o 49 /\ L5.u64_at (hl_segs L) M (o + 8) (Z.of_nat (length s)) /\ L5.u64_at (hl_segs L) M (o + 16) p /\ L5.bytes_at (hl_segs L) M p s.
Definition str_push_back_short_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o c sp r : Z) (s : list Z),
    PMSA.cps_asan L ar HI pc r sp PMSA.STR_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R o /\ PMSA.a1 R c /\ 0 <= c < 256 /\ sso_nonul M o s /\ L5.defined M o 24 /\ PMLA.fobj M FF o 24 /\
                  PMSA.stksh ar M sp PMSA.STR_SCR /\ (Z.of_nat (length s) = 22 -> acredit_ok L cr 48))
      (fun R M R' M' LB' cr' LBk W => sso_grownA LB FF cr M' o (s ++ [c]) LB' cr' /\ LBk = LB /\ W = [(o, 24)]).
Definition str_push_back_l48_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o p c sp r : Z) (s : list Z),
    PMSA.cps_asan L ar HI pc r sp PMSA.STR_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R o /\ PMSA.a1 R c /\ 0 <= c < 256 /\ l48_nonul M o p s /\ Z.of_nat (length s) < 47 /\ In (p, 48) LB /\ shadow_blk M p 48 /\
                  PMLA.fobj M FF o 24 /\ PMSA.stksh ar M sp PMSA.STR_SCR)
      (fun R M R' M' LB' cr' LBk W => PMLA.str_at (hl_segs L) M' o (PML.SLong 48 p (s ++ [c])) /\ shadow_blk M' p 48 /\ LB' = LB /\ cr' = cr /\
                                      LBk = lb_remove p LB /\ W = [(o, 24)]).
Definition PC_PUSH_BACK_casan : Z := 0xf07bc.

Definition prettify_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (buf len k o sp r : Z) (s0 : list Z),
    PMSA.cps_asan L ar HI pc r sp PR_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R buf /\ PMSA.a1 R len /\ PMSA.a2 R k /\ PMSA.a3 R (-4) /\ getr R 14%bv = Z_to_bv 64 17 /\ getr R 15%bv = Z_to_bv 64 o /\
                  1 <= len <= 21 /\ -343 <= k <= 309 /\
                  L5.defined M buf 24 /\ buf mod 8 = 0 /\ shadow_zero M buf 3 /\ CL5A.ainfr FF buf 24 /\
                  PMLA.str_at (hl_segs L) M o (PML.SShort s0) /\ (s0 = [] \/ s0 = [45]) /\ L5.defined M o 24 /\ PMLA.fobj M FF o 24 /\ PMLA.apart buf 24 o 24 /\
                  PMSA.stksh ar M sp PR_SCR /\ acredit_ok L cr 48)
      (fun R M R' M' LB' cr' LBk W => (exists s', 1 <= Z.of_nat (length s') <= 47 /\ sso_grownA LB FF cr M' o s' LB' cr') /\ LBk = LB /\ W = [(o, 24)]).

Definition dump_buffer_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (buf len dp o sp r : Z),
    PMSA.cps_asan L ar HI pc r sp DB_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R buf /\ PMSA.a1 R len /\ PMSA.a2 R dp /\ PMSA.a3 R o /\ 1 <= len <= 25 /\ 0 <= dp <= 255 /\
                  L5.defined M buf 32 /\ buf mod 8 = 0 /\ shadow_zero M buf 4 /\ CL5A.ainfr FF buf 32 /\
                  PMLA.str_at (hl_segs L) M o (PML.SShort []) /\ L5.defined M o 24 /\ PMLA.fobj M FF o 24 /\ PMLA.apart buf 32 o 24 /\
                  PMSA.stksh ar M sp DB_SCR /\ acredit_ok L cr 48)
      (fun R M R' M' LB' cr' LBk W => (exists s', 1 <= Z.of_nat (length s') <= 47 /\ sso_grownA LB FF cr M' o s' LB' cr') /\ LBk = LB /\ W = [(o, 24)]).

Definition dtoa_specA (pc scr dd : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (dp o sp r : Z),
    PMSA.cps_asan L ar HI pc r sp scr LB FF LK cr A dd
      (fun R M => PMSA.a0 R dp /\ 0 <= dp <= 255 /\ PMSA.a1 R o /\
                  PMLA.str_at (hl_segs L) M o (PML.SShort []) /\ L5.defined M o 24 /\ PMLA.fobj M FF o 24 /\
                  PMSA.stksh ar M sp scr /\ PMLA.img_ro IC M /\ acredit_ok L cr 48 /\ sp mod 32 = 0)
      (fun R M R' M' LB' cr' LBk W => PMSA.a0 R' 1 /\ (exists s', 1 <= Z.of_nat (length s') <= 47 /\ sso_grownA LB FF cr M' o s' LB' cr') /\ LBk = LB /\
                                      W = [(o, 24); (hl_tp L - 164, 4)]).
Definition dtoa_false_specA (pc : Z) : Prop := dtoa_specA pc DF_SCR DF_D.
Definition dtoa_true_specA (pc : Z) : Prop := dtoa_specA pc DT_SCR DT_D.

End SpecsA.
End PMFCA.
