(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface N6_tac N6_mem_is_zero N6_rip N6_quick N6_memset N6_memcpy N6_imm N6_memmove.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import N8Store.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section IMEMMOVE.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src junk : list byte) (lo : Z).
  Hypothesis SRC : bytes_at asegs m (bv_unsigned a1) src.
  Hypothesis LEN : length src = Z.to_nat (bv_unsigned a2).
  Hypothesis DST : rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk].
  Hypothesis SEP : bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1.
  Hypothesis ACCS : accessible m (bv_unsigned a1) (bv_unsigned a2).
  Hypothesis ACCD : accessible m (bv_unsigned a0) (bv_unsigned a2).
  Hypothesis SVS : shvis m (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2).
  Hypothesis SVD : shvis m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2).
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - AINTRIN_STACK.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis AC : ACONST m.
  (* [comment removed for export] *)
  Hypothesis N40 : bv_unsigned a2 <= 2^40.
  Hypothesis INMS : in_app_mem (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2).
  Hypothesis INMD : in_app_mem (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2).
  Hypothesis AOK : aconst_ok (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2).
  Hypothesis DJD : bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0.
  Hypothesis DJS : bv_unsigned a1 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a1.

  Notation dst := (bv_unsigned a0).
  Notation sa := (bv_unsigned a1).
  Notation n := (bv_unsigned a2).
  Notation POST := (amemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a2 src lo m).
  Notation SP2 := (Z_to_bv 64 (bv_unsigned sp + -2144)).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - 4096, bv_unsigned sp)].
  (* [comment removed for export] *)
  Notation RST pc x1 x5 x9 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 mm :=
    (MS (mkR x1 SP2 gp tp x5 t1 t2 sp x9 a0 a1 a2 x13 x14 x15 x16 x17 x18 x19 x20 SP2 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation FRAME mm := (rw_cells asegs mm (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  (* [comment removed for export] *)
  Section JM.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis SRCm : bytes_at asegs mm (bv_unsigned a1) src.
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk].
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis G1 : rw_cells asegs mm 1791384 [C8 (Z_to_bv 64 1835576)].
    Hypothesis C1 : rw_cells asegs mm 1835576 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 1791392 [C8 (Z_to_bv 64 1838888)].
    Hypothesis G3 : rw_cells asegs mm 1791400 [C8 (Z_to_bv 64 1838896)].
    Hypothesis G4 : rw_cells asegs mm 1791408 [C8 (Z_to_bv 64 1838880)].
    Hypothesis C4 : rw_cells asegs mm 1838880 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

    (* [comment removed for export] *)
  End JM.

  (* [comment removed for export] *)
  Section JRD.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis SRCm : bytes_at asegs mm (bv_unsigned a1) src.
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk].
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis G1 : rw_cells asegs mm 1791384 [C8 (Z_to_bv 64 1835576)].
    Hypothesis C1 : rw_cells asegs mm 1835576 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 1791392 [C8 (Z_to_bv 64 1838888)].
    Hypothesis G3 : rw_cells asegs mm 1791400 [C8 (Z_to_bv 64 1838896)].
    Hypothesis G4 : rw_cells asegs mm 1791408 [C8 (Z_to_bv 64 1838880)].
    Hypothesis C4 : rw_cells asegs mm 1838880 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

    (* [comment removed for export] *)
  End JRD.

  (* [comment removed for export] *)
  Section JQD.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis SRCm : bytes_at asegs mm (bv_unsigned a1) src.
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk].
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis G1 : rw_cells asegs mm 1791384 [C8 (Z_to_bv 64 1835576)].
    Hypothesis C1 : rw_cells asegs mm 1835576 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 1791392 [C8 (Z_to_bv 64 1838888)].
    Hypothesis G3 : rw_cells asegs mm 1791400 [C8 (Z_to_bv 64 1838896)].
    Hypothesis G4 : rw_cells asegs mm 1791408 [C8 (Z_to_bv 64 1838880)].
    Hypothesis C4 : rw_cells asegs mm 1838880 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
    Hypothesis N64 : 1 <= bv_unsigned a2 <= 64.

    (* [comment removed for export] *)

    Section LoopD.
      Variables (q1 : Z) (qj : list byte).
      Hypothesis QA : u8arr asegs mm (8 * q1) qj.
      Hypothesis QB : 8 * q1 <= sh dst /\ sh (dst + n - 1) < 8 * q1 + Z.of_nat (length qj).
      Hypothesis SR12 : 2147450880 <= sh dst /\ sh (dst + n - 1) < 17594333495296.
    End LoopD.

    Hypothesis SVDm : stk asegs mm (sh (hull_lo dst)) (sh (hull_hi (dst + n))).

    (* [comment removed for export] *)
  End JQD.

  (* [comment removed for export] *)
  Section JD.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis SRCm : bytes_at asegs mm (bv_unsigned a1) src.
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk].
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis G1 : rw_cells asegs mm 1791384 [C8 (Z_to_bv 64 1835576)].
    Hypothesis C1 : rw_cells asegs mm 1835576 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 1791392 [C8 (Z_to_bv 64 1838888)].
    Hypothesis G3 : rw_cells asegs mm 1791400 [C8 (Z_to_bv 64 1838896)].
    Hypothesis G4 : rw_cells asegs mm 1791408 [C8 (Z_to_bv 64 1838880)].
    Hypothesis C4 : rw_cells asegs mm 1838880 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
    Hypothesis SVDm : stk asegs mm (sh (hull_lo dst)) (sh (hull_hi (dst + n))).

    (* [comment removed for export] *)
  End JD.

  (* [comment removed for export] *)
  Section JS.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis SRCm : bytes_at asegs mm (bv_unsigned a1) src.
    Hypothesis DSTm : rw_cells asegs mm (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk].
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2072 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis G1 : rw_cells asegs mm 1791384 [C8 (Z_to_bv 64 1835576)].
    Hypothesis C1 : rw_cells asegs mm 1835576 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 1791392 [C8 (Z_to_bv 64 1838888)].
    Hypothesis G3 : rw_cells asegs mm 1791400 [C8 (Z_to_bv 64 1838896)].
    Hypothesis G4 : rw_cells asegs mm 1791408 [C8 (Z_to_bv 64 1838880)].
    Hypothesis C4 : rw_cells asegs mm 1838880 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
    Hypothesis SVDm : stk asegs mm (sh (hull_lo dst)) (sh (hull_hi (dst + n))).

    (* [comment removed for export] *)

    Hypothesis N64 : 1 <= bv_unsigned a2 <= 64.

    (* [comment removed for export] *)

    Section LoopS.
      Variables (q1 : Z) (qj : list byte).
      Hypothesis QA : u8arr asegs mm (8 * q1) qj.
      Hypothesis QB : 8 * q1 <= sh sa /\ sh (sa + n - 1) < 8 * q1 + Z.of_nat (length qj).
      Hypothesis SR12 : 2147450880 <= sh sa /\ sh (sa + n - 1) < 17594333495296.
    End LoopS.

    Hypothesis SVSm : stk asegs mm (sh (hull_lo sa)) (sh (hull_hi (sa + n))).

    (* [comment removed for export] *)
  End JS.

End IMEMMOVE.
(* [comment removed for export] *)
