From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
Import ListNotations.
Open Scope Z_scope.

(** reac_headamp_prop_parse_result(props, out, max, res) (reac-pw f86a30a3 src/reac_headamp_prop.c:108-182; 1188
    bytes, 297 instructions at 0x14cd0 in the UBSan image; frame 0x90 bytes, saves ra, s0-s11 at sp - 8 .. sp - 104
    and fs0 at sp - 112, then s0 = res, s2 = max, s3 = out). The plain logic (lib/Prog/reac_headamp_prop_parse_result_c.v)
    with the UBSan numbers (strncmp 0x1dd0c, strtol 0x1ce98 with dot at sp + 0x18 of its frame, strcmp 0x1dc44, SSP
    GOT 0x1f3e8 -> guard 0x509d0) and 17 trap branches, all to the one `unimp` 0x15170, each discharged by a premise below or by a fact of the walk:
      0x14d20 / 0x15158 res & 3 (alignment of the res stores, res <> 0 only): R mod 4 = 0;
      0x14d3c props & 3: P mod 16 = 0;
      0x14dd4 prop & 3: the found prop is P + 16 + 8k (find-loop invariant);
      0x14e30 C = 0, 0x14e6c / 0x14e7c the key's end pointer: C >= P + 24 > 0 and P + len <= lo < 2^64;
      0x14ed8 keys + 1 overflow: keys <= the pod's length / 8; 0x14ee0 key + 13 wrap: key < P + len;
      0x14f08 dot = 0, 0x14f20 dot = -1: dot = rest + end with end >= 1, inside the pod;
      0x15010 / 0x15024 / 0x15028 out + 3n (null, wrap, sign): O <> 0, 0 <= n < cap, O + 3 (cap + 1) <= lo;
      0x150b4 / 0x150c4 the float-to-long cast bounds of reac_float_nearest: 0 <= d < 256 tested first
        (Prog/ParseFP.v rfn_hw_above / rfn_hw_below, with the words 0xc3e0000000000001 and 0x43e0000000000000);
      0x150dc r - 1 overflow: dead, t = trunc d >= 0.
    It writes its frame [sp - 0x90, sp), the stack of strtol (0x120) and __intscan (0x50) below it, errno, out[0, 3n),
    res when res <> 0; the caller-saved registers and the FP state (stated free, frm kept 0).

    Callee contracts its walk takes as premises: U/Prog/strtol_c.v strtol_contract (STRTOL = 0x1ce98), U/Prog/strncmp_c.v strncmp_contract (0x1dd0c), U/Prog/strcmp_c.v
    strcmp_contract (0x1dc44), Prog/ParseFP.v (kit: rfn_hw_nearest, rfn_hw_t_range,
    rfn_hw_above, rfn_hw_below), Pod/SpaBool.v spa_get_bool. U/Prog/ParseSites.v states what the walk must show at
    each of these call sites. The answer is Pod/Headamp.v's parse_props, whose parse_key reads Pod/Strtol.v's s10_val /
    s10_end (re-exported from the PLAIN Prog/__intscan_c.v); U/Prog/strtol_c.v states its post with U/Prog/__intscan_c.v's
    s10_*, the same bodies: the walk joins the two by eq_refl.

    Call sites (LLVMFuzzerTestOneInput, UBSan), sp = S - 608 (the harness frame):
      0x14158 `jal reac_headamp_prop_parse_result` with
        a0 = s5 = (null ? 0 : pod) (0x1413c `ld s8,0x10(sp)`: the frame cell sp + 0x10 = 1 - null; 0x14140
             `neg a0,s8`, 0x14144 `and s5,a0,s1`; s1 = pod, malloc(len) at 0x140e0 filled by memcpy at 0x14100);
        a1 = s3 = out (malloc(3cap + 3) at 0x14114, memset 0xa5 at 0x14128); a2 = s2 = cap (0x140ec
             `lbu s2,8(sp)`); a3 = sp + 0x178 = &res (0x14148), set to 0x5a at 0x14134-0x14138;
      and, with res = NULL, through reac_headamp_prop_parse (U/Prog/reac_headamp_prop_parse_c.v) at 0x14818.
    Why each premise holds there: as in the plain file, with res = S - 608 + 0x178 4-aligned and lo + 512 <= S - 608:
    U/Prog/HeadSites.v parse_site_check, parse_site_plain. *)
Definition HA_PARSE_RESULT : Z := 0x14cd0.
Definition PARSE_FRAME : Z := 0x90.
Definition PARSE_STACK : Z := 0x90 + 0x120 + 0x50.
Definition PARSE_SSP_GOT : Z := 0x1f3e8.
Definition PARSE_SSP_GUARD : Z := 0x509d0.
(* errno: __errno_location (0x167f0) is `mv a0,tp; addi a0,a0,-0xa4`. *)
Definition PARSE_ERRNO (tp : word) : Z := bv_unsigned tp + -164.

Definition parse_arg (null : bool) (bs : list byte) : option (list byte) := if null then None else Some bs.

Definition parse_writes (sp O n E R : Z) : list ivl :=
  [(sp - PARSE_STACK, sp); (O, O + 3 * n); (E, E + 4)] ++ (if R =? 0 then [] else [(R, R + 12)]).
Definition parse_space (lo sp O cap E R : Z) : list ivl :=
  [(lo, sp); (O, O + 3 * (cap + 1)); (E, E + 4)] ++ (if R =? 0 then [] else [(R, R + 12)]).

Definition parse_args (m : word -> option byte) (lo sp : Z) (tp : word) (P O cap R : Z) (bs : list byte)
    (ev can : word) : Prop :=
  bytes_at rsegs m P bs /\ 0 < P /\ P mod 16 = 0 /\
  8 <= Z.of_nat (length bs) <= 16384 /\ u32_at bs 0 = Z.of_nat (length bs) - 8 /\
  P + Z.of_nat (length bs) <= lo /\
  0 <= cap <= 9 /\ 0 < O /\ wr_at rsegs m O (3 * (cap + 1)) /\ O + 3 * (cap + 1) <= lo /\
  (O + 3 * (cap + 1) <= P \/ P + Z.of_nat (length bs) <= O) /\
  (R = 0 \/ (wr_at rsegs m R 12 /\ R mod 4 = 0 /\ sp <= R)) /\
  rw_cells rsegs m (PARSE_ERRNO tp) [C4 ev] /\
  disjoint_from [(lo, sp); (P, P + Z.of_nat (length bs)); (O, O + 3 * (cap + 1))] (PARSE_ERRNO tp) 4 /\
  (R = 0 \/ disjoint_from [(PARSE_ERRNO tp, PARSE_ERRNO tp + 4)] R 12) /\
  bytes_at rsegs m PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD)) /\
  bytes_at rsegs m PARSE_SSP_GUARD (le8 can) /\
  disjoint_from (parse_space lo sp O cap (PARSE_ERRNO tp) R) PARSE_SSP_GOT 8 /\
  disjoint_from (parse_space lo sp O cap (PARSE_ERRNO tp) R) PARSE_SSP_GUARD 8.

Definition parse_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : word -> option byte)
    (lo O R : Z) (o : answer) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (ev' : word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (ans_rc o)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\
    munch (parse_writes (bv_unsigned sp) O (Z.of_nat (length (ans_cells o))) (PARSE_ERRNO tp) R) m m' /\
    bytes_at rsegs m' O (ha_cells_bytes (ans_cells o)) /\
    (R <> 0 -> bytes_at rsegs m' R (ans_res_bytes o)) /\
    rw_cells rsegs m' (PARSE_ERRNO tp) [C4 ev'] /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

Definition reac_headamp_prop_parse_result_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (null : bool) (lo P O cap R : Z)
         (bs : list byte) (ev can : word),
    a0 = Z_to_bv 64 (if null then 0 else P) -> a1 = Z_to_bv 64 O -> a2 = Z_to_bv 64 cap -> a3 = Z_to_bv 64 R ->
    parse_args m lo (bv_unsigned sp) tp P O cap R bs ev can ->
    stk rsegs m lo (bv_unsigned sp) -> lo + PARSE_STACK <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    frm0 fc -> mem_inv rsegs m ->
    evt rsegs
      (parse_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo O R (parse_props (parse_arg null bs) cap))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HA_PARSE_RESULT) fc None m (seg_rom rsegs)).
