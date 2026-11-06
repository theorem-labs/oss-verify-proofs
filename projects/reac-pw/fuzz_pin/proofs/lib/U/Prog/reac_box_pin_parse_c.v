From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import fuzz_catalogue_row_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_box_pin_parse(spec, model, label) (reac-pw src/reac_box_pin.c, read from the binary; 420 bytes, 105
    instructions at 0x12f08 in the UBSan image; frame 128 bytes, saves ra, s0-s11 at sp-8 .. sp-104; model is spilled
    to sp+8, the count is at sp+16). The plain algorithm (lib/Prog/reac_box_pin_parse_c.v) with the UBSan addresses:
    strcspn 0x1b13c (0x12f70), reac_box_catalogue 0x13134 with &count = sp + 16 (0x12f7c), strlen 0x1b334 (0x12fe4),
    strncmp 0x1b3c4 (0x12ff8); the loop counts i up to count and walks s7 = table + 0x128 i. Its one trap site,
    0x130a8 `unimp`, is reached from nine UBSan checks:
      0x12fbc / 0x12fc0 / 0x12fd4: table + i * 0x128 null, wrapped, or i * 0x128 overflowing (pointer-overflow);
      0x12fd8: table null or not 8-aligned (type-mismatch / alignment, s11);
      0x13014 / 0x13024 / 0x1302c: spec + toklen wrapped, null, or spec + toklen + 1 wrapping (= 2^64 - 1);
      0x1304c: model not 8-aligned; 0x1305c: label not 8-aligned (tested after *model is stored).
    The table is FUZZ_CATALOGUE = 0x1c848 (8-aligned, nonzero) and i * 0x128 < 3256, so the first four never fire;
    bytes_at of spec's string, NUL and slack gives spec + |str| + 1 + |slack| <= 2^64, and spec <> 0 when live, so
    the next three never fire (toklen + 1 <= |str| on that path, spec[toklen] being ':'); the last two are this
    contract's alignment premise on model and label (the plain contract has none: the plain code stores at any
    address). Writes: its frame and strcspn's 96 bytes below it, [sp - 224, sp), and on success the 8 bytes at model
    and at label. The return value is 0 or -1.

    Callee contracts its walk takes as premises (the released forms relocated to pin's UBSan image): U/Prog/strcspn_c.v
    strcspn_contract (STRCSPN = 0x1b13c, CSPN_SSP_GOT = 0x1d590, CSPN_SSP_GUARD = 0x4eb80; its own proof takes
    memset_contract and strchrnul_contract), U/Prog/reac_box_catalogue_c.v reac_box_catalogue_contract
    (REAC_BOX_CATALOGUE = 0x13134, BOX_CATALOGUE = 0x1c848; c = sp + 16, 8-aligned and writable), U/Prog/strlen_c.v
    (0x1b334) and U/Prog/strncmp_c.v (STRNCMP = 0x1b3c4).

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x12df8 `jal reac_box_pin_parse` with sp = S - 80, fl = s3 and
      a0 = 0 if fl bit 0 else spec (0x12dc4 `andi a0,s3,1`, 0x12de4 `addi a0,a0,-1`, 0x12dec `and a0,a0,s0`);
      a1 = 0 if fl bit 1 else sp + 16 (0x12dc8 `slli a1,s3,62`, 0x12dd4 `srli`, 0x12dd8 `addi`, 0x12ddc `and a1,a1,a2`);
      a2 = 0 if fl bit 2 else sp + 8 (0x12dd0 `slli s3,s3,61`, 0x12de8 `srli a3,s3,63`, `addi`, 0x12df4 `and`);
    the cells were zeroed at 0x12dbc / 0x12dc0; sp is 16-aligned (GV), so both cells are 8-aligned. Why each premise
    holds there: as in the plain build (FrameAPI U: ms_got_guard = 0x1d590, ms_guard = 0x4eb80). *)
Definition REAC_BOX_PIN_PARSE : Z := 0x12f08.
Definition PARSE_STACK : Z := 224.
Definition PARSE_SSP_GOT : Z := 0x1d590.
Definition PARSE_SSP_GUARD : Z := 0x4eb80.

(** spec, model and label are all non-NULL. *)
Definition parse_live (a0 a1 a2 : word) : bool :=
  negb (bv_unsigned a0 =? 0) && negb (bv_unsigned a1 =? 0) && negb (bv_unsigned a2 =? 0).

(** The plain build's parse_args, and model and label 8-aligned (the UBSan alignment checks). *)
Definition parse_args (m : word -> option byte) (lo sp sa mo lb : Z) (str slack : list byte) : Prop :=
  bytes_at rsegs m sa (str ++ NUL :: slack) /\ ~ In NUL str /\
  (- (sa + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) /\
  (sa + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ sp <= sa) /\
  wr_at rsegs m mo 8 /\ wr_at rsegs m lb 8 /\ (mo + 8 <= lb \/ lb + 8 <= mo) /\
  (mo + 8 <= lo \/ sp <= mo) /\ (lb + 8 <= lo \/ sp <= lb) /\
  mo mod 8 = 0 /\ lb mod 8 = 0.

Definition parse_mem (m m' : word -> option byte) (sp mo lb : Z) (o : option (Z * Z)) : Prop :=
  match o with
  | Some (row, lab) =>
      munch [(sp - PARSE_STACK, sp); (mo, mo + 8); (lb, lb + 8)] m m' /\
      bytes_at rsegs m' mo (le8 (Z_to_bv 64 row)) /\ bytes_at rsegs m' lb (le8 (Z_to_bv 64 lab))
  | None => munch [(sp - PARSE_STACK, sp)] m m'
  end.

Definition reac_box_pin_parse_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte) (lo : Z) (can : word),
    (parse_live a0 a1 a2 = true ->
       parse_args m lo (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) str slack) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + PARSE_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    (forall a, FUZZ_CATALOGUE <= a < FUZZ_CATALOGUE + CAT_BYTES -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    bytes_at rsegs m PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD)) ->
    bytes_at rsegs m PARSE_SSP_GUARD (le8 can) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (parse_rc (parse_out FUZZ_CATALOGUE (bv_unsigned a0) (parse_live a0 a1 a2) str)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         parse_mem m m' (bv_unsigned sp) (bv_unsigned a1) (bv_unsigned a2)
           (parse_out FUZZ_CATALOGUE (bv_unsigned a0) (parse_live a0 a1 a2) str))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_PIN_PARSE) fc None m (seg_rom rsegs)).
