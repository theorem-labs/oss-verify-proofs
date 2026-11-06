From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec fuzz_catalogue_row_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_box_pin_parse(spec, model, label) (reac-pw src/reac_box_pin.c, which the tree does not hold: read from the
    binary; 268 bytes, 67 instructions at 0x12e90 in the plain image; frame 80 bytes, saves ra, s0-s7 at sp-8 ..
    sp-72). In order:
      - a0 = 0, a2 = 0, a1 = 0 (in that order) or the byte at spec = 0: return -1 (0x12f6c), having stored only its
        frame;
      - toklen = strcspn(spec, ":") (0x12ee8, `jal 0x1b020`; the set ":" NUL is at 0x103a5 in .rodata);
      - table = reac_box_catalogue(&count) with &count = its sp (0x12ef4, `jal 0x13024`): FUZZ_CATALOGUE, count = 11;
      - for rows i = 0..count-1 (s4 = table + 0x128 i, s7 counts down): strlen(row token) (0x12f10, `jal 0x1b218`);
        when it is toklen, strncmp(spec, token, toklen) (0x12f24, `jal 0x1b2a8`); 0 selects row i (first match);
      - no row: return -1; row i: label = spec + toklen + 1 when spec[toklen] = ':' and spec[toklen + 1] <> 0, else
        the row's display pointer `ld s3,8(s4)`; then *model = row (0x12f64), *label = label (0x12f68), return 0.
    So it is parse_out FUZZ_CATALOGUE spec (spec, model, label all non-NULL) s of pin_spec. It reads spec's string
    and, through strcspn's word-at-a-time scan (via __strchrnul, the set having one byte), the bytes after its NUL up
    to the next 8-byte boundary (the slack premise, strcspn_c.v's for a set of length <= 1); the table (rw- segment:
    hence the table premise) and the tokens and ":" (.rodata, read-only: mem_inv); strcspn reads the stack-protector
    GOT cell and the guard. Writes: its frame and strcspn's 96 bytes below it, [sp - 176, sp) (reac_box_catalogue's
    count is in its frame), and, on success only, the 8 bytes at model and at label. The return value is 0 or -1
    (s2 = `addi s2,zero,-1`, the word 2^64 - 1). Every s register, sp, gp, tp and ra come back (its frame restores
    s0-s7 and ra; the callees keep s8-s11).

    Callee contracts its walk takes as premises (the released forms relocated to pin's image):
    strcspn_contract (Prog/strcspn_c.v, STRCSPN = 0x1b020, CSPN_SSP_GOT = 0x1d478, CSPN_SSP_GUARD = 0x4ea60; its own
    proof takes memset_contract and strchrnul_contract), reac_box_catalogue_contract (Prog/reac_box_catalogue_c.v,
    REAC_BOX_CATALOGUE = 0x13024, BOX_CATALOGUE = 0x1c730; c = sp, 8-aligned and writable), strlen_contract
    (Prog/strlen_c.v, 0x1b218) and strncmp_contract (Prog/strncmp_c.v, STRNCMP = 0x1b2a8, strncmp_model).

    Call site (LLVMFuzzerTestOneInput, plain): 0x12db8 `jal reac_box_pin_parse` with sp = S - 64 (the harness frame),
    fl = the flags byte (s3) and
      a0 = 0 if fl bit 0 else spec (0x12d84 `andi a0,s3,1`, 0x12da4 `addi a0,a0,-1`, 0x12dac `and a0,a0,s0`);
      a1 = 0 if fl bit 1 else sp + 8 (0x12d88 `slli a1,s3,62`, `srli a1,a1,63`, `addi a1,a1,-1`, `and a1,a1,a2`);
      a2 = 0 if fl bit 2 else sp (0x12d90 `slli s3,s3,61`, `srli a3,s3,63`, `addi a3,a3,-1`, `and a2,a3,a2`);
    the cells at sp + 8 and sp were zeroed at 0x12d7c / 0x12d80. So parse_live a0 a1 a2 = fl_live fl (spec <> 0 by
    malloc_ret, sp + 8 and sp <> 0).
    Why each premise holds there (when live): str = s, the k copied bytes (pin_str of the input: no NUL,
    pin_spec.pin_str_no_nul), then the NUL the harness stored, then slack = the bytes from spec + k + 1 to the next
    8-byte boundary, present by the frame's block_slack_present for the block (spec, k + 1) (identity's slack_ok); the
    block lies below alloc_ceiling <= lo = S - 65536, so below the stack region; the out cells sp + 8 and sp are 8
    disjoint bytes each of the harness frame, writable (FR), at or above this sp; stk, the region's writability and its
    absence from the image as for fuzz_catalogue_row; the table from FR's relro; the GOT cell holds the guard's address
    and the guard is a readable word by the allocator relation's statics (Reusable/YL01.v ax_statics: word_mem
    ms_got_guard = ms_guard, exists g, word_mem ms_guard g; frame_facts_plain: ms_got_guard = 0x1d478, ms_guard =
    0x4ea60); mem_inv as for fuzz_catalogue_row. *)
Definition REAC_BOX_PIN_PARSE : Z := 0x12e90.
Definition PARSE_STACK : Z := 176.
Definition PARSE_SSP_GOT : Z := 0x1d478.
Definition PARSE_SSP_GUARD : Z := 0x4ea60.

(** spec, model and label are all non-NULL. *)
Definition parse_live (a0 a1 a2 : word) : bool :=
  negb (bv_unsigned a0 =? 0) && negb (bv_unsigned a1 =? 0) && negb (bv_unsigned a2 =? 0).

(** What the caller supplies when the three arguments are non-NULL: the spec string str at sa with its NUL and the
    slack to the next 8-byte boundary, outside the stack region [lo, sp); two disjoint writable 8-byte out cells at
    mo and lb, outside [lo, sp). *)
Definition parse_args (m : word -> option byte) (lo sp sa mo lb : Z) (str slack : list byte) : Prop :=
  bytes_at rsegs m sa (str ++ NUL :: slack) /\ ~ In NUL str /\
  (- (sa + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) /\
  (sa + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ sp <= sa) /\
  wr_at rsegs m mo 8 /\ wr_at rsegs m lb 8 /\ (mo + 8 <= lb \/ lb + 8 <= mo) /\
  (mo + 8 <= lo \/ sp <= mo) /\ (lb + 8 <= lo \/ sp <= lb).

(** Memory after the call: success stores row at mo and the label at lb; refusal stores nothing outside the stack. *)
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
