From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_drivable_csv(mask, buf, buflen) (reac_rate_cfg.c:49-75; 396 bytes, 99 instructions at 0x14a78 in the
    plain image; frame 176 bytes: ra, s0-s11 at sp + 0x48 .. sp + 0xaf, buf at sp + 8, buflen at sp + 0x10,
    cell[16] at sp + 0x18, tmp[32] at sp + 0x28; reac_rate_bit inlined):
      0x14a78 .. 0x14b00 entry: saves, `sb zero,0x28(sp)` (tmp[0] = 0), s3 = mask, s1 = len = 0, s6 = tmp,
              s7 = ORDERED (0x10678, .rodata: 44100, 48000, 96000), s0 = ORDERED + 12, s8 = 44100, s5 = 48000,
              s11 = 96000, s9 = "," (0x10373), s10 = "" (0x1032e), s4 = FMT_SD (0x10470, "%s%d");
      0x14b04 .. 0x14b8c the loop over i = 0, 1, 2 (`bne s7,s0` 0x14b8c): `lw a4,0(s7)`; the reac_rate_bit compare
              chain; `and a0,a0,s3`; `beqz a0` skips the pass; a3 = len ? "," : ""; snprintf(cell, 16, "%s%d", a3, a4)
              (`jal` 0x14b50 -> 0x188a8); `bltz a0` and `bltu 31,len + n` skip (both dead: the list is at most 17
              bytes); memcpy(tmp + len, cell, n) (0x14b70 -> 0x1ce2c); `sb zero` at tmp[len + n]; len += n;
      0x14b90 .. 0x14c00 exit: buflen = 0 returns len; else copy = min(len, buflen - 1) (unsigned), memcpy(buf, tmp,
              copy) (0x14bb8 -> 0x1ce2c), `sb zero,0(buf + copy)`, returns len; restores ra, s0-s11.
    So it returns |csv_list mask| (Pod/RateCsv.v; mask = bv_unsigned a0, every bit of it, 64-bit `and` at 0x14b30)
    and, for buflen > 0, leaves csv_cut L buflen and a NUL at buf; for buflen = 0 it writes nothing outside its
    stack. It writes its frame, the snprintf chain's stack below it (SNPRINTF_K = 5936 bytes, Prog/snprintf_c.v), and
    only the copy + 1 <= buflen bytes at buf; it writes the caller-saved integer registers, F at f10 (snprintf's post,
    printf_facts_c.v printf_post) and any fcsr with frm 0. It has no canary of its own; snprintf reads the guard
    cells.

    Callee contracts its walk takes as premises: snprintf_contract (Prog/snprintf_c.v, SNPRINTF = 0x188a8; disco's,
    relocated) with fmt = "%s%d" at FMT_SD, args [APtr sep; AInt rate] (sep "" at STR_EMPTY with slack
    byte 0x1032f, or "," at STR_COMMA with slack 0x10375-0x10377; rate = ordered[i], sign-extended by the lw),
    D = sp + 0x18 (the cell, 16 bytes), T = sep ++ pf_dec rate (5 or 6 bytes), lo + DCSV_K <= S, IMG_END <= lo,
    S < 2^63, frm0, mem_inv, task_mem and the two guard cells, all carried from this contract's premises (snprintf's
    and memcpy's posts keep them: munch outside the stack and buf, task_mem, frm0); memcpy_contract (Prog/memcpy_c.v,
    0x1ce2c; role's, relocated), twice per pass and once at the exit (copy = 0 included). pf_dec of the
    three rates is csv_dec of them (both texts are the same function; RateCsv.csv_dec_rates), and pf_bytes is
    csv_bytes ([pf_bytes_csv]).

    Call site (LLVMFuzzerTestOneInput, plain): 0x14534 `jal reac_rate_drivable_csv`, with sp = S0 - 544 (the
    harness frame, S0 = main's entry sp) and
      a0 = s9 = mask (0x14528 `mv a0,s9`), input byte 1;
      a1 = s4 = buf (0x1452c `mv a1,s4`), malloc(bl)'s result (0x14510 `jal malloc` with a0 = s5 = bl =
           buflen + (buflen = 0), 0x14504-0x14508; 0x14514 `beqz a0` to abort not taken; 0x14518 `mv s4,a0`), every
           byte set to 0x5a by memset(buf, 0x5a, bl) (0x14524);
      a2 = s10 = buflen (0x14530 `mv a2,s10`), input byte 2 mod 24.
    The result goes to check_csv's a2 (0x14538 `mv a2,a0`). Why each premise holds there (rate_csv_contract, the M03
    segment from the cut 0x14504): buflen <= 23 is the `mulhu` remainder; for buflen > 0 buf is a malloc block of
    buflen bytes (rw_cells, nonzero, below the stack region); the walk (Prog/rate_csv.v) takes lo := S0 - 544 -
    CSV_STACK (stk_split of the evt's [lo, sp)), so lo + 6112 <= S0 - 544 and drivable_csv's munch stays inside the
    evt's [sp - CSV_STACK, sp); IMG_END <= STACK_LO_MIN <= lo and S0 < 2^63 (the stack window); frm0, mem_inv,
    task_mem and the guard cells are carried by the cut (frame facts from ax_statics: the .got slot 0x1ea28 holds
    &__stack_chk_guard = 0x50010).
    The post's F' and fc' (any FP state with frm 0) are what the cut K1454c allows. *)
Definition REAC_RATE_DRIVABLE_CSV : Z := 0x14a78.
Definition DCSV_F : Z := 176.
Definition DCSV_K : Z := DCSV_F + SNPRINTF_K.
Definition ORDERED : Z := 0x10678.
Definition FMT_SD : Z := 0x10470.
Definition STR_COMMA : Z := 0x10373.
Definition STR_EMPTY : Z := 0x1032e.

Lemma pf_bytes_csv : forall l, pf_bytes l = csv_bytes l.
Proof. reflexivity. Qed.

Lemma pf_dec_csv : forall v, pf_dec v = csv_dec v.
Proof.
  assert (forall f x acc, pf_digits f x acc = csv_digits f x acc) as H.
  { induction f as [|f IH]; intros x acc; [reflexivity|]. cbn. destruct (x <? 10); [reflexivity | apply IH]. }
  intros v. unfold pf_dec, csv_dec. rewrite !H. reflexivity.
Qed.

Definition reac_rate_drivable_csv_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (canary : word) (junk : list byte),
    let S := bv_unsigned sp in let buf := bv_unsigned a1 in let n := bv_unsigned a2 in
    let L := csv_list (bv_unsigned a0) in
    n <= 23 ->
    (0 < n -> 0 < buf /\ rw_cells rsegs m buf [CB (Z.to_nat n) junk] /\ (buf + n <= lo \/ S <= buf)) ->
    stk rsegs m lo S -> lo + DCSV_K <= S -> IMG_END <= lo -> S < 2^63 ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length L))) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
         frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ stk rsegs m' lo S /\
         (n = 0 -> munch [(lo, S)] m m') /\
         (0 < n -> munch [(lo, S); (buf, buf + n)] m m' /\ bytes_at rsegs m' buf (csv_bytes (csv_cut L n ++ [0]))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_RATE_DRIVABLE_CSV) fc None m (seg_rom rsegs)).
