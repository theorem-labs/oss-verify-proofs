From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_drivable_csv(mask, buf, buflen) (reac_rate_cfg.c:49-75; 456 bytes, 114 instructions at 0x14dcc in the
    UBSan image; frame 176 bytes: ra, s0-s11 at sp + 0x48 .. sp + 0xaf, buflen at sp + 8, buf at sp + 0x10,
    cell[16] at sp + 0x18, tmp[32] at sp + 0x28; reac_rate_bit inlined):
      0x14dcc .. 0x14e58 entry: saves, `sb zero,0x28(sp)`, s3 = mask, s2 = len = 0, s6 = 3 (passes left),
              s8 = ~(sp + 0x28), s9 = ORDERED (0x10644, .rodata: 44100, 48000, 96000), s10 = 44100, s5 = 48000,
              s0 = 96000, s11 = "," (0x10373), s7 = "" (0x1032e), s4 = FMT_SD (0x10470, "%s%d");
      0x14e5c .. 0x14ef8 the loop (`bnez s6` 0x14ef8): `lw a4,0(s9)`; the compare chain; `and a0,a0,s3`; `beqz`
              skips; a3 = len ? "," : ""; snprintf(cell, 16, "%s%d", a3, a4) (`jal` 0x14ea8 -> 0x18c90); `bltz a0`
              and `bltu 31,len + n` skip (dead); trap test 0x14ec0 `bltu s8,s2` (tmp + len overflows); memcpy(tmp + len,
              cell, n) (0x14ed0 -> 0x1d214); trap test 0x14ed4 `bltu s8,s1` (tmp + len + n); `sb zero` at
              tmp[len + n]; len += n;
      0x14efc .. 0x14f8c exit: buflen = 0 returns len; else copy = min(len, buflen - 1), memcpy(buf, tmp, copy)
              (0x14f24 -> 0x1d214); trap tests 0x14f2c `bltu s0,s1` (buf + copy wraps), 0x14f40 (buf <> 0 xor
              buf + copy = 0) and 0x14f48 (buf = 0); `sb zero,0(buf + copy)`; returns len; 0x14f90 unimp (the trap).
    The five trap branches are never taken: sp + 0x28 + 17 < 2^64 (S < 2^63, len <= 17), buf > 0 and
    buf + buflen <= 2^64 (rw_cells' bound). So it returns |csv_list mask| (Pod/RateCsv.v; 64-bit `and` at 0x14e88)
    and, for buflen > 0, leaves csv_cut L buflen and a NUL at buf; for buflen = 0 it writes nothing outside its
    stack. It writes its frame, the snprintf chain's stack below it (SNPRINTF_K = 5936 bytes, U/Prog/snprintf_c.v),
    and only the copy + 1 <= buflen bytes at buf; it writes the caller-saved integer registers, F at f10 and any fcsr
    with frm 0.

    Callee contracts its walk takes as premises: snprintf_contract (U/Prog/snprintf_c.v, SNPRINTF = 0x18c90; disco's,
    relocated) with fmt "%s%d" at FMT_SD, args [APtr sep; AInt rate] (sep "" at STR_EMPTY with slack byte
    0x1032f, or "," at STR_COMMA with slack 0x10375-0x10377), D = sp + 0x18, T = sep ++ pf_dec rate, carried as in the
    plain image; memcpy_contract (U/Prog/memcpy_c.v, 0x1d214; role's, relocated). pf_dec is csv_dec
    ([pf_dec_csv]) and pf_bytes is csv_bytes ([pf_bytes_csv]).

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x14648 `jal reac_rate_drivable_csv`, with sp = S0 - 592 (the harness
    frame) and
      a0 = s10 = mask (0x1463c `mv a0,s10`), input byte 1;
      a1 = s4 = buf (0x14640 `mv a1,s4`), malloc(bl)'s result (0x14624 `jal malloc` with a0 = s5 = bl =
           buflen + (buflen = 0), 0x14618-0x1461c; 0x14628 `beqz a0` to abort not taken; 0x1462c `mv s4,a0`), every
           byte set to 0x5a by memset(buf, 0x5a, bl) (0x14638);
      a2 = s0 = buflen (0x14644 `mv a2,s0`; 0x14614 `ld s0,0x30(sp)`), input byte 2 mod 24.
    The result goes to check_csv's a2 (0x1464c `mv a2,a0`). Why each premise holds there: as in the plain image
    (Prog/reac_rate_drivable_csv_c.v), with the walk (U/Prog/rate_csv.v) taking lo := S0 - 592 - CSV_STACK, so
    lo + 6112 <= S0 - 592 and drivable_csv's munch stays inside the evt's [sp - CSV_STACK, sp), IMG_END = 0x50cc8 <=
    lo, and the guard cells at the .got slot 0x1ee78 (holding &__stack_chk_guard = 0x50460) and 0x50460. *)
Definition REAC_RATE_DRIVABLE_CSV : Z := 0x14dcc.
Definition DCSV_F : Z := 176.
Definition DCSV_K : Z := DCSV_F + SNPRINTF_K.
Definition ORDERED : Z := 0x10644.
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
