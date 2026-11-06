(* Shared definitions of the check_as_written walk (fs.asan 0x81590, 308 instructions): the code table, the shadow-base
   span the token engine runs over, and the canonical symbolic states of the two loops of the inlined expected_body
   (fs.c:71-102). Definitions only.

   The method (MEASURED with the engine, see the lane notes): the ASan checks are walked with the TOKEN engine
   (Reusable/YCbn.v tok_load / tok_branch over YCbq.v SRr_run_tok_AJ, in U form FSW_K.fsw_run_tok_AJU and the tactic
   fsw_aj_run_tokU); a `lb` of a shadow byte becomes a fresh token atom and the following `bnez` is resolved by the
   engine's slow-block pattern (`andi u, x, 7; blt u, tok` / `bge u, tok; j`), which leaves the fast path and asks
   `need x (k+1)`: that is DISCHARGED by an SH entry (shent) covering the byte, so no obligation is left and the
   __asan_report_* calls are never reached.
   Two engine facts the states rely on:
   - an address the code computes as base + index (`add a2, a0, a3`) is NOT an atom, so the store `sb t2, 0(a2)` would
     stop the engine; the state carries an ALIAS fact (YP0e.v aliased2 / alias_lin_lookup) mapping the linear form
     of that sum to a fresh atom, and a one-byte region based at that atom;
   - the byte values the code reads are given by one-byte region chunks based on the pointer atoms. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AF0l AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the code of check_as_written (308 instructions, 0x81590 .. 0x81a3c; MEASURED: 1232 bytes, no compressed
   instruction) ---- *)
Definition caw_tbl : ctable := Eval vm_compute in build_table tfibsegs A_check_as_written 308 TEmpty.
Lemma caw_tbl_ok : table_ok tfibsegs caw_tbl.
Proof.
assert (E : caw_tbl = build_table tfibsegs A_check_as_written 308 TEmpty) by (vm_cast_no_check (eq_refl caw_tbl)).
rewrite E. apply build_table_ok0. unfold A_check_as_written. lia.
Qed.

(* ---- the token engine's shadow base: atom 32 of the entry env (FSW_K fss0T), the span of the ASan shadow ---- *)
Definition caw_Bx : sv := SOff 32 0.
Definition caw_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the upper bound of every client pointer (YCbq.v asan_consts: alloc_ceiling <= 0x7fffff800000) *)
Definition CAW_CEIL : Z := 140737479966720.
Definition CAW_F : Z := 48.                       (* the frame of check_as_written (dis: addi sp, sp, -0x30) *)
Definition CAW_WSMASK : Z := 4294977024.          (* 2^32 + 2^13 + 2^10 + 2^9, the whitespace mask of 0x81628 *)

(* the stack frame as the prologue (0x81590-0x815a8) leaves it: ra and s0..s4 saved *)
Definition caw_stk : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0
    [YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
     YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
     YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].

(* ---- loop 1, the scan loop (0x8163c .. 0x81704, head 0x8163c), fs.c:80-95 ----
   atoms: 31 RA (see below), 33 six, 34 want, 35 P = text + j, 36 A = P + 1, 37 C = the current character,
   38 M = m (sextets so far), 39 PAD = pad, 40 Q = six + m, 41 N = the next character, 42-46 scratch
   (t2, t3, t4, t5, t6).
   registers: a0 = six, a1 = A, a2 = C, a3 = M, a4 = PAD, a5 = 25, a6 = 61 ('='), a7 = 9, t0 = the whitespace mask,
   t1 = 43 ('+'), s2 = want, s3 = P, s4 = the shadow base, s0 = l, s1 = body.
   ra is the ATOM 31, not the literal 0x815f8 (a Theorem Labs lane ruling 2026-10-29, from a Theorem Labs lane's measurement: after
   `jal __wrap_malloc` at 0x815f4 no contract gives ra = 0x815f8 - fsw_aj_malloc04U / acall_post give pc = raw and
   aregs_preserved, and YG0d.v:19-22 acallee_saved is 2,3,4,8,9,18-27, which excludes ra). No segment of this walk
   READS ra (the epilogue reloads it from the frame, caw_stk's chunk at -8 = the ENTRY ra, atom 1); the atom is
   carried through every re-key like the scratch atoms. Slot 31 is free in every state of this walk (no state names
   the entry t6), so run_K and every agreement bound of the engine are unchanged. *)
Definition caw_regs1 : list sv :=
  [SLit 0; SOff 31 0; SOff 2 (-48); SOff 3 0; SOff 4 0;
   SLit CAW_WSMASK; SLit 43; SOff 42 0;
   SOff 12 0; SOff 11 0;
   SOff 33 0; SOff 36 0; SOff 37 0; SOff 38 0; SOff 39 0;
   SLit 25; SLit 61; SLit 9;
   SOff 34 0; SOff 35 0; SOff 32 0;
   SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 43 0; SOff 44 0; SOff 45 0; SOff 46 0].
(* the next text byte (read at 0x816c0 after `addi s3, s3, 1`) and the byte six[m] the iteration may write *)
Definition caw_txt1 : YP09.region :=
  YP09.mkRegion (Some 35%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 41 0))].
Definition caw_six1 : YP09.region := YP09.mkRegion (Some 40%nat) 0 1 0 1 [].
Definition caw_mem1 : smem := [caw_stk; caw_txt1; caw_six1].
(* the atom facts of the loop head; `cls` is the character class interval the case walks (the engine decides the
   classification branches from it: [65;90], [97;122], [48;57], [43;43], [47;47], [61;61], [9;10], [13;13], [32;32],
   and the intervals of the complement) *)
Definition caw_facts1 (clo chi : Z) : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 4096 CAW_CEIL 0);
           (34%nat, mkAF 4096 CAW_CEIL 0);
           (35%nat, mkAF 4096 CAW_CEIL 0);
           (36%nat, mkAF 4096 CAW_CEIL 0);
           (37%nat, mkAF clo chi 0);
           (38%nat, mkAF 0 3145728 0);
           (39%nat, mkAF 0 2147483647 0);
           (40%nat, mkAF 4096 CAW_CEIL 0);
           (41%nat, mkAF 0 255 0)]
          []
          [(SAlu ALU_ADD (SOff 33 0) (SOff 38 0), SOff 40 0)].
Definition caw_ss1 (clo chi : Z) : sstate := mkSS 0x8163c caw_regs1 caw_mem1 None (caw_facts1 clo chi).
(* the shadow entries: the next text byte and the byte six[m]; both are discharged from the walk's range premises *)
Definition caw_SH1 : list shent := [mkSHE 35 1 2; mkSHE 40 0 1].
Definition caw_K1 : nat := Eval vm_compute in run_K 0 caw_Bx caw_SH1 (caw_ss1 0 255).

(* ---- loop 2, the emit loop (0x817dc .. 0x81904, head 0x817dc), fs.c:97-101 ----
   it reads four sextets six[i..i+3] and writes up to three bytes want[n..n+2].
   atoms: 31 RA (as in the scan loop, see caw_regs1), 33 six, 34 want, 47 K = i + 4 (the loop counter a1/a6 at the
   head), 48 = six + K, 38 M = m, 49 N = n,
   50 = want + n, 51 = six + 1 + K, 52-55 the four sextet values, 56-60 scratch. *)
Definition caw_regs2 : list sv :=
  [SLit 0; SOff 31 0; SOff 2 (-48); SOff 3 0; SOff 4 0;
   SOff 56 0; SOff 57 0; SOff 58 0;
   SOff 12 0; SOff 11 0;
   SOff 33 0; SOff 47 0; SOff 59 0; SOff 38 0; SOff 33 1;
   SLit (-1); SOff 47 0; SOff 60 0;
   SOff 34 0; SOff 49 0; SOff 32 0;
   SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 61 0; SOff 62 0; SOff 63 0; SOff 64 0].
Definition caw_mem2 : smem :=
  [caw_stk;
   (* the four sextets of the group, read through a7 = six + 1 + K at offsets -5 .. -2 *)
   YP09.mkRegion (Some 51%nat) (-5) (-1) 0 0
     [YP09.mkChunk (-5) (CVal 1 (SOff 52 0)); YP09.mkChunk (-4) (CVal 1 (SOff 53 0));
      YP09.mkChunk (-3) (CVal 1 (SOff 54 0)); YP09.mkChunk (-2) (CVal 1 (SOff 55 0))];
   (* the three bytes the group writes, based at want + n *)
   YP09.mkRegion (Some 50%nat) 0 3 0 3 []].
Definition caw_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 4096 CAW_CEIL 0);
           (34%nat, mkAF 4096 CAW_CEIL 0);
           (38%nat, mkAF 0 3145728 0);
           (47%nat, mkAF 4 3145728 0);
           (48%nat, mkAF 4096 CAW_CEIL 0);
           (49%nat, mkAF 0 3145728 0);
           (50%nat, mkAF 4096 CAW_CEIL 0);
           (51%nat, mkAF 4096 CAW_CEIL 0);
           (52%nat, mkAF 0 63 0); (53%nat, mkAF 0 63 0); (54%nat, mkAF 0 63 0); (55%nat, mkAF 0 63 0)]
          []
          [(SAlu ALU_ADD (SOff 33 0) (SOff 47 0), SOff 48 0);
           (SAlu ALU_ADD (SOff 33 1) (SOff 47 0), SOff 51 0);
           (SAlu ALU_ADD (SOff 34 0) (SOff 49 0), SOff 50 0)].
Definition caw_ss2 : sstate := mkSS 0x817dc caw_regs2 caw_mem2 None caw_facts2.
Definition caw_SH2 : list shent := [mkSHE 51 (-5) (-1); mkSHE 50 0 3].
Definition caw_K2 : nat := Eval vm_compute in run_K 0 caw_Bx caw_SH2 caw_ss2.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* one byte of the machine's own memory *)
Definition caw_at (W : world tfibsegs) (mem : word -> option byte) (a v : Z) : Prop :=
  val_mem tfibsegs (rdW W mem) a 1 v.
(* the bytes of a block, by index *)
Definition caw_bytes (W : world tfibsegs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  forall i, (i < length l)%nat -> caw_at W mem (p + Z.of_nat i) (nth i l 0).
End c.
