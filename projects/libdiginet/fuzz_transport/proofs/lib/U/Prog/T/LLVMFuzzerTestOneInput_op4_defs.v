(* The program points of case 4 of the ubsan LLVMFuzzerTestOneInput between the case entry 0x13a48 and the raw /
   tagged split, as machine-state predicates (the tagged entry 0x141a4 is LLVMFuzzerTestOneInput_op4_mid.v's
   llvm_op4_mid):
     op4_s1  0x13a94 (`beqz s6`): op_begin done, s0 = (int)before, the struct diginet_cmd at sp+0x60 zero;
     op4_s2  0x13e94: kb in a1, ab in a2, the cursor after them in s3 (address) / a0 (n);
     op4_r   0x14488: the raw arm after the u16 w (low byte in a1, high in a2), the cursor after it in s3 / a0,
             the struct = cmd_struct (24 zero bytes) 0 display key. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_op4_mid.
Import ListNotations.
Open Scope Z_scope.

Definition op4_s1 (data : Z) (D : list byte) (regs0 : bvmap 5 word) (m0 : word -> option byte)
    (Sp lo ops : Z) (c c1 : fuzz_in) (before : Z) (B1 : list byte) (F : bvmap 5 word) (fc : bv 32)
    (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (j10 jio jhi : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2
                 (Z_to_bv 64 (bv_swrap 32 before)) (Z_to_bv 64 1)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c1)) (Z_to_bv 64 7) (Z_to_bv 64 (data + fi_off c))
                 (Z_to_bv 64 (fi_n c1)) (Z_to_bv 64 (fi_n c))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 0x13a94) fc None m (seg_rom rsegs) /\
    0 <= ops < OPS_MAX /\ fi_n c <> 0 /\ llvm_cursor D c /\ c1 = fst (fuzz_u8_m D c) /\
    0 <= before < 2 ^ 32 /\ length jhi = 8%nat /\
    llvm_mem data D regs0 m0 Sp lo B1 m j10 jio (repeat (b8 0) 32 ++ jhi).

Definition op4_s2 (data : Z) (D : list byte) (regs0 : bvmap 5 word) (m0 : word -> option byte)
    (Sp lo ops : Z) (c2 : fuzz_in) (kb ab before : Z) (B1 : list byte) (F : bvmap 5 word) (fc : bv 32)
    (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a3 a4 a5 a6 a7 s5 s6 s7 t3 t4 t5 t6 : word) (m : word -> option byte) (j10 jio jhi : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2
                 (Z_to_bv 64 (bv_swrap 32 before)) (Z_to_bv 64 1)
                 (Z_to_bv 64 (fi_n c2)) (Z_to_bv 64 kb) (Z_to_bv 64 ab) a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c2)) (Z_to_bv 64 7) s5 s6 s7
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 0x13e94) fc None m (seg_rom rsegs) /\
    0 <= ops < OPS_MAX /\ llvm_cursor D c2 /\ 0 <= kb < 256 /\ 0 <= ab < 256 /\
    0 <= before < 2 ^ 32 /\ length jhi = 8%nat /\
    llvm_mem data D regs0 m0 Sp lo B1 m j10 jio (repeat (b8 0) 32 ++ jhi).

Definition op4_r (data : Z) (D : list byte) (regs0 : bvmap 5 word) (m0 : word -> option byte)
    (Sp lo ops : Z) (c4 : fuzz_in) (lo8 hi8 before : Z) (B1 : list byte) (display key : Z)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a3 a4 a5 a6 a7 s5 s6 s7 t3 t4 t5 t6 : word) (m : word -> option byte) (j10 jio jhi : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2
                 (Z_to_bv 64 (bv_swrap 32 before)) (Z_to_bv 64 1)
                 (Z_to_bv 64 (fi_n c4)) (Z_to_bv 64 lo8) (Z_to_bv 64 hi8) a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c4)) (Z_to_bv 64 7) s5 s6 s7
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 0x14488) fc None m (seg_rom rsegs) /\
    0 <= ops < OPS_MAX /\ llvm_cursor D c4 /\ 0 <= lo8 < 256 /\ 0 <= hi8 < 256 /\
    0 <= before < 2 ^ 32 /\ 0 <= display <= 1 /\ 0 <= key < 2 ^ 32 /\ length jhi = 8%nat /\
    llvm_mem data D regs0 m0 Sp lo B1 m j10 jio (cmd_struct (repeat (b8 0) 24) 0 display key ++ jhi).

(* debugging aids for the walk files (print the goal / the hypotheses into the build log) *)
Ltac dbg_goal := match goal with |- ?G => idtac G end.
Ltac dbg_hyps := try (match goal with H : ?T |- _ => idtac H ":" T; fail end).

(* a branch whose condition the context decides: the registers are unwrapped to [_ mod 2^64] (no side condition)
   and the comparison is closed by lia, with the Euclidean equations of the mod when it survives *)
Ltac uns := rewrite ?unsigned_lit by lia.
Ltac zsolve := first [ lia | (Z.div_mod_to_equations; lia) ].
Ltac bsolve2 :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); bsolve2
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); bsolve2
  | |- Z.eqb _ _ = true => apply Z.eqb_eq; zsolve
  | |- Z.eqb _ _ = false => apply Z.eqb_neq; zsolve
  | |- Z.ltb _ _ = true => apply Z.ltb_lt; zsolve
  | |- Z.ltb _ _ = false => apply Z.ltb_ge; zsolve
  | |- Z.leb _ _ = true => apply Z.leb_le; zsolve
  | |- Z.leb _ _ = false => apply Z.leb_gt; zsolve
  | |- _ = _ => reflexivity
  end.
(* literal powers of two left by a shift, computed *)
Ltac pow_lits := repeat match goal with |- context [2 ^ ?k] =>
                    is_Zlit k; let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v end.
Ltac brv v :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v;
      [cbv iota | symmetry; unfold_cond; fold_lit_ux; rewrite ?unsigned_lit_wrap;
                  rewrite ?Z.shiftl_mul_pow2 by lia; pow_lits; bsolve2]
  end.
Ltac br := first [ brv true | brv false
                 | match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                     idtac "BRFAIL:" c; fail 100 "br: the branch condition is not decided" end ].
