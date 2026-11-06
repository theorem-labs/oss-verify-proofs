From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_CTRL_IDENTITY_REPLY : Z := 0x14b5c.
Definition REAC_CTRL_IDENTITY_REPLY_K : Z := 176.

Definition reac_ctrl_identity_reply_fp (fr len pa pp pn S : Z) (g : list byte) : list (Z * Z) :=
  (if reply_ok fr len pa pp pn g then [(pa, pa + 2); (pp, pp + 8); (pn, pn + 8)] else []) ++
  [(S - REAC_CTRL_IDENTITY_REPLY_K, S)].

Definition reac_ctrl_identity_reply_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fr len pa pp pn S : Z) (g ja jp jn : list byte),
    a0 = Z_to_bv 64 fr -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 pa -> a3 = Z_to_bv 64 pp -> a4 = Z_to_bv 64 pn ->
    sp = Z_to_bv 64 S ->
    0 <= fr < 2^64 -> 0 <= len < 2^64 -> 0 <= pa < 2^64 -> 0 <= pp < 2^64 -> 0 <= pn < 2^64 ->
    S < 2^64 -> S mod 16 = 0 ->
    REAC_CTRL_IDENTITY_REPLY_K <= S -> stk rsegs m (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    mem_inv rsegs m ->
    length g = 50%nat ->
    (reply_args fr pa pp pn = true -> 50 <= len ->
       fr + 50 <= 2^64 /\ bytes_at rsegs m fr g /\ (fr + 50 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= fr)) ->
    (reply_args fr pa pp pn = true ->
       pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       rw_cells rsegs m pa [CB 2 ja] /\ rw_cells rsegs m pp [CB 8 jp] /\ rw_cells rsegs m pn [CB 8 jn] /\
       (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
       (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\ (pn + 8 <= fr \/ fr + 50 <= pn) /\
       (pa + 2 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= pa) /\
       (pp + 8 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= pp) /\
       (pn + 8 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= pn)) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (reply_ret fr len pa pp pn g))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_identity_reply_fp fr len pa pp pn S g) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_IDENTITY_REPLY_K) S /\
         (reply_ok fr len pa pp pn g = true ->
            rw_cells rsegs m' pa [CB 2 (reply_addr g)] /\
            rw_cells rsegs m' pp [CB 8 (le8 (Z_to_bv 64 (fr + 38)))] /\
            rw_cells rsegs m' pn [CB 8 (le8 (Z_to_bv 64 (ir_s g - 13)))]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m (seg_rom rsegs)).
