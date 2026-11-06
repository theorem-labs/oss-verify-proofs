(* lib/B/Prog/record_sum_closes_c_on.v -- route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane): the ADDITIVE `_on` form of
   record_sum_closes_c.v's record_sum_closes_contract_F, STATEMENT ONLY (LEAF: it Requires only what
   record_sum_closes_c.v Requires, plus record_sum_closes_c). record_sum_closes_c.v stays unchanged apart from comment text. The proof is
   lib/B/Prog/record_sum_closesF_on.v, record_sum_closes_holds_F_on.
   rule 24: no function proved.

   The binders, the premises (the footprint ones included) and the post are those of record_sum_closes_contract_F,
   with ONE change: the premise `(1 <= bv_unsigned a1 -> shadow_rw m)` is DROPPED (a Theorem Labs lane's rule for a shadow premise the
   proof never uses, as a Theorem Labs lane applied it to record_cksum_verify, 11:29Z), so this contract is strictly stronger
   than record_sum_closes_contract_F and a caller needs no shadow fact.
   Why the premise is unused: record_sum_closes_holds_F names it HSW (record_sum_closesF.v:119), clears it on the a1 = 0
   path (:129), specializes it on the a1 >= 1 path (:141) and never uses it after. The run's only shadow accesses are the
   1-byte loads of shadow_addr x for each byte x of [a0, a0 + a1) (:92-98), closed from RK (:87-88), which comes from
   the addressable premise through rt_shadow_rd (:148). The run stores no shadow byte: the post's munch is the 16-byte
   frame [sp - 16, sp), and the last premise puts every shadow byte outside that frame.
   POST: unchanged; it states no shadow fact. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import record_sum_closes_c.
Import ListNotations.
Open Scope Z_scope.

Definition record_sum_closes_contract_F_on : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (bs : list byte),
    length bs = Z.to_nat (bv_unsigned a1) ->
    (bv_unsigned a1 = 0 \/
     (bv_unsigned a0 <> 0 /\ bv_unsigned a0 + bv_unsigned a1 <= 2^64 /\ bytes_at rsegs m (bv_unsigned a0) bs /\
      (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - RECORD_SUM_CLOSES_FRAME \/
       bv_unsigned sp <= bv_unsigned a0))) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + RECORD_SUM_CLOSES_FRAME <= bv_unsigned sp ->
    (1 <= bv_unsigned a1 -> asan_cells m) ->
    (1 <= bv_unsigned a1 -> addressable m (bv_unsigned a0) (bv_unsigned a1)) ->
    (1 <= bv_unsigned a1 ->
     forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - RECORD_SUM_CLOSES_FRAME, bv_unsigned sp)] x) ->
    rng RNG (bv_unsigned sp - RECORD_SUM_CLOSES_FRAME) RECORD_SUM_CLOSES_FRAME ->
    (1 <= bv_unsigned a1 -> rng RNG GOT_CELL_K 8) ->
    (1 <= bv_unsigned a1 -> rng RNG CELL_K 8) ->
    (1 <= bv_unsigned a1 -> rng RNG (bv_unsigned a0) (bv_unsigned a1)) ->
    (1 <= bv_unsigned a1 ->
     rng RNG (bv_unsigned a0 / 8 + ASAN_K) ((bv_unsigned a0 + bv_unsigned a1 - 1) / 8 - bv_unsigned a0 / 8 + 1)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (if recsum bs =? 0 then 1 else 0))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RECORD_SUM_CLOSES_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RECORD_SUM_CLOSES) fc None m (seg_rom rsegs)).
