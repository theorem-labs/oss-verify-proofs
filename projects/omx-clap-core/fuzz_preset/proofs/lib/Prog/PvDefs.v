From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Cells Step Exec Frame FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct PjIn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Definition num_tok (x : list Z) : option (list Z * list Z) :=
  let j := match x with b :: _ => if b =? 45 then 1%nat else 0%nat | [] => 0%nat end in
  match skipn j x with
  | [] => None
  | c :: z =>
    if negb (digit c) then None
    else if (c =? 48) && match z with c1 :: _ => digit c1 | [] => false end then None
    else let (a, r) := span numch z in Some (firstn j x ++ c :: a, r)
  end.

Definition lit_sel (b wa ty : Z) : Prop :=
  b = 116 /\ wa = 0x10349 /\ ty = 2 \/ b = 102 /\ wa = 0x10298 /\ ty = 1 \/ b = 110 /\ wa = 0x102ed /\ ty = 0.

Definition other_b (b : Z) : Prop :=
  b <> 123 /\ b <> 91 /\ b <> 34 /\ b <> 116 /\ b <> 102 /\ b <> 110.

Definition pv_disp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (q text len p d : Z) (tb : list byte) (v lo : Z) : machine_state -> Prop :=
  fun ms' => exists (P : Z) (m' : word -> option byte)
      (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    text <= P <= text + len /\ rest_at tb text P = skip (rest_at tb text p) /\
    pj_in_ok rsegs m' q text len P d tb /\ wmono rsegs m m' /\
    ( ((rest_at tb text P = [] \/ exists b y, rest_at tb text P = b :: y /\ other_b b /\ num_tok (b :: y) = None) /\
       munch [(bv_unsigned sp - 64, bv_unsigned sp); (q, q + 8)] m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
       pj_zero rsegs m' v /\
       ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom rsegs))
    \/ (exists (o : bool) y, rest_at tb text P = (if o then 123 else 91) :: y /\
          munch [(bv_unsigned sp - 64, bv_unsigned sp); (q, q + 8)] m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
          pj_zero rsegs m' v /\
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 q) (Z_to_bv 64 v) (Z_to_bv 64 (if o then 1 else 0))
                        a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 0x16340) fc None m' (seg_rom rsegs))
    \/ (exists b y wa ty, rest_at tb text P = b :: y /\ lit_sel b wa ty /\
          munch [(bv_unsigned sp - 64, bv_unsigned sp); (q, q + 8)] m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
          pj_zero rsegs m' v /\
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 q) (Z_to_bv 64 wa) (Z_to_bv 64 ty) (Z_to_bv 64 v)
                        a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 0x1692c) fc None m' (seg_rom rsegs))
    \/ (exists y, rest_at tb text P = 34 :: y /\
          munch [(bv_unsigned sp - 64, bv_unsigned sp); (q, q + 8); (v, v + 4)] m m' /\
          stk rsegs m' lo (bv_unsigned sp - 48) /\
          rw_cells rsegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
          pj_rw rsegs m' v /\ bytes_at rsegs m' v (le4 (Z_to_bv 64 4)) /\
          bytes_at rsegs m' (v + 4) (repeat (Z_to_bv 8 0) 52) /\
          ms' = MS (mkR (Z_to_bv 64 0x15a8c) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0' t1' t2'
                        (Z_to_bv 64 v) (Z_to_bv 64 q) (Z_to_bv 64 q) a1' a2' a3' a4' a5' a6' a7'
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 0x165e8) fc None m' (seg_rom rsegs))
    \/ (exists b y txt r, rest_at tb text P = b :: y /\ other_b b /\ num_tok (b :: y) = Some (txt, r) /\
          munch [(bv_unsigned sp - 64, bv_unsigned sp); (q, q + 8)] m m' /\
          stk rsegs m' lo (bv_unsigned sp - 48) /\
          rw_cells rsegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
          pj_zero rsegs m' v /\
          ms' = MS (mkR (Z_to_bv 64 0x15b48) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0' t1' t2'
                        (Z_to_bv 64 v) (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (length txt) + 1)) a1' a2' a3' a4' a5' a6' a7'
                        (Z_to_bv 64 (-1)) (Z_to_bv 64 (Z.of_nat (length txt))) (Z_to_bv 64 (P + Z.of_nat (length txt)))
                        s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 0x15454) fc None m' (seg_rom rsegs)) ).

Definition pv_num_post (rao spo gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (q text len P d : Z) (tb : list byte) (v res : Z) (txt : list Z) (lo : Z)
    : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
      (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms' = MS (mkR rao spo gp tp t0' t1' t2' s0o s1o a0' a1' a2' a3' a4' a5' a6' a7'
                  s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc rao) fc' None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\ MemNorm.ro_agree rsegs m' /\
    ( (res = 0 /\ a0' = Z_to_bv 64 (-1) /\ F' = F /\ fc' = fc /\
       munch [(v + 16, v + 24)] m m' /\ pj_zero rsegs m' v /\ pj_in_ok rsegs m' q text len P d tb)
    \/ (res <> 0 /\
        exists c bits, strtod_c.strtod_model txt = Some (bits, c) /\ 0 <= c <= Z.of_nat (length txt) /\
        (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k) /\
        frm0 fc' /\
        munch [(bv_unsigned spo - 64 - strtod_c.STRTOD_K, bv_unsigned spo); (res, res + Z.of_nat (length txt) + 1);
               (v, v + 24); (q, q + 8); (strtod_c.STRTOD_ERRNO, strtod_c.STRTOD_ERRNO + 4)] m m' /\
        (exists ev', rw_cells rsegs m' strtod_c.STRTOD_ERRNO [C4 ev']) /\
        pj_cbytes rsegs m' res txt /\
        ( (c = Z.of_nat (length txt) /\ PjGrammar.finite bits = true /\ a0' = Z_to_bv 64 0 /\
           pj_hdr rsegs m' v 3 bits res 0 0 0 0 /\
           pj_in_ok rsegs m' q text len (P + Z.of_nat (length txt)) d tb)
        \/ ((c <> Z.of_nat (length txt) \/ PjGrammar.finite bits = false) /\ a0' = Z_to_bv 64 (-1) /\
           pj_hdr rsegs m' v 0 bits res 0 0 0 0 /\
           pj_in_ok rsegs m' q text len P d tb)) ) ).
