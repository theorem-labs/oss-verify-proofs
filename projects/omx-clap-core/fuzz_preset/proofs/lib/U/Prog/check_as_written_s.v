From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Cells Step Exec Frame FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ex_value_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import strtod_c ex_value_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require LedgerCells fuzz_alloc_ran_out_c.
Import ListNotations.
Open Scope Z_scope.

(* The #102 ubsan check_as_written (FUNC LOCAL 0x13ad4, 280 bytes, in the .symtab of the twin
   agents/pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.ubsan, sha256 27566683952ebd54...; listing
   h-cmd-a7's new-ubsan-caw.ann.s, sha256 7dfcf9f91bb66b71). The frame is 80 bytes and
   saves s2 too; struct ex is at sp + 8. Run 1 is the entry (the two pointer-overflow traps on data + size) to the
   malloc call (0x18390, malloc); run 2 is from malloc's return (a0 <> 0) to the free call (0x18250, free), across
   ex_value (0x14710) and ex_ws (0x14cbc); run 3 is from free's return to the return of check_as_written, across
   out_of_memory(): lbu g_own_ran_out, then fuzz_alloc_ran_out (0x15f90) when it is 0. *)
Definition CAW_ENTRY : Z := 0x13ad4.
Definition CAW_AFTER_MALLOC : Z := 0x13b1c.
Definition CAW_MALLOC : Z := 0x18390.
Definition CAW_FREE : Z := 0x18250.
Definition CAW_RET_REFUSE : Z := 0x13b48.
Definition CAW_RET_ACCEPT : Z := 0x13b80.

Definition caw_v (rcv doc : Z) : Z := if rcv =? 0 then doc else 0.

Definition caw_pe (rest : list Z) : bool := match skip rest with [] => true | _ :: _ => false end.

(* out_of_memory()'s answer from the two bytes, and so the value check_as_written returns *)
Definition caw_rv (go gr : Z) : Z := if (go =? 0) && (gr =? 0) then 0 else 1.

Definition caw_run1_prop : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (data size lo : Z),
    a0 = Z_to_bv 64 data -> a1 = Z_to_bv 64 size -> 0 < data -> 0 <= size -> data + size < 2 ^ 62 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp ->
    evt rsegs
      (fun ms' => exists (m' : word -> option byte) (j0 j1 j2 : list byte),
         ms' = MS (mkR (Z_to_bv 64 CAW_AFTER_MALLOC) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 a2 a3
                       (Z_to_bv 64 (size + 1)) a1 (Z_to_bv 64 (data + size)) (Z_to_bv 64 0) a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CAW_MALLOC) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' (bv_unsigned sp - 80)
           [CB 8 j0; C8 (Z_to_bv 64 data); C8 (Z_to_bv 64 (data + size)); C8 (Z_to_bv 64 0); CB 8 j1; CB 8 j2;
            C8 s2; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CAW_ENTRY) fc None m (seg_rom rsegs)).

(* At the free call: s0 still holds rc, s2 is the caller's; on the accepted arm s1 holds whether ex_ws reached the end *)
Definition caw_mid2 (gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : word -> option byte)
    (S1 rcv doc bb : Z) (x : list byte) (t : jv) : machine_state -> Prop :=
  fun ms' => exists (ra' t0 t1 t2 s1' a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                    (m' : word -> option byte) (dl' : Z),
    ms' = MS (mkR ra' (Z_to_bv 64 S1) gp tp t0 t1 t2 s0 s1' (Z_to_bv 64 bb) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 CAW_FREE) fc' None m' (seg_rom rsegs) /\
    ex_value_c.ex_fkeep F F' /\ frm0 fc' /\
    munch [(S1 - ex_value_K 0, S1); (S1 + 8, S1 + 48); (bb, bb + Z.of_nat (length x) + 1);
           (STRTOD_ERRNO, STRTOD_ERRNO + 4)] m m' /\
    wmono rsegs m m' /\
    rw_cells rsegs m' (S1 + 32) [C8 (Z_to_bv 64 bb); C4 (Z_to_bv 64 dl')] /\ (dl' = 0 \/ dl' = 1) /\
    match ex_value_c.ex_V 0 (map bv_unsigned x) with
    | None => ra' = Z_to_bv 64 CAW_RET_REFUSE
    | Some (u, rest) =>
        ra' = Z_to_bv 64 CAW_RET_ACCEPT /\ s1' = Z_to_bv 64 (if caw_pe rest then 1 else 0) /\
        (dl' = 1 <-> caw_v rcv doc <> 0 /\ t <> u)
    end.

Definition caw_run2_prop : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S1 data rcv doc bb lo : Z) (x : list byte)
         (j0 j1 j2 : list byte) (lblk : Z -> Z -> Prop) (t : jv) (D : list (Z * Z)) (canary ev : word),
    sp = Z_to_bv 64 S1 -> s0 = Z_to_bv 64 rcv -> s1 = Z_to_bv 64 doc -> a0 = Z_to_bv 64 bb ->
    tp = Z_to_bv 64 STRTOD_TP -> 0 <= rcv < 2 ^ 64 -> 0 <= doc < 2 ^ 64 ->
    rw_cells rsegs m S1 [CB 8 j0; C8 (Z_to_bv 64 data); C8 (Z_to_bv 64 (data + Z.of_nat (length x)));
                         C8 (Z_to_bv 64 0); CB 8 j1; CB 8 j2] ->
    S1 mod 16 = 0 -> S1 < 2 ^ 62 -> stk rsegs m lo S1 -> lo <= S1 - ex_value_K 0 ->
    STRTOD_GLOBALS_TOP <= S1 - ex_value_K 0 ->
    bytes_at rsegs m data x -> 0 < data -> data + Z.of_nat (length x) < 2 ^ 62 -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
    stk rsegs m bb (bb + Z.of_nat (length x) + 1) -> 4096 <= bb ->
    bb + Z.of_nat (length x) + 1 <= STRTOD_IMG_LO \/ STRTOD_GLOBALS_TOP <= bb ->
    bb + Z.of_nat (length x) + 1 <= S1 - ex_value_K 0 ->
    (caw_v rcv doc = 0 \/
     pj_node rsegs m lblk (caw_v rcv doc) t D /\ Forall (fun ak => 0 < fst ak /\ fst ak mod 8 = 0) D) ->
    (caw_v rcv doc <> 0 ->
       ex_value_c.ex_off (caw_v rcv doc) D (S1 + 8) 40 /\
       ex_value_c.ex_off (caw_v rcv doc) D bb (Z.of_nat (length x) + 1) /\
       ex_value_c.ex_off (caw_v rcv doc) D (S1 - ex_value_K 0) (ex_value_K 0) /\
       ex_value_c.ex_off (caw_v rcv doc) D STRTOD_ERRNO 4) ->
    ex_value_c.ex_apart (S1 + 8) 40 data (Z.of_nat (length x)) ->
    ex_value_c.ex_apart (S1 + 8) 40 bb (Z.of_nat (length x) + 1) ->
    ex_value_c.ex_apart data (Z.of_nat (length x)) bb (Z.of_nat (length x) + 1) ->
    ex_value_c.ex_apart data (Z.of_nat (length x)) (S1 - ex_value_K 0) (ex_value_K 0) ->
    ex_value_c.ex_apart data (Z.of_nat (length x)) STRTOD_ERRNO 4 ->
    rw_cells rsegs m STRTOD_GOT_GUARD [C8 (Z_to_bv 64 STRTOD_GUARD)] -> rw_cells rsegs m STRTOD_GUARD [C8 canary] ->
    rw_cells rsegs m STRTOD_ERRNO [C4 ev] ->
    mem_inv rsegs m -> MemNorm.task_mem rsegs m -> frm0 fc ->
    evt rsegs (caw_mid2 gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m S1 rcv doc bb x t)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CAW_AFTER_MALLOC) fc None m (seg_rom rsegs)).

(* the return of check_as_written, with a0 = r *)
Definition caw_ret (rav r sp' gp tp s0v s1v s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms' = MS (mkR rav sp' gp tp t0 t1 t2 s0v s1v r a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6)
             F (ret_pc rav) fc None m (seg_rom rsegs).

(* g_own_ran_out = go and g_ran_out = gr in m, one byte each *)
Definition caw_flags (m : word -> option byte) (go gr : Z) : Prop :=
  0 <= go < 2 ^ 8 /\ 0 <= gr < 2 ^ 8 /\
  bytes_at rsegs m LedgerCells.GL_OWN_RAN_OUT (le1 (Z_to_bv 64 go)) /\
  bytes_at rsegs m fuzz_alloc_ran_out_c.G_RAN_OUT (le1 (Z_to_bv 64 gr)).

Definition caw_run3a_prop : Prop :=
  fuzz_alloc_ran_out_c.fuzz_alloc_ran_out_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S1 rcv go gr : Z) (rav s0v s1v s2v : word),
    sp = Z_to_bv 64 S1 -> 0 <= S1 -> S1 + 80 < 2 ^ 64 -> s0 = Z_to_bv 64 rcv -> 0 <= rcv < 2 ^ 64 -> rcv <> 0 ->
    caw_flags m go gr ->
    bytes_at rsegs m (S1 + 48) (le8 s2v ++ le8 s1v ++ le8 s0v ++ le8 rav) ->
    evt rsegs (caw_ret rav (Z_to_bv 64 (caw_rv go gr)) (Z_to_bv 64 (S1 + 80)) gp tp s0v s1v s2v s3 s4 s5 s6 s7 s8 s9
                 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CAW_RET_REFUSE) fc None m (seg_rom rsegs)).

Definition caw_run3b_prop : Prop :=
  fuzz_alloc_ran_out_c.fuzz_alloc_ran_out_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S1 rcv dl go gr : Z) (pe : bool)
         (rav s0v s1v s2v : word),
    sp = Z_to_bv 64 S1 -> 0 <= S1 -> S1 + 80 < 2 ^ 64 -> s0 = Z_to_bv 64 rcv -> 0 <= rcv < 2 ^ 64 ->
    s1 = Z_to_bv 64 (if pe then 1 else 0) ->
    (rcv = 0 <-> pe = true) -> (dl = 0 \/ dl = 1) -> (rcv = 0 -> dl = 0) ->
    caw_flags m go gr ->
    bytes_at rsegs m (S1 + 40) (le4 (Z_to_bv 64 dl)) ->
    bytes_at rsegs m (S1 + 48) (le8 s2v ++ le8 s1v ++ le8 s0v ++ le8 rav) ->
    evt rsegs (caw_ret rav (Z_to_bv 64 (caw_rv go gr)) (Z_to_bv 64 (S1 + 80)) gp tp s0v s1v s2v s3 s4 s5 s6 s7 s8 s9
                 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CAW_RET_ACCEPT) fc None m (seg_rom rsegs)).
