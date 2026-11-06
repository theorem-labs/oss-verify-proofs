From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_json_text.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_DISCO_TABLE_JSON : Z := 0x15874.
Definition TJ_F : Z := 288.
Definition TJ_K : Z := TJ_F + Z.max SNPRINTF_K BN_K.

Definition box_tok (f a b : Z) : option (list Z) :=
  if bn_ret f [] a b =? 0 then Some (bn_TK (bn_NM f [] a b)) else None.

Definition tj_entry (T : list byte) (i : Z) : entry :=
  mkE (map bv_unsigned (mac_of T i)) (role_of_e T i) (hd_of T i) (din_of T i) (dout_of T i)
      (u_at T (48 * i + 15) 1) (owned_of T i) (last_of T i).

Definition tj_entries (T : list byte) : list entry :=
  map (fun k => tj_entry T (Z.of_nat k)) (seq 0 (Z.to_nat (n_of T))).

Definition tj_text (T : list byte) (now : Z) : list Z := table_json_text box_tok (tj_entries T) now.

Definition bn_table : list byte := le8 (Z_to_bv 64 BN_S1) ++ le8 (Z_to_bv 64 BN_S2) ++ le8 (Z_to_bv 64 BN_S3).

Definition reac_disco_table_json_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (canary : word)
         (T junk : list byte),
    let S := bv_unsigned sp in let t := bv_unsigned a0 in let now := bv_unsigned a1 in
    let buf := bv_unsigned a2 in let cap := bv_unsigned a3 in
    let text := tj_text T now in let len := Z.of_nat (length text) in
    bytes_at rsegs m t T -> length T = 400%nat -> 0 < t -> t mod 8 = 0 -> disco_table_c.table_ok T ->
    (t + 400 <= lo \/ S <= t) ->
    cap < 2^31 ->
    (3 <= cap ->
       0 < buf /\ rw_cells rsegs m buf [CB (Z.to_nat cap) junk] /\
       (buf + cap <= lo \/ S <= buf) /\ (buf + cap <= t \/ t + 400 <= buf) /\ pf_img_free buf cap) ->
    stk rsegs m lo S -> lo + TJ_K <= S -> IMG_END <= lo -> S < 2^63 -> S mod 16 = 0 ->
    bytes_at rsegs m BN_TS bn_table ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
         frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ stk rsegs m' lo S /\
         (cap < 3 -> a0' = Z_to_bv 64 (-1) /\ munch [(lo, S)] m m') /\
         (3 <= cap -> len < cap ->
            a0' = Z_to_bv 64 len /\ munch [(lo, S); (buf, buf + len + 1)] m m' /\
            bytes_at rsegs m' buf (pf_bytes (text ++ [0]))) /\
         (3 <= cap -> cap <= len -> a0' = Z_to_bv 64 (-1) /\ munch [(lo, S); (buf, buf + cap)] m m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_DISCO_TABLE_JSON) fc None m (seg_rom rsegs)).
