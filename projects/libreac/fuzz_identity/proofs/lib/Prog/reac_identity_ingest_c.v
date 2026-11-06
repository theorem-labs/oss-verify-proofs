From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import RcIdentModel.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_IDENTITY_INGEST : Z := 0x145fc.

Definition ingest_refused (id p len : Z) : bool := (id =? 0) || (negb (len =? 0) && (p =? 0)).

Definition ingest_ret (id ad p len : Z) (idb pb : list byte) : Z :=
  if ingest_refused id p len then -1 else fst (ING idb ad pb).

Definition reac_identity_ingest_post (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (id ad p len : Z) (idb pb : list byte)
    : machine_state -> Prop :=
  fun ms' => exists (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (Z_to_bv 64 (ingest_ret id ad p len idb pb))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(id, id + 38)] m m' /\ wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m')
    /\ (ingest_refused id p len = true -> m' = m)
    /\ (ingest_refused id p len = false -> rw_cells rsegs m' id [CB 38 (snd (ING idb ad pb))]).

Definition reac_identity_ingest_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (id ad p len : Z) (idb pb : list byte),
    a0 = Z_to_bv 64 id -> a1 = Z_to_bv 64 ad -> a2 = Z_to_bv 64 p -> a3 = Z_to_bv 64 len ->
    0 <= id < 2^64 -> 0 <= ad < 65536 -> 0 <= p < 2^64 -> 0 <= len < 2^64 ->
    (id <> 0 -> id mod 2 = 0 /\ rw_cells rsegs m id [CB 38 idb]) ->
    length pb = Z.to_nat len ->
    (0 < len -> p <> 0 -> bytes_at rsegs m p pb) ->
    (id <> 0 -> 0 < len -> p <> 0 -> p + len <= id \/ id + 38 <= p) ->
    evt rsegs
      (reac_identity_ingest_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
         id ad p len idb pb)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_IDENTITY_INGEST) fc None m (seg_rom rsegs)).

Definition reac_identity_ingest_id_ok_kept : Prop :=
  forall (idb pb : list byte) (ad : Z), length idb = 38%nat -> id_ok idb -> id_ok (snd (ING idb ad pb)).
