From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import CtrlParsed disco_classify_c.
Import ListNotations.
Open Scope Z_scope.

Definition CLASSIFY_CORE : Z := 0x15164.
Definition CLASSIFY_CORE_K : Z := 192.

Definition disj (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.

Definition classify_core_pre (m : word -> option byte) (S lo lk f len u o : Z) (FB U OB : list byte)
    (L : option (list byte)) : Prop :=
  S mod 16 = 0 /\ stk rsegs m lo S /\ lo + CLASSIFY_CORE_K <= S /\
  0 <= len < 2 ^ 64 /\ 0 <= f < 2 ^ 64 /\ length FB = 50%nat /\
  (50 <= len -> 0 < f /\ bytes_at rsegs m f FB /\ disj f 50 (S - CLASSIFY_CORE_K) CLASSIFY_CORE_K /\
                disj o 24 f 50) /\
  length U = 6%nat /\ bytes_at rsegs m u U /\ disj u 6 (S - CLASSIFY_CORE_K) CLASSIFY_CORE_K /\
  0 < o /\ o mod 4 = 0 /\ rw_cells rsegs m o [CB 24 OB] /\ disj o 24 (S - CLASSIFY_CORE_K) CLASSIFY_CORE_K /\
  disj o 24 u 6 /\
  match L with
  | None => lk = 0
  | Some Lb => 0 < lk /\ lk mod 4 = 0 /\ rw_cells rsegs m lk [CB 12 Lb] /\
               disj lk 12 (S - CLASSIFY_CORE_K) CLASSIFY_CORE_K /\ disj lk 12 o 24 /\ disj lk 12 u 6 /\
               (50 <= len -> disj lk 12 f 50)
  end /\
  mem_inv rsegs m.

Definition classify_core_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo lk len o : Z) (FB U OB : list byte) (L : option (list byte)) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (cm_ret FB len U L)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch ((bv_unsigned sp - CLASSIFY_CORE_K, bv_unsigned sp) :: (o, o + 24)
             :: match L with None => [] | Some _ => [(lk, lk + 12)] end) m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    rw_cells rsegs m' o [CB 24 (cm_out FB len U L OB)] /\
    match cm_lock FB len U L with None => True | Some Lb' => rw_cells rsegs m' lk [CB 12 Lb'] end.

Definition classify_core_spec (entry : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo lk f len u o : Z) (FB U OB : list byte)
         (L : option (list byte)),
    a0 = Z_to_bv 64 lk -> a1 = Z_to_bv 64 f -> a2 = Z_to_bv 64 len -> a3 = Z_to_bv 64 u -> a4 = Z_to_bv 64 o ->
    classify_core_pre m (bv_unsigned sp) lo lk f len u o FB U OB L ->
    evt rsegs (classify_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo lk len o FB U OB L)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).

Definition classify_core_contract : Prop := classify_core_spec CLASSIFY_CORE.
