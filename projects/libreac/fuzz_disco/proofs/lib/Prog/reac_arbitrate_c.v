From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c reac_rival_kind_of_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_ARBITRATE : Z := 0x162dc.
Definition REAC_ARBITRATE_K : Z := 96.
Definition REAC_DISCO_STALE_NS : Z := 5 * 10^9.

Definition slots_of (T : list byte) (i : Z) : Z := u_at T (48 * i + 16) 1.
Definition ch_of (T : list byte) (i : Z) : Z := u_at T (48 * i + 20) 4.

Fixpoint bytes_eqb (l r : list byte) : bool :=
  match l, r with
  | [], [] => true
  | x :: l', y :: r' => (bv_unsigned x =? bv_unsigned y) && bytes_eqb l' r'
  | _, _ => false
  end.

Definition stale (T : list byte) (now i : Z) : bool :=
  (last_of T i <? now) && (REAC_DISCO_STALE_NS <? now - last_of T i).

Definition cand (T P : list byte) (our now i : Z) : bool :=
  (role_of_e T i =? 2) && ((our =? 0) || negb (bytes_eqb (mac_of T i) P)) && negb (stale T now i).

Definition cands (T P : list byte) (our now : Z) : list Z :=
  List.filter (cand T P our now) (map Z.of_nat (seq 0 (Z.to_nat (n_of T)))).

Definition best (t : Z) (T P : list byte) (our now : Z) : option Z :=
  if t =? 0 then None
  else match cands T P our now with
       | [] => None
       | j :: _ =>
           let M := fold_right (fun i acc => Z.max (last_of T i) acc) (last_of T j) (cands T P our now) in
           List.find (fun i => last_of T i =? M) (cands T P our now)
       end.

Definition rival_of (T : list byte) (j : Z) : Z :=
  reac_rival_kind_model (hd_of T j) (role_of_e T j) (slots_of T j) (ch_of T j).

Definition z4 (v : Z) : list byte := le4 (Z_to_bv 64 v).

Definition MAC0 : list byte := repeat (Z_to_bv 8 0) 6.

Definition arb_bytes (state : Z) (mac : list byte) (have_mac pace conflict rival rival_channels : Z) : list byte :=
  z4 state ++ mac ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++ z4 have_mac ++ z4 pace ++ z4 conflict ++ z4 rival ++
  z4 rival_channels.

Definition arb_model (t our : Z) (T P : list byte) (fsm pace now : Z) : list byte :=
  let our_mac := if our =? 0 then MAC0 else P in
  let our_have := if our =? 0 then 0 else 1 in
  match best t T P our now with
  | Some j =>
      if (fsm =? 2) || (fsm =? 3) then arb_bytes 1 our_mac our_have pace 1 (rival_of T j) (ch_of T j)
      else arb_bytes 2 (mac_of T j) 1 1 0 (rival_of T j) (ch_of T j)
  | None =>
      if (fsm =? 2) || (fsm =? 3) then arb_bytes 1 our_mac our_have pace 0 0 0
      else if fsm =? 1 then arb_bytes 1 our_mac our_have pace 0 0 0
      else arb_bytes 0 MAC0 0 pace 0 0 0
  end.

Definition reac_arbitrate_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t our fsm pace now out lo : Z) (T P O : list byte),
    a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 our -> a2 = Z_to_bv 64 fsm -> a3 = Z_to_bv 64 pace ->
    a4 = Z_to_bv 64 now -> a5 = Z_to_bv 64 out ->
    0 <= t < 2^64 -> 0 <= our < 2^64 -> -2^31 <= fsm < 2^31 -> -2^31 <= pace < 2^31 -> 0 <= now < 2^64 ->
    0 < out < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_ARBITRATE_K <= bv_unsigned sp ->
    (t <> 0 -> t mod 8 = 0 /\ length T = 400%nat /\ bytes_at rsegs m t T /\ table_ok T /\
               off_window sp REAC_ARBITRATE_K t 400 /\ (out + 32 <= t \/ t + 400 <= out)) ->
    (our <> 0 -> length P = 6%nat /\ bytes_at rsegs m our P /\
                 off_window sp REAC_ARBITRATE_K our 6 /\ (out + 32 <= our \/ our + 6 <= out)) ->
    out mod 4 = 0 -> length O = 32%nat -> bytes_at rsegs m out O -> wr_at rsegs m out 32 ->
    off_window sp REAC_ARBITRATE_K out 32 ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_ARBITRATE_K, bv_unsigned sp); (out, out + 32)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' out (arb_model t our T P fsm pace now) /\
         (t <> 0 -> bytes_at rsegs m' t T) /\ (our <> 0 -> bytes_at rsegs m' our P))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_ARBITRATE) fc None m (seg_rom rsegs)).
