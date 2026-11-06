From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_DISCO_TABLE_OBSERVE : Z := 0x1557c.
Definition REAC_DISCO_TABLE_OBSERVE_K : Z := 80.

Definition fam_of (T : list byte) (i : Z) : Z := u_at T (48 * i + 15) 1.
Definition slots_of (T : list byte) (i : Z) : Z := u_at T (48 * i + 16) 1.
Definition ch_of (T : list byte) (i : Z) : Z := u_at T (48 * i + 20) 4.
Definition zeros (n : nat) : list byte := repeat (Z_to_bv 8 0) n.

Definition observe_known (T G : list byte) (ow now i : Z) : list byte * Z :=
  let e := 48 * i in
  let Ta := upd T (e + 40) (Z_to_le_bytes 8 now) in
  let c_role := negb (s_role G =? 0) && negb (role_of_e T i =? s_role G) &&
                negb ((role_of_e T i =? 1) && (s_role G =? 2)) in
  let Tb := if c_role then upd Ta (e + 8) (sub G 8 4) else Ta in
  let c_decl := negb (s_hd G =? 0) &&
                ((hd_of T i =? 0) || negb (din_of T i =? s_din G) || negb (dout_of T i =? s_dout G)) in
  let Tc := if c_decl then upd (upd (upd Tb (e + 12) [Z_to_bv 8 1]) (e + 13) (sub G 13 1)) (e + 14) (sub G 14 1)
            else Tb in
  let c_slots := negb (s_slots G =? 0) && negb (slots_of T i =? s_slots G) in
  let Td := if c_slots then upd Tc (e + 16) (sub G 16 1) else Tc in
  let c_fam := negb (s_fam G =? 0) && negb (fam_of T i =? s_fam G) in
  let Te := if c_fam then upd Td (e + 15) (sub G 15 1) else Td in
  let c_ch := ch_of T i <? s_ch G in
  let Tf := if c_ch then upd Te (e + 20) (sub G 20 4) else Te in
  let c_own := negb (ow =? 0) && (owned_of T i =? 0) in
  let Tg := if c_own then upd Tf (e + 24) (Z_to_le_bytes 4 1) else Tf in
  if c_role || c_decl || c_slots || c_fam || c_ch || c_own
  then (upd Tg 392 (Z_to_le_bytes 4 (seq_of T + 1)), 1)
  else (Tg, 0).

Definition observe_full (T : list byte) : list byte * Z :=
  if ov_of T =? 0
  then (upd (upd T 388 (Z_to_le_bytes 4 1)) 392 (Z_to_le_bytes 4 (seq_of T + 1)), 0)
  else (T, 0).

Definition new_entry (G : list byte) (ow now : Z) : list byte :=
  s_mac G ++ zeros 2 ++ sub G 8 4 ++ sub G 12 1 ++ sub G 13 1 ++ sub G 14 1 ++ sub G 15 1 ++ sub G 16 1 ++
  zeros 3 ++ sub G 20 4 ++ Z_to_le_bytes 4 (if ow =? 0 then 0 else 1) ++ zeros 4 ++
  Z_to_le_bytes 8 now ++ Z_to_le_bytes 8 now.

Definition observe_new (T G : list byte) (ow now : Z) : list byte * Z :=
  (upd (upd (upd T 384 (Z_to_le_bytes 4 (n_of T + 1))) (48 * n_of T) (new_entry G ow now))
       392 (Z_to_le_bytes 4 (seq_of T + 1)), 1).

Definition observe_model (T G : list byte) (ow now : Z) (T' : list byte) (ret : Z) : Prop :=
  exists r, find_res T (s_mac G) r /\
    ((0 <= r /\ (T', ret) = observe_known T G ow now r) \/
     (r = -1 /\ 8 <= n_of T /\ (T', ret) = observe_full T) \/
     (r = -1 /\ n_of T < 8 /\ (T', ret) = observe_new T G ow now)).

Definition reac_disco_table_observe_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo t s ow now : Z) (T G : list byte),
    a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 ow -> a3 = Z_to_bv 64 now ->
    -2^31 <= ow < 2^31 -> 0 <= now < 2^64 ->
    t <> 0 -> t mod 8 = 0 ->
    rw_cells rsegs m t [CB 400 T] -> length T = 400%nat ->
    s <> 0 -> s mod 4 = 0 ->
    bytes_at rsegs m s G -> length G = 24%nat ->
    s + 24 <= t \/ t + 400 <= s ->
    tbl_T1 T -> tbl_T2 T -> tbl_T3 T -> sighting_S1 G -> sighting_S2 G ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_DISCO_TABLE_OBSERVE_K <= bv_unsigned sp ->
    off_window sp REAC_DISCO_TABLE_OBSERVE_K t 400 -> off_window sp REAC_DISCO_TABLE_OBSERVE_K s 24 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte) (T' : list byte) (ret : Z),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 ret) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(t, t + 400); (bv_unsigned sp - REAC_DISCO_TABLE_OBSERVE_K, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' t [CB 400 T'] /\ bytes_at rsegs m' s G /\
         observe_model T G ow now T' ret /\
         tbl_T1 T' /\ tbl_T2 T' /\ tbl_T3 T' /\ (tbl_T4 T -> tbl_T4 T'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_DISCO_TABLE_OBSERVE) fc None m (seg_rom rsegs)).
