From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c hunt_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_master_only_cadence_ns_c reac_rate_snap_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_sender_kind_c reac_disco_table_age_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_arbitrate_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_HUNT_STEP : Z := 0x16680.
Definition REAC_HUNT_STEP_K : Z := 208.
Definition REAC_HUNT_WINDOW_NS : Z := 3000000000.

Definition fs_of (T : list byte) (i : Z) : Z := u_at T (48 * i + 32) 8.

Definition hs_kind (h : Z) (T : list byte) (now i : Z) : Z :=
  reac_sender_kind_model (h + 48 * i) (role_of_e T i) (hd_of T i) (slots_of T i) (ch_of T i) (fs_of T i) now.

Definition hs_idx (T : list byte) : list Z := map Z.of_nat (seq 0 (Z.to_nat (n_of T))).

Definition desk_geometry_live (h : Z) (T U : list byte) (now : Z) : bool :=
  existsb (fun i => negb (disco_stale T i now) && negb (bytes_eqb (mac_of T i) U) && (role_of_e T i =? 0) &&
                    negb (ch_of T i =? 0) && (hs_kind h T now i =? 3)) (hs_idx T).

Definition box_present (h : Z) (T : list byte) (now : Z) : bool :=
  existsb (fun i => negb (disco_stale T i now) &&
                    ((role_of_e T i =? 1) || ((role_of_e T i =? 0) && (hs_kind h T now i =? 2)))) (hs_idx T).

Definition decide_model (pinned pin st rv sil op v0 now : Z) (dgl bp : bool) : Z :=
  if negb (pinned =? 0) then
    (if (pin =? 0) && (st =? 2) && (rv =? 2) then 2 else if pin =? 1 then 2 else 1)
  else if st =? 2 then (if rv =? 4 then v0 else if rv =? 3 then 3 else 2)
  else if dgl then 0
  else if negb (sil =? 0) then 1
  else if (now - op) mod 2^64 <? REAC_HUNT_WINDOW_NS then 0
  else if bp then 1
  else 0.

Definition hs_table (H : list byte) (now : Z) : list byte := fst (age_model (sub H 0 400) now).

Definition hs_arb (h : Z) (H : list byte) (now : Z) : list byte :=
  arb_model h (h + 412) (hs_table H now) (sub H 412 6) 0 0 now.

Definition hs_verdict (h : Z) (H : list byte) (now : Z) : Z :=
  decide_model (s32_at H 432) (s32_at H 436) (s32_at (hs_arb h H now) 0) (s32_at (hs_arb h H now) 24)
               (s32_at H 420) (u_at H 424 8) (s32_at H 440) now
               (desk_geometry_live h (hs_table H now) (sub H 412 6) now) (box_present h (hs_table H now) now).

Definition hs_hunt (h : Z) (H : list byte) (now : Z) : list byte :=
  hs_table H now ++ sub H 400 40 ++ le4 (Z_to_bv 64 (hs_verdict h H now)) ++ hs_arb h H now ++ skipn 476 H.

Definition reac_hunt_step_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo h now : Z) (H : list byte),
    a0 = Z_to_bv 64 h -> a1 = Z_to_bv 64 now -> 0 <= now < 2^64 ->
    0 < h -> h mod 8 = 0 -> rw_cells rsegs m h [CB 480 H] -> hunt_ok H ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + REAC_HUNT_STEP_K <= bv_unsigned sp ->
    off_window sp REAC_HUNT_STEP_K h 480 ->
    mem_inv rsegs m ->
    RT + 12 <= lo -> bytes_at rsegs m RT RATES ->
    bytes_at rsegs m A_P6000 (le8 (Z_to_bv 64 D6000)) -> bytes_at rsegs m A_P3837 (le8 (Z_to_bv 64 D3837)) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (F' : bvmap 5 word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (if hs_verdict h H now =? s32_at H 440 then 0 else 1)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom rsegs) /\
         freg_kept F F' /\
         munch [(bv_unsigned sp - REAC_HUNT_STEP_K, bv_unsigned sp); (h, h + 400); (h + 440, h + 476)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' h [CB 480 (hs_hunt h H now)] /\ hunt_ok (hs_hunt h H now))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_HUNT_STEP) fc None m (seg_rom rsegs)).
