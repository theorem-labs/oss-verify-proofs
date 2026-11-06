From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import CtrlParsed disco_classify_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c classify_core_c reac_frame_clean_len_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_table_observe_c hunt_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_HUNT_OBSERVE : Z := 0x16530.
Definition REAC_HUNT_OBSERVE_K : Z := 288.

Definition ho_entry (T G : list byte) (i : Z) : list byte :=
  sub G 0 8 ++ sub T (48 * i + 8) 9 ++ sub G 17 3 ++ sub T (48 * i + 20) 4.

Definition ho_answer (T G A : list byte) : Prop :=
  exists r, find_res T (s_mac G) r /\ A = (if r <? 0 then G else ho_entry T G r).

Definition ho_facts (H FR : list byte) (L : Z) (T A : list byte) : Prop :=
  50 <= L /\ s_mac A = sub FR 6 6 /\ s_mac A <> sub H 412 6 /\
  geo L <= s_ch A /\
  (s_role A = 0 \/ s_role A = 1 \/ s_role A = 2) /\
  ((fb FR 16 = 0 /\ fb FR 17 = 0) \/ fsum FR = 0) /\
  (s_hd A = 0 \/ s_hd A = 1) /\ (s_hd A <> 0 -> s_din A <= 40 /\ s_dout A <= 40) /\
  ((exists j, 0 <= j < n_of T /\ mac_of T j = s_mac A /\ role_of_e T j = 1) -> s_role A = 1).

Definition ho_post (H FR O : list byte) (len now out r : Z) (H' : list byte) (m' : word -> option byte) : Prop :=
  let FB := firstn 50 FR in
  let L := reac_frame_clean_len_model len in
  let T := sub H 0 400 in
  let U := sub H 412 6 in
  let Lk := Some (sub H 400 12) in
  let Lk' := match cm_lock FB L U Lk with Some x => x | None => sub H 400 12 end in
  (cm_ret FB L U Lk <> 0 ->
     r = -1 /\ H' = T ++ Lk' ++ skipn 412 H /\ (out <> 0 -> rw_cells rsegs m' out [CB 24 O])) /\
  (cm_ret FB L U Lk = 0 ->
     exists T' c, observe_model T (sight FB L) 0 now T' c /\ r = (if c =? 0 then 0 else 1) /\
       H' = T' ++ Lk' ++ sub H 412 12 ++ (if n_of T =? 0 then le8 (Z_to_bv 64 now) else sub H 424 8) ++
            skipn 432 H /\
       (out <> 0 -> exists A, ho_answer T' (sight FB L) A /\ rw_cells rsegs m' out [CB 24 A] /\
                              ho_facts H FR L T A)).

Definition reac_hunt_observe_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo h f len now out : Z) (H FR O : list byte),
    a0 = Z_to_bv 64 h -> a1 = Z_to_bv 64 f -> a2 = Z_to_bv 64 len -> a3 = Z_to_bv 64 now -> a4 = Z_to_bv 64 out ->
    0 <= len < 2^64 -> 0 <= now < 2^64 -> 0 <= out < 2^64 ->
    0 < h -> h mod 8 = 0 -> rw_cells rsegs m h [CB 480 H] -> hunt_ok H ->
    bytes_at rsegs m f FR -> length FR = Z.to_nat len -> (50 <= len -> 0 < f) ->
    (0 < len -> disj f len h 480 /\ off_window sp REAC_HUNT_OBSERVE_K f len) ->
    (out <> 0 -> out mod 4 = 0 /\ rw_cells rsegs m out [CB 24 O] /\ disj out 24 h 480 /\
                 (0 < len -> disj out 24 f len) /\ off_window sp REAC_HUNT_OBSERVE_K out 24) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + REAC_HUNT_OBSERVE_K <= bv_unsigned sp ->
    off_window sp REAC_HUNT_OBSERVE_K h 480 ->
    mem_inv rsegs m ->
    bytes_at rsegs m A_M (le8 (Z_to_bv 64 KM)) -> bytes_at rsegs m A_T (le8 (Z_to_bv 64 KT)) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte) (r : Z) (H' : list byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch ((bv_unsigned sp - REAC_HUNT_OBSERVE_K, bv_unsigned sp) :: (h, h + 480) ::
                (if out =? 0 then [] else [(out, out + 24)])) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' f FR /\ rw_cells rsegs m' h [CB 480 H'] /\ hunt_ok H' /\
         (r = -1 \/ r = 0 \/ r = 1) /\
         ho_post H FR O len now out r H' m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_HUNT_OBSERVE) fc None m (seg_rom rsegs)).
