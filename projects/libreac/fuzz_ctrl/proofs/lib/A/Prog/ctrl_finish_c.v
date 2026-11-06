From Stdlib Require Import ZArith List.
From Stdlib Require Import Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcFin.
Import ListNotations.
Open Scope Z_scope.

Definition CTRL_FINISH : Z := 0x85994.
Definition CTRL_FINISH_FRAME : Z := 16.

Definition ctrl_finish_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p f c o n lo : Z) (row B : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 f ->
    f mod 8 = 0 -> f + 24 <= 2^64 -> length row = 24%nat -> bytes_at rsegs m f row ->
    ubat row 20 = c -> ubat row 18 = o -> ubat row 19 = n ->
    c <= 2 -> (c = 2 -> 2 <= n /\ o + n <= 31) ->
    0 < p -> p + 50 <= 2^64 ->
    (c = 1 \/ c = 2 -> rw_cells rsegs m (p + 18) [CB 32 B]) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CTRL_FINISH_FRAME <= bv_unsigned sp ->
    (bv_unsigned sp <= f \/ f + 24 <= bv_unsigned sp - CTRL_FINISH_FRAME) ->
    (c = 1 \/ c = 2 -> bv_unsigned sp <= p + 18 \/ p + 50 <= bv_unsigned sp - CTRL_FINISH_FRAME) ->
    asan_cells m -> shadow_rw m ->
    addressable m (f + 18) 3 ->
    (c = 1 \/ c = 2 -> addressable m (p + 18) 32) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside ((bv_unsigned sp - CTRL_FINISH_FRAME, bv_unsigned sp) :: fin_w c o n p) x) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch ((bv_unsigned sp - CTRL_FINISH_FRAME, bv_unsigned sp) :: fin_w c o n p) m m'
         /\ wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp)
         /\ (c = 1 \/ c = 2 ->
               rw_cells rsegs m' (p + 18) [CB 32 (fin c o n B)]
               /\ closes c o n (fin c o n B) /\ (closes c o n B -> fin c o n B = B)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_FINISH) fc None m (seg_rom rsegs)).

(* Footprint form (RECIPE.md step 1 (a working note, not in this delivery)): the same run as an ExecF.evtF under a footprint RNG, with one rng
   premise per region the run reads or writes: the 16-byte frame; the GOT cell and the runtime cell that hold the
   shadow offset (the outside premise above names the same cells); the 24 bytes of the row at f and the shadow bytes
   of the 3 checked bytes at f + 18; and, when c is 1 or 2, the 32 bytes at p + 18 and their shadow bytes. Shadow
   spans are byte-exact ((x >> 3) + ASAN_K per checked byte).
   ctrl_finish_contract_of_F gives the old statement back with RNG_all. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.

Definition ctrl_finish_contract_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p f c o n lo : Z) (row B : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 f ->
    f mod 8 = 0 -> f + 24 <= 2^64 -> length row = 24%nat -> bytes_at rsegs m f row ->
    ubat row 20 = c -> ubat row 18 = o -> ubat row 19 = n ->
    c <= 2 -> (c = 2 -> 2 <= n /\ o + n <= 31) ->
    0 < p -> p + 50 <= 2^64 ->
    (c = 1 \/ c = 2 -> rw_cells rsegs m (p + 18) [CB 32 B]) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CTRL_FINISH_FRAME <= bv_unsigned sp ->
    (bv_unsigned sp <= f \/ f + 24 <= bv_unsigned sp - CTRL_FINISH_FRAME) ->
    (c = 1 \/ c = 2 -> bv_unsigned sp <= p + 18 \/ p + 50 <= bv_unsigned sp - CTRL_FINISH_FRAME) ->
    asan_cells m -> shadow_rw m ->
    addressable m (f + 18) 3 ->
    (c = 1 \/ c = 2 -> addressable m (p + 18) 32) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside ((bv_unsigned sp - CTRL_FINISH_FRAME, bv_unsigned sp) :: fin_w c o n p) x) ->
    rng RNG (bv_unsigned sp - CTRL_FINISH_FRAME) CTRL_FINISH_FRAME ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    rng RNG f 24 ->
    rng RNG ((f + 18) / 8 + ASAN_K) ((f + 20) / 8 - (f + 18) / 8 + 1) ->
    (c = 1 \/ c = 2 ->
       rng RNG (p + 18) 32 /\ rng RNG ((p + 18) / 8 + ASAN_K) ((p + 49) / 8 - (p + 18) / 8 + 1)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch ((bv_unsigned sp - CTRL_FINISH_FRAME, bv_unsigned sp) :: fin_w c o n p) m m'
         /\ wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp)
         /\ (c = 1 \/ c = 2 ->
               rw_cells rsegs m' (p + 18) [CB 32 (fin c o n B)]
               /\ closes c o n (fin c o n B) /\ (closes c o n B -> fin c o n B = B)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_FINISH) fc None m (seg_rom rsegs)).

(* The old statement is the _F statement at the footprint that admits every access (every rng premise by rng_all). *)
Lemma ctrl_finish_contract_of_F : ctrl_finish_contract_F -> ctrl_finish_contract.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p f c o n lo row B Ha0 Ha1 Hf8 Hf24 Hrl HR Hc Ho Hn Hc2 Hrec Hp Hp50 HRW ST HLO HDf HDp HCE HSW HADf HADp
    HWO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  pose proof (bytes_at_bound rsegs m f row HR) as Bf.
  assert (RFR : rng RNG_all (bv_unsigned sp - CTRL_FINISH_FRAME) CTRL_FINISH_FRAME)
    by (apply rng_all; unfold CTRL_FINISH_FRAME in *; lia).
  assert (RGK : rng RNG_all GOT_CELL_K 8) by (apply rng_all; unfold GOT_CELL_K; lia).
  assert (RCK : rng RNG_all CELL_K 8) by (apply rng_all; unfold CELL_K; lia).
  assert (RROW : rng RNG_all f 24) by (apply rng_all; lia).
  assert (RSf : rng RNG_all ((f + 18) / 8 + ASAN_K) ((f + 20) / 8 - (f + 18) / 8 + 1))
    by (apply rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia).
  assert (RP : c = 1 \/ c = 2 ->
               rng RNG_all (p + 18) 32 /\
               rng RNG_all ((p + 18) / 8 + ASAN_K) ((p + 49) / 8 - (p + 18) / 8 + 1))
    by (intros _; split; apply rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia).
  exact (evtF_evt rsegs RNG_all _ _
           (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc m p f c o n lo row B Ha0 Ha1 Hf8 Hf24 Hrl HR Hc Ho Hn Hc2 Hrec Hp Hp50 HRW ST HLO HDf HDp
               HCE HSW HADf HADp HWO RFR RGK RCK RROW RSf RP)).
Qed.

(* Route (C) (a Theorem Labs lane 2026-10-29 09:20Z; form of a Theorem Labs lane 09:38Z): ctrl_finish_contract_on and
   ctrl_finish_contract_F_on are the two statements above with ONE change: the premise `shadow_rw m` is DROPPED.  The
   run reads no shadow byte through it.  The only shadow bytes the run loads are those of the 3 checked bytes at
   f + 18 and, when c is 1 or 2, of the 32 bytes at p + 18; the premises `addressable m (f + 18) 3` and
   `addressable m (p + 18) 32` give each of those bytes present with its value (AsanRT.addr_byte).  Both proofs bind
   the premise and do not use it (ctrl_finish.v:247 and ctrl_finishF.v:257, HSW).  The post has no shadow_rw.  Each old
   statement follows in one step (the _of_on lemmas); ctrl_finish_contract_on_of_F_on is ctrl_finish_contract_of_F for
   the new pair. *)
Definition ctrl_finish_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p f c o n lo : Z) (row B : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 f ->
    f mod 8 = 0 -> f + 24 <= 2^64 -> length row = 24%nat -> bytes_at rsegs m f row ->
    ubat row 20 = c -> ubat row 18 = o -> ubat row 19 = n ->
    c <= 2 -> (c = 2 -> 2 <= n /\ o + n <= 31) ->
    0 < p -> p + 50 <= 2^64 ->
    (c = 1 \/ c = 2 -> rw_cells rsegs m (p + 18) [CB 32 B]) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CTRL_FINISH_FRAME <= bv_unsigned sp ->
    (bv_unsigned sp <= f \/ f + 24 <= bv_unsigned sp - CTRL_FINISH_FRAME) ->
    (c = 1 \/ c = 2 -> bv_unsigned sp <= p + 18 \/ p + 50 <= bv_unsigned sp - CTRL_FINISH_FRAME) ->
    asan_cells m ->
    addressable m (f + 18) 3 ->
    (c = 1 \/ c = 2 -> addressable m (p + 18) 32) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside ((bv_unsigned sp - CTRL_FINISH_FRAME, bv_unsigned sp) :: fin_w c o n p) x) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch ((bv_unsigned sp - CTRL_FINISH_FRAME, bv_unsigned sp) :: fin_w c o n p) m m'
         /\ wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp)
         /\ (c = 1 \/ c = 2 ->
               rw_cells rsegs m' (p + 18) [CB 32 (fin c o n B)]
               /\ closes c o n (fin c o n B) /\ (closes c o n B -> fin c o n B = B)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_FINISH) fc None m (seg_rom rsegs)).

Lemma ctrl_finish_contract_of_on : ctrl_finish_contract_on -> ctrl_finish_contract.
Proof.
  intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p f c o n lo row B Ha0 Ha1 Hf8 Hf24 Hrl HR Hc Ho Hn Hc2 Hrec Hp Hp50 HRW ST HLO HDf HDp HCE _ HADf HADp
    HWO.
  exact (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m p f c o n lo row B Ha0 Ha1 Hf8 Hf24 Hrl HR Hc Ho Hn Hc2 Hrec Hp Hp50 HRW ST HLO HDf HDp HCE HADf HADp
           HWO).
Qed.

Definition ctrl_finish_contract_F_on : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p f c o n lo : Z) (row B : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 f ->
    f mod 8 = 0 -> f + 24 <= 2^64 -> length row = 24%nat -> bytes_at rsegs m f row ->
    ubat row 20 = c -> ubat row 18 = o -> ubat row 19 = n ->
    c <= 2 -> (c = 2 -> 2 <= n /\ o + n <= 31) ->
    0 < p -> p + 50 <= 2^64 ->
    (c = 1 \/ c = 2 -> rw_cells rsegs m (p + 18) [CB 32 B]) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CTRL_FINISH_FRAME <= bv_unsigned sp ->
    (bv_unsigned sp <= f \/ f + 24 <= bv_unsigned sp - CTRL_FINISH_FRAME) ->
    (c = 1 \/ c = 2 -> bv_unsigned sp <= p + 18 \/ p + 50 <= bv_unsigned sp - CTRL_FINISH_FRAME) ->
    asan_cells m ->
    addressable m (f + 18) 3 ->
    (c = 1 \/ c = 2 -> addressable m (p + 18) 32) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside ((bv_unsigned sp - CTRL_FINISH_FRAME, bv_unsigned sp) :: fin_w c o n p) x) ->
    rng RNG (bv_unsigned sp - CTRL_FINISH_FRAME) CTRL_FINISH_FRAME ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    rng RNG f 24 ->
    rng RNG ((f + 18) / 8 + ASAN_K) ((f + 20) / 8 - (f + 18) / 8 + 1) ->
    (c = 1 \/ c = 2 ->
       rng RNG (p + 18) 32 /\ rng RNG ((p + 18) / 8 + ASAN_K) ((p + 49) / 8 - (p + 18) / 8 + 1)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch ((bv_unsigned sp - CTRL_FINISH_FRAME, bv_unsigned sp) :: fin_w c o n p) m m'
         /\ wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp)
         /\ (c = 1 \/ c = 2 ->
               rw_cells rsegs m' (p + 18) [CB 32 (fin c o n B)]
               /\ closes c o n (fin c o n B) /\ (closes c o n B -> fin c o n B = B)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_FINISH) fc None m (seg_rom rsegs)).

Lemma ctrl_finish_contract_F_of_F_on : ctrl_finish_contract_F_on -> ctrl_finish_contract_F.
Proof.
  intros H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p f c o n lo row B Ha0 Ha1 Hf8 Hf24 Hrl HR Hc Ho Hn Hc2 Hrec Hp Hp50 HRW ST HLO HDf HDp HCE _ HADf HADp
    HWO RFR RGK RCK RROW RSf RP.
  exact (H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m p f c o n lo row B Ha0 Ha1 Hf8 Hf24 Hrl HR Hc Ho Hn Hc2 Hrec Hp Hp50 HRW ST HLO HDf HDp HCE HADf HADp
           HWO RFR RGK RCK RROW RSf RP).
Qed.

(* ctrl_finish_contract_of_F for the route (C) pair. *)
Lemma ctrl_finish_contract_on_of_F_on : ctrl_finish_contract_F_on -> ctrl_finish_contract_on.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p f c o n lo row B Ha0 Ha1 Hf8 Hf24 Hrl HR Hc Ho Hn Hc2 Hrec Hp Hp50 HRW ST HLO HDf HDp HCE HADf HADp
    HWO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  pose proof (bytes_at_bound rsegs m f row HR) as Bf.
  assert (RFR : rng RNG_all (bv_unsigned sp - CTRL_FINISH_FRAME) CTRL_FINISH_FRAME)
    by (apply rng_all; unfold CTRL_FINISH_FRAME in *; lia).
  assert (RGK : rng RNG_all GOT_CELL_K 8) by (apply rng_all; unfold GOT_CELL_K; lia).
  assert (RCK : rng RNG_all CELL_K 8) by (apply rng_all; unfold CELL_K; lia).
  assert (RROW : rng RNG_all f 24) by (apply rng_all; lia).
  assert (RSf : rng RNG_all ((f + 18) / 8 + ASAN_K) ((f + 20) / 8 - (f + 18) / 8 + 1))
    by (apply rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia).
  assert (RP : c = 1 \/ c = 2 ->
               rng RNG_all (p + 18) 32 /\
               rng RNG_all ((p + 18) / 8 + ASAN_K) ((p + 49) / 8 - (p + 18) / 8 + 1))
    by (intros _; split; apply rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia).
  exact (evtF_evt rsegs RNG_all _ _
           (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc m p f c o n lo row B Ha0 Ha1 Hf8 Hf24 Hrl HR Hc Ho Hn Hc2 Hrec Hp Hp50 HRW ST HLO HDf HDp
               HCE HADf HADp HWO RFR RGK RCK RROW RSf RP)).
Qed.

Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_finish_c.ctrl_finish_contract_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_finish_c.ctrl_finish_contract_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_finish_c.ctrl_finish_contract_F_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_finish_c.ctrl_finish_contract_F_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_finish_c.ctrl_finish_contract_of_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_finish_c.ctrl_finish_contract_of_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_finish_c.ctrl_finish_contract_F_of_F_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_finish_c.ctrl_finish_contract_F_of_F_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_finish_c.ctrl_finish_contract_on_of_F_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_finish_c.ctrl_finish_contract_on_of_F_on.
