From Stdlib Require Import ZArith List.
From Stdlib Require Import Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcFin.
Import ListNotations.
Open Scope Z_scope.

Definition CTRL_FINISH : Z := 0x864e4.
Definition CTRL_FINISH_FRAME : Z := 32.

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
    (bv_unsigned sp <= f \/ f + 24 <= bv_unsigned sp - 16) ->
    (c = 1 \/ c = 2 -> bv_unsigned sp <= p + 18 \/ p + 50 <= bv_unsigned sp - CTRL_FINISH_FRAME) ->
    asan_cells m -> shadow_rw m ->
    addressable m (f + 18) 3 ->
    (c = 1 \/ c = 2 -> addressable m (p + 18) 32) ->
    (forall x, RT_LO <= x < RT_HI \/ in_shadow x ->
       outside ((bv_unsigned sp - CTRL_FINISH_FRAME, bv_unsigned sp) :: fin_w c o n p) x) ->
    evt rsegs
      (fun ms' => exists (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
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
   premise per region the run reads or writes: the 32-byte frame; the runtime words [RT_LO, RT_HI) (the GOT cell and
   the cell of the shadow offset live there, and the outside premise above names the same range); the 24 bytes of the
   row at f and the shadow bytes of the 3 checked bytes at f + 18; and, when c is 1 or 2, the 32 bytes at p + 18 and
   their shadow bytes. Shadow spans are byte-exact ((x >> 3) + ASAN_K per checked byte).
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
    (bv_unsigned sp <= f \/ f + 24 <= bv_unsigned sp - 16) ->
    (c = 1 \/ c = 2 -> bv_unsigned sp <= p + 18 \/ p + 50 <= bv_unsigned sp - CTRL_FINISH_FRAME) ->
    asan_cells m -> shadow_rw m ->
    addressable m (f + 18) 3 ->
    (c = 1 \/ c = 2 -> addressable m (p + 18) 32) ->
    (forall x, RT_LO <= x < RT_HI \/ in_shadow x ->
       outside ((bv_unsigned sp - CTRL_FINISH_FRAME, bv_unsigned sp) :: fin_w c o n p) x) ->
    rng RNG (bv_unsigned sp - CTRL_FINISH_FRAME) CTRL_FINISH_FRAME ->
    rng RNG RT_LO (RT_HI - RT_LO) ->
    rng RNG f 24 ->
    rng RNG ((f + 18) / 8 + ASAN_K) ((f + 20) / 8 - (f + 18) / 8 + 1) ->
    (c = 1 \/ c = 2 ->
       rng RNG (p + 18) 32 /\ rng RNG ((p + 18) / 8 + ASAN_K) ((p + 49) / 8 - (p + 18) / 8 + 1)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
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
  assert (RRT : rng RNG_all RT_LO (RT_HI - RT_LO)) by (apply rng_all; unfold RT_LO, RT_HI; lia).
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
               HCE HSW HADf HADp HWO RFR RRT RROW RSf RP)).
Qed.

(* Route (C), premise DROPPED (a Theorem Labs lane's rule; approved a Theorem Labs lane 11:29Z). ctrl_finish reads and stores NO shadow
   byte THROUGH the shadow_rw premise: its only use of HSW in ctrl_finishF.v was to feed the block / record
   cksum_stamp callees, and both of those are now premise-free (their _on contracts take no shadow_rw). Its own
   f+18 shadow check reads through addressable (rt_shadow_rd). So the _on forms drop `shadow_rw m ->` and name no
   region. Image-A form: premise DROPPED (A Theorem Labs lane parent, ctrl_finish_contract_on). *)
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
    (bv_unsigned sp <= f \/ f + 24 <= bv_unsigned sp - 16) ->
    (c = 1 \/ c = 2 -> bv_unsigned sp <= p + 18 \/ p + 50 <= bv_unsigned sp - CTRL_FINISH_FRAME) ->
    asan_cells m ->
    addressable m (f + 18) 3 ->
    (c = 1 \/ c = 2 -> addressable m (p + 18) 32) ->
    (forall x, RT_LO <= x < RT_HI \/ in_shadow x ->
       outside ((bv_unsigned sp - CTRL_FINISH_FRAME, bv_unsigned sp) :: fin_w c o n p) x) ->
    evt rsegs
      (fun ms' => exists (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
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
Proof. unfold ctrl_finish_contract_on, ctrl_finish_contract. intros H. intros. eapply H; eassumption. Qed.

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
    (bv_unsigned sp <= f \/ f + 24 <= bv_unsigned sp - 16) ->
    (c = 1 \/ c = 2 -> bv_unsigned sp <= p + 18 \/ p + 50 <= bv_unsigned sp - CTRL_FINISH_FRAME) ->
    asan_cells m ->
    addressable m (f + 18) 3 ->
    (c = 1 \/ c = 2 -> addressable m (p + 18) 32) ->
    (forall x, RT_LO <= x < RT_HI \/ in_shadow x ->
       outside ((bv_unsigned sp - CTRL_FINISH_FRAME, bv_unsigned sp) :: fin_w c o n p) x) ->
    rng RNG (bv_unsigned sp - CTRL_FINISH_FRAME) CTRL_FINISH_FRAME ->
    rng RNG RT_LO (RT_HI - RT_LO) ->
    rng RNG f 24 ->
    rng RNG ((f + 18) / 8 + ASAN_K) ((f + 20) / 8 - (f + 18) / 8 + 1) ->
    (c = 1 \/ c = 2 ->
       rng RNG (p + 18) 32 /\ rng RNG ((p + 18) / 8 + ASAN_K) ((p + 49) / 8 - (p + 18) / 8 + 1)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch ((bv_unsigned sp - CTRL_FINISH_FRAME, bv_unsigned sp) :: fin_w c o n p) m m'
         /\ wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp)
         /\ (c = 1 \/ c = 2 ->
               rw_cells rsegs m' (p + 18) [CB 32 (fin c o n B)]
               /\ closes c o n (fin c o n B) /\ (closes c o n B -> fin c o n B = B)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_FINISH) fc None m (seg_rom rsegs)).

Lemma ctrl_finish_contract_F_of_on : ctrl_finish_contract_F_on -> ctrl_finish_contract_F.
Proof. unfold ctrl_finish_contract_F_on, ctrl_finish_contract_F. intros H. intros. eapply H; eassumption. Qed.
