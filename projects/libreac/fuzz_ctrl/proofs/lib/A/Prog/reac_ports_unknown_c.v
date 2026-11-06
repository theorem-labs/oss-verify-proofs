From Stdlib Require Import ZArith List.
From Stdlib Require Import Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcPorts.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_PORTS_UNKNOWN : Z := 0x87848.
Definition REAC_PORTS_UNKNOWN_FRAME : Z := 16.

Definition reac_ports_unknown_W (sp c : Z) : list ivl :=
  (sp - REAC_PORTS_UNKNOWN_FRAME, sp) :: (if c =? 0 then [] else [(c, c + 1)]).

Definition reac_ports_unknown_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p c lo : Z) (bs : list byte),
    bv_unsigned a0 = p ->
    bv_unsigned a1 = c ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_PORTS_UNKNOWN_FRAME <= bv_unsigned sp ->
    (p <> 0 -> p + 20 <= 2^64 /\ length bs = 20%nat /\ bytes_at rsegs m p bs /\
               (p + 20 <= bv_unsigned sp - REAC_PORTS_UNKNOWN_FRAME \/ bv_unsigned sp <= p)) ->
    (c <> 0 -> wr_at rsegs m c 1 /\ (p <> 0 -> c + 1 <= p \/ p + 20 <= c) /\
               (c + 1 <= bv_unsigned sp - REAC_PORTS_UNKNOWN_FRAME \/ bv_unsigned sp <= c)) ->
    asan_cells m -> shadow_rw m ->
    (c <> 0 -> addressable m c 1) ->
    (p <> 0 -> addressable m p 20) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside (reac_ports_unknown_W (bv_unsigned sp) c) x) ->
    evt rsegs
      (fun ms' => exists (a2' a3' a4' a5' a6' a7' t0' t1' t2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if pu_ok p bs then 4 * pu_nunk bs 12 else -1))
                       a1 a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch (reac_ports_unknown_W (bv_unsigned sp) c) m m'
         /\ wmono rsegs m m'
         /\ stk rsegs m' lo (bv_unsigned sp)
         /\ (mem_inv rsegs m -> mem_inv rsegs m')
         /\ (c <> 0 -> bytes_at rsegs m' c [Z_to_bv 8 (if pu_ok p bs then pu_first bs 12 else 0)]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_PORTS_UNKNOWN) fc None m (seg_rom rsegs)).

(* ---- the footprint form (RECIPE.md step 1 (a working note, not in this delivery)) ----
   The same run as an ExecF.evtF under any footprint RNG that holds every region the run reads or writes: the frame
   [sp - 16, sp), the two runtime cells GOT_CELL_K and CELL_K (8 bytes each), and, when the pointer is not 0, the
   20 bytes at p, the byte at c and the shadow bytes of each ((x >> 3) + ASAN_K, unaligned form of RECIPE step 1).
   reac_ports_unknown_contract_of_F gives the old statement back with ExecF.RNG_all. *)
Definition reac_ports_unknown_post (ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p c lo : Z) (bs : list byte)
    : machine_state -> Prop :=
  fun ms' => exists (a2' a3' a4' a5' a6' a7' t0' t1' t2' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if pu_ok p bs then 4 * pu_nunk bs 12 else -1))
                  a1 a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (reac_ports_unknown_W (bv_unsigned sp) c) m m'
    /\ wmono rsegs m m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ (mem_inv rsegs m -> mem_inv rsegs m')
    /\ (c <> 0 -> bytes_at rsegs m' c [Z_to_bv 8 (if pu_ok p bs then pu_first bs 12 else 0)]).

Definition reac_ports_unknown_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p c lo : Z) (bs : list byte),
    bv_unsigned a0 = p ->
    bv_unsigned a1 = c ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_PORTS_UNKNOWN_FRAME <= bv_unsigned sp ->
    (p <> 0 -> p + 20 <= 2^64 /\ length bs = 20%nat /\ bytes_at rsegs m p bs /\
               (p + 20 <= bv_unsigned sp - REAC_PORTS_UNKNOWN_FRAME \/ bv_unsigned sp <= p)) ->
    (c <> 0 -> wr_at rsegs m c 1 /\ (p <> 0 -> c + 1 <= p \/ p + 20 <= c) /\
               (c + 1 <= bv_unsigned sp - REAC_PORTS_UNKNOWN_FRAME \/ bv_unsigned sp <= c)) ->
    asan_cells m -> shadow_rw m ->
    (c <> 0 -> addressable m c 1) ->
    (p <> 0 -> addressable m p 20) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside (reac_ports_unknown_W (bv_unsigned sp) c) x) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_PORTS_UNKNOWN_FRAME) REAC_PORTS_UNKNOWN_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (p <> 0 -> ExecF.rng RNG p 20 /\
               ExecF.rng RNG (shadow_addr p) (shadow_addr (p + 19) - shadow_addr p + 1)) ->
    (c <> 0 -> ExecF.rng RNG c 1 /\ ExecF.rng RNG (shadow_addr c) 1) ->
    ExecF.evtF rsegs RNG
      (reac_ports_unknown_post ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p c lo bs)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_PORTS_UNKNOWN) fc None m (seg_rom rsegs)).

(* The old statement is the _F statement at the footprint that admits every access. *)
Lemma reac_ports_unknown_contract_of_F : reac_ports_unknown_contract_F -> reac_ports_unknown_contract.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p c lo bs Ha0 Ha1 ST HLO HP HC HCE HSW HAC HAP HW.
  pose proof (bv_unsigned_in_range 64 a0) as Rp. change (bv_modulus 64) with (2^64) in Rp. rewrite Ha0 in Rp.
  pose proof (bv_unsigned_in_range 64 a1) as Rc. change (bv_modulus 64) with (2^64) in Rc. rewrite Ha1 in Rc.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  unfold REAC_PORTS_UNKNOWN_FRAME in *.
  assert (RFR : ExecF.rng ExecF.RNG_all (bv_unsigned sp - 16) 16) by (apply ExecF.rng_all; lia).
  assert (RGOT : ExecF.rng ExecF.RNG_all GOT_CELL_K 8) by (apply ExecF.rng_all; unfold GOT_CELL_K; lia).
  assert (RCELL : ExecF.rng ExecF.RNG_all CELL_K 8) by (apply ExecF.rng_all; unfold CELL_K; lia).
  assert (RGP : p <> 0 -> ExecF.rng ExecF.RNG_all p 20 /\
                 ExecF.rng ExecF.RNG_all (shadow_addr p) (shadow_addr (p + 19) - shadow_addr p + 1)).
  { intros P0. destruct (HP P0) as (H20 & _ & _). split; apply ExecF.rng_all;
      unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia. }
  assert (RGC : c <> 0 -> ExecF.rng ExecF.RNG_all c 1 /\ ExecF.rng ExecF.RNG_all (shadow_addr c) 1).
  { intros C0. split; apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia. }
  exact (ExecF.evtF_evt rsegs ExecF.RNG_all _ _
           (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4
               t5 t6 F fc m p c lo bs Ha0 Ha1 ST HLO HP HC HCE HSW HAC HAP HW
               RFR RGOT RCELL RGP RGC)).
Qed.

(* ---- route (C): the region form (a Theorem Labs lane FORM RULE 09:37Z, POST FORM 09:38Z, ruling 09:58Z) ----
   Each declaration above that takes the universal A.AsanRT.shadow_rw m has an _on twin. The run READS no shadow
   byte through that premise: its ASan checks read the shadow bytes of p and c, but the proofs justify those reads
   from addressable m p 20 / addressable m c 1 and the runtime cells (reac_ports_unknown.v and
   reac_ports_unknownF.v: the first introduces HSW and clears it unused, the second proves the _on form, which has no such premise; a Theorem Labs lane via a Theorem Labs lane 09:58Z). So the _on twins DROP
   the premise (R = none). The post states no shadow_rw m', so the post is unchanged. The old statements are
   unchanged; each follows from its twin by forgetting shadow_rw m. The run calls no function, so no callee region
   enters. *)

Definition reac_ports_unknown_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p c lo : Z) (bs : list byte),
    bv_unsigned a0 = p ->
    bv_unsigned a1 = c ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_PORTS_UNKNOWN_FRAME <= bv_unsigned sp ->
    (p <> 0 -> p + 20 <= 2^64 /\ length bs = 20%nat /\ bytes_at rsegs m p bs /\
               (p + 20 <= bv_unsigned sp - REAC_PORTS_UNKNOWN_FRAME \/ bv_unsigned sp <= p)) ->
    (c <> 0 -> wr_at rsegs m c 1 /\ (p <> 0 -> c + 1 <= p \/ p + 20 <= c) /\
               (c + 1 <= bv_unsigned sp - REAC_PORTS_UNKNOWN_FRAME \/ bv_unsigned sp <= c)) ->
    asan_cells m ->
    (c <> 0 -> addressable m c 1) ->
    (p <> 0 -> addressable m p 20) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside (reac_ports_unknown_W (bv_unsigned sp) c) x) ->
    evt rsegs
      (fun ms' => exists (a2' a3' a4' a5' a6' a7' t0' t1' t2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if pu_ok p bs then 4 * pu_nunk bs 12 else -1))
                       a1 a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch (reac_ports_unknown_W (bv_unsigned sp) c) m m'
         /\ wmono rsegs m m'
         /\ stk rsegs m' lo (bv_unsigned sp)
         /\ (mem_inv rsegs m -> mem_inv rsegs m')
         /\ (c <> 0 -> bytes_at rsegs m' c [Z_to_bv 8 (if pu_ok p bs then pu_first bs 12 else 0)]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_PORTS_UNKNOWN) fc None m (seg_rom rsegs)).

(* The old statement from the region form: forget shadow_rw m. *)
Lemma reac_ports_unknown_contract_of_on : reac_ports_unknown_contract_on -> reac_ports_unknown_contract.
Proof.
  intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p c lo bs
    Ha0 Ha1 ST HLO HP HC HCE _.
  exact (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p c lo bs
    Ha0 Ha1 ST HLO HP HC HCE).
Qed.

Definition reac_ports_unknown_contract_F_on : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p c lo : Z) (bs : list byte),
    bv_unsigned a0 = p ->
    bv_unsigned a1 = c ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_PORTS_UNKNOWN_FRAME <= bv_unsigned sp ->
    (p <> 0 -> p + 20 <= 2^64 /\ length bs = 20%nat /\ bytes_at rsegs m p bs /\
               (p + 20 <= bv_unsigned sp - REAC_PORTS_UNKNOWN_FRAME \/ bv_unsigned sp <= p)) ->
    (c <> 0 -> wr_at rsegs m c 1 /\ (p <> 0 -> c + 1 <= p \/ p + 20 <= c) /\
               (c + 1 <= bv_unsigned sp - REAC_PORTS_UNKNOWN_FRAME \/ bv_unsigned sp <= c)) ->
    asan_cells m ->
    (c <> 0 -> addressable m c 1) ->
    (p <> 0 -> addressable m p 20) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside (reac_ports_unknown_W (bv_unsigned sp) c) x) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_PORTS_UNKNOWN_FRAME) REAC_PORTS_UNKNOWN_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (p <> 0 -> ExecF.rng RNG p 20 /\
               ExecF.rng RNG (shadow_addr p) (shadow_addr (p + 19) - shadow_addr p + 1)) ->
    (c <> 0 -> ExecF.rng RNG c 1 /\ ExecF.rng RNG (shadow_addr c) 1) ->
    ExecF.evtF rsegs RNG
      (reac_ports_unknown_post ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p c lo bs)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_PORTS_UNKNOWN) fc None m (seg_rom rsegs)).

(* The old footprint statement from the region form, as reac_ports_unknown_contract_of_on. *)
Lemma reac_ports_unknown_contract_F_of_on : reac_ports_unknown_contract_F_on -> reac_ports_unknown_contract_F.
Proof.
  intros H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p c
    lo bs Ha0 Ha1 ST HLO HP HC HCE _.
  exact (H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p c
    lo bs Ha0 Ha1 ST HLO HP HC HCE).
Qed.

(* reac_ports_unknown_contract_of_F between the region forms: the proof of reac_ports_unknown_contract_of_F above without HSW, a premise the _on form does not have (ruling a Theorem Labs lane 09:58Z: a lemma whose
   premise is a contract keeps its own proof, since contract does not give contract_on;
   reac_ports_unknown_contract_of_F above is byte-identical). *)
Lemma reac_ports_unknown_contract_on_of_F_on : reac_ports_unknown_contract_F_on -> reac_ports_unknown_contract_on.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p c lo bs Ha0 Ha1 ST HLO HP HC HCE HAC HAP HW.
  pose proof (bv_unsigned_in_range 64 a0) as Rp. change (bv_modulus 64) with (2^64) in Rp. rewrite Ha0 in Rp.
  pose proof (bv_unsigned_in_range 64 a1) as Rc. change (bv_modulus 64) with (2^64) in Rc. rewrite Ha1 in Rc.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  unfold REAC_PORTS_UNKNOWN_FRAME in *.
  assert (RFR : ExecF.rng ExecF.RNG_all (bv_unsigned sp - 16) 16) by (apply ExecF.rng_all; lia).
  assert (RGOT : ExecF.rng ExecF.RNG_all GOT_CELL_K 8) by (apply ExecF.rng_all; unfold GOT_CELL_K; lia).
  assert (RCELL : ExecF.rng ExecF.RNG_all CELL_K 8) by (apply ExecF.rng_all; unfold CELL_K; lia).
  assert (RGP : p <> 0 -> ExecF.rng ExecF.RNG_all p 20 /\
                 ExecF.rng ExecF.RNG_all (shadow_addr p) (shadow_addr (p + 19) - shadow_addr p + 1)).
  { intros P0. destruct (HP P0) as (H20 & _ & _). split; apply ExecF.rng_all;
      unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia. }
  assert (RGC : c <> 0 -> ExecF.rng ExecF.RNG_all c 1 /\ ExecF.rng ExecF.RNG_all (shadow_addr c) 1).
  { intros C0. split; apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia. }
  exact (ExecF.evtF_evt rsegs ExecF.RNG_all _ _
           (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4
               t5 t6 F fc m p c lo bs Ha0 Ha1 ST HLO HP HC HCE HAC HAP HW
               RFR RGOT RCELL RGP RGC)).
Qed.
