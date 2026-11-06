From Stdlib Require Import ZArith List.
From Stdlib Require Import Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLeaf.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_PORTS_PARSE : Z := 0x883d0.
Definition REAC_PORTS_PARSE_FRAME : Z := 16.

Definition reac_ports_parse_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p q : Z) (bs : list byte)
    : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' t3' t4' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if ports_ok p q bs then 0 else -1))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp) /\
    if ports_ok p q bs
    then bytes_at rsegs m' q (le4 (Z_to_bv 64 (4 * n_in bs))) /\
         bytes_at rsegs m' (q + 4) (le4 (Z_to_bv 64 (4 * n_out bs))) /\
         bytes_at rsegs m' (q + 8) (le4 (Z_to_bv 64 (16 * bt bs 7))) /\
         munch [(bv_unsigned sp - REAC_PORTS_PARSE_FRAME, bv_unsigned sp); (q, q + 12)] m m'
    else munch [(bv_unsigned sp - REAC_PORTS_PARSE_FRAME, bv_unsigned sp)] m m'.

Definition reac_ports_parse_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p q lo : Z) (bs : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q ->
    0 <= p < 2^64 -> 0 <= q < 2^64 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_PORTS_PARSE_FRAME <= bv_unsigned sp ->
    (p <> 0 -> q <> 0 -> length bs = 20%nat /\ bytes_at rsegs m p bs) ->
    (p <> 0 -> q <> 0 -> q mod 4 = 0 /\ wr_at rsegs m q 12 /\ (q + 12 <= p \/ p + 20 <= q) /\
       (p + 20 <= bv_unsigned sp - REAC_PORTS_PARSE_FRAME \/ bv_unsigned sp <= p) /\
       (q + 12 <= bv_unsigned sp - REAC_PORTS_PARSE_FRAME \/ bv_unsigned sp <= q)) ->
    (p <> 0 -> q <> 0 -> asan_cells m /\ shadow_rw m /\ addressable m p 20 /\ addressable m q 12) ->
    (p <> 0 -> q <> 0 ->
       forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_PORTS_PARSE_FRAME, bv_unsigned sp); (q, q + 12)] x) ->
    evt rsegs
      (reac_ports_parse_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m lo p q bs)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_PORTS_PARSE) fc None m (seg_rom rsegs)).

(* ---- the footprint form (RECIPE.md step 1 (a working note, not in this delivery)) ----
   The same run as an ExecF.evtF under any footprint RNG that holds every region the run reads or writes: the frame
   [sp - 16, sp), and, when p and q are not 0, the two runtime cells GOT_CELL_K and CELL_K (8 bytes each), the 20
   bytes at p, the 12 bytes at q and the shadow bytes of each ((x >> 3) + ASAN_K, unaligned form of RECIPE step 1).
   reac_ports_parse_contract_of_F gives the old statement back with ExecF.RNG_all. *)
Definition reac_ports_parse_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p q lo : Z) (bs : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q ->
    0 <= p < 2^64 -> 0 <= q < 2^64 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_PORTS_PARSE_FRAME <= bv_unsigned sp ->
    (p <> 0 -> q <> 0 -> length bs = 20%nat /\ bytes_at rsegs m p bs) ->
    (p <> 0 -> q <> 0 -> q mod 4 = 0 /\ wr_at rsegs m q 12 /\ (q + 12 <= p \/ p + 20 <= q) /\
       (p + 20 <= bv_unsigned sp - REAC_PORTS_PARSE_FRAME \/ bv_unsigned sp <= p) /\
       (q + 12 <= bv_unsigned sp - REAC_PORTS_PARSE_FRAME \/ bv_unsigned sp <= q)) ->
    (p <> 0 -> q <> 0 -> asan_cells m /\ shadow_rw m /\ addressable m p 20 /\ addressable m q 12) ->
    (p <> 0 -> q <> 0 ->
       forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_PORTS_PARSE_FRAME, bv_unsigned sp); (q, q + 12)] x) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_PORTS_PARSE_FRAME) REAC_PORTS_PARSE_FRAME ->
    (p <> 0 -> q <> 0 ->
       ExecF.rng RNG GOT_CELL_K 8 /\ ExecF.rng RNG CELL_K 8 /\
       ExecF.rng RNG p 20 /\ ExecF.rng RNG (shadow_addr p) (shadow_addr (p + 19) - shadow_addr p + 1) /\
       ExecF.rng RNG q 12 /\ ExecF.rng RNG (shadow_addr q) (shadow_addr (q + 11) - shadow_addr q + 1)) ->
    ExecF.evtF rsegs RNG
      (reac_ports_parse_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m lo p q bs)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_PORTS_PARSE) fc None m (seg_rom rsegs)).

(* RECIPE step 1: the old statement as a corollary of the footprint form at ExecF.RNG_all, every rng premise by
   ExecF.rng_all (the p and q ranges and their shadow bytes are inside the application memory by addressable).
   reac_ports_parseF.v proves reac_ports_parse_contract_F and derives reac_ports_parse_contract from it. *)
Lemma reac_ports_parse_contract_of_F : reac_ports_parse_contract_F -> reac_ports_parse_contract.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p q lo bs E0 E1 Hp Hq ST HLO HR HWR HAS HWS.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & ST1 & _).
  eapply ExecF.evtF_evt,
    (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
        F fc m p q lo bs); try assumption.
  - apply ExecF.rng_all; lia.
  - intros P0 Q0. destruct (HAS P0 Q0) as (_ & _ & HADRp & HADRq).
    destruct HADRp as (Ap0 & _ & Apn & _). destruct HADRq as (Aq0 & _ & Aqn & _).
    unfold APPMEM_END in Apn, Aqn. unfold shadow_addr, ASAN_K, GOT_CELL_K, CELL_K.
    do 5 (split; [apply ExecF.rng_all; try Z.div_mod_to_equations; lia|]).
    apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
Qed.

(* Route (C), a Theorem Labs lane 11:17Z: the run reads no shadow byte through shadow_rw (its p / q shadow reads come from
   addressable; the F proof, reac_ports_parse_F_holds_on, has no shadow_rw component), so the _on forms DROP the `shadow_rw m`
   conjunct of the guarded premise, keeping asan_cells and the two addressable. Twin of image A's reac_ports_parse
   (d4f70537e6f). The old statements follow by supplying shadow_rw back. *)
Definition reac_ports_parse_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p q lo : Z) (bs : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q ->
    0 <= p < 2^64 -> 0 <= q < 2^64 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_PORTS_PARSE_FRAME <= bv_unsigned sp ->
    (p <> 0 -> q <> 0 -> length bs = 20%nat /\ bytes_at rsegs m p bs) ->
    (p <> 0 -> q <> 0 -> q mod 4 = 0 /\ wr_at rsegs m q 12 /\ (q + 12 <= p \/ p + 20 <= q) /\
       (p + 20 <= bv_unsigned sp - REAC_PORTS_PARSE_FRAME \/ bv_unsigned sp <= p) /\
       (q + 12 <= bv_unsigned sp - REAC_PORTS_PARSE_FRAME \/ bv_unsigned sp <= q)) ->
    (p <> 0 -> q <> 0 -> asan_cells m /\ addressable m p 20 /\ addressable m q 12) ->
    (p <> 0 -> q <> 0 ->
       forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_PORTS_PARSE_FRAME, bv_unsigned sp); (q, q + 12)] x) ->
    evt rsegs
      (reac_ports_parse_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m lo p q bs)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_PORTS_PARSE) fc None m (seg_rom rsegs)).

Lemma reac_ports_parse_contract_of_on : reac_ports_parse_contract_on -> reac_ports_parse_contract.
Proof.
  intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q lo bs
    E0 E1 Hp Hq ST HLO HR HWR HAS HWS.
  apply H; try assumption.
  intros P0 Q0. destruct (HAS P0 Q0) as (HCE & _ & HAD). exact (conj HCE HAD).
Qed.

Definition reac_ports_parse_contract_F_on : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p q lo : Z) (bs : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q ->
    0 <= p < 2^64 -> 0 <= q < 2^64 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_PORTS_PARSE_FRAME <= bv_unsigned sp ->
    (p <> 0 -> q <> 0 -> length bs = 20%nat /\ bytes_at rsegs m p bs) ->
    (p <> 0 -> q <> 0 -> q mod 4 = 0 /\ wr_at rsegs m q 12 /\ (q + 12 <= p \/ p + 20 <= q) /\
       (p + 20 <= bv_unsigned sp - REAC_PORTS_PARSE_FRAME \/ bv_unsigned sp <= p) /\
       (q + 12 <= bv_unsigned sp - REAC_PORTS_PARSE_FRAME \/ bv_unsigned sp <= q)) ->
    (p <> 0 -> q <> 0 -> asan_cells m /\ addressable m p 20 /\ addressable m q 12) ->
    (p <> 0 -> q <> 0 ->
       forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_PORTS_PARSE_FRAME, bv_unsigned sp); (q, q + 12)] x) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_PORTS_PARSE_FRAME) REAC_PORTS_PARSE_FRAME ->
    (p <> 0 -> q <> 0 ->
       ExecF.rng RNG GOT_CELL_K 8 /\ ExecF.rng RNG CELL_K 8 /\
       ExecF.rng RNG p 20 /\ ExecF.rng RNG (shadow_addr p) (shadow_addr (p + 19) - shadow_addr p + 1) /\
       ExecF.rng RNG q 12 /\ ExecF.rng RNG (shadow_addr q) (shadow_addr (q + 11) - shadow_addr q + 1)) ->
    ExecF.evtF rsegs RNG
      (reac_ports_parse_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m lo p q bs)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_PORTS_PARSE) fc None m (seg_rom rsegs)).

Lemma reac_ports_parse_contract_F_of_on : reac_ports_parse_contract_F_on -> reac_ports_parse_contract_F.
Proof.
  intros H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q lo bs
    E0 E1 Hp Hq ST HLO HR HWR HAS HWS RFR RRG.
  apply H; try assumption.
  intros P0 Q0. destruct (HAS P0 Q0) as (HCE & _ & HAD). exact (conj HCE HAD).
Qed.

(* The plain _on from the footprint _on, the _on analog of reac_ports_parse_contract_of_F. *)
Lemma reac_ports_parse_contract_on_of_F_on : reac_ports_parse_contract_F_on -> reac_ports_parse_contract_on.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p q lo bs E0 E1 Hp Hq ST HLO HR HWR HAS HWS.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & ST1 & _).
  eapply ExecF.evtF_evt,
    (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
        F fc m p q lo bs); try assumption.
  - apply ExecF.rng_all; lia.
  - intros P0 Q0. destruct (HAS P0 Q0) as (_ & HADRp & HADRq).
    destruct HADRp as (Ap0 & _ & Apn & _). destruct HADRq as (Aq0 & _ & Aqn & _).
    unfold APPMEM_END in Apn, Aqn. unfold shadow_addr, ASAN_K, GOT_CELL_K, CELL_K.
    do 5 (split; [apply ExecF.rng_all; try Z.div_mod_to_equations; lia|]).
    apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
Qed.
