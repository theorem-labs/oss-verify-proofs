From Stdlib Require Import ZArith List.
From Stdlib Require Import Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOX_CATALOGUE : Z := 0x84dec.
Definition REAC_BOX_CATALOGUE_FRAME : Z := 16.
Definition BOX_CATALOGUE : Z := 0x9f620.

Definition reac_box_catalogue_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c lo : Z),
    a0 = Z_to_bv 64 c ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_BOX_CATALOGUE_FRAME <= bv_unsigned sp ->
    asan_cells m -> shadow_rw m ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_BOX_CATALOGUE_FRAME, bv_unsigned sp); (c, c + 8)] x) ->
    c = 0 \/ (c mod 8 = 0 /\ wr_at rsegs m c 8 /\
              (c + 8 <= bv_unsigned sp - REAC_BOX_CATALOGUE_FRAME \/ bv_unsigned sp <= c) /\
              addressable m c 8) ->
    evt rsegs
      (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BOX_CATALOGUE) a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_BOX_CATALOGUE_FRAME, bv_unsigned sp); (c, c + 8)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp) /\
         if c =? 0 then munch [(bv_unsigned sp - REAC_BOX_CATALOGUE_FRAME, bv_unsigned sp)] m m'
         else bytes_at rsegs m' c (le8 (Z_to_bv 64 11)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_CATALOGUE) fc None m (seg_rom rsegs)).

(* ---- the footprint form (RECIPE.md step 1 (a working note, not in this delivery)) ----
   The same run as an ExecF.evtF under any footprint RNG that holds every region the run reads or writes: the frame
   [sp - 16, sp), the two runtime cells GOT_CELL_K and CELL_K, and, when c is not 0, the 8 bytes at c and their
   shadow bytes ((x >> 3) + ASAN_K; c is 8-aligned, so the 8 bytes have ONE shadow byte).
   reac_box_catalogue_contract_of_F gives the old statement back with ExecF.RNG_all. *)
Definition reac_box_catalogue_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c lo : Z)
    : machine_state -> Prop :=
  fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BOX_CATALOGUE) a1' a2' a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - REAC_BOX_CATALOGUE_FRAME, bv_unsigned sp); (c, c + 8)] m m' /\
    wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp) /\
    (if c =? 0 then munch [(bv_unsigned sp - REAC_BOX_CATALOGUE_FRAME, bv_unsigned sp)] m m'
     else bytes_at rsegs m' c (le8 (Z_to_bv 64 11))).

Definition reac_box_catalogue_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c lo : Z),
    a0 = Z_to_bv 64 c ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_BOX_CATALOGUE_FRAME <= bv_unsigned sp ->
    asan_cells m -> shadow_rw m ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_BOX_CATALOGUE_FRAME, bv_unsigned sp); (c, c + 8)] x) ->
    c = 0 \/ (c mod 8 = 0 /\ wr_at rsegs m c 8 /\
              (c + 8 <= bv_unsigned sp - REAC_BOX_CATALOGUE_FRAME \/ bv_unsigned sp <= c) /\
              addressable m c 8) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_BOX_CATALOGUE_FRAME) REAC_BOX_CATALOGUE_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (c <> 0 -> ExecF.rng RNG c 8 /\
               ExecF.rng RNG (shadow_addr c) (shadow_addr (c + 7) - shadow_addr c + 1)) ->
    ExecF.evtF rsegs RNG
      (reac_box_catalogue_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         t3 t4 t5 t6 F fc m c lo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_CATALOGUE) fc None m (seg_rom rsegs)).

(* RECIPE step 1: the old statement as a corollary of the footprint form at ExecF.RNG_all, every rng premise by
   ExecF.rng_all (the 8 bytes at c and their shadow byte are inside the application memory by addressable).
   reac_box_catalogueF.v proves reac_box_catalogue_contract_F and derives reac_box_catalogue_contract from it. *)
Lemma reac_box_catalogue_contract_of_F : reac_box_catalogue_contract_F -> reac_box_catalogue_contract.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m c lo E0 ST HLO HCE HSW HW Hpre.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & ST1 & _).
  pose proof HLO as HLOz. unfold REAC_BOX_CATALOGUE_FRAME in HLOz.
  eapply ExecF.evtF_evt,
    (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
        F fc m c lo); try assumption.
  - apply ExecF.rng_all; unfold REAC_BOX_CATALOGUE_FRAME; lia.
  - apply ExecF.rng_all; unfold GOT_CELL_K; lia.
  - apply ExecF.rng_all; unfold CELL_K; lia.
  - intros Hc. destruct Hpre as [|(H8 & HWR & HD & HADR)]; [contradiction|].
    destruct HADR as (Ac0 & _ & Acn & _). unfold APPMEM_END in Acn.
    unfold shadow_addr, ASAN_K.
    split; apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
Qed.

(* ---- route (C): the region form (a Theorem Labs lane 09:20Z; form rule a Theorem Labs lane 09:37Z, 09:38Z; R amended 10:33Z) ----
   Image B twin of image A's block (A/Prog/reac_box_catalogue_c.v, a Theorem Labs lane d68c95046c8): the statements below are
   A's text, byte for byte; the names REAC_BOX_CATALOGUE / BOX_CATALOGUE are this file's image-B constants.
   R is the set of shadow bytes the run needs PRESENT through its shadow_rw premise (the bytes it reads AND the bytes
   it stores into). For this run R is EMPTY, so each _on statement is the old one with the premise shadow_rw m DROPPED
   (no fun _ => False region). Reads: when c is not 0 the run's one instrumented check reads the shadow byte of
   [c, c + 8) (shadow_addr c; c is 8-aligned), but that byte comes from the premise addressable m c 8 (B.AsanRT.addr_byte:
   mrd rsegs m (wa (shadow_addr a)) = Some b), not from shadow_rw: the image-B proofs reac_box_catalogue_holds_on
   (reac_box_catalogue.v) and reac_box_catalogue_F_holds_on (reac_box_catalogueF.v) never use the premise (the old
   proofs named it HSW in their intro patterns only). Stores: the run stores only its frame [sp - 16, sp) and the 8
   bytes at c, both outside the shadow (the premise forall x, ... in_shadow x -> outside [...] x, and app_mem by
   addressable): no shadow byte. No post names shadow_rw m', so nothing else changes. The old statements above stay
   byte-identical; each follows from its _on twin in one line. *)
Definition reac_box_catalogue_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c lo : Z),
    a0 = Z_to_bv 64 c ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_BOX_CATALOGUE_FRAME <= bv_unsigned sp ->
    asan_cells m ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_BOX_CATALOGUE_FRAME, bv_unsigned sp); (c, c + 8)] x) ->
    c = 0 \/ (c mod 8 = 0 /\ wr_at rsegs m c 8 /\
              (c + 8 <= bv_unsigned sp - REAC_BOX_CATALOGUE_FRAME \/ bv_unsigned sp <= c) /\
              addressable m c 8) ->
    evt rsegs
      (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BOX_CATALOGUE) a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_BOX_CATALOGUE_FRAME, bv_unsigned sp); (c, c + 8)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp) /\
         if c =? 0 then munch [(bv_unsigned sp - REAC_BOX_CATALOGUE_FRAME, bv_unsigned sp)] m m'
         else bytes_at rsegs m' c (le8 (Z_to_bv 64 11)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_CATALOGUE) fc None m (seg_rom rsegs)).

Lemma reac_box_catalogue_contract_of_on : reac_box_catalogue_contract_on -> reac_box_catalogue_contract.
Proof. intros H; red; intros; apply H; assumption. Qed.

Definition reac_box_catalogue_contract_F_on : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c lo : Z),
    a0 = Z_to_bv 64 c ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_BOX_CATALOGUE_FRAME <= bv_unsigned sp ->
    asan_cells m ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_BOX_CATALOGUE_FRAME, bv_unsigned sp); (c, c + 8)] x) ->
    c = 0 \/ (c mod 8 = 0 /\ wr_at rsegs m c 8 /\
              (c + 8 <= bv_unsigned sp - REAC_BOX_CATALOGUE_FRAME \/ bv_unsigned sp <= c) /\
              addressable m c 8) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_BOX_CATALOGUE_FRAME) REAC_BOX_CATALOGUE_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (c <> 0 -> ExecF.rng RNG c 8 /\
               ExecF.rng RNG (shadow_addr c) (shadow_addr (c + 7) - shadow_addr c + 1)) ->
    ExecF.evtF rsegs RNG
      (reac_box_catalogue_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         t3 t4 t5 t6 F fc m c lo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_CATALOGUE) fc None m (seg_rom rsegs)).

Lemma reac_box_catalogue_contract_F_of_on : reac_box_catalogue_contract_F_on -> reac_box_catalogue_contract_F.
Proof. intros H; red; intros; apply H; assumption. Qed.

(* reac_box_catalogue_contract_of_F's proof, re-run over the _on twins. reac_box_catalogue_contract_of_F above keeps
   its own proof: it cannot follow from this one, as its premise reac_box_catalogue_contract_F is weaker than
   reac_box_catalogue_contract_F_on. *)
Lemma reac_box_catalogue_contract_of_F_on : reac_box_catalogue_contract_F_on -> reac_box_catalogue_contract_on.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m c lo E0 ST HLO HCE HW Hpre.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & ST1 & _).
  pose proof HLO as HLOz. unfold REAC_BOX_CATALOGUE_FRAME in HLOz.
  eapply ExecF.evtF_evt,
    (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
        F fc m c lo); try assumption.
  - apply ExecF.rng_all; unfold REAC_BOX_CATALOGUE_FRAME; lia.
  - apply ExecF.rng_all; unfold GOT_CELL_K; lia.
  - apply ExecF.rng_all; unfold CELL_K; lia.
  - intros Hc. destruct Hpre as [|(H8 & HWR & HD & HADR)]; [contradiction|].
    destruct HADR as (Ac0 & _ & Acn & _). unfold APPMEM_END in Acn.
    unfold shadow_addr, ASAN_K.
    split; apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
Qed.
