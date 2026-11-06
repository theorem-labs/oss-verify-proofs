(* lib/B/Prog/joined_byte_c_on.v -- route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane, form of ASSIGN.md (a working note, not in this delivery)): the _on
   forms of image B's joined_byte (entry 0x836ac; lib/B/Prog/joined_byte_c.v).  joined_byte_c.v and joined_byteF.v are
   FROZEN (a Theorem Labs lane FROZEN-INTERFACES.md:37 (a working note, not in this delivery), B footprint twins), so by ASSIGN.md:79 (a working note, not in this delivery) the twins are in this separate file
   and the frozen files stay identical outside comments.  Writer: a Theorem Labs lane.  rule 24: no function proved.

   PRE.  The run needs NO shadow byte through its shadow_rw premise: its two shadow loads (shadow_addr (a0 + 4) and
   shadow_addr ja) are read through `addressable` (rt_shadow_rd, in jbF_shadow), and joined_byte_holds_F introduces the
   premise as HSW and clears it unused (joined_byteF.v:165, :181 at 6c3b15fd429; the plain proof the same,
   joined_byte.v:135, :150).  Its one store is ra at S - 8, inside the frame, which the premise at :48-49 keeps apart
   from the shadow, so it stores no shadow byte.  By the form's rule "no read: premise dropped" (ASSIGN.md:9-10 and
   the amendment :74), the _on forms are the contracts WITHOUT `shadow_rw m ->`.

   POST.  The form (ASSIGN.md:11) rewrites a post `shadow_rw m'`; joined_byte's post states no shadow fact, and the
   form is silent on that case.  The image-B stage W4c (seg_F16, runs 2 and 3, which call joined_byte) needs the shadow
   kept across the call, so the _on posts add ONE conjunct, last, in the wave's form
   `forall P, shadow_rw_on P m -> shadow_rw_on P m'` (it follows from the munch of the frame, wmono and the frame being
   apart from the shadow: the argument of B.ShadowRwOnT.fl_shadow_rw_on).  Every other premise and conjunct is
   joined_byte_c.v's text, in order.  The old statements follow by dropping the conjunct (joined_byte_contract_of_on,
   joined_byte_contract_F_of_F_on); the proofs are in joined_byteF_on.v. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import joined_byte_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

Definition joined_byte_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo i : Z) (nb b : byte),
    (i = 9 \/ i = 10) -> a2 = Z_to_bv 64 i ->                                          (* S1.2 *)
    bv_unsigned a0 mod 4 = 0 ->                                                        (* S1.3 *)
    bytes_at rsegs m (bv_unsigned a0 + 4) [nb] ->                                      (* S1.4 *)
    (bv_unsigned nb <= i -> bv_unsigned a1 <> 0) ->                                    (* S1.6: q <> 0 *)
    bytes_at rsegs m (jb_addr (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned nb) i) [b] -> (* S1.5, S1.6 *)
    stk rsegs m lo (bv_unsigned sp) -> lo + JOINED_BYTE_FRAME <= bv_unsigned sp ->
    (bv_unsigned a0 + 5 <= bv_unsigned sp - JOINED_BYTE_FRAME \/ bv_unsigned sp <= bv_unsigned a0 + 4) ->
    (jb_addr (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned nb) i + 1 <= bv_unsigned sp - JOINED_BYTE_FRAME \/
     bv_unsigned sp <= jb_addr (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned nb) i) ->
    (* asan-ubsan *)
    asan_cells m ->
    addressable m (bv_unsigned a0 + 4) 1 ->
    addressable m (jb_addr (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned nb) i) 1 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - JOINED_BYTE_FRAME, bv_unsigned sp)] x) ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (zxb b) a1' a2' a3' a4' a5' a6' a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - JOINED_BYTE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp) /\
         (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 JOINED_BYTE) fc None m (seg_rom rsegs)).

Definition joined_byte_contract_F_on : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo i : Z) (nb b : byte),
    (i = 9 \/ i = 10) -> a2 = Z_to_bv 64 i ->                                          (* S1.2 *)
    bv_unsigned a0 mod 4 = 0 ->                                                        (* S1.3 *)
    bytes_at rsegs m (bv_unsigned a0 + 4) [nb] ->                                      (* S1.4 *)
    (bv_unsigned nb <= i -> bv_unsigned a1 <> 0) ->                                    (* S1.6: q <> 0 *)
    bytes_at rsegs m (jb_addr (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned nb) i) [b] -> (* S1.5, S1.6 *)
    stk rsegs m lo (bv_unsigned sp) -> lo + JOINED_BYTE_FRAME <= bv_unsigned sp ->
    (bv_unsigned a0 + 5 <= bv_unsigned sp - JOINED_BYTE_FRAME \/ bv_unsigned sp <= bv_unsigned a0 + 4) ->
    (jb_addr (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned nb) i + 1 <= bv_unsigned sp - JOINED_BYTE_FRAME \/
     bv_unsigned sp <= jb_addr (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned nb) i) ->
    (* asan-ubsan *)
    asan_cells m ->
    addressable m (bv_unsigned a0 + 4) 1 ->
    addressable m (jb_addr (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned nb) i) 1 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - JOINED_BYTE_FRAME, bv_unsigned sp)] x) ->
    (* footprint *)
    rng RNG (bv_unsigned sp - JOINED_BYTE_FRAME) JOINED_BYTE_FRAME ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    rng RNG (bv_unsigned a0 + 4) 1 ->
    rng RNG (jb_addr (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned nb) i) 1 ->
    rng RNG (shadow_addr (bv_unsigned a0 + 4)) 1 ->
    rng RNG (shadow_addr (jb_addr (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned nb) i)) 1 ->
    evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (zxb b) a1' a2' a3' a4' a5' a6' a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - JOINED_BYTE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp) /\
         (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 JOINED_BYTE) fc None m (seg_rom rsegs)).

(* The old statements are the _on ones with the unused premise added and the post's last conjunct dropped. *)
Lemma joined_byte_contract_of_on : joined_byte_contract_on -> joined_byte_contract.
Proof.
  intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo i nb b
    Hi Ha2 Hal HN Hq HB ST HLO DN DB HCE _ HAN HAB HW.
  eapply evt_mono;
    [exact (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo i nb b
              Hi Ha2 Hal HN Hq HB ST HLO DN DB HCE HAN HAB HW)|].
  intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & m' & E & MU & WM & MI & ST' & _).
  exists a1', a2', a3', a4', a5', a6', m'. exact (conj E (conj MU (conj WM (conj MI ST')))).
Qed.

Lemma joined_byte_contract_F_of_F_on : joined_byte_contract_F_on -> joined_byte_contract_F.
Proof.
  intros H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo i nb b Hi Ha2 Hal HN Hq HB ST HLO DN DB HCE _ HAN HAB HW RFR RGOT RCELL RN RB RSN RSB.
  eapply evtF_mono;
    [exact (H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              lo i nb b Hi Ha2 Hal HN Hq HB ST HLO DN DB HCE HAN HAB HW RFR RGOT RCELL RN RB RSN RSB)|].
  intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & m' & E & MU & WM & MI & ST' & _).
  exists a1', a2', a3', a4', a5', a6', m'. exact (conj E (conj MU (conj WM (conj MI ST')))).
Qed.

(* The _on statement is the _F_on statement at the footprint that allows every access (as joined_byte_contract_of_F,
   without the shadow_rw premise). *)
Lemma joined_byte_contract_on_of_F_on : joined_byte_contract_F_on -> joined_byte_contract_on.
Proof.
  unfold joined_byte_contract_F_on, joined_byte_contract_on. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo i nb b
    Hi Ha2 Hal HN Hq HB ST HLO DN DB HCE HAN HAB HW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  pose proof HN as (HN0 & HN1 & _). pose proof HB as (HB0 & HB1 & _).
  change (Z.of_nat (length [nb])) with 1 in HN1. change (Z.of_nat (length [b])) with 1 in HB1.
  pose proof HAN as (_ & _ & HAN1 & _). pose proof HAB as (_ & _ & HAB1 & _).
  apply (evtF_evt rsegs RNG_all).
  apply (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m lo i nb b); try assumption; apply rng_all;
    unfold shadow_addr, GOT_CELL_K, CELL_K, ASAN_K, APPMEM_END, JOINED_BYTE_FRAME in *;
    Z.div_mod_to_equations; lia.
Qed.
