From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
Import ListNotations.
Open Scope Z_scope.

(* joined_byte of the v1.9.0 harness (fuzz/fuzz_ctrl.c:251-254), image B (asan-ubsan fuzz_ctrl, the pin
   (internal path), sha256 12136677c5cf9891): [0x836ac, 0x8375c), 176 bytes.
   The frame is 16 bytes (`addi sp,sp,-16`); the function stores ra at sp - 8 and loads it back before `ret`. *)
Definition JOINED_BYTE : Z := 0x836ac.
Definition JOINED_BYTE_FRAME : Z := 16.

(* ja(p, q, nb, i): the address that joined_byte reads its result from. first->body[i] at p + 5 + i when
   i < nb, else last[9 + i - nb] at q + (9 + i - nb) (a Theorem Labs lane's joined_byte.md (a working note, not in this delivery)). *)
Definition jb_addr (p q nb i : Z) : Z := if i <? nb then p + 5 + i else q + (9 + i - nb).

(* Contract C1 of a Theorem Labs lane's joined_byte.md (a working note, not in this delivery; S1.1-S1.6 -> C1.1-C1.5) for image B. p = a0, q = a1, i = a2, nb = the byte at
   p + 4, b = the byte at ja(p, q, nb, i), S = sp at the entry.
   The UBSan checks T1-T5 trap with `unimp` at 0x8373c; S1.2-S1.6 make each check false.
   Image B adds (the form of lib/B/Prog/record_sum_closes_c.v and reac_ctrl_kind_name_c.v):
   - the frame: [S - 16, S) is stack memory (stk), and the two bytes that the function reads are apart from it;
   - the memory-checking runtime: its cells (asan_cells: the GOT cell at GOT_CELL_K holds CELL_K, and CELL_K holds
     the shadow offset ASAN_K) and the shadow map (shadow_rw) are present, and they are apart from [S - 16, S);
   - the byte at p + 4 and the byte at ja are addressable. Before each of the two loads the code loads the shadow
     byte k at (a >> 3) + ASAN_K and goes on when k = 0 or (a mod 8) < k; the error path (the call of
     __asan_report_load1 at 0x5927c) is not reached.
   Result: the run reaches ret_pc ra with a0 = b zero-extended (C1.2); sp, ra, gp, tp, t0-t6, s0-s11, a7, the float
   registers and fcsr keep their values; only a1-a6 can change (C1.1). Memory changes only in [S - 16, S) (the 8
   bytes of ra at S - 8), every writable byte stays writable, mem_inv is kept and [lo, S) stays stack memory
   (C1.3). *)
Definition joined_byte_contract : Prop :=
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
    asan_cells m -> shadow_rw m ->
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
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 JOINED_BYTE) fc None m (seg_rom rsegs)).

(* Footprint form (RECIPE.md step 1 (a working note, not in this delivery)): the same run as an ExecF.evtF under a footprint RNG. The premises of
   joined_byte_contract are unchanged and in order; then one rng premise per region the run reads or writes: the
   16-byte frame [S - 16, S) (the store and the reload of ra at S - 8), the GOT cell GOT_CELL_K and the runtime cell
   CELL_K of the shadow offset (two 8-byte loads), the byte nb at p + 4 and the byte b at ja (two 1-byte loads), and
   the shadow byte of each of these two bytes (the function checks each with one single-byte `lb` load at
   (a >> 3) + ASAN_K = shadow_addr a, so the cover is byte-exact). The data premises of the two bytes carry no guard,
   so their rng premises carry none. joined_byte calls no function, so no rng_bytes premise. RNG binds first. *)
From Stdlib Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.

Definition joined_byte_contract_F : Prop :=
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
    asan_cells m -> shadow_rw m ->
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
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 JOINED_BYTE) fc None m (seg_rom rsegs)).

(* The old contract as a corollary: evtF_evt of the footprint form at RNG_all, each rng premise by rng_all (the
   bounds come from stk, bytes_at and addressable). *)
Lemma joined_byte_contract_of_F : joined_byte_contract_F -> joined_byte_contract.
Proof.
  unfold joined_byte_contract_F, joined_byte_contract. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo i nb b
    Hi Ha2 Hal HN Hq HB ST HLO DN DB HCE HSW HAN HAB HW.
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
