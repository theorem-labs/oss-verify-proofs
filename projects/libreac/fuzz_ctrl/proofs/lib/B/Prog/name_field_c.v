From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcBox.
Import ListNotations.
Open Scope Z_scope.

Definition NAME_FIELD : Z := 0x879e4.
(* K = 32 + K(__asan_memset) 2208 (contracts/libreac/name_field@reac_box_synth.md Names). *)
Definition NAME_FIELD_K : Z := 2240.

(* The ubsan contract (lib/U/Prog/name_field_c.v) with the window K of this build and the premises of the asan-ubsan
   build (S1.2 and S1.7 of the English contract): the runtime's cells and shadow; the 8 bytes at m + 280, the name
   bytes and the 16 bytes at N addressable; N + 16 in AppMem and the 16 bytes apart from [RT_LO, RT_HI); the window in
   AppMem above the shadow (the premises of __asan_memset at the zero fill of the 16 bytes at N). *)
Definition name_field_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (name : word) (nb junk : list byte),
    stk rsegs m (bv_unsigned sp - NAME_FIELD_K) (bv_unsigned sp) ->
    bv_unsigned a0 <> 0 -> bv_unsigned a0 mod 8 = 0 -> bv_unsigned a0 + 288 <= 2^64 ->
    bytes_at rsegs m (bv_unsigned a0 + 280) (le8 name) ->
    bv_unsigned a1 + 16 <= 2^64 ->
    rw_cells rsegs m (bv_unsigned a1) [CB 16 junk] ->
    (bv_unsigned name = 0 /\ nb = [] \/
     bv_unsigned name <> 0 /\ name_ok nb /\ bv_unsigned name + Z.of_nat (length nb) <= 2^64 /\
     bytes_at rsegs m (bv_unsigned name) nb) ->
    (bv_unsigned sp <= bv_unsigned a0 + 280 \/ bv_unsigned a0 + 288 <= bv_unsigned sp - NAME_FIELD_K) ->
    (bv_unsigned sp <= bv_unsigned name \/
     bv_unsigned name + Z.of_nat (length nb) <= bv_unsigned sp - NAME_FIELD_K) ->
    (bv_unsigned sp <= bv_unsigned a1 \/ bv_unsigned a1 + 16 <= bv_unsigned sp - NAME_FIELD_K) ->
    (bv_unsigned a1 + 16 <= bv_unsigned a0 + 280 \/ bv_unsigned a0 + 288 <= bv_unsigned a1) ->
    (bv_unsigned a1 + 16 <= bv_unsigned name \/ bv_unsigned name + Z.of_nat (length nb) <= bv_unsigned a1) ->
    mem_inv rsegs m ->
    (* asan-ubsan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - NAME_FIELD_K -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned a0 + 280) 8 ->
    addressable m (bv_unsigned name) (Z.of_nat (length nb)) ->
    addressable m (bv_unsigned a1) 16 -> app_mem (bv_unsigned a1 + 16) ->
    (bv_unsigned a1 + 16 <= RT_LO \/ RT_HI <= bv_unsigned a1) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ bytes_at rsegs m' (bv_unsigned a1) (nmf nb)
         /\ munch [(bv_unsigned sp - NAME_FIELD_K, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 16)] m m'
         /\ wmono rsegs m m'
         /\ mem_inv rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - NAME_FIELD_K) (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 NAME_FIELD) fc None m (seg_rom rsegs)).

(* Footprint form (image B; the twin the fuzz_ctrl ASan port's kit bridge evtF_to_SRr lifts): the same run as an
   ExecF.evtF under a footprint RNG (RNG binds first). The premises of name_field_contract, unchanged and in order,
   then the footprint premises of the run and of its one callee __asan_memset, whose footprint form is a Theorem Labs lane's
   asan_memset_contract_F (lib/B/Prog/asan_memset_cF.v, from a working branch 9869f1d1f86):
   - RngBytes.rng_bytes RNG: that callee form carries it (the footprint is decided byte by byte);
   - the image [IMG_LO, IMG_HI) of lib/B/Prog/ImgBounds.v: the GOT cell and the cell of the shadow offset (the
     function's two loads of the shadow base), and __asan_memset's reads of the image and of the runtime words
     [RT_LO, RT_HI), which lie inside it;
   - the window K: the 32-byte frame and __asan_memset's window [sp - 32 - ASAN_MEMSET_K, sp - 32) below it;
   - the 8-aligned shadow word cover of __asan_memset's window [sp - NAME_FIELD_K, sp - 32) (the callee may read
     the shadow of its own frame);
   - the 8 bytes at m + 280 (the load of the name pointer) and their one shadow byte (m + 280 is 8-aligned; the
     function's own lbu check of the 8-byte load);
   - when name <> 0 (the guard of the name bytes' data premise): the name bytes and their byte-exact shadow span
     [shadow_addr name, shadow_addr (name + |nb| - 1)] (the function's own lbu check of each 1-byte load);
   - the 16 bytes at N (the zero fill and the copy) and the 8-aligned shadow word cover of [N, N + 16) (__asan_memset's
     quick check loads whole aligned shadow words; the function's lbu checks of the 1-byte stores at N + i fall
     inside it).
   Data accesses only: step_accesses lists no instruction fetch. name_field_contract_of_F re-derives
   name_field_contract from this form at ExecF.RNG_all. *)
From Stdlib Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import ImgBounds.

Definition name_field_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (name : word) (nb junk : list byte),
    stk rsegs m (bv_unsigned sp - NAME_FIELD_K) (bv_unsigned sp) ->
    bv_unsigned a0 <> 0 -> bv_unsigned a0 mod 8 = 0 -> bv_unsigned a0 + 288 <= 2^64 ->
    bytes_at rsegs m (bv_unsigned a0 + 280) (le8 name) ->
    bv_unsigned a1 + 16 <= 2^64 ->
    rw_cells rsegs m (bv_unsigned a1) [CB 16 junk] ->
    (bv_unsigned name = 0 /\ nb = [] \/
     bv_unsigned name <> 0 /\ name_ok nb /\ bv_unsigned name + Z.of_nat (length nb) <= 2^64 /\
     bytes_at rsegs m (bv_unsigned name) nb) ->
    (bv_unsigned sp <= bv_unsigned a0 + 280 \/ bv_unsigned a0 + 288 <= bv_unsigned sp - NAME_FIELD_K) ->
    (bv_unsigned sp <= bv_unsigned name \/
     bv_unsigned name + Z.of_nat (length nb) <= bv_unsigned sp - NAME_FIELD_K) ->
    (bv_unsigned sp <= bv_unsigned a1 \/ bv_unsigned a1 + 16 <= bv_unsigned sp - NAME_FIELD_K) ->
    (bv_unsigned a1 + 16 <= bv_unsigned a0 + 280 \/ bv_unsigned a0 + 288 <= bv_unsigned a1) ->
    (bv_unsigned a1 + 16 <= bv_unsigned name \/ bv_unsigned name + Z.of_nat (length nb) <= bv_unsigned a1) ->
    mem_inv rsegs m ->
    (* asan-ubsan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - NAME_FIELD_K -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned a0 + 280) 8 ->
    addressable m (bv_unsigned name) (Z.of_nat (length nb)) ->
    addressable m (bv_unsigned a1) 16 -> app_mem (bv_unsigned a1 + 16) ->
    (bv_unsigned a1 + 16 <= RT_LO \/ RT_HI <= bv_unsigned a1) ->
    (* footprint *)
    RngBytes.rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (bv_unsigned sp - NAME_FIELD_K) NAME_FIELD_K ->
    ExecF.rng RNG (shadow_addr (bv_unsigned sp - NAME_FIELD_K) / 8 * 8)
      (shadow_addr (bv_unsigned sp - 32 - 1) / 8 * 8 + 8 - shadow_addr (bv_unsigned sp - NAME_FIELD_K) / 8 * 8) ->
    ExecF.rng RNG (bv_unsigned a0 + 280) 8 ->
    ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 280)) 1 ->
    (bv_unsigned name <> 0 -> ExecF.rng RNG (bv_unsigned name) (Z.of_nat (length nb))) ->
    (bv_unsigned name <> 0 ->
     ExecF.rng RNG (shadow_addr (bv_unsigned name))
       (shadow_addr (bv_unsigned name + Z.of_nat (length nb) - 1) - shadow_addr (bv_unsigned name) + 1)) ->
    ExecF.rng RNG (bv_unsigned a1) 16 ->
    ExecF.rng RNG (shadow_addr (bv_unsigned a1) / 8 * 8)
      (shadow_addr (bv_unsigned a1 + 16 - 1) / 8 * 8 + 8 - shadow_addr (bv_unsigned a1) / 8 * 8) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ bytes_at rsegs m' (bv_unsigned a1) (nmf nb)
         /\ munch [(bv_unsigned sp - NAME_FIELD_K, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 16)] m m'
         /\ wmono rsegs m m'
         /\ mem_inv rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - NAME_FIELD_K) (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 NAME_FIELD) fc None m (seg_rom rsegs)).

(* The plain contract is the footprint form at ExecF.RNG_all (rng_bytes holds of it outright; every rng premise by
   ExecF.rng_all). *)
Lemma name_field_contract_of_F : name_field_contract_F -> name_field_contract.
Proof.
  unfold name_field_contract_F, name_field_contract. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    name nb junk HST HA0 HA8 HA HNM HA1 HRW HN S0 SN S1 D0 DN HMI HC HSR HLO HHI AD0 ADN AD1 HAM HRT.
  pose proof AD0 as (P0 & _ & E0 & _). pose proof ADN as (PN & _ & EN & _). pose proof AD1 as (P1 & _ & E1 & _).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m name nb junk HST HA0 HA8 HA HNM HA1 HRW HN S0 SN S1 D0 DN HMI HC HSR HLO HHI AD0 ADN AD1 HAM HRT);
    clear HF;
    first
      [ intros ? ? _ _ _; exact I
      | try intros _; apply ExecF.rng_all;
        unfold IMG_LO, IMG_HI, HIGHMEM_BEG, APPMEM_END, NAME_FIELD_K, shadow_addr, ASAN_K in *;
        first [ lia | Z.div_mod_to_equations; lia ] ].
Qed.
