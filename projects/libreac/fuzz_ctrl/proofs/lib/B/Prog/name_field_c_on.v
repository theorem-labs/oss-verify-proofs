(* lib/B/Prog/name_field_c_on.v -- route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane): the ADDITIVE `_on` STATEMENTS of
   name_field_c.v (LEAF: it Requires only what name_field_c.v Requires, plus name_field_c, B.ShadowRwOn and
   B.Prog.sh_word_on). name_field_c.v stays identical apart from comments. The proof is lib/B/Prog/name_fieldF_on.v,
   name_field_holds_F_on. rule 24: no function proved.

   The binders, the premises (the footprint ones included) and the post are those of name_field_contract /
   name_field_contract_F, with ONE change each way:
     - the universal premise `shadow_rw m` becomes `shadow_rw_on (name_field_shadow_R (bv_unsigned a1)) m`;
     - the post's `shadow_rw m'` becomes `forall P, shadow_rw_on P m -> shadow_rw_on P m'` (the wave's post form,
       a Theorem Labs lane 09:38Z): every shadow region the caller holds before the call it holds after it.
   R, MEASURED on name_field_holds_F (name_fieldF.v): the proof uses its shadow_rw premise at two places only.
     - name_fieldF.v:380 (HSW) -> :410 shadow_rw_kept carries it to the memory of the call, -> :439 it closes the
       shadow premise of __asan_memset(N, 0, 16). In the callee's _on form (asan_memset_cF_on.v) that premise is
       shadow_rw_on (asan_memset_shadow_R N 16), that is sh_word_on N 16: the aligned 8-byte shadow words of
       [N, N + 16), which the callee's check READS. N is the register a1 of name_field (mv s0,a1; mv a0,s0).
     - name_fieldF.v:94 (HSW, Section NFF) -> :162 nfF_cells (shadow_rw_kept) -> :175, :180 the post's shadow_rw m'.
       This reads and stores no byte: it is the post's transport, which the forall-P post form replaces
       (ShadowRwOnT.shadow_rw_on_kept from munch W0 and wmono, no premise needed).
   The callee's post fact on the shadow (name_fieldF.v:453, HSW2) is never used. The function's own shadow loads (the
   lbu checks of the 8 bytes at m + 280, of the name bytes and of the stores at N + i: name_fieldF.v:331, :347, :297,
   :465) take their shadow byte from the addressable premises (AsanRT.addr_byte through name_field.v's nf_sh8 and
   nf_sh), not from shadow_rw. The run stores no shadow byte: the post's munch is the window [sp - K, sp) and
   [N, N + 16), all in AppMem (name_field.v nf_aw). So R = sh_word_on N 16, the reads of the one callee. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcBox.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import name_field_c sh_word_on.
Import ListNotations.
Open Scope Z_scope.

(* The shadow bytes the run needs present through its shadow premise: the aligned shadow words of the 16 bytes at N,
   which __asan_memset(N, 0, 16) reads. *)
Definition name_field_shadow_R (N : Z) (a : Z) : Prop := sh_word_on N 16 a.

Definition name_field_post_on (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (a1 : word) (nb : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ bytes_at rsegs m' (bv_unsigned a1) (nmf nb)
    /\ munch [(bv_unsigned sp - NAME_FIELD_K, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 16)] m m'
    /\ wmono rsegs m m'
    /\ mem_inv rsegs m'
    /\ stk rsegs m' (bv_unsigned sp - NAME_FIELD_K) (bv_unsigned sp)
    /\ asan_cells m' /\ (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m').

Definition name_field_contract_on : Prop :=
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
    asan_cells m -> shadow_rw_on (name_field_shadow_R (bv_unsigned a1)) m ->
    HIGHMEM_BEG <= bv_unsigned sp - NAME_FIELD_K -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned a0 + 280) 8 ->
    addressable m (bv_unsigned name) (Z.of_nat (length nb)) ->
    addressable m (bv_unsigned a1) 16 -> app_mem (bv_unsigned a1 + 16) ->
    (bv_unsigned a1 + 16 <= RT_LO \/ RT_HI <= bv_unsigned a1) ->
    evt rsegs (name_field_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a1 nb m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 NAME_FIELD) fc None m (seg_rom rsegs)).

From Stdlib Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import ImgBounds.

Definition name_field_contract_F_on : Prop :=
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
    asan_cells m -> shadow_rw_on (name_field_shadow_R (bv_unsigned a1)) m ->
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
    ExecF.evtF rsegs RNG (name_field_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a1 nb m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 NAME_FIELD) fc None m (seg_rom rsegs)).

(* The plain _on contract is the footprint form at ExecF.RNG_all: name_field_contract_of_F's script for the twins. *)
Lemma name_field_contract_on_of_F_on : name_field_contract_F_on -> name_field_contract_on.
Proof.
  unfold name_field_contract_F_on, name_field_contract_on. intros HF.
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
