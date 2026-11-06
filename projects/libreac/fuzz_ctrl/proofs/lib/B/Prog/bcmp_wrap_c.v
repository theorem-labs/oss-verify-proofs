From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import memcmp_c.
Import ListNotations.
Open Scope bv_scope.

Definition BCMP_WRAP : Z := 0x42aac.
Definition BCMP_WRAP_K : Z := 4560.
Definition BCMP : Z := 0x98930.
Definition REAL_BCMP : Z := 0xa2610.
Definition REAL_MEMCMP : Z := 0xa2608.
Definition GOT_CF : Z := 0xa08e0.
Definition CF : Z := 0x13b1e8.

Definition bcmp_wrap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (ls rs : list byte) (v lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1' a2' a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ asan_cells m' /\ shadow_rw m'
    /\ bytes_at rsegs m' (bv_unsigned a0) (firstn (Z.to_nat (bv_unsigned a2)) ls)
    /\ bytes_at rsegs m' (bv_unsigned a1) (firstn (Z.to_nat (bv_unsigned a2)) rs).

Definition bcmp_wrap_contract : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v lo : Z),
  let L := bv_unsigned a0 in let R := bv_unsigned a1 in let N := bv_unsigned a2 in
  bytes_at rsegs m L ls ->
  bytes_at rsegs m R rs ->
  memcmp_model ls rs (Z.to_nat N) = Some v ->
  mem_inv rsegs m ->
  (N <= 2^40)%Z -> addressable m L N -> addressable m R N -> end_in_app L N -> end_in_app R N ->
  (N = 0 \/ app_mem (L + 7))%Z -> (N = 0 \/ app_mem (R + 7))%Z ->
  (L + N <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L)%Z ->
  (R + N <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + BCMP_WRAP_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shadow_rw m ->
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
  bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
  bytes_at rsegs m (CF + 254)%Z [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255)%Z [Z_to_bv 8 1] ->
  evt rsegs (bcmp_wrap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BCMP_WRAP) fc None m (seg_rom rsegs)).

From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import ImgBounds.
Local Open Scope Z_scope.

(* The footprint form of bcmp_wrap_contract (RECIPE step 1): the text that the image-B footprint proofs
   reac_ctrl_parseF.v, reac_ctrl_classify_box_frame_F.v and reac_ctrl_identity_fragment_F.v take as their hypothesis,
   moved here from reac_ctrl_parseF.v unchanged. It is the text of lib/A/Prog/reac_ctrl_identity_fragment_F.v's
   bcmp_wrap_contract_F, with its two shadow covers written in the [x / 8 * 8] form of the asan_memset and
   asan_memcpy footprint contracts (the same range, 8 * (y / 8) there). The premises of bcmp_wrap_contract are
   unchanged, then: the footprint is decided byte by byte, the image, the stack window [sp - BCMP_WRAP_K, sp), the
   N bytes at each of the two buffers and the 8-ALIGNED shadow word cover of each. *)
Definition bcmp_wrap_contract_F : Prop :=
  forall (RNG : ExecF.footprint) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v lo : Z),
  let L := bv_unsigned a0 in let R := bv_unsigned a1 in let N := bv_unsigned a2 in
  bytes_at rsegs m L ls ->
  bytes_at rsegs m R rs ->
  memcmp_model ls rs (Z.to_nat N) = Some v ->
  mem_inv rsegs m ->
  (N <= 2^40)%Z -> addressable m L N -> addressable m R N -> end_in_app L N -> end_in_app R N ->
  (N = 0 \/ app_mem (L + 7))%Z -> (N = 0 \/ app_mem (R + 7))%Z ->
  (L + N <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L)%Z ->
  (R + N <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + BCMP_WRAP_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shadow_rw m ->
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
  bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
  bytes_at rsegs m (CF + 254)%Z [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255)%Z [Z_to_bv 8 1] ->
  rng_bytes RNG ->
  ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  ExecF.rng RNG (bv_unsigned sp - BCMP_WRAP_K) BCMP_WRAP_K ->
  ExecF.rng RNG L N ->
  (N = 0 \/ ExecF.rng RNG (shadow_addr L / 8 * 8) (shadow_addr (L + N - 1) / 8 * 8 + 8 - shadow_addr L / 8 * 8)) ->
  ExecF.rng RNG R N ->
  (N = 0 \/ ExecF.rng RNG (shadow_addr R / 8 * 8) (shadow_addr (R + N - 1) / 8 * 8 + 8 - shadow_addr R / 8 * 8)) ->
  ExecF.evtF rsegs RNG (bcmp_wrap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BCMP_WRAP) fc None m (seg_rom rsegs)).

Lemma bcmp_wrap_contract_of_F : bcmp_wrap_contract_F -> bcmp_wrap_contract.
Proof.
  unfold bcmp_wrap_contract_F, bcmp_wrap_contract. cbv zeta.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ls rs v lo HBL HBR HV MI HN ADL ADR EAL EAR A7L A7R HSPl HSPr ST HLO HHM HAE HC HSW
    HRB HRM HCF HCF1 HCF2.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ADL as (AL0 & AL1 & AL2 & _). pose proof ADR as (AR0 & AR1 & AR2 & _).
  assert (R0 : rng_bytes RNG_all) by (intros b j _ _ _; exact I).
  assert (R1 : rng RNG_all IMG_LO (IMG_HI - IMG_LO)) by (apply rng_all; cbv [IMG_LO IMG_HI]; lia).
  assert (R2 : rng RNG_all (bv_unsigned sp - BCMP_WRAP_K) BCMP_WRAP_K)
    by (clear - Rsp HLO HHM; apply rng_all; unfold BCMP_WRAP_K, HIGHMEM_BEG in *; lia).
  assert (R3 : rng RNG_all (bv_unsigned a0) (bv_unsigned a2))
    by (clear - AL0 AL1 AL2; apply rng_all; unfold APPMEM_END in *; lia).
  assert (R4 : bv_unsigned a2 = 0 \/
               rng RNG_all (shadow_addr (bv_unsigned a0) / 8 * 8)
                 (shadow_addr (bv_unsigned a0 + bv_unsigned a2 - 1) / 8 * 8 + 8
                  - shadow_addr (bv_unsigned a0) / 8 * 8)).
  { destruct (Z.eq_dec (bv_unsigned a2) 0) as [E|E]; [left; exact E | right].
    clear - AL0 AL1 AL2 E. apply rng_all; unfold shadow_addr, ASAN_K, APPMEM_END in *;
      Z.div_mod_to_equations; lia. }
  assert (R5 : rng RNG_all (bv_unsigned a1) (bv_unsigned a2))
    by (clear - AR0 AR1 AR2; apply rng_all; unfold APPMEM_END in *; lia).
  assert (R6 : bv_unsigned a2 = 0 \/
               rng RNG_all (shadow_addr (bv_unsigned a1) / 8 * 8)
                 (shadow_addr (bv_unsigned a1 + bv_unsigned a2 - 1) / 8 * 8 + 8
                  - shadow_addr (bv_unsigned a1) / 8 * 8)).
  { destruct (Z.eq_dec (bv_unsigned a2) 0) as [E|E]; [left; exact E | right].
    clear - AR0 AR1 AR2 E. apply rng_all; unfold shadow_addr, ASAN_K, APPMEM_END in *;
      Z.div_mod_to_equations; lia. }
  exact (evtF_evt rsegs RNG_all _ _
           (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc m ls rs v lo HBL HBR HV MI HN ADL ADR EAL EAR A7L A7R HSPl HSPr ST HLO HHM HAE HC HSW
               HRB HRM HCF HCF1 HCF2 R0 R1 R2 R3 R4 R5 R6)).
Qed.
