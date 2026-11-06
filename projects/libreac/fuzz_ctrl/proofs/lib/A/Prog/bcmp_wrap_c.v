From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c.
Import ListNotations.
Open Scope bv_scope.

Definition BCMP_WRAP : Z := 0x42970.
Definition BCMP_WRAP_K : Z := 4560.
Definition BCMP : Z := 0x97b0c.
Definition REAL_BCMP : Z := 0xa17f0.
Definition REAL_MEMCMP : Z := 0xa17e8.
Definition GOT_CF : Z := 0x9fac0.
Definition CF : Z := 0x13a3a8.

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

(* Footprint form (re-walk (D), RECIPE.md step 1 (a working note, not in this delivery); text of a working branch 5ecd7d5585, with the image
   range of fuzz_ctrl A): the same run, every access inside the image, the wrapper's stack window and the string
   bytes with the aligned 8-byte shadow words of each string (the range check loads whole aligned shadow words).
   The proof is route 1 one level down (ROUTE1.md (a working note, not in this delivery); the Bz pieces of route 2 do not exist), whose last
   step evtF_RNG_P_weaken needs rng_bytes RNG; a site discharges it with fp_ok_rng_bytes. A and B carry the same
   statement (with a Theorem Labs lane, 10:17Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.

(* The image's address range [IMG_LO, IMG_HI). IMG_HI is the image's end of writable data rounded up to 4096, from the
   ELF's program headers, taken by name from AsanRT.RT_GT (already Required above; the same 0x5fe000 as the generated
   Contract.GT). It is NOT taken from A.Contract any more: `Require Contract` pulled 62 files the image-A walk's closure
   must not load (a Theorem Labs lane's B5.5 closure scan, a Theorem Labs lane 12:24Z). `Eval compute` stores the literal either way, so the
   definition's value and every statement below are unchanged. IMG_LO is the p_vaddr of the image's first PT_LOAD; no
   generated file names it, and it is 0x10000 in both libreac v1.8 and v1.9.0. bcmp_wrap_F.v's rsegs_in_img checks both
   bounds against rsegs by vm_compute. *)
Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := Eval compute in OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.RT_GT.

Definition bcmp_wrap_contract_F : Prop :=
  forall (RNG : footprint) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
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
  rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  rng RNG (bv_unsigned sp - BCMP_WRAP_K) BCMP_WRAP_K ->
  rng RNG L N -> (N = 0 \/ rng RNG (8 * (shadow_addr L / 8)) (8 * (shadow_addr (L + N - 1) / 8) + 8 - 8 * (shadow_addr L / 8))) ->
  rng RNG R N -> (N = 0 \/ rng RNG (8 * (shadow_addr R / 8)) (8 * (shadow_addr (R + N - 1) / 8) + 8 - 8 * (shadow_addr R / 8))) ->
  evtF rsegs RNG (bcmp_wrap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BCMP_WRAP) fc None m (seg_rom rsegs)).

Lemma bcmp_wrap_contract_of_F : bcmp_wrap_contract_F -> bcmp_wrap_contract.
Proof.
  unfold bcmp_wrap_contract_F, bcmp_wrap_contract. cbv zeta. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v lo.
  intros BL BR HM HMI HN ADL ADR EL ER AL AR SL SR HST HK HLO HSP HC HSR HRB HRM HGCF HCF1 HCF2.
  pose proof ADL as (L0 & N0 & LE & _). pose proof ADR as (R0 & _ & RE & _).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. unfold HIGHMEM_BEG, APPMEM_END in *.
  apply (evtF_evt rsegs RNG_all). apply HF; try assumption; try right;
    first [ intros ? ? ? ? ?; exact I | apply rng_all ];
    unfold shadow_addr, ASAN_K, IMG_LO, IMG_HI; Z.div_mod_to_equations; lia.
Qed.
