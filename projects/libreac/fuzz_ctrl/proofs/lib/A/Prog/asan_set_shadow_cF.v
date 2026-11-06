From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_set_shadow_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Export ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.
Import ListNotations.
Open Scope Z_scope.

(* Footprint form (D) of the shadow fill helpers __asan_set_shadow_{00,f5,f8} of image A (fuzz_ctrl.asan, libreac
   v1.9.0) at ASAN_SET_SHADOW_00 = 0x54ee8, ASAN_SET_SHADOW_F5 = 0x54ff0, ASAN_SET_SHADOW_F8 = 0x55008.

   FORM: the shape of asan_memset_contract_F (asan_memset_cF.v), which follows ROUTE1.md (a working note, not in this delivery) and
   a Theorem Labs lane's rewalk-F-policy.md (a working note, not in this delivery). The binders, the premises and the post of
   asan_set_shadow_contract (asan_set_shadow_c.v) are repeated UNCHANGED, in the same order -- that file is
   frozen and this one does not touch it -- with
     - the footprint RNG universally quantified, FIRST among the binders;
     - `RngBytes.rng_bytes RNG` FIRST among the footprint premises: an access may straddle two adjacent rng
       ranges, and the route-1 proof needs the footprint byte-wise;
     - one `rng` premise per region the call reads or writes, LAST, after every original premise;
     - the run an ExecF.evtF on RNG instead of an Exec.evt.
   Apply it with NAMED arguments (`asan_set_shadow_contract_F entry v RNG:=...`), not positionally.

   THE REGIONS, and why each one is in the list:
     - the image [IMG_LO, IMG_HI): the code fetched (the helper and musl memset), the GOT cell GOT_REAL_MEMSET =
       0x9faf0 and the runtime cell REAL_MEMSET = 0xa1938 that the helper loads (lib/A/AsanRT.v). They lie inside
       [RT_LO, RT_HI) = [0x9fad0, 0xa9578), inside the image, so they need no premise of their own.
     - the helper's own stack window [sp - ASAN_SET_SHADOW_K, sp), with ASAN_SET_SHADOW_K = 0 (below): empty. It is
       kept so that the premise list has the same positions as asan_memset_contract_F's.
     - the written range [A, A + N): the N shadow bytes musl memset fills with v.
   NOT in the list, unlike asan_memset_contract_F:
     - no shadow cover of [A, A + N): the helper does no ASan check, so it reads no shadow of the range it writes
       (the range is itself shadow, and its bytes are covered by the written-range premise);
     - no shadow cover of the stack frame: the frame is empty and nothing reads its shadow.

   ASAN_SET_SHADOW_K, from the disassembly fuzz_ctrl.objdump.txt (a working note, not in this delivery):
     __asan_set_shadow_f8 0x55008: auipc a2 ; ld a2,-1304(a2) (GOT 0x9faf0) ; ld t1,0(a2) (REAL_MEMSET 0xa1938) ;
                                   mv a2,a1 ; li a1,248 ; jr t1                                (0x55008 .. 0x5501c)
     __asan_set_shadow_f5 0x54ff0: the same six instructions with li a1,245                    (0x54ff0 .. 0x55004)
     __asan_set_shadow_00 0x54ee8: mv a2,a1 ; auipc a1 ; ld a1,-1020(a1) (GOT 0x9faf0) ; ld t1,0(a1) ; li a1,0 ;
                                   jr t1                                                       (0x54ee8 .. 0x54efc)
     jr t1 is a TAIL CALL to REAL(memset) = MUSL_MEMSET = memset 0x98010 (asan_cells pins the cell), whose body
     0x98010 .. 0x98104 is beqz / sb / sw / sd / add / sub / and / mulhu / bltu and ends with `ret` at 0x98104.
   No instruction on any path of the helper or of musl memset reads, writes or adjusts sp (no `addi sp`, no
   sp-relative load or store), and musl memset calls nothing (no jal / jalr other than the final ret). Every path
   is the helper's six instructions followed by one path through memset (an early exit at its beqz or at one of
   its bltu tests, or its 32-byte loop), and none of them has a frame. So the deepest stack along EVERY path is 0 bytes:
   ASAN_SET_SHADOW_K = 0 is EXACT, not a bound. The post's `munch [(A, A + N)]` (asan_set_shadow_c.v) already rules
   out any stack write. *)
Definition ASAN_SET_SHADOW_K : Z := 0.

Definition asan_set_shadow_contract_F (entry v : Z) : Prop :=
  forall (RNG : ExecF.footprint)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  let A := bv_unsigned a0 in let N := bv_unsigned a1 in
  (forall i, (0 <= i < N)%Z -> in_shadow (A + i)) ->
  rw_cells rsegs m A [CB (Z.to_nat N) junk] ->
  asan_cells m -> mem_inv rsegs m ->
  (* the footprint premises: the footprint is byte-wise, then one per region the call reads or writes *)
  RngBytes.rng_bytes RNG ->
  ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  ExecF.rng RNG (bv_unsigned sp - ASAN_SET_SHADOW_K) ASAN_SET_SHADOW_K ->
  ExecF.rng RNG A N ->
  ExecF.evtF rsegs RNG (asan_set_shadow_post v ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).

Definition asan_set_shadow_00_contract_F : Prop := asan_set_shadow_contract_F ASAN_SET_SHADOW_00 0x00.
Definition asan_set_shadow_f5_contract_F : Prop := asan_set_shadow_contract_F ASAN_SET_SHADOW_F5 0xf5.
Definition asan_set_shadow_f8_contract_F : Prop := asan_set_shadow_contract_F ASAN_SET_SHADOW_F8 0xf8.

(* ---- the two forms are linked: the frozen contract is the footprint form at RNG_all ---- *)

Lemma asan_set_shadow_contract_of_F : forall entry v,
  asan_set_shadow_contract_F entry v -> asan_set_shadow_contract entry v.
Proof.
  intros entry v HF. unfold asan_set_shadow_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk.
  cbv zeta.
  intros HSh Hrw Hac Hmi.
  assert (H64 : (2^64)%Z = 18446744073709551616%Z) by reflexivity.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a1) as RN.
  unfold bv_modulus in Rsp, RN. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp, RN.
  pose proof Hrw as [_ (W0 & W1 & _)].
  cbn [cells_size csize] in W1. rewrite ?Nat.add_0_r, Z2Nat.id in W1 by lia.
  eapply ExecF.evtF_evt.
  (* eapply: `junk` occurs in no conclusion, so it is an evar that rw_cells closes. *)
  eapply (HF ExecF.RNG_all); try eassumption.
  - (* RNG_all is byte-wise; ctrl's lib/Lib/RngBytes.v has no rng_bytes_all lemma, so its one-line proof is here *)
    intros ? ? _ _ _. exact I.
  - apply ExecF.rng_all; cbv [IMG_LO IMG_HI]; lia.
  - apply ExecF.rng_all; unfold ASAN_SET_SHADOW_K; lia.
  - apply ExecF.rng_all; lia.
Qed.

Lemma asan_set_shadow_00_contract_of_F : asan_set_shadow_00_contract_F -> asan_set_shadow_00_contract.
Proof. apply asan_set_shadow_contract_of_F. Qed.

Lemma asan_set_shadow_f5_contract_of_F : asan_set_shadow_f5_contract_F -> asan_set_shadow_f5_contract.
Proof. apply asan_set_shadow_contract_of_F. Qed.

Lemma asan_set_shadow_f8_contract_of_F : asan_set_shadow_f8_contract_F -> asan_set_shadow_f8_contract.
Proof. apply asan_set_shadow_contract_of_F. Qed.
