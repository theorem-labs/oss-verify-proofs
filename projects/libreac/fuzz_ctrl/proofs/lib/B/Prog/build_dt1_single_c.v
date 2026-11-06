From Stdlib Require Import ZArith List.
From Stdlib Require Import Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox.
Import ListNotations.
Open Scope Z_scope.

Definition BUILD_DT1_SINGLE : Z := 0x87430.
(* K = 48 + max(K(dt1_head) 16, K(__asan_memcpy) 2224) (contracts/libreac/build_dt1_single@reac_box_synth.md Names). *)
Definition BUILD_DT1_SINGLE_K : Z := 2272.

(* The plain contract (lib/Prog/build_dt1_single_c.v) with the window K of this build and the premises of the
   asan-ubsan build (S1.6 of the English contract and those of __asan_memcpy at the copy of the n bytes at d to o + 20): the
   runtime's cells and shadow, the 32 bytes at o and the n bytes at d addressable, their ends in AppMem, the window in
   AppMem above the shadow, and the 32 bytes at o apart from [RT_LO, RT_HI). *)
Definition build_dt1_single_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ob D : list byte),
    stk rsegs m (bv_unsigned sp - BUILD_DT1_SINGLE_K) (bv_unsigned sp) ->
    bv_unsigned a3 <= 9 ->
    bv_unsigned a0 <> 0 -> bv_unsigned a0 + 32 <= 2^64 ->
    rw_cells rsegs m (bv_unsigned a0) [CB 32 ob] ->
    bv_unsigned a2 + bv_unsigned a3 <= 2^64 ->
    length D = Z.to_nat (bv_unsigned a3) ->
    bytes_at rsegs m (bv_unsigned a2) D ->
    (bv_unsigned a2 + bv_unsigned a3 <= bv_unsigned a0 \/ bv_unsigned a0 + 32 <= bv_unsigned a2) ->
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a0 + 32 <= bv_unsigned sp - BUILD_DT1_SINGLE_K) ->
    (bv_unsigned sp <= bv_unsigned a2 \/ bv_unsigned a2 + bv_unsigned a3 <= bv_unsigned sp - BUILD_DT1_SINGLE_K) ->
    mem_inv rsegs m ->
    (* asan-ubsan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - BUILD_DT1_SINGLE_K -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned a0) 32 -> addressable m (bv_unsigned a2) (bv_unsigned a3) ->
    app_mem (bv_unsigned a0 + 32) -> end_in_app (bv_unsigned a2) (bv_unsigned a3) ->
    (bv_unsigned a3 = 0 \/ app_mem (bv_unsigned a2 + 7)) ->
    (bv_unsigned a0 + 32 <= RT_LO \/ RT_HI <= bv_unsigned a0) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ bytes_at rsegs m' (bv_unsigned a0) (dt1_out (Z.to_nat (bv_unsigned a3)) (bv_unsigned a1) D ob)
         /\ psum (skipn 16 (dt1_out (Z.to_nat (bv_unsigned a3)) (bv_unsigned a1) D ob))
                 (Z.to_nat (bv_unsigned a3) + 5) mod 128 = 0
         /\ psum (dt1_out (Z.to_nat (bv_unsigned a3)) (bv_unsigned a1) D ob) 32 mod 256 = 0
         /\ munch [(bv_unsigned sp - BUILD_DT1_SINGLE_K, bv_unsigned sp);
                   (bv_unsigned a0, bv_unsigned a0 + 22 + bv_unsigned a3);
                   (bv_unsigned a0 + 31, bv_unsigned a0 + 32)] m m'
         /\ wmono rsegs m m'
         /\ mem_inv rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - BUILD_DT1_SINGLE_K) (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 BUILD_DT1_SINGLE) fc None m (seg_rom rsegs)).

(* ------------------------------------------------------------------------------------------------------------ *)
(* The footprint twin of the statement above (RECIPE.md step 1 (a working note, not in this delivery)): the same run as an ExecF.evtF under a
   footprint RNG. The premises of build_dt1_single_contract are unchanged and RNG is the first binder; then one rng
   premise per region the run reads or writes (data accesses only): the image [IMG_LO, IMG_HI)
   (lib/B/Prog/ImgBounds.v), which the footprint contract of __asan_memcpy (lib/B/Prog/asan_memcpy_cF.v) takes for
   its code, GOT cells and runtime cells; the window K below sp, which holds this frame and the frames of dt1_head
   and of __asan_memcpy; the 8-ALIGNED shadow word span of that window (sh_word_rng of rng_asan.v), which
   holds the shadow of __asan_memcpy's own frame that its contract takes; the runtime words [RT_LO, RT_HI), which
   hold the GOT cell 0xa08f0 and the cell that gives the shadow offset, both read before the call of dt1_head; the
   32 bytes at o, stored by this code, by dt1_head and by the destination side of the copy; the n bytes at d, read
   by the source side of the copy; and the shadow bytes of those two ranges. Each shadow premise is the 8-ALIGNED
   shadow word cover of its range, because the quick check of __asan_memcpy loads whole aligned shadow words; the
   byte-exact spans that this image's own 1-byte shadow loads and dt1_head's need lie inside it. The shadow premise
   of d is guarded by n = 0, exactly as the old statement guards the premises of d (with n = 0 no byte of d and no
   shadow byte of d is read). The rng_bytes premise (lib/Lib/RngBytes.v) says the footprint is decided byte by
   byte; the footprint contract of __asan_memcpy, which this run calls, takes it.
   build_dt1_single_contract_of_F gives the old statement back with RNG_all. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_memcpy_cF.

Definition build_dt1_single_contract_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ob D : list byte),
    stk rsegs m (bv_unsigned sp - BUILD_DT1_SINGLE_K) (bv_unsigned sp) ->
    bv_unsigned a3 <= 9 ->
    bv_unsigned a0 <> 0 -> bv_unsigned a0 + 32 <= 2^64 ->
    rw_cells rsegs m (bv_unsigned a0) [CB 32 ob] ->
    bv_unsigned a2 + bv_unsigned a3 <= 2^64 ->
    length D = Z.to_nat (bv_unsigned a3) ->
    bytes_at rsegs m (bv_unsigned a2) D ->
    (bv_unsigned a2 + bv_unsigned a3 <= bv_unsigned a0 \/ bv_unsigned a0 + 32 <= bv_unsigned a2) ->
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a0 + 32 <= bv_unsigned sp - BUILD_DT1_SINGLE_K) ->
    (bv_unsigned sp <= bv_unsigned a2 \/ bv_unsigned a2 + bv_unsigned a3 <= bv_unsigned sp - BUILD_DT1_SINGLE_K) ->
    mem_inv rsegs m ->
    (* asan-ubsan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - BUILD_DT1_SINGLE_K -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned a0) 32 -> addressable m (bv_unsigned a2) (bv_unsigned a3) ->
    app_mem (bv_unsigned a0 + 32) -> end_in_app (bv_unsigned a2) (bv_unsigned a3) ->
    (bv_unsigned a3 = 0 \/ app_mem (bv_unsigned a2 + 7)) ->
    (bv_unsigned a0 + 32 <= RT_LO \/ RT_HI <= bv_unsigned a0) ->
    (* the footprint *)
    rng_bytes RNG ->
    rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    rng RNG (bv_unsigned sp - BUILD_DT1_SINGLE_K) BUILD_DT1_SINGLE_K ->
    sh_word_rng RNG (bv_unsigned sp - BUILD_DT1_SINGLE_K) BUILD_DT1_SINGLE_K ->
    rng RNG RT_LO (RT_HI - RT_LO) ->
    rng RNG (bv_unsigned a0) 32 ->
    rng RNG ((bv_unsigned a0 / 8 + ASAN_K) / 8 * 8)
            (((bv_unsigned a0 + 31) / 8 + ASAN_K) / 8 * 8 + 8 - (bv_unsigned a0 / 8 + ASAN_K) / 8 * 8) ->
    rng RNG (bv_unsigned a2) (bv_unsigned a3) ->
    (bv_unsigned a3 = 0 \/
     rng RNG ((bv_unsigned a2 / 8 + ASAN_K) / 8 * 8)
             (((bv_unsigned a2 + bv_unsigned a3 - 1) / 8 + ASAN_K) / 8 * 8 + 8
              - (bv_unsigned a2 / 8 + ASAN_K) / 8 * 8)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ bytes_at rsegs m' (bv_unsigned a0) (dt1_out (Z.to_nat (bv_unsigned a3)) (bv_unsigned a1) D ob)
         /\ psum (skipn 16 (dt1_out (Z.to_nat (bv_unsigned a3)) (bv_unsigned a1) D ob))
                 (Z.to_nat (bv_unsigned a3) + 5) mod 128 = 0
         /\ psum (dt1_out (Z.to_nat (bv_unsigned a3)) (bv_unsigned a1) D ob) 32 mod 256 = 0
         /\ munch [(bv_unsigned sp - BUILD_DT1_SINGLE_K, bv_unsigned sp);
                   (bv_unsigned a0, bv_unsigned a0 + 22 + bv_unsigned a3);
                   (bv_unsigned a0 + 31, bv_unsigned a0 + 32)] m m'
         /\ wmono rsegs m m'
         /\ mem_inv rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - BUILD_DT1_SINGLE_K) (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 BUILD_DT1_SINGLE) fc None m (seg_rom rsegs)).

(* The old statement is the _F statement at the footprint that admits every access (every rng premise by rng_all):
   the _F statement asks for nothing the old one lacks. *)
Lemma build_dt1_single_contract_of_F : build_dt1_single_contract_F -> build_dt1_single_contract.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ob D ST Hn Ho0 Ho32 HO Hd HLD HD DdO DfO Dfd MI HCE HSW HHM HAE HADo HADd HAPo HEd H7d HRTo.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof HADo as (ADo0 & _ & ADo2 & _). pose proof HADd as (ADd0 & ADd1 & ADd2 & _).
  assert (RBY : rng_bytes RNG_all) by (intros b j _ _ _; exact I).
  assert (RIMG : rng RNG_all IMG_LO (IMG_HI - IMG_LO))
    by (pose proof two64 as H64; apply rng_all; cbv [IMG_LO IMG_HI]; lia).
  assert (RWIN : rng RNG_all (bv_unsigned sp - BUILD_DT1_SINGLE_K) BUILD_DT1_SINGLE_K)
    by (apply rng_all; unfold BUILD_DT1_SINGLE_K, HIGHMEM_BEG in *; lia).
  assert (RWS : sh_word_rng RNG_all (bv_unsigned sp - BUILD_DT1_SINGLE_K) BUILD_DT1_SINGLE_K)
    by (apply sh_word_rng_all; unfold BUILD_DT1_SINGLE_K, HIGHMEM_BEG in *; lia).
  assert (RRT : rng RNG_all RT_LO (RT_HI - RT_LO)) by (apply rng_all; unfold RT_LO, RT_HI; lia).
  assert (ROUT : rng RNG_all (bv_unsigned a0) 32) by (apply rng_all; unfold APPMEM_END in *; lia).
  assert (RSO : rng RNG_all ((bv_unsigned a0 / 8 + ASAN_K) / 8 * 8)
                  (((bv_unsigned a0 + 31) / 8 + ASAN_K) / 8 * 8 + 8 - (bv_unsigned a0 / 8 + ASAN_K) / 8 * 8))
    by (apply rng_all; unfold ASAN_K, APPMEM_END in *; Z.div_mod_to_equations; lia).
  assert (RDAT : rng RNG_all (bv_unsigned a2) (bv_unsigned a3)) by (apply rng_all; unfold APPMEM_END in *; lia).
  assert (RSD : bv_unsigned a3 = 0 \/
                rng RNG_all ((bv_unsigned a2 / 8 + ASAN_K) / 8 * 8)
                  (((bv_unsigned a2 + bv_unsigned a3 - 1) / 8 + ASAN_K) / 8 * 8 + 8
                   - (bv_unsigned a2 / 8 + ASAN_K) / 8 * 8)).
  { destruct (Z.eq_dec (bv_unsigned a3) 0) as [E|E]; [left; exact E | right].
    apply rng_all; unfold ASAN_K, APPMEM_END in *; Z.div_mod_to_equations; lia. }
  exact (evtF_evt rsegs RNG_all _ _
           (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc m ob D ST Hn Ho0 Ho32 HO Hd HLD HD DdO DfO Dfd MI HCE HSW HHM HAE HADo HADd HAPo HEd
               H7d HRTo RBY RIMG RWIN RWS RRT ROUT RSO RDAT RSD)).
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* Route (C) (a Theorem Labs lane 2026-10-29 09:20Z; wave lead a Theorem Labs lane; a Theorem Labs lane's brief dt1-on-B): the _on twins of the two
   statements above. Image-B twin of A's (a working branch ec2ad5b4f4f, lib/A/Prog/build_dt1_single_c.v
   blob 80b1de9255d): A's text with lib.A -> lib.B and the comment `asan-ubsan`. The run uses the universal
   `shadow_rw m` premise ONLY through the shadow premises of its two callees (measured on a working branch
   5c355e74408: build_dt1_singleF.v HSW :121 feeds only bdbF_rt :206, whose shadow_rw goes to the post :325, to
   __asan_memcpy's premise :579 and to dt1_head's premise :675; build_dt1_single.v :90 / :145 the same). dt1_head's _on
   contract (dt1_head_c.v) has NO shadow premise (dropped: dt1_head reads its shadow through addressable). The call
   __asan_memcpy(o + 20, d, n), whose _on contract (asan_memcpy_c_on.v / asan_memcpy_cF_on.v) takes the region
   asan_memcpy_shadow_R (o + 20) d n = the aligned shadow words of the source [d, d + n) and of the destination
   [o + 20, o + 20 + n), is the one shadow read through the premise: build_dt1_single_shadow_R o d n below is exactly
   that region (A's R). The window's shadow span (its sh_word_rng, a footprint premise) is NOT in R: neither this run
   nor __asan_memcpy's _on contract reads or stores it through shadow_rw (asan_memcpy_cF_on.v: "not in R"), as on A.
   The checks of the 32 bytes at o read their shadow through `addressable m o 32` (rt_shadow_rd / rt_addressable of
   RcAsanRT.v), and the run stores no shadow byte (its munch: the window, [o, o + 22 + n), o + 31). The post's
   `shadow_rw m'` becomes: each shadow region the caller holds in m it holds in m'. No other premise or conjunct
   changes. The old statements follow from the twins: build_dt1_single_contract_of_on,
   build_dt1_single_contract_F_of_F_on; build_dt1_single_contract_on_of_F_on is build_dt1_single_contract_of_F for
   the twins. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require sh_word_on.

Definition build_dt1_single_shadow_R (o d n : Z) (a : Z) : Prop :=
  B.Prog.sh_word_on.sh_word_on d n a \/ B.Prog.sh_word_on.sh_word_on (o + 20) n a.

Definition build_dt1_single_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ob D : list byte),
    stk rsegs m (bv_unsigned sp - BUILD_DT1_SINGLE_K) (bv_unsigned sp) ->
    bv_unsigned a3 <= 9 ->
    bv_unsigned a0 <> 0 -> bv_unsigned a0 + 32 <= 2^64 ->
    rw_cells rsegs m (bv_unsigned a0) [CB 32 ob] ->
    bv_unsigned a2 + bv_unsigned a3 <= 2^64 ->
    length D = Z.to_nat (bv_unsigned a3) ->
    bytes_at rsegs m (bv_unsigned a2) D ->
    (bv_unsigned a2 + bv_unsigned a3 <= bv_unsigned a0 \/ bv_unsigned a0 + 32 <= bv_unsigned a2) ->
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a0 + 32 <= bv_unsigned sp - BUILD_DT1_SINGLE_K) ->
    (bv_unsigned sp <= bv_unsigned a2 \/ bv_unsigned a2 + bv_unsigned a3 <= bv_unsigned sp - BUILD_DT1_SINGLE_K) ->
    mem_inv rsegs m ->
    (* asan-ubsan *)
    asan_cells m ->
    B.ShadowRwOn.shadow_rw_on (build_dt1_single_shadow_R (bv_unsigned a0) (bv_unsigned a2) (bv_unsigned a3)) m ->
    HIGHMEM_BEG <= bv_unsigned sp - BUILD_DT1_SINGLE_K -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned a0) 32 -> addressable m (bv_unsigned a2) (bv_unsigned a3) ->
    app_mem (bv_unsigned a0 + 32) -> end_in_app (bv_unsigned a2) (bv_unsigned a3) ->
    (bv_unsigned a3 = 0 \/ app_mem (bv_unsigned a2 + 7)) ->
    (bv_unsigned a0 + 32 <= RT_LO \/ RT_HI <= bv_unsigned a0) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ bytes_at rsegs m' (bv_unsigned a0) (dt1_out (Z.to_nat (bv_unsigned a3)) (bv_unsigned a1) D ob)
         /\ psum (skipn 16 (dt1_out (Z.to_nat (bv_unsigned a3)) (bv_unsigned a1) D ob))
                 (Z.to_nat (bv_unsigned a3) + 5) mod 128 = 0
         /\ psum (dt1_out (Z.to_nat (bv_unsigned a3)) (bv_unsigned a1) D ob) 32 mod 256 = 0
         /\ munch [(bv_unsigned sp - BUILD_DT1_SINGLE_K, bv_unsigned sp);
                   (bv_unsigned a0, bv_unsigned a0 + 22 + bv_unsigned a3);
                   (bv_unsigned a0 + 31, bv_unsigned a0 + 32)] m m'
         /\ wmono rsegs m m'
         /\ mem_inv rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - BUILD_DT1_SINGLE_K) (bv_unsigned sp)
         /\ asan_cells m'
         /\ (forall P : Z -> Prop, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 BUILD_DT1_SINGLE) fc None m (seg_rom rsegs)).

Definition build_dt1_single_contract_F_on : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ob D : list byte),
    stk rsegs m (bv_unsigned sp - BUILD_DT1_SINGLE_K) (bv_unsigned sp) ->
    bv_unsigned a3 <= 9 ->
    bv_unsigned a0 <> 0 -> bv_unsigned a0 + 32 <= 2^64 ->
    rw_cells rsegs m (bv_unsigned a0) [CB 32 ob] ->
    bv_unsigned a2 + bv_unsigned a3 <= 2^64 ->
    length D = Z.to_nat (bv_unsigned a3) ->
    bytes_at rsegs m (bv_unsigned a2) D ->
    (bv_unsigned a2 + bv_unsigned a3 <= bv_unsigned a0 \/ bv_unsigned a0 + 32 <= bv_unsigned a2) ->
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a0 + 32 <= bv_unsigned sp - BUILD_DT1_SINGLE_K) ->
    (bv_unsigned sp <= bv_unsigned a2 \/ bv_unsigned a2 + bv_unsigned a3 <= bv_unsigned sp - BUILD_DT1_SINGLE_K) ->
    mem_inv rsegs m ->
    (* asan-ubsan *)
    asan_cells m ->
    B.ShadowRwOn.shadow_rw_on (build_dt1_single_shadow_R (bv_unsigned a0) (bv_unsigned a2) (bv_unsigned a3)) m ->
    HIGHMEM_BEG <= bv_unsigned sp - BUILD_DT1_SINGLE_K -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned a0) 32 -> addressable m (bv_unsigned a2) (bv_unsigned a3) ->
    app_mem (bv_unsigned a0 + 32) -> end_in_app (bv_unsigned a2) (bv_unsigned a3) ->
    (bv_unsigned a3 = 0 \/ app_mem (bv_unsigned a2 + 7)) ->
    (bv_unsigned a0 + 32 <= RT_LO \/ RT_HI <= bv_unsigned a0) ->
    (* the footprint *)
    rng_bytes RNG ->
    rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    rng RNG (bv_unsigned sp - BUILD_DT1_SINGLE_K) BUILD_DT1_SINGLE_K ->
    sh_word_rng RNG (bv_unsigned sp - BUILD_DT1_SINGLE_K) BUILD_DT1_SINGLE_K ->
    rng RNG RT_LO (RT_HI - RT_LO) ->
    rng RNG (bv_unsigned a0) 32 ->
    rng RNG ((bv_unsigned a0 / 8 + ASAN_K) / 8 * 8)
            (((bv_unsigned a0 + 31) / 8 + ASAN_K) / 8 * 8 + 8 - (bv_unsigned a0 / 8 + ASAN_K) / 8 * 8) ->
    rng RNG (bv_unsigned a2) (bv_unsigned a3) ->
    (bv_unsigned a3 = 0 \/
     rng RNG ((bv_unsigned a2 / 8 + ASAN_K) / 8 * 8)
             (((bv_unsigned a2 + bv_unsigned a3 - 1) / 8 + ASAN_K) / 8 * 8 + 8
              - (bv_unsigned a2 / 8 + ASAN_K) / 8 * 8)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ bytes_at rsegs m' (bv_unsigned a0) (dt1_out (Z.to_nat (bv_unsigned a3)) (bv_unsigned a1) D ob)
         /\ psum (skipn 16 (dt1_out (Z.to_nat (bv_unsigned a3)) (bv_unsigned a1) D ob))
                 (Z.to_nat (bv_unsigned a3) + 5) mod 128 = 0
         /\ psum (dt1_out (Z.to_nat (bv_unsigned a3)) (bv_unsigned a1) D ob) 32 mod 256 = 0
         /\ munch [(bv_unsigned sp - BUILD_DT1_SINGLE_K, bv_unsigned sp);
                   (bv_unsigned a0, bv_unsigned a0 + 22 + bv_unsigned a3);
                   (bv_unsigned a0 + 31, bv_unsigned a0 + 32)] m m'
         /\ wmono rsegs m m'
         /\ mem_inv rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - BUILD_DT1_SINGLE_K) (bv_unsigned sp)
         /\ asan_cells m'
         /\ (forall P : Z -> Prop, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 BUILD_DT1_SINGLE) fc None m (seg_rom rsegs)).

(* The old statement from the twin: the universal premise gives the region (shadow_rw_on_of_shadow_rw), and the
   post's region transport at the whole shadow (P := fun _ => True) gives `shadow_rw m'` back (shadow_rw_of_on_all). *)
Lemma build_dt1_single_contract_of_on : build_dt1_single_contract_on -> build_dt1_single_contract.
Proof.
  intros HON ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ob D ST Hn Ho0 Ho32 HO Hd HLD HD DdO DfO Dfd MI HCE HSW HHM HAE HADo HADd HAPo HEd H7d HRTo.
  eapply evt_mono.
  - exact (HON ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m ob D ST Hn Ho0 Ho32 HO Hd HLD HD DdO DfO Dfd MI HCE
             (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW) HHM HAE HADo HADd HAPo HEd H7d HRTo).
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
                & E & B & S16 & S32 & MU & WM & MI' & ST' & AC & SR).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    refine (conj E (conj B (conj S16 (conj S32 (conj MU (conj WM (conj MI' (conj ST' (conj AC _))))))))).
    apply B.ShadowRwOn.shadow_rw_of_on_all, SR, B.ShadowRwOn.shadow_rw_on_of_shadow_rw, HSW.
Qed.

(* The same for the footprint statements. *)
Lemma build_dt1_single_contract_F_of_F_on : build_dt1_single_contract_F_on -> build_dt1_single_contract_F.
Proof.
  intros HON RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ob D ST Hn Ho0 Ho32 HO Hd HLD HD DdO DfO Dfd MI HCE HSW HHM HAE HADo HADd HAPo HEd H7d HRTo
    RBY RIMG RWIN RWS RRT ROUT RSO RDAT RSD.
  eapply evtF_mono.
  - exact (HON RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m ob D ST Hn Ho0 Ho32 HO Hd HLD HD DdO DfO Dfd MI HCE
             (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW) HHM HAE HADo HADd HAPo HEd H7d HRTo
             RBY RIMG RWIN RWS RRT ROUT RSO RDAT RSD).
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
                & E & B & S16 & S32 & MU & WM & MI' & ST' & AC & SR).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    refine (conj E (conj B (conj S16 (conj S32 (conj MU (conj WM (conj MI' (conj ST' (conj AC _))))))))).
    apply B.ShadowRwOn.shadow_rw_of_on_all, SR, B.ShadowRwOn.shadow_rw_on_of_shadow_rw, HSW.
Qed.

(* build_dt1_single_contract_of_F for the twins: the _F twin at RNG_all gives the plain twin. *)
Lemma build_dt1_single_contract_on_of_F_on : build_dt1_single_contract_F_on -> build_dt1_single_contract_on.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ob D ST Hn Ho0 Ho32 HO Hd HLD HD DdO DfO Dfd MI HCE HSW HHM HAE HADo HADd HAPo HEd H7d HRTo.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof HADo as (ADo0 & _ & ADo2 & _). pose proof HADd as (ADd0 & ADd1 & ADd2 & _).
  assert (RBY : rng_bytes RNG_all) by (intros b j _ _ _; exact I).
  assert (RIMG : rng RNG_all IMG_LO (IMG_HI - IMG_LO))
    by (pose proof two64 as H64; apply rng_all; cbv [IMG_LO IMG_HI]; lia).
  assert (RWIN : rng RNG_all (bv_unsigned sp - BUILD_DT1_SINGLE_K) BUILD_DT1_SINGLE_K)
    by (apply rng_all; unfold BUILD_DT1_SINGLE_K, HIGHMEM_BEG in *; lia).
  assert (RWS : sh_word_rng RNG_all (bv_unsigned sp - BUILD_DT1_SINGLE_K) BUILD_DT1_SINGLE_K)
    by (apply sh_word_rng_all; unfold BUILD_DT1_SINGLE_K, HIGHMEM_BEG in *; lia).
  assert (RRT : rng RNG_all RT_LO (RT_HI - RT_LO)) by (apply rng_all; unfold RT_LO, RT_HI; lia).
  assert (ROUT : rng RNG_all (bv_unsigned a0) 32) by (apply rng_all; unfold APPMEM_END in *; lia).
  assert (RSO : rng RNG_all ((bv_unsigned a0 / 8 + ASAN_K) / 8 * 8)
                  (((bv_unsigned a0 + 31) / 8 + ASAN_K) / 8 * 8 + 8 - (bv_unsigned a0 / 8 + ASAN_K) / 8 * 8))
    by (apply rng_all; unfold ASAN_K, APPMEM_END in *; Z.div_mod_to_equations; lia).
  assert (RDAT : rng RNG_all (bv_unsigned a2) (bv_unsigned a3)) by (apply rng_all; unfold APPMEM_END in *; lia).
  assert (RSD : bv_unsigned a3 = 0 \/
                rng RNG_all ((bv_unsigned a2 / 8 + ASAN_K) / 8 * 8)
                  (((bv_unsigned a2 + bv_unsigned a3 - 1) / 8 + ASAN_K) / 8 * 8 + 8
                   - (bv_unsigned a2 / 8 + ASAN_K) / 8 * 8)).
  { destruct (Z.eq_dec (bv_unsigned a3) 0) as [E|E]; [left; exact E | right].
    apply rng_all; unfold ASAN_K, APPMEM_END in *; Z.div_mod_to_equations; lia. }
  exact (evtF_evt rsegs RNG_all _ _
           (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc m ob D ST Hn Ho0 Ho32 HO Hd HLD HD DdO DfO Dfd MI HCE HSW HHM HAE HADo HADd HAPo HEd
               H7d HRTo RBY RIMG RWIN RWS RRT ROUT RSO RDAT RSD)).
Qed.
