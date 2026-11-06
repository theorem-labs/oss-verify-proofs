From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOX_FAMILY_OF : Z := 0x13ef8.
Definition REAC_BOX_FAMILY_OF_FRAME : Z := 32.

Definition FAMOF_HW1 : list Z := [0; 0; 0; 1; 0; 0; 0; 0].
Definition FAMOF_HW2 : list Z := [0; 0; 0; 2; 0; 3; 0; 2].
Definition FAMOF_HW3 : list Z := [0; 0; 0; 2; 0; 1; 0; 2].

Definition FAMOF_FAM (id : Z) (idb : list byte) : Z :=
  if id =? 0 then 0
  else if bv_unsigned (nth 36 idb (Z_to_bv 8 0)) =? 0 then 0
  else
    let hw := map bv_unsigned (firstn 8 (skipn 28 idb)) in
    if list_eq_dec Z.eq_dec hw FAMOF_HW1 then 1
    else if list_eq_dec Z.eq_dec hw FAMOF_HW2 then 2
    else if list_eq_dec Z.eq_dec hw FAMOF_HW3 then 3
    else 0.

Definition reac_box_family_of_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (idb : list byte),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + REAC_BOX_FAMILY_OF_FRAME <= bv_unsigned sp ->
    mem_inv rsegs m ->
    (bv_unsigned a0 = 0 \/
     (bytes_at rsegs m (bv_unsigned a0) idb /\ length idb = 38%nat /\
      (bv_unsigned a0 + 38 <= bv_unsigned sp - REAC_BOX_FAMILY_OF_FRAME \/ bv_unsigned sp <= bv_unsigned a0))) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (FAMOF_FAM (bv_unsigned a0) idb)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_BOX_FAMILY_OF_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         mem_inv rsegs m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_FAMILY_OF) fc None m (seg_rom rsegs)).
