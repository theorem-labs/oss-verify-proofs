(* lib/A/Prog/reac_box_model_block_c_on.v -- route (C): the `_on` STATEMENTS for reac_box_model_block, split out
   of reac_box_model_block_c.v (a Theorem Labs lane request, 2026-10-29 11:54Z) so that a consumer takes them BY PATH without
   rebuilding the whole reac_box_model_block_c family; reac_box_model_block_c.v, a Theorem Labs lane's file, still states the same four declarations
   too (appended to its text from a working branch d69f7c708f6).  The text of the four declarations below is unchanged by the copy.
   THERE IS NO PROOF of reac_box_model_block_contract_on here: it is a STATEMENT (see the comment below). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcSynth.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c RcAsanFP
  reac_box_model_block_c sh_word_on asan_stack_malloc_c_on.
Import ListNotations.
Open Scope Z_scope.

(* Route (C) (a Theorem Labs lane 2026-10-29 09:20Z; form of a Theorem Labs lane 09:38Z): reac_box_model_block_contract_on, the statement
   above with TWO changes:
     - the premise `shadow_rw m` becomes `shadow_rw_on (reac_box_model_block_shadow_R S FS p b o row nb) m`
       (S = bv_unsigned sp);
     - the post's `shadow_rw m'` becomes `forall P, shadow_rw_on P m -> shadow_rw_on P m'`
       (reac_box_model_block_post_on): every shadow region the caller holds before the call it holds after it.
   reac_box_model_block_shadow_R names, as 8-aligned shadow-word covers (sh_word_on, a Theorem Labs lane's
   lib/A/Prog/sh_word_on.v), the shadow the run and its callees can read or write: the window [S - K, S), which holds
   the real-stack frame [A - 64, A) and its 8 shadow bytes (reac_box_model_block.v fk_facts) and the callees'
   real-stack frames (__asan_memset, __asan_memcpy, build_dt1_single); the shadow of the side stack's class-0 block
   [shadow_addr (fs_frame FS 0 0), + 131072), which holds the class-0 frame's 8 shadow bytes and
   __asan_stack_malloc_0's stores (a Theorem Labs lane 10:57Z, side-stack-shadow.md (a working note, not in this delivery): the class-c block is asan_stack_malloc's
   R; the side-stack header's shadow is not in R); and, under the guard of its data premise, each block the run or a
   callee reads or writes: the row
   p (p <> 0), the name (p <> 0, b = 5, 6, has row, rname row <> 0), the output o (o <> 0) and the JOIN block (b = 1, 2).
   These are the class-0 frame, md, name and JOIN rows of ctrl_lay_block_contract_F's table for this callee.  No other
   shadow byte is read or written by the run.
   This is a STATEMENT: it is proved when reac_box_model_block's run narrows (route (C) L2, which takes the callees'
   _on contracts); until then cite it only as a hypothesis, as the old contract is cited.  The old statement follows
   (reac_box_model_block_contract_of_on). *)


Definition reac_box_model_block_shadow_R (S FS p b o : Z) (row nb : list byte) (a : Z) : Prop :=
  sh_word_on (S - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K a \/
  asan_stack_malloc_shadow_R FS 0%nat a \/
  (p <> 0 /\ sh_word_on p 296 a) \/
  (p <> 0 /\ (b = 5 \/ b = 6) /\ has row <> 0 /\ rname row <> 0 /\ sh_word_on (rname row) (Z.of_nat (length nb)) a) \/
  (o <> 0 /\ sh_word_on o 32 a) \/
  (b = 1 /\ sh_word_on JOIN_0014 32 a) \/ (b = 2 /\ sh_word_on JOIN_0013 32 a).

(* reac_box_model_block_post with the post's region transport in place of `shadow_rw m'`. *)
Definition reac_box_model_block_post_on (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (p b o FS : Z) (row nb : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if (p =? 0) || (o =? 0) then -1 else rc row b))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ (if (p =? 0) || (o =? 0)
        then munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp)] ++
                    reac_box_model_block_X (bv_unsigned sp) FS) m m'
        else bytes_at rsegs m' o (synth row b nb) /\
             munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp); (o, o + 32)] ++
                    reac_box_model_block_X (bv_unsigned sp) FS) m m')
    /\ wmono rsegs m m'
    /\ mem_inv rsegs m'
    /\ stk rsegs m' (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp)
    /\ asan_cells m' /\ (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m')
    /\ addressable m' (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K
    /\ fp [0%nat] m' (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp)
         (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o)
    /\ reac_box_model_block_tls m' (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp).

(* reac_box_model_block_contract with the narrowed premise and post. *)
Definition reac_box_model_block_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p b o FS : Z) (row nb ob : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 o ->
    0 <= p < 2^64 -> 0 <= b < 2^64 -> 0 <= o < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) ->
    (p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
               (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) /\
               (o = 0 \/ o + 32 <= p \/ p + 296 <= o)) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               name_ok nb /\ bytes_at rsegs m (rname row) nb /\
               (bv_unsigned sp <= rname row \/
                rname row + Z.of_nat (length nb) <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) /\
               (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o)) ->
    (o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
               (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) /\
               (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o)) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw_on (reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K ->
    (p <> 0 -> addressable m p 296) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               addressable m (rname row) (Z.of_nat (length nb))) ->
    (o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o)) ->
    (b = 1 -> addressable m JOIN_0014 32) -> (b = 2 -> addressable m JOIN_0013 32) ->
    fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp)
      (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS)) ->
    reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) ->
    evt rsegs
      (reac_box_model_block_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None m (seg_rom rsegs)).

(* The old statement: the universal shadow_rw gives the region (shadow_rw_on_of_shadow_rw), and the post's region
   transport at P := fun _ => True gives the universal post back (shadow_rw_of_on_all). *)
Lemma reac_box_model_block_contract_of_on : reac_box_model_block_contract_on -> reac_box_model_block_contract.
Proof.
  intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p b o FS row nb ob Ea0 Ea1 Ea2 Rp Rb Ro SP16 ST HP HN HO MI AC SW HHM HAE AW AP AN AO AJ14 AJ13 FP FPN
    TLS.
  eapply evt_mono.
  - exact (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m p b o FS row nb ob Ea0 Ea1 Ea2 Rp Rb Ro SP16 ST HP HN HO MI AC (shadow_rw_on_of_shadow_rw _ m SW)
             HHM HAE AW AP AN AO AJ14 AJ13 FP FPN TLS).
  - intros ms' Hq. unfold reac_box_model_block_post_on in Hq. unfold reac_box_model_block_post.
    destruct Hq as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                    Ems & MU & WM & MI' & ST' & AC' & SW' & Rest).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    refine (conj Ems (conj MU (conj WM (conj MI' (conj ST' (conj AC' (conj _ Rest))))))).
    exact (shadow_rw_of_on_all m' (SW' (fun _ => True) (shadow_rw_on_of_shadow_rw _ m SW))).
Qed.

Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block_c_on.reac_box_model_block_contract_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block_c_on.reac_box_model_block_contract_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block_c_on.reac_box_model_block_contract_of_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block_c_on.reac_box_model_block_contract_of_on.
