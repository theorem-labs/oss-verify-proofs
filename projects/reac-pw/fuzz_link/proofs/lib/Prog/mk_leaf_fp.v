(* reac-pw/fuzz_link, PLAIN build: the `leaf_fp` twin of lib/Prog/mk_leaf.v `leaf_intro`. A walk over
   `mkR ra sp ... t6` gives link_mem's `leaf_fp` contract; the floating-point file, the rounding mode
   and the memory carry over unchanged between a register map and its `mkR` copy. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Regs6ss RegisterBridge.
Local Open Scope Z_scope.

Definition leaf_fp_walk (pc K : Z)
    (Pre : bvmap 5 word -> (word -> option byte) -> Prop)
    (Wr : bvmap 5 word -> (word -> option byte) -> list ivl)
    (Post : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop)
  : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    let regs := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 in
    Pre regs m ->
    mem_inv rsegs m -> task_mem rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + K <= bv_unsigned sp -> bv_unsigned sp < 2 ^ 63 -> frm0 fc ->
    A_IMG_TOP <= lo ->
    bytes_at rsegs m A_GOT_GUARD (le8 (wz A_GUARD)) -> (exists c, bytes_at rsegs m A_GUARD (le8 c)) ->
    evt rsegs
      (fun ms' => exists (regs' Ft : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
         ms' = MS regs' Ft (ret_pc ra) fc' None m' (seg_rom rsegs) /\
         frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) /\
         regs_preserved regs regs' /\
         munch ((bv_unsigned sp - K, bv_unsigned sp) :: Wr regs m) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ task_mem rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Post regs m regs' m')
      (MS regs F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma leaf_fp_intro : forall pc K Pre Wr Post,
  pre_ext Pre -> wr_ext Wr -> post_ext Post ->
  leaf_fp_walk pc K Pre Wr Post -> leaf_fp pc K Pre Wr Post.
Proof.
  intros pc K Pre Wr Post HP HW HQ H. unfold leaf_fp.
  intros regs F fc m lo Hpre MI TM ST LO SP FRM ITOP GG GQ.
  pose proof (mkR_of_same regs) as E.
  assert (E2 : spZ regs = bv_unsigned (reg_get regs 2)) by reflexivity.
  assert (E1 : getr regs 1 = reg_get regs 1) by reflexivity.
  specialize (H (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
                (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10)
                (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15)
                (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
                (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
                (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30)
                (reg_get regs 31) F fc m lo).
  cbv zeta in H. fold (mkR_of regs) in H.
  rewrite E2 in ST, LO, SP.
  specialize (H (HP _ _ _ E Hpre) MI TM ST LO SP FRM ITOP GG GQ).
  pose proof (canonical_contract_transport rsegs _ (MS regs F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)) H) as T.
  eapply evt_mono; [exact T|].
  intros actual (c & (regs' & Ft & fc' & m' & Hc & FR' & FK & RP & MU & WM & MI' & TM' & ST' & PO) & EQ).
  subst c. destruct actual as [Ra Fa pca svca rva fca ma roa].
  destruct EQ as (ER & EF & EP & ES & EV & EC & EM & EO). cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending
    ms_resv ms_fcsr ms_mem ms_rom MS] in *. subst Fa pca svca rva fca ma roa.
  assert (ES' : getr_same regs' Ra) by (intros r; apply getr_eqv, ER).
  assert (ESy : getr_same (mkR_of regs) regs) by (intros r; symmetry; apply E).
  exists Ra, Ft, fc', m'. split; [rewrite E1; reflexivity|].
  split; [exact FR'|]. split; [exact FK|].
  split; [exact (regs_preserved_same _ _ _ _ ESy ES' RP)|].
  rewrite E2. rewrite (HW _ _ m ESy) in MU.
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact TM'|]. split; [exact ST'|].
  exact (HQ _ _ _ _ _ _ ESy ES' PO).
Qed.
