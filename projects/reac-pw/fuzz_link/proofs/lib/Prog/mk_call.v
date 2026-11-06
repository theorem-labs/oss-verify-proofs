(* reac-pw/fuzz_link, PLAIN build: calling a `leaf` / `leaf_fp` contract (lib/Prog/link_mem.v) from
   inside a walk over `mkR` registers, and continuing the walk.

   The callee's contract returns a register map `regs'` that agrees with the call's map on the
   callee-saved registers. The walk tactics need `mkR` form, so the call lemmas hand the
   continuation `mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' .. a7' s2 .. s11 t3' .. t6'` (the saved words
   unchanged, the others fresh) and move the result back to `regs'` with
   lib/Lib/RegisterBridge.v (`canonical_contract_transport`). That needs the caller's goal `Q` to be
   closed under register-equivalent states (`q_ext`); `leaf_q_ext` / `leaf_fp_q_ext` give it for
   the two postcondition shapes a walk proves. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_leaf_fp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Regs6ss RegisterBridge.
Local Open Scope Z_scope.

Definition q_ext (Q : machine_state -> Prop) : Prop := forall c a, Q c -> ms_eqv c a -> Q a.

Lemma evt_canon : forall Q R F pc fc rv m ro, q_ext Q ->
  evt rsegs Q (MS (mkR_of R) F pc fc rv m ro) -> evt rsegs Q (MS R F pc fc rv m ro).
Proof.
  intros Q R F pc fc rv m ro HQ H.
  pose proof (canonical_contract_transport rsegs Q (MS R F pc fc rv m ro) H) as T.
  eapply evt_mono; [exact T|]. intros a (c & Hc & HE). exact (HQ c a Hc HE).
Qed.

Lemma leaf_q_ext : forall R0 F rpc fc m0 lo sp0 K W (P : bvmap 5 word -> (word -> option byte) -> Prop),
  (forall q1 q2 m', getr_same q1 q2 -> P q1 m' -> P q2 m') ->
  q_ext (fun ms' => exists (regs' : bvmap 5 word) (m' : word -> option byte),
           ms' = MS regs' F rpc fc None m' (seg_rom rsegs) /\
           regs_preserved R0 regs' /\
           munch ((sp0 - K, sp0) :: W) m0 m' /\
           wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo sp0 /\
           P regs' m').
Proof.
  intros R0 F rpc fc m0 lo sp0 K W P HP c a (regs' & m' & -> & RP & MU & WM & MI & ST & PO) HE.
  destruct a as [Ra Fa pca svca rva fca ma roa].
  destruct HE as (ER & EF & EP & ES & EV & EC & EM & EO). cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending
    ms_resv ms_fcsr ms_mem ms_rom MS] in *. subst Fa pca svca rva fca ma roa.
  assert (E : getr_same regs' Ra) by (intros r; apply getr_eqv, ER).
  exists Ra, m'. split; [reflexivity|].
  split; [exact (regs_preserved_same R0 R0 regs' Ra (fun r => eq_refl) E RP)|].
  repeat (split; [eassumption|]). exact (HP _ _ _ E PO).
Qed.

Lemma leaf_fp_q_ext : forall R0 F rpc m0 lo sp0 K W (P : bvmap 5 word -> (word -> option byte) -> Prop),
  (forall q1 q2 m', getr_same q1 q2 -> P q1 m' -> P q2 m') ->
  q_ext (fun ms' => exists (regs' Ft : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
           ms' = MS regs' Ft rpc fc' None m' (seg_rom rsegs) /\
           frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) /\
           regs_preserved R0 regs' /\
           munch ((sp0 - K, sp0) :: W) m0 m' /\
           wmono rsegs m0 m' /\ mem_inv rsegs m' /\ task_mem rsegs m' /\ stk rsegs m' lo sp0 /\
           P regs' m').
Proof.
  intros R0 F rpc m0 lo sp0 K W P HP c a (regs' & Ft & fc' & m' & -> & FR & FK & RP & MU & WM & MI & TM & ST & PO) HE.
  destruct a as [Ra Fa pca svca rva fca ma roa].
  destruct HE as (ER & EF & EP & ES & EV & EC & EM & EO). cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending
    ms_resv ms_fcsr ms_mem ms_rom MS] in *. subst Fa pca svca rva fca ma roa.
  assert (E : getr_same regs' Ra) by (intros r; apply getr_eqv, ER).
  exists Ra, Ft, fc', m'. split; [reflexivity|].
  split; [exact FR|]. split; [exact FK|].
  split; [exact (regs_preserved_same R0 R0 regs' Ra (fun r => eq_refl) E RP)|].
  repeat (split; [eassumption|]). exact (HP _ _ _ E PO).
Qed.

(* the callee-saved words of a map that `regs_preserved` keeps from an `mkR` map *)
Section Saved.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Let R := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Lemma canon_of_preserved : forall regs', regs_preserved R regs' ->
  mkR_of regs' = mkR (reg_get regs' 1) sp gp tp (reg_get regs' 5) (reg_get regs' 6) (reg_get regs' 7) s0 s1
                     (reg_get regs' 10) (reg_get regs' 11) (reg_get regs' 12) (reg_get regs' 13)
                     (reg_get regs' 14) (reg_get regs' 15) (reg_get regs' 16) (reg_get regs' 17)
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                     (reg_get regs' 28) (reg_get regs' 29) (reg_get regs' 30) (reg_get regs' 31).
Proof.
  intros regs' RP.
  assert (C : forall r, callee_saved r -> reg_get regs' (Z_to_bv 5 r) = reg_get R (Z_to_bv 5 r)).
  { intros r Hr. pose proof (RP r Hr) as H. unfold YK11.getr in H. unfold callee_saved in Hr.
    replace (bv_eqb (Z_to_bv 5 r) 0) with false in H; [exact H|].
    symmetry. unfold bv_eqb. rewrite Z_to_bv_unsigned. apply Z.eqb_neq. unfold bv_wrap.
    change (bv_modulus 5) with 32. rewrite Z.mod_small by lia.
    intros E. assert (Z0 : bv_unsigned (0 : bv 5) = 0) by (vm_compute; reflexivity). rewrite Z0 in E. lia. }
  unfold mkR_of. f_equal;
    match goal with |- reg_get regs' ?l = _ =>
      let z := eval vm_compute in (bv_unsigned l) in exact (C z ltac:(unfold callee_saved; lia)) end.
Qed.
End Saved.

Lemma leaf_call : forall pcC KC PreC WrC PostC, leaf pcC KC PreC WrC PostC -> post_ext PostC ->
  forall Q, q_ext Q ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc m lo,
  PreC (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + KC <= bv_unsigned sp -> bv_unsigned sp < 2 ^ 63 ->
  (forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
     munch ((bv_unsigned sp - KC, bv_unsigned sp)
            :: WrC (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m)
           m m' ->
     wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
     PostC (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m
           (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           m' ->
     evt rsegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 pcC) fc None m (seg_rom rsegs)).
Proof.
  intros pcC KC PreC WrC PostC HC HPE Q HQ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
    s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo HPre MI ST LO SP K.
  eapply evt_cut; [exact (HC _ F fc m lo HPre MI ST LO SP)|].
  intros ms' (regs' & m' & -> & RP & MU & WM & MI' & ST' & PO).
  apply evt_canon; [exact HQ|].
  pose proof (mkR_of_same regs') as ES.
  rewrite (canon_of_preserved ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 regs' RP) in ES |- *.
  apply K; try assumption.
  exact (HPE _ _ _ _ _ _ (fun r => eq_refl) ES PO).
Qed.

Lemma leaf_fp_call : forall pcC KC PreC WrC PostC, leaf_fp pcC KC PreC WrC PostC -> post_ext PostC ->
  forall Q, q_ext Q ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc m lo,
  PreC (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m ->
  mem_inv rsegs m -> task_mem rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> lo + KC <= bv_unsigned sp -> bv_unsigned sp < 2 ^ 63 -> frm0 fc ->
  A_IMG_TOP <= lo ->
  bytes_at rsegs m A_GOT_GUARD (le8 (wz A_GUARD)) -> (exists c, bytes_at rsegs m A_GUARD (le8 c)) ->
  (forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m',
     frm0 fc' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) ->
     munch ((bv_unsigned sp - KC, bv_unsigned sp)
            :: WrC (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m)
           m m' ->
     wmono rsegs m m' -> mem_inv rsegs m' -> task_mem rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
     PostC (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m
           (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           m' ->
     evt rsegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     Ft (ret_pc ra) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 pcC) fc None m (seg_rom rsegs)).
Proof.
  intros pcC KC PreC WrC PostC HC HPE Q HQ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
    s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo HPre MI TM ST LO SP FRM ITOP GG GQ K.
  eapply evt_cut; [exact (HC _ F fc m lo HPre MI TM ST LO SP FRM ITOP GG GQ)|].
  intros ms' (regs' & Ft & fc' & m' & -> & FR & FK & RP & MU & WM & MI' & TM' & ST' & PO).
  apply evt_canon; [exact HQ|].
  pose proof (mkR_of_same regs') as ES.
  rewrite (canon_of_preserved ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 regs' RP) in ES |- *.
  apply K; try assumption.
  exact (HPE _ _ _ _ _ _ (fun r => eq_refl) ES PO).
Qed.
