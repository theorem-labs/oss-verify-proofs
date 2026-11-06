(* Walking past a `leaf` call (lib/Prog/link_mem.v) inside a segment of the slot, plain image.

   A `leaf` contract gives the register file after the call only up to `regs_preserved`, so the
   walk goes on from the canonical state (lib/Lib/RegisterBridge.v) and its post holds up to
   `ms_eqv`: LDefs.eqv_cl. `leaf_call_eqv` is that step: from the Pre at an `mkR` state at the
   callee's entry to the continuation at the `mkR` state at the return address, where the
   callee-saved words are the caller's and the others are any words. The continuation gets the
   leaf's Post over the actual register map and the fact that it reads as that `mkR` map. *)
From Stdlib Require Import Classical.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs.
Local Open Scope Z_scope.

Lemma xregs_eqv_refl : forall R, xregs_eqv R R.
Proof. intros R r _. reflexivity. Qed.

Lemma xregs_eqv_trans : forall R1 R2 R3, xregs_eqv R1 R2 -> xregs_eqv R2 R3 -> xregs_eqv R1 R3.
Proof. intros R1 R2 R3 H1 H2 r Hr. rewrite (H1 r Hr). exact (H2 r Hr). Qed.

Lemma ms_eqv_refl : forall ms, ms_eqv ms ms.
Proof. intros ms. split; [apply xregs_eqv_refl|]. repeat split; reflexivity. Qed.

Lemma ms_eqv_trans : forall a b c, ms_eqv a b -> ms_eqv b c -> ms_eqv a c.
Proof.
  intros a b c (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  split; [eapply xregs_eqv_trans; eassumption|]. repeat split; congruence.
Qed.

Lemma eqv_cl_intro : forall (P : machine_state -> Prop) ms, P ms -> eqv_cl P ms.
Proof. intros P ms H. exists ms. split; [exact H | apply ms_eqv_refl]. Qed.

Lemma eqv_cl_idem : forall (P : machine_state -> Prop) ms, eqv_cl (eqv_cl P) ms -> eqv_cl P ms.
Proof.
  intros P ms (c & (c0 & H0 & E0) & E). exists c0. split; [exact H0|]. eapply ms_eqv_trans; eassumption.
Qed.

Lemma eqv_cl_mono : forall (P Q : machine_state -> Prop) ms,
  (forall c, P c -> Q c) -> eqv_cl P ms -> eqv_cl Q ms.
Proof. intros P Q ms K (c & H & E). exists c. split; [apply K, H | exact E]. Qed.

(* go on from an eqv-related state: evt (eqv_cl Q) holds of every state ms_eqv to one where it holds *)
Lemma evt_eqv_transport : forall (Q : machine_state -> Prop) c ms,
  ms_eqv c ms -> evt rsegs (eqv_cl Q) c -> evt rsegs (eqv_cl Q) ms.
Proof.
  intros Q c ms E H. pose proof (evt_register_transport rsegs _ c ms E H) as T.
  eapply evt_mono; [exact T|]. intros x Hx. apply eqv_cl_idem. exact Hx.
Qed.

(* chain two segments stated up to ms_eqv *)
Lemma evt_eqv_bind : forall (P Q : machine_state -> Prop) ms,
  evt rsegs (eqv_cl P) ms -> (forall c, P c -> evt rsegs (eqv_cl Q) c) -> evt rsegs (eqv_cl Q) ms.
Proof.
  intros P Q ms H K. eapply evt_cut; [exact H|].
  intros ms' (c & HP & E). exact (evt_eqv_transport Q c ms' E (K c HP)).
Qed.

Lemma evt_eqv_done : forall (Q : machine_state -> Prop) ms, Q ms -> evt rsegs (eqv_cl Q) ms.
Proof. intros Q ms H. apply evt_done, eqv_cl_intro, H. Qed.

(* the segment footprint (LDefs.seg_fp) through the steps of a walk *)
Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn; [tauto|]. rewrite IH. tauto.
Qed.

Lemma seg_fp_refl : forall S hp m, seg_fp S hp m m.
Proof.
  intros S hp m. exists []. split; [apply munch_refl|]. split; [apply wmono_refl|].
  intros x _ H. exfalso. apply H. exact I.
Qed.

Lemma seg_fp_trans : forall S hp m0 m1 m2, seg_fp S hp m0 m1 -> seg_fp S hp m1 m2 -> seg_fp S hp m0 m2.
Proof.
  intros S hp m0 m1 m2 (W1 & M1 & W1m & O1) (W2 & M2 & W2m & O2). exists (W1 ++ W2).
  split; [|split].
  - intros x Hx. apply outside_app in Hx. destruct Hx as [H1 H2]. rewrite (M2 x H2). exact (M1 x H1).
  - eapply wmono_trans; eassumption.
  - intros x Hr Hx. destruct (classic (outside W1 x)) as [H1|H1].
    + apply O2; [exact Hr|]. intros H2. apply Hx. apply outside_app. split; assumption.
    + apply O1; assumption.
Qed.

(* a leaf call whose footprint W (its frame and its Wr) lies in own_w *)
Lemma seg_fp_call : forall S hp m0 m m' W,
  seg_fp S hp m0 m -> munch W m m' -> wmono rsegs m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> own_w S hp x) -> seg_fp S hp m0 m'.
Proof.
  intros S hp m0 m m' W H MU WM O. eapply seg_fp_trans; [exact H|]. exists W. auto.
Qed.

(* a store of the walk's own code *)
Lemma seg_fp_write : forall S hp m0 m (a : Z) (bs : list byte),
  seg_fp S hp m0 m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> own_w S hp x) ->
  seg_fp S hp m0 (write_to_mem m (wa a) bs).
Proof.
  intros S hp m0 m a bs H Ha Hl O. eapply seg_fp_trans; [exact H|].
  exists [(a, a + Z.of_nat (length bs))]. split; [|split].
  - apply munch_write; [apply munch_refl | exact Ha | exact Hl | cbn; left; lia].
  - apply wmono_write, wmono_refl.
  - intros x _ Hx. apply O. cbn in Hx. destruct (classic (a <= x < a + Z.of_nat (length bs))); [exact H0|].
    exfalso. apply Hx. split; [exact H0 | exact I].
Qed.

Lemma reg_get_getr : forall (R : bvmap 5 word) (n : Z), 1 <= n < 32 ->
  reg_get R (Z_to_bv 5 n) = getr R (Z_to_bv 5 n).
Proof.
  intros R n Hn. unfold getr.
  assert (E : bv_eqb (Z_to_bv 5 n) 0 = false).
  { apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32. change (bv_unsigned (0 : bv 5)) with 0. rewrite Z.mod_small; lia. }
  rewrite E. reflexivity.
Qed.

(* the canonical map of a register file that kept the callee-saved words of an mkR map *)
Lemma mkR_of_preserved :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (regs' : bvmap 5 word),
    regs_preserved (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   regs' ->
    mkR_of regs' =
    mkR (reg_get regs' 1) sp gp tp (reg_get regs' 5) (reg_get regs' 6) (reg_get regs' 7) s0 s1
        (reg_get regs' 10) (reg_get regs' 11) (reg_get regs' 12) (reg_get regs' 13) (reg_get regs' 14)
        (reg_get regs' 15) (reg_get regs' 16) (reg_get regs' 17)
        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
        (reg_get regs' 28) (reg_get regs' 29) (reg_get regs' 30) (reg_get regs' 31).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 regs' H.
  unfold mkR_of.
  assert (G : forall n, callee_saved n -> reg_get regs' (Z_to_bv 5 n) =
     getr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          (Z_to_bv 5 n)).
  { intros n Hn. rewrite reg_get_getr by (unfold callee_saved in Hn; lia). apply H, Hn. }
  f_equal.
  all: lazymatch goal with
       | |- reg_get ?R ?k = _ =>
           let z := eval vm_compute in (bv_unsigned k) in
           transitivity (reg_get R (Z_to_bv 5 z)); [reflexivity|];
           rewrite (G z ltac:(unfold callee_saved; lia)); reflexivity
       end.
Qed.

Lemma getr_same_canon : forall (regs : bvmap 5 word) (r : reg), getr regs r = getr (mkR_of regs) r.
Proof.
  intros regs r. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  apply mkR_of_eqv. unfold is_x0. apply Z.eqb_neq. intros H0.
  assert (r = 0%bv) by (apply bv_eq; rewrite H0; reflexivity). subst r.
  rewrite bv_eqb_refl in E. discriminate.
Qed.

(* THE STEP: a call of a `leaf` callee inside a segment stated up to ms_eqv *)
Lemma leaf_call_eqv : forall (pc K : Z) Pre Wr Post (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  leaf pc K Pre Wr Post ->
  Pre (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + K <= bv_unsigned sp -> bv_unsigned sp < 2 ^ 63 ->
  (forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     (exists regs' : bvmap 5 word,
        (forall r, getr regs' r =
           getr (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') r) /\
        Post (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             m regs' m') ->
     munch ((bv_unsigned sp - K, bv_unsigned sp)
            :: Wr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m)
           m m' ->
     wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
     evt rsegs (eqv_cl Q)
       (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs (eqv_cl Q)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros pc K Pre Wr Post Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m lo HL HP MI ST LO SP KC.
  eapply evt_cut; [exact (HL _ F fc m lo HP MI ST LO SP)|].
  intros ms' (regs' & m' & -> & RP & MU & WM & MI' & ST' & PO).
  set (R0 := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) in *.
  pose proof (mkR_of_preserved ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 regs' RP) as EC.
  assert (EQ : ms_eqv (MS (mkR_of regs') F (ret_pc (getr R0 1)) fc None m' (seg_rom rsegs))
                      (MS regs' F (ret_pc (getr R0 1)) fc None m' (seg_rom rsegs))).
  { split; [apply xregs_eqv_sym, mkR_of_eqv|]. repeat split; reflexivity. }
  eapply evt_eqv_transport; [exact EQ|].
  rewrite EC. change (getr R0 1) with ra.
  apply KC; [| exact MU | exact WM | exact MI' | exact ST'].
  exists regs'. split; [| exact PO].
  intros r. rewrite (getr_same_canon regs' r), EC. reflexivity.
Qed.
