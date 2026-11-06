(* Arm c2 (op_mark), piece B: the walk's tools. c2b_call runs one `leaf` call from the slot's frame
   (sp = S - 480, stack floor S - 65536) and continues in the canonical mkR form (the callee-saved words
   kept, the others read out of the callee's register file); c2b_ex_done / c2b_lh_done close the walk at
   L_EXIT / L_LH; c2b_tail is the code after check_requests (0x13dd8 .. 0x14078). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem check_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC2Defs LC2BSpec.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Readings of a register file written as mkR
   ========================================================================== *)

Section Get.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Lemma c2b_g1 :
  getr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 1 = ra.
Proof. reflexivity. Qed.
Lemma c2b_g10 :
  getr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 10 = a0.
Proof. reflexivity. Qed.
Lemma c2b_g11 :
  getr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 11 = a1.
Proof. reflexivity. Qed.
Lemma c2b_arg0 :
  arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 0
  = bv_unsigned a0.
Proof. reflexivity. Qed.
Lemma c2b_arg1 :
  arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 1
  = bv_unsigned a1.
Proof. reflexivity. Qed.
Lemma c2b_spZ :
  spZ (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
  = bv_unsigned sp.
Proof. reflexivity. Qed.
End Get.

(* check_mark's premise: a0 = the library's code, a1 = the model's *)
Lemma c2b_mark_pre : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                             t3 t4 t5 t6 : word) (x y : Z),
  same_rc x y = true -> - 2 ^ 31 <= x < 2 ^ 31 ->
  same_rc_regs (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 x) (Z_to_bv 64 y) a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
Proof.
  intros. unfold same_rc_regs. rewrite c2b_g10, c2b_g11. unfold wz. apply c2b_rc_regs; assumption.
Qed.

(* ==========================================================================
   2. One leaf call from the slot's frame
   ========================================================================== *)

Ltac c2b_rp RP :=
  lazymatch goal with |- reg_get _ ?k = _ =>
    let z := eval vm_compute in (bv_unsigned k) in
    exact (RP z ltac:(unfold callee_saved; lia))
  end.

Lemma c2b_call : forall (pc K : Z) Pre Wr Post, leaf pc K Pre Wr Post ->
  forall (E : lenv) (m0 : word -> option byte) (Q : machine_state -> Prop)
    (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  lenv_ok E -> 0 <= K <= 65056 ->
  Pre (mkR ra (Z_to_bv 64 (e_S E - SLOT_FRAME)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m ->
  mem_inv rsegs m -> stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  (forall (regs' : bvmap 5 word) (m' : word -> option byte),
     munch ((e_S E - SLOT_FRAME - K, e_S E - SLOT_FRAME) ::
            Wr (mkR ra (Z_to_bv 64 (e_S E - SLOT_FRAME)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m) m m' ->
     wmono rsegs m m' -> mem_inv rsegs m' ->
     stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
     Post (mkR ra (Z_to_bv 64 (e_S E - SLOT_FRAME)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m regs' m' ->
     evt rsegs (c2_post E m0 Q)
       (MS (mkR (reg_get regs' 1) (Z_to_bv 64 (e_S E - SLOT_FRAME)) gp tp
                (reg_get regs' 5) (reg_get regs' 6) (reg_get regs' 7) s0 s1
                (reg_get regs' 10) (reg_get regs' 11) (reg_get regs' 12) (reg_get regs' 13)
                (reg_get regs' 14) (reg_get regs' 15) (reg_get regs' 16) (reg_get regs' 17)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (reg_get regs' 28) (reg_get regs' 29) (reg_get regs' 30) (reg_get regs' 31))
           F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs (c2_post E m0 Q)
    (MS (mkR ra (Z_to_bv 64 (e_S E - SLOT_FRAME)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros pc K Pre Wr Post HL E m0 Q ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
    s10 s11 t3 t4 t5 t6 F fc m HE HK HP MI ST KC.
  destruct (c2b_env E HE) as (HS & _).
  assert (SP : spZ (mkR ra (Z_to_bv 64 (e_S E - SLOT_FRAME)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) = e_S E - SLOT_FRAME).
  { rewrite c2b_spZ. apply unsigned_lit. unfold SLOT_FRAME. lia. }
  eapply evt_cut.
  - refine (HL _ F fc m (e_S E - SLOT_STACK_Z) HP MI _ _ _); rewrite SP.
    + exact ST.
    + unfold SLOT_STACK_Z, SLOT_FRAME. lia.
    + unfold SLOT_FRAME. lia.
  - intros ms' (regs' & m' & EQ & RP & MU & WM & MI' & ST' & PO). subst ms'.
    rewrite SP in MU, ST'. rewrite c2b_g1.
    pose proof (KC regs' m' MU WM MI' ST' PO) as T.
    assert (EQV : ms_eqv
      (MS (mkR (reg_get regs' 1) (Z_to_bv 64 (e_S E - SLOT_FRAME)) gp tp
               (reg_get regs' 5) (reg_get regs' 6) (reg_get regs' 7) s0 s1
               (reg_get regs' 10) (reg_get regs' 11) (reg_get regs' 12) (reg_get regs' 13)
               (reg_get regs' 14) (reg_get regs' 15) (reg_get regs' 16) (reg_get regs' 17)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               (reg_get regs' 28) (reg_get regs' 29) (reg_get regs' 30) (reg_get regs' 31))
          F (ret_pc ra) fc None m' (seg_rom rsegs))
      (MS regs' F (ret_pc ra) fc None m' (seg_rom rsegs))).
    { split; [|repeat split]. cbn [ms_regs MS].
      apply xregs_eqv_sym. apply mkR_eqv_of; first [ reflexivity | c2b_rp RP ]. }
    pose proof (evt_register_transport rsegs _ _ _ EQV T) as T2.
    eapply evt_mono; [exact T2|].
    intros a (c & (c' & (HQ & FP) & E1) & E2).
    exists c'. split; [split; [exact HQ | exact FP] | exact (c2_ms_eqv_trans _ _ _ E1 E2)].
Qed.

Ltac c2b_retpc :=
  match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

(* a callee frame of K bytes below sp = S - 480 lies in the window c2b_W S *)
Ltac c2b_weaken MU :=
  eapply munch_weaken; [| exact MU]; unfold sub_fp, c2b_W; cbn [outside];
  intros ?x [?Hx _]; split; [unfold SLOT_FRAME in *; lia | exact I].

(* ==========================================================================
   3. The two ends of the walk
   ========================================================================== *)

Lemma c2b_ex_done : forall (E : lenv) (gp : word) (m0 m : word -> option byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 pc : word)
    (F : bvmap 5 word) (fc : bv 32) (P N : Z) (j0 j1 j2 : list byte) (Q : machine_state -> Prop),
  pc = Z_to_bv 64 L_EXIT -> frm0 fc -> c2_frame E P N j0 j1 j2 m ->
  bytes_at rsegs m (e_S E - 104) (e_saved E) -> wr_at rsegs m A_ERRNO 4 -> guard_m m -> la_ok m ->
  mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  seg_fp (e_S E) (c2_hp E) m0 m ->
  (forall c, ex_ms E gp c -> Q c) ->
  evt rsegs (c2_post E m0 Q)
    (MS (mkR ra (Z_to_bv 64 (e_S E - SLOT_FRAME)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (e_md E)) s1
             a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (e_mk E)) s8 s9 s10 s11 t3 t4 t5 t6)
        F pc fc None m (seg_rom rsegs)).
Proof.
  intros E gp m0 m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 pc F fc
    P N j0 j1 j2 Q -> FC FR SV ER GD LA MI TM ST FP HQ.
  apply evt_done.
  match goal with |- c2_post _ _ _ ?st => exists st end.
  split; [split; [apply HQ | exact FP] | apply c2_ms_eqv_refl].
  unfold c2_frame in FR. destruct (rw_cells_forget _ _ _ _ FR) as (j & HJ).
  unfold ex_ms.
  exists ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s1, s2, s3, s4, s5, s6, s8, s9, s10, s11, t3, t4, t5,
    t6, F, fc, m, j.
  split; [reflexivity|]. split; [exact FC|]. split; [exact HJ|].
  split; [exact SV|]. split; [exact ER|]. split; [exact GD|]. split; [exact LA|]. split; [exact MI|].
  split; [exact TM|].
  exact ST.
Qed.

Lemma c2b_lh_done : forall (E : lenv) (i : Z) (gp : word) (m0 m : word -> option byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s11 t3 t4 t5 t6 pc : word)
    (F : bvmap 5 word) (fc : bv 32) (P N : Z) (j0 j1 j2 kbs mbs gbs : list byte) (Q : machine_state -> Prop),
  0 <= i < 47 -> 1 <= N -> s2 = Z_to_bv 64 N -> s11 = Z_to_bv 64 (i + 1) -> pc = Z_to_bv 64 L_LH ->
  frm0 fc -> c2_frame E P N j0 j1 j2 m -> c2b_rest E (i + 1) P N kbs mbs gbs m ->
  mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  seg_fp (e_S E) (c2_hp E) m0 m ->
  (forall c, (i < 47 /\ lh_ms E (i + 1) gp c) -> Q c) ->
  evt rsegs (c2_post E m0 Q)
    (MS (mkR ra (Z_to_bv 64 (e_S E - SLOT_FRAME)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (e_md E))
             (Z_to_bv 64 GNL40) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 46) (Z_to_bv 64 A_JT)
             (Z_to_bv 64 (e_mk E)) (Z_to_bv 64 0xab) (Z_to_bv 64 4) (Z_to_bv 64 (e_md E + MD_N_REQ))
             s11 t3 t4 t5 t6)
        F pc fc None m (seg_rom rsegs)).
Proof.
  intros E i gp m0 m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s11 t3 t4 t5 t6 pc F fc P N j0 j1 j2
    kbs mbs gbs Q Hi HN -> -> -> FC FR REST MI TM ST FP HQ.
  apply evt_done.
  match goal with |- c2_post _ _ _ ?st => exists st end.
  split; [split; [apply HQ; split; [lia|] | exact FP] | apply c2_ms_eqv_refl].
  unfold lh_ms.
  exists ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s3, s4, t3, t4, t5, t6, F, fc, m, P, N, kbs, mbs, gbs.
  split; [reflexivity|]. split; [exact FC|]. split; [lia|]. split; [lia|].
  split; [|split; [exact MI | split; [exact TM | exact ST]]].
  split; [exists j0, j1, j2, N; exact FR | exact REST].
Qed.

(* ==========================================================================
   4. 0x13dd8 .. 0x14078: `bltu s5, s11` (46 < i: exit); j 0x1406c; ld s2, 0x48(sp) (= N);
      addiw s11, s11, 1; bnez s2 (the loop head of i + 1); j 0x1413c (the exit)
   ========================================================================== *)

Lemma c2b_tail : forall (E : lenv) (i : Z) (gp : word) (m0 m : word -> option byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (P N : Z) (j0 j1 j2 kbs mbs gbs : list byte),
  lenv_ok E -> 0 <= i <= 47 -> frm0 fc ->
  c2_frame E P N j0 j1 j2 m -> c2b_rest E (i + 1) P N kbs mbs gbs m ->
  mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  seg_fp (e_S E) (c2_hp E) m0 m ->
  evt rsegs (c2_post E m0 (fun c => (i < 47 /\ lh_ms E (i + 1) gp c) \/ ex_ms E gp c))
    (MS (mkR ra (Z_to_bv 64 (e_S E - SLOT_FRAME)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (e_md E))
             (Z_to_bv 64 GNL40) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 46) (Z_to_bv 64 A_JT)
             (Z_to_bv 64 (e_mk E)) (Z_to_bv 64 0xab) (Z_to_bv 64 4) (Z_to_bv 64 (e_md E + MD_N_REQ))
             (Z_to_bv 64 i) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13dd8) fc None m (seg_rom rsegs)).
Proof.
  intros E i gp m0 m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 F fc P N j0 j1 j2 kbs mbs gbs
    HE Hi FC FR REST MI TM ST FP.
  pose proof (c2b_rest_N E (i + 1) P N kbs mbs gbs m HE REST) as HN.
  destruct (c2b_rest_ex E (i + 1) P N kbs mbs gbs m REST) as (SV & ER & GD).
  pose proof (c2b_rest_la E (i + 1) P N kbs mbs gbs m REST) as LA.
  destruct (c2b_env E HE) as (HS1 & _).
  assert (SF : SLOT_FRAME = 480) by reflexivity.
  pose proof FR as FR'. unfold c2_frame, lh_cells, wz in FR'.
  step.
  if_cases HC.
  - eapply c2b_ex_done; [reflexivity | exact FC | exact FR | exact SV | exact ER | exact GD | exact LA
                        | exact MI | exact TM | exact ST | exact FP | intros c Hc; right; exact Hc].
  - zify_cond HC. rewrite ?unsigned_lit in HC by lia.
    step. step. step. step.
    if_cases HC2.
    + zify_cond HC2. rewrite ?unsigned_lit in HC2 by lia.
      eapply c2b_lh_done with (i := i) (N := N) (P := P) (j0 := j0) (j1 := j1) (j2 := j2)
                              (kbs := kbs) (mbs := mbs) (gbs := gbs);
        [lia | lia | reflexivity | apply c2b_addiw; lia | reflexivity | exact FC | exact FR
        | exact REST | exact MI | exact TM | exact ST | exact FP
        | intros c Hc; left; exact Hc].
    + step.
      eapply c2b_ex_done; [reflexivity | exact FC | exact FR | exact SV | exact ER | exact GD | exact LA
                          | exact MI | exact TM | exact ST | exact FP | intros c Hc; right; exact Hc].
Qed.
