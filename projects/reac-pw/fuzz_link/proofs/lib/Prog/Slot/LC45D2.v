(* Piece d of the C45 brief: op_decide's segment d2 (fuzz_link.c:749, plain image,
   link/ct/dis/plain/LLVMFuzzerTestOneInput.s lines 157-169), from text_of's second return to the call
   of free (own1):

     0x13ab8 mv s3, a0 ; mv a0, s2 ; mv a1, s3 ; jal reac_served_decide (0x16404, ra 0x13ac8)
     0x13ac8 mv s4, a0 ; mv a0, s2 ; mv a1, s3 ; jal model_decide (0x15eac, ra 0x13ad8)
     0x13ad8 mv a1, a0 ; mv a0, s4 ; jal check_verdict (0x15f18, ra 0x13ae4)
     0x13ae4 ld a0, 0x78(sp) ; jal free (0x173d4, ra 0x13aec)

   The two deciders are one `leaf` contract (model_decide_c.v, K 16, writes nothing): each answers
   wz (decide (Some t1v) (Some t2v)) for the two strings text_of answered, so check_verdict's premise
   (a0 = a1, check_verdict_c.v, K 0) holds. The callee contracts are Section hypotheses. Each 16-byte
   leaf frame lies in [sp - 16, sp), so the segment writes only that window of the stack. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf model_decide_c check_verdict_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC45Defs LC45Call LC45DLib.
Local Open Scope Z_scope.

(* the memory facts d2 carries across its three calls *)
Definition d2st (E : lenv) (own1 own2 s1 s2v : Z) (t1v t2v : list byte) (i P N : Z)
    (kbs mbs gbs j0 j1 j2 : list byte) (m : word -> option byte) : Prop :=
  c45_frame E j0 P N m /\
  rw_cells rsegs m (c45_sp E + FO_B40) [C8 (wz own2)] /\
  rw_cells rsegs m (c45_sp E + FO_B40 + 8) [CB 32 j1] /\
  rw_cells rsegs m (c45_sp E + FO_B256) [C8 (wz own1)] /\
  rw_cells rsegs m (c45_sp E + FO_B256 + 8) [CB 248 j2] /\
  cstr_at m s1 t1v /\ cstr_at m s2v t2v /\
  c45_kmg E i kbs mbs gbs m /\ c45_keep E m /\ MemNorm.task_mem rsegs m.

Lemma d2st_carry : forall E lo hi m m' own1 own2 s1 s2v t1v t2v i P N kbs mbs gbs j0 j1 j2,
  d2st E own1 own2 s1 s2v t1v t2v i P N kbs mbs gbs j0 j1 j2 m ->
  dwin E lo hi m m' -> stk rsegs m lo hi -> c45_loc E own1 s1 t1v -> c45_loc E own2 s2v t2v ->
  d2st E own1 own2 s1 s2v t1v t2v i P N kbs mbs gbs j0 j1 j2 m'.
Proof.
  intros E lo hi m m' own1 own2 s1 s2v t1v t2v i P N kbs mbs gbs j0 j1 j2
    (FR & B1 & B2 & B3 & B4 & C1 & C2 & K & KP & T) DW ST L1 L2.
  pose proof DW as (OK & LO & HI & MU & WM).
  refine (conj (dc_frame _ _ _ _ _ DW _ _ _ FR)
         (conj _ (conj _ (conj _ (conj _
         (conj (dc_str _ _ _ _ _ DW _ _ _ L1 C1)
         (conj (dc_str _ _ _ _ _ DW _ _ _ L2 C2)
         (conj (dc_kmg _ _ _ _ _ DW _ _ _ _ KP K)
         (conj (dc_keep _ _ _ _ _ DW KP)
               (dc_task _ _ _ _ _ DW ST T)))))))))).
  all: apply (dc_cells _ _ _ _ _ DW); [assumption | unfold FO_B40, FO_B256; lia].
Qed.

Lemma d2_strs : forall E own1 own2 s1 s2v t1v t2v i P N kbs mbs gbs j0 j1 j2 m,
  d2st E own1 own2 s1 s2v t1v t2v i P N kbs mbs gbs j0 j1 j2 m ->
  cstr_at m s1 t1v /\ cstr_at m s2v t2v /\ cstr_at m A_PREFIX S_PREFIX /\ cstr_at m A_VLAN S_VLAN.
Proof.
  intros until m. intros (_ & _ & _ & _ & _ & C1 & C2 & _ & (_ & _ & (P1 & _ & P3 & _) & _) & _).
  exact (conj C1 (conj C2 (conj P1 P3))).
Qed.

Section Get.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Lemma d_getr10 :
  getr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 10 = a0.
Proof. reflexivity. Qed.
Lemma d_getr11 :
  getr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 11 = a1.
Proof. reflexivity. Qed.
End Get.

Lemma d_dpost_ext : post_ext (fun regs m regs' m' =>
  forall k a, str_arg m (arg regs 0) k -> str_arg m (arg regs 1) a -> getr regs' 10 = wz (decide k a)).
Proof.
  intros r1 r2 m q1 q2 m' E1 E2 H. cbv beta in H |- *. intros k a Hk Ha. unfold arg in *.
  rewrite <- E2. apply H; rewrite E1; assumption.
Qed.

Lemma d_unch_ext : post_ext unchanged.
Proof. intros r1 r2 m q1 q2 m' _ _ H. exact H. Qed.

Section D2.
Hypothesis RSD : reac_served_decide_contract.
Hypothesis MDC : model_decide_contract.
Hypothesis CVC : check_verdict_contract.

(* the side conditions of a leaf call at sp = c45_sp E with lo = S - 65536 *)
Ltac dside :=
  first [ assumption
        | rewrite unsigned_lit by lia;
          first [ assumption | unfold c45_sp, SLOT_FRAME, SLOT_STACK_Z in *; lia ] ].

(* decide's Pre for a0 = s1, a1 = s2v (the two strings text_of answered) *)
Ltac dpre :=
  split; [cbn [str_arg]; rewrite mkR_a0, unsigned_lit by lia; split; assumption|];
  split; [cbn [str_arg]; rewrite mkR_a1, unsigned_lit by lia; split; assumption|];
  split; [intros t Ht; injection Ht as <-; unfold apart_frame; rewrite mkR_sp, mkR_a0, !unsigned_lit by lia;
          left; unfold c45_sp, SLOT_FRAME in *; lia|];
  split; [intros t Ht; injection Ht as <-; unfold apart_frame; rewrite mkR_sp, mkR_a1, !unsigned_lit by lia;
          left; unfold c45_sp, SLOT_FRAME in *; lia|];
  split; assumption.

Lemma c45_d2 : forall E i gp own1 own2 ms, lenv_ok E -> c45_13ab8 E i gp own1 own2 ms ->
  evt rsegs (eqv_cl (c45_post E (ms_mem ms) (c45_13ae8 E i gp own1 own2))) ms.
Proof.
  intros E i gp own1 own2 ms OK H.
  destruct H as (ra & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 & F & fc & m
    & P & N & s1 & s2v & kbs & mbs & gbs & j0 & j1 & j2 & t1v & t2v & EQ & FC & HI & FR & CU & B1 & B2 & B3 & B4
    & N1 & C1 & L1 & N2 & C2 & L2 & KMG & KEEP & MI & TM & ST).
  subst ms. cbn [ms_mem].
  pose proof (d_env E OK) as EV.
  pose proof (d_loc_bound E own1 s1 t1v OK L1) as LB1.
  pose proof (d_loc_bound E own2 s2v t2v OK L2) as LB2.
  assert (SPR : 0 <= c45_sp E < 2 ^ 63) by (unfold c45_sp, SLOT_FRAME; lia).
  assert (D0 : d2st E own1 own2 s1 s2v t1v t2v i P N kbs mbs gbs j0 j1 j2 m)
    by exact (conj FR (conj B1 (conj B2 (conj B3 (conj B4 (conj C1 (conj C2 (conj KMG (conj KEEP TM))))))))).
  clear FR B1 B2 B3 B4 C1 C2 KMG KEEP TM.
  unfold c45_R, wz, C45_TO2_RA.
  do 4 step.
  (* reac_served_decide (a0 = s1, a1 = s2v) *)
  pose proof RSD as HR. unfold reac_served_decide_contract, decide_contract in HR.
  destruct (d2_strs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D0) as (C1 & C2 & PX & PV).
  eapply (c45_leaf_call _ _ _ _ _ HR d_dpost_ext _ (c45_eqv_cl_ext _)) with (lo := e_S E - SLOT_STACK_Z).
  { cbv beta. exists (Some t1v), (Some t2v). dpre. }
  { exact MI. }
  { dside. }
  { dside. }
  { dside. }
  intros ra1 t01 t11 t21 a01 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61 m1 MU1 WM1 MI1 ST1 PO1.
  cbv beta in PO1. unfold writes_nothing in MU1.
  rewrite !(unsigned_lit (c45_sp E)) in MU1, ST1 by lia.
  specialize (PO1 (Some t1v) (Some t2v)). rewrite mkR_a0, mkR_a1, d_getr10 in PO1.
  rewrite !unsigned_lit in PO1 by lia.
  specialize (PO1 (conj N1 C1) (conj N2 C2)).
  pose proof (d2st_carry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D0 (d_dwin16 E m m1 OK MU1 WM1)
                (d_stk16 E m OK ST) L1 L2) as D1.
  clear C1 C2 PX PV.
  rewrite ret_pc_even by (lia || reflexivity).
  do 4 step.
  (* model_decide (a0 = s1, a1 = s2v) *)
  pose proof MDC as HM. unfold model_decide_contract, decide_contract in HM.
  destruct (d2_strs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D1) as (C1 & C2 & PX & PV).
  eapply (c45_leaf_call _ _ _ _ _ HM d_dpost_ext _ (c45_eqv_cl_ext _)) with (lo := e_S E - SLOT_STACK_Z).
  { cbv beta. exists (Some t1v), (Some t2v). dpre. }
  { exact MI1. }
  { dside. }
  { dside. }
  { dside. }
  intros ra2 t02 t12 t22 a02 a12 a22 a32 a42 a52 a62 a72 t32 t42 t52 t62 m2 MU2 WM2 MI2 ST2 PO2.
  cbv beta in PO2. unfold writes_nothing in MU2.
  rewrite !(unsigned_lit (c45_sp E)) in MU2, ST2 by lia.
  specialize (PO2 (Some t1v) (Some t2v)). rewrite mkR_a0, mkR_a1, d_getr10 in PO2.
  rewrite !unsigned_lit in PO2 by lia.
  specialize (PO2 (conj N1 C1) (conj N2 C2)).
  pose proof (d2st_carry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D1 (d_dwin16 E m1 m2 OK MU2 WM2)
                (d_stk16 E m1 OK ST1) L1 L2) as D2.
  clear C1 C2 PX PV.
  rewrite ret_pc_even by (lia || reflexivity).
  do 3 step.
  (* check_verdict (a0 = the first answer, a1 = the second) *)
  pose proof CVC as HV. unfold check_verdict_contract in HV.
  eapply (c45_leaf_call _ _ _ _ _ HV d_unch_ext _ (c45_eqv_cl_ext _)) with (lo := e_S E - SLOT_STACK_Z).
  { cbv beta. rewrite d_getr10, d_getr11, PO1, PO2. reflexivity. }
  { exact MI2. }
  { dside. }
  { dside. }
  { dside. }
  intros ra3 t03 t13 t23 a03 a13 a23 a33 a43 a53 a63 a73 t33 t43 t53 t63 m3 MU3 WM3 MI3 ST3 PO3.
  cbv [unchanged] in PO3. subst m3.
  rewrite ret_pc_even by (lia || reflexivity).
  (* ld a0, 0x78(sp) (own1) ; jal free *)
  destruct D2 as (FR2 & B12 & B22 & B32 & B42 & _ & _ & K2 & KP2 & TM2).
  assert (B3x : rw_cells rsegs m2 (c45_sp E + 120) [C8 (wz own1)]) by exact B32.
  do 2 step.
  apply evt_done. apply c45_eqv_cl_of. unfold c45_post. split.
  - do 17 eexists. exists F, fc, m2, P, N, kbs, mbs, gbs, j0, j1, j2.
    split; [reflexivity|]. split; [exact FC|]. split; [exact HI|]. split; [exact FR2|]. split; [exact CU|].
    split; [exact B12|]. split; [exact B22|]. split; [exact B32|]. split; [exact B42|].
    split; [exact K2|]. split; [exact KP2|]. split; [exact MI2|]. split; [exact TM2|]. exact ST2.
  - apply (d_fp_win E m m2 (c45_sp E - 16)); [unfold c45_sp, SLOT_FRAME, SLOT_STACK_Z; lia | | ].
    + exact (munch_trans _ _ _ _ MU1 MU2).
    + exact (wmono_trans rsegs _ _ _ WM1 WM2).
Qed.

End D2.

Check c45_d2.
Print Assumptions c45_d2.
