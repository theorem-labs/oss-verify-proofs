(* Arm c2 (op_mark) of the slot LLVMFuzzerTestOneInput, plain image, piece DECIDE: from c2_1407c (model_read
   answered 0) to c2_13da4 (model_mark is done) or c2_140d4 (model_remember is next).
   The code (link/ct/dis/plain/LLVMFuzzerTestOneInput.s):
     0x1407c  addi a0, sp, 0x50; addi a1, sp, 0x78; jal model_decide (ra 0x14088)
     0x14088  mv s3, a0; li a0, 1; beq s3, a0, 0x140b4; bnez s3, 0x13da4
     0x14098  a2 = 0x10341 ("reac-pw:served"); mv a0, s0; mv a1, s2; jal model_write (ra 0x140ac)
     0x140ac  bnez a0, 0x13da0; j 0x140d4
     0x140b4  a0 = sp + 0x78; a1 = 0x10341; li a2, 15; jal bcmp (ra 0x140c8)
     0x140c8  beqz a0, 0x140d4; li s3, 1; j 0x13da4
     0x13da0  mv s3, a0  (then 0x13da4)
   The three callees enter as Section hypotheses (their contracts lib/Prog/model_decide_c.v, bcmp_c.v,
   model_write_c.v). The lemmas the walk uses are in LC2DecCall.v (calling a `leaf`) and LC2DecLib.v (the
   memory facts across a call, the pure facts). *)
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem model_decide_c bcmp_c model_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC2Defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import mk_leaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LC2DecCall LC2DecLib.
Local Open Scope Z_scope.

(* ==========================================================================
   The two ends of the piece
   ========================================================================== *)

Lemma c2d_post13 : forall E i gp s m0 m F fc P N j0 j1 j2 kbs mbs gbs
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (v3 : Z) R pc,
  R = mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
          a0 a1 a2 a3 a4 a5 a6 a7 (wz (sel_ptr s)) (wz v3) s4 (wz 46) (wz A_JT) (wz (e_mk E))
          (wz 0xab) (wz 4) (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6 ->
  pc = wz 0x13da4 ->
  v3 = m_rc (c2_MM s kbs gbs) ->
  frm0 fc -> 0 <= i <= 47 -> 0 <= s <= 255 ->
  c2d_rest E i s P N j0 j1 j2 kbs gbs m -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  model_at m (e_md E) mbs -> model_wf mbs ->
  md_reqs mbs = m_reqs (c2_MM s kbs gbs) -> md_marks mbs = m_marks (c2_MM s kbs gbs) ->
  munch (c2d_W E) m0 m -> wmono rsegs m0 m ->
  evt rsegs (c2_post E m0 (fun c => c2_13da4 E i gp s c \/ c2_140d4 E i gp s c))
      (MS R F pc fc None m (seg_rom rsegs)).
Proof.
  intros E i gp s m0 m F fc P N j0 j1 j2 kbs mbs gbs ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 v3 R pc
    -> -> -> FRM Hi Hs RST MI TM ST MA MW MRQ MMK MU WM.
  match goal with |- evt _ _ ?st => apply evt_done; exists st end.
  split; [split | apply c2_ms_eqv_refl].
  - left. unfold c2_13da4.
    exists ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s4, t3, t4, t5, t6, F, fc, m, P, N, j0, j1, j2, kbs, mbs, gbs.
    pose proof RST as (FR & SV & GN & OD & PO & LA & TX & IP & ER & GU & CU & NM & KN & MK).
    split; [reflexivity|]. split; [exact FRM|]. split; [exact Hi|]. split; [exact Hs|]. split; [exact FR|].
    split; [exact (c2d_fix_of _ _ _ _ _ _ _ _ _ _ _ RST MI TM ST)|].
    split; [exact CU|]. split; [exact NM|]. split; [exact KN|]. split; [exact MK|].
    split; [exact MA|]. split; [exact MW|]. split; [exact MRQ | exact MMK].
  - exact (c2d_seg_fp E m0 m MU WM).
Qed.

Lemma c2d_post14 : forall E i gp s m0 m F fc P N j0 j1 j2 kbs mbs gbs t
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (v3 : Z) R pc,
  R = mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
          a0 a1 a2 a3 a4 a5 a6 a7 (wz (sel_ptr s)) (wz v3) s4 (wz 46) (wz A_JT) (wz (e_mk E))
          (wz 0xab) (wz 4) (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6 ->
  pc = wz 0x140d4 ->
  v3 = m_rc (c2_MM s kbs gbs) ->
  frm0 fc -> 0 <= i <= 47 -> 0 <= s <= 255 -> sel_name s = Some t -> t <> [] ->
  c2d_rest E i s P N j0 j1 j2 kbs gbs m -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  model_at m (e_md E) mbs -> model_wf mbs -> marks_are gbs mbs ->
  md_reqs mbs = m_reqs (c2_MM s kbs gbs) -> m_marks (c2_MM s kbs gbs) = remember (mk_names gbs) t ->
  munch (c2d_W E) m0 m -> wmono rsegs m0 m ->
  evt rsegs (c2_post E m0 (fun c => c2_13da4 E i gp s c \/ c2_140d4 E i gp s c))
      (MS R F pc fc None m (seg_rom rsegs)).
Proof.
  intros E i gp s m0 m F fc P N j0 j1 j2 kbs mbs gbs t ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 v3 R pc
    -> -> -> FRM Hi Hs Hst Htn RST MI TM ST MA MW MAR MRQ MMK MU WM.
  match goal with |- evt _ _ ?st => apply evt_done; exists st end.
  split; [split | apply c2_ms_eqv_refl].
  - right. unfold c2_140d4.
    exists ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s4, t3, t4, t5, t6, F, fc, m, P, N, j0, j1, j2, kbs, mbs, gbs, t.
    pose proof RST as (FR & SV & GN & OD & PO & LA & TX & IP & ER & GU & CU & NM & KN & MK).
    split; [reflexivity|]. split; [exact FRM|]. split; [exact Hi|]. split; [exact Hs|].
    split; [exact Hst|]. split; [exact Htn|]. split; [exact FR|].
    split; [exact (c2d_fix_of _ _ _ _ _ _ _ _ _ _ _ RST MI TM ST)|].
    split; [exact CU|]. split; [exact NM|]. split; [exact KN|]. split; [exact MK|].
    split; [exact MA|]. split; [exact MW|]. split; [exact MAR|]. split; [exact MRQ | exact MMK].
  - exact (c2d_seg_fp E m0 m MU WM).
Qed.

(* a pointer the interface table holds, read back from memory with any high bits, is apart from the
   callee's frame *)
Lemma c2d_apart_ptr : forall p q n lo hi, p mod 2 ^ 64 = q -> 0 <= q -> q + n <= lo -> 0 <= n ->
  lo <= hi -> hi < 2 ^ 64 -> p + n <= lo \/ hi <= p.
Proof.
  intros p q n lo hi Hq Q0 Qn N0 LH H64.
  pose proof (Z.div_mod p (2 ^ 64) ltac:(lia)) as D. pose proof (Z.mod_pos_bound p (2 ^ 64) ltac:(lia)) as B.
  destruct (Z.lt_trichotomy (p / 2 ^ 64) 0) as [K|[K|K]].
  - left. nia.
  - left. rewrite K in D. lia.
  - right. nia.
Qed.

Lemma c2d_bveqb_nz : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> z <> 0 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof.
  intros z R NZ. unfold bv_eqb. apply Z.eqb_neq. intros H. apply NZ. apply c2d_wz_zero; [exact R|].
  unfold wz. rewrite H. reflexivity.
Qed.

(* closed `bv_unsigned (Z_to_bv 64 e)` to its numeral *)
Ltac c2d_cl :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
    tryif (match z with context [?x] => is_var x end) then fail
    else (let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 z)) in change (bv_unsigned (Z_to_bv 64 z)) with v)
  end.

Ltac c2d_cl_in H :=
  repeat match type of H with context [bv_unsigned (Z_to_bv 64 ?z)] =>
    tryif (match z with context [?x] => is_var x end) then fail
    else (let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 z)) in change (bv_unsigned (Z_to_bv 64 z)) with v in H)
  end.

Ltac c2d_ret :=
  match goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

Section D.
Hypothesis MODEL_DECIDE_OK : model_decide_contract.
Hypothesis BCMP_OK : bcmp_contract.
Hypothesis MODEL_WRITE_OK : model_write_contract.

Lemma c2_dec : forall (E : lenv) (i : Z) (gp : word) (s : Z) (ms : machine_state),
  lenv_ok E -> c2_1407c E i gp s ms ->
  evt rsegs (c2_post E (ms_mem ms) (fun c => c2_13da4 E i gp s c \/ c2_140d4 E i gp s c)) ms.
Proof.
  intros E i gp s ms LE H.
  destruct H as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 & F & fc &
                 m & P & N & j0 & j1 & j2 & kbs & mbs & gbs & t & -> & FRM & Hi & Hs & Hst & Htn & FR & FX & CU & NM &
                 KN & MK & Hrc & MA & MW & MAR & MKS & MRQ & CK & CA).
  match goal with |- evt _ (c2_post _ ?m0 _) _ => change m0 with m end.
  pose proof (c2d_rest_of E i s P N j0 j1 j2 kbs gbs m FR FX CU NM KN MK) as RST.
  pose proof FX as (SV & GN & OD & PO & LA & TX & IP & ER & GU & MI & TM & ST).
  destruct (c2d_frame_j2 E P N j0 j1 j2 m FR) as [J2B J2L].
  pose proof (c2d_alias_len t kbs) as ALn.
  assert (PF : firstn (S (length (r_alias (c2_rd t kbs)))) j2 = r_alias (c2_rd t kbs) ++ [zb 0]).
  { apply (c2d_prefix m (e_S E - SLOT_FRAME + FO_B256)); [exact CA | exact J2B | lia]. }
  pose proof (proj2 CA) as NNa.
  assert (SPB : 0x10000 <= sel_ptr s /\ sel_ptr s + Z.of_nat (length t) + 1 <= 0x960e0 /\ (length t <= 11)%nat).
  { destruct NM as [_ SB]. destruct (SB t Hst) as (Lt & Pl & _).
    destruct Pl as [(P1 & P2) | (k & Hk & Ek & Lk)]; unfold A_RO_LO, A_RO_END, A_G_NAMES in *; lia. }
  assert (SK : str_arg m (e_S E - SLOT_FRAME + 80) (Some (r_kind (c2_rd t kbs)))) by (split; [c2d_lia LE | exact CK]).
  assert (SAl : str_arg m (e_S E - SLOT_FRAME + 120) (Some (r_alias (c2_rd t kbs)))) by (split; [c2d_lia LE | exact CA]).
  unfold wz.
  (* 0x1407c - 0x14084: the two buffers, then model_decide *)
  step. step. step.
  pose proof MODEL_DECIDE_OK as HD. unfold model_decide_contract, decide_contract in HD.
  eapply (c2d_leaf_call _ _ _ _ _ HD) with (lo := e_S E - SLOT_STACK_Z).
  { intros r1 r2 mm q1 q2 mm' E1 E2 Hq k a Hk Ha. unfold getr_same in E1, E2. unfold arg in *. rewrite <- E2.
    apply Hq; [rewrite E1; exact Hk | rewrite E1; exact Ha]. }
  { apply c2d_post_ext. }
  { exists (Some (r_kind (c2_rd t kbs))), (Some (r_alias (c2_rd t kbs))).
    unfold apart_frame. rewrite c2d_arg0, c2d_arg1, c2d_spZ.
    rewrite !unsigned_lit by c2d_lia LE.
    split; [exact SK|]. split; [exact SAl|].
    split; [intros t7 Ht7; right; c2d_lia LE|].
    split; [intros t7 Ht7; right; c2d_lia LE|].
    pose proof PO as (P1 & P2 & P3 & P4). split; [exact P1 | exact P3]. }
  { exact MI. }
  { rewrite unsigned_lit by c2d_lia LE. exact ST. }
  { rewrite unsigned_lit by c2d_lia LE. c2d_lia LE. }
  { rewrite unsigned_lit by c2d_lia LE. c2d_lia LE. }
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 MU1 WM1 MI1 ST1 PD.
  assert (A0 : a0' = wz (decide (Some (r_kind (c2_rd t kbs))) (Some (r_alias (c2_rd t kbs))))).
  { rewrite <- (PD _ _); [reflexivity | |].
    - rewrite c2d_arg0, unsigned_lit by c2d_lia LE. exact SK.
    - rewrite c2d_arg1, unsigned_lit by c2d_lia LE. exact SAl. }
  subst a0'.
  (* model_decide wrote only its frame below sp *)
  rewrite !unsigned_lit in MU1, ST1 by c2d_lia LE. unfold writes_nothing in MU1.
  assert (AVd : c2d_avoid E [(e_S E - SLOT_FRAME - 16, e_S E - SLOT_FRAME)]).
  { intros x Hx Hn. apply c2d_not_out1 in Hn. left. c2d_lia LE. }
  assert (MVd : c2d_mv E [(e_S E - SLOT_FRAME - 16, e_S E - SLOT_FRAME)] m m1)
    by (split; [exact LE | split; [exact MU1 | split; [exact WM1 | exact AVd]]]).
  pose proof (c2d_rest_tr _ _ _ _ MVd _ _ _ _ _ _ _ _ _ RST) as RST1.
  pose proof (c2d_task_tr _ _ _ _ MVd TM) as TM1.
  pose proof (c2d_munch_W _ _ _ _ AVd MU1) as MUc1.
  assert (MA1 : model_at m1 (e_md E) mbs).
  { destruct MA as [U L]. split; [|exact L]. apply (u8arr_transport rsegs _ m m1 _ _ U MU1 WM1).
    cbn [disjoint_from]. rewrite L. split; [c2d_lia LE | exact I]. }
  pose proof RST1 as (FR1 & SV1 & GN1 & OD1 & PO1 & LA1 & TX1 & IP1 & ER1 & GU1 & CU1 & NM1 & KN1 & MK1).
  destruct (decide_cases (Some (r_kind (c2_rd t kbs))) (Some (r_alias (c2_rd t kbs)))) as [V|[V|[V|V]]].
  - (* V_MARK: model_write (m, name, "reac-pw:served") *)
    rewrite V. unfold V_MARK, wz. c2d_ret.
    step. step. step. if_false. step. if_false. step. step. step. step. step.
    pose proof MODEL_WRITE_OK as HW. unfold model_write_contract in HW.
    pose proof KN1 as (NL1 & WF1 & TB1 & _).
    pose proof PO1 as (Q1 & Q2 & Q3 & Q4).
    assert (NMS1 : str_arg m1 (sel_ptr s) (sel_name s)) by exact (proj1 NM1).
    assert (SRV1 : str_arg m1 A_SERVED (Some S_SERVED)) by (split; [unfold A_SERVED; lia | exact Q2]).
    eapply (c2d_leaf_call _ _ _ _ _ HW) with (lo := e_S E - SLOT_STACK_Z).
    { intros r1 r2 mm q1 q2 mm' E1 E2 Hq. unfold getr_same in E1, E2.
      assert (A : forall k, arg r1 k = arg r2 k) by (intros k; unfold arg; rewrite E1; reflexivity).
      intros mb kb tb nm al H1 H2 H3 H4 H5. rewrite <- !A in H1, H4, H5 |- *. rewrite <- E2.
      exact (Hq mb kb tb nm al H1 H2 H3 H4 H5). }
    { apply c2d_post_ext. }
    { exists mbs, kbs, link_tab, (sel_name s), (Some S_SERVED).
      unfold frame_apart_gnl, apart_frame. rewrite c2d_arg0, c2d_arg1, c2d_arg2, !c2d_spZ.
      c2d_cl. rewrite !unsigned_lit by c2d_lia LE.
      split; [exact MA1|]. split; [exact MW|]. split; [exact NL1|].
      split; [unfold apart_gnl, A_G_NL, NK_SIZE; right; c2d_lia LE|].
      split; [exact WF1|]. split; [exact TB1|]. split; [exact NMS1|]. split; [exact SRV1|].
      split; [unfold apart_gnl, A_G_NL, NK_SIZE; c2d_lia LE|].
      split; [left; c2d_lia LE|].
      split; [intros s0 Hs0; rewrite Hst in Hs0; injection Hs0 as Hs0; subst s0; left; c2d_lia LE|].
      split; [intros s0 Hs0; injection Hs0 as Hs0; subst s0; left; c2d_zn; c2d_lia LE|].
      split.
      { intros s0 Hs0; injection Hs0 as Hs0; subst s0. exists []. split.
        - apply bytes_at_nil. c2d_zn. lia.
        - c2d_zn. apply Z.leb_le. vm_compute. reflexivity. }
      intros i0 n2 ix p Hn Hp. destruct (c2d_link_names i0 n2 ix Hn) as [Ln Li].
      destruct (c2d_link_ptrs_bound i0 Li) as [B1 B2].
      pose proof (c2d_u64_mod m1 _ p _ Hp (IP1 i0 Li)) as Mo.
      rewrite (Z.mod_small (nth i0 link_ptrs 0)) in Mo by lia.
      apply (c2d_apart_ptr p (nth i0 link_ptrs 0)); [exact Mo | lia | c2d_lia LE | lia | c2d_lia LE | c2d_lia LE]. }
    { exact MI1. }
    { rewrite unsigned_lit by c2d_lia LE. exact ST1. }
    { rewrite unsigned_lit by c2d_lia LE. c2d_lia LE. }
    { rewrite unsigned_lit by c2d_lia LE. c2d_lia LE. }
    intros ra2 t02 t12 t22 b0 b1 b2 b3 b4 b5 b6 b7 t32 t42 t52 t62 m2 MU2 WM2 MI2 ST2 PO2.
    pose proof (PO2 mbs kbs link_tab (sel_name s) (Some S_SERVED)) as PW.
    rewrite c2d_arg0, c2d_arg1, c2d_arg2 in PW. c2d_cl_in PW. rewrite !unsigned_lit in PW by c2d_lia LE.
    specialize (PW MA1 NL1 TB1 NMS1 SRV1).
    rewrite Hst, MRQ, MKS in PW.
    destruct PW as (B0 & mbs' & MA2 & MW2 & _ & _ & _ & MRQ2 & _ & MNM2 & MMK2).
    assert (Eb0 : b0 = wz (w_rc (write_model link_tab (Some t) (Some S_SERVED) (r_reqs (c2_rd t kbs))
                                              (r_state (c2_rd t kbs)))))
      by (rewrite <- B0; reflexivity).
    subst b0. unfold wz.
    (* model_write wrote its frame below sp and the model block *)
    rewrite c2d_arg0 in MU2. rewrite !unsigned_lit in MU2 by c2d_lia LE. rewrite !unsigned_lit in ST2 by c2d_lia LE.
    assert (AVw : c2d_avoid E [(e_S E - SLOT_FRAME - 704, e_S E - SLOT_FRAME); (e_md E, e_md E + MD_SIZE)]).
    { intros x Hx Hn. apply c2d_not_out2 in Hn. unfold c2d_rg. c2d_lia LE. }
    assert (MVw : c2d_mv E [(e_S E - SLOT_FRAME - 704, e_S E - SLOT_FRAME); (e_md E, e_md E + MD_SIZE)] m1 m2)
      by (split; [exact LE | split; [exact MU2 | split; [exact WM2 | exact AVw]]]).
    pose proof (c2d_rest_tr _ _ _ _ MVw _ _ _ _ _ _ _ _ _ RST1) as RST2.
    pose proof (c2d_task_tr _ _ _ _ MVw TM1) as TM2.
    pose proof (munch_trans _ m m1 m2 MUc1 (c2d_munch_W _ _ _ _ AVw MU2)) as MUc2.
    pose proof (wmono_trans rsegs m m1 m2 WM1 WM2) as WMc2.
    assert (WR : - 2 ^ 31 <= w_rc (write_model link_tab (Some t) (Some S_SERVED) (r_reqs (c2_rd t kbs))
                                               (r_state (c2_rd t kbs))) <= RC_FAILS).
    { pose proof MW as (_ & _ & W3 & W4 & _). pose proof WF1 as (_ & _ & _ & _ & _ & _ & _ & _ & W9 & _).
      rewrite <- MKS. apply c2d_wrc_range; [exact W3 | exact W4 | exact W9]. }
    c2d_ret.
    step.
    destruct (Z.eq_dec (w_rc (write_model link_tab (Some t) (Some S_SERVED) (r_reqs (c2_rd t kbs))
                                          (r_state (c2_rd t kbs)))) 0) as [W0|W0].
    + (* the write answered 0: 0x140b0 j 0x140d4, model_remember next *)
      rewrite W0. if_false. step.
      assert (MM : c2_MM s kbs gbs =
        Mres 0 (remember (mk_names gbs) t)
             (w_reqs (write_model link_tab (Some t) (Some S_SERVED) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs))))
             (w_state (write_model link_tab (Some t) (Some S_SERVED) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs))))).
      { rewrite (c2d_MM_eq s kbs gbs t Hst Htn Hrc), V, W0. reflexivity. }
      eapply (c2d_post14 E i gp s m m2 F fc P N j0 j1 j2 kbs mbs' gbs t);
        [reflexivity | reflexivity | rewrite MM; reflexivity | exact FRM | exact Hi | exact Hs | exact Hst | exact Htn
        | exact RST2 | exact MI2 | exact TM2 | exact ST2 | exact MA2 | exact MW2 | | rewrite MM; exact MRQ2
        | rewrite MM; reflexivity | exact MUc2 | exact WMc2].
      split; [rewrite MNM2; exact (proj1 MAR) | rewrite MMK2; exact (proj2 MAR)].
    + (* the write failed: 0x13da0 mv s3, a0 *)
      assert (WRr : - 2 ^ 63 <= w_rc (write_model link_tab (Some t) (Some S_SERVED) (r_reqs (c2_rd t kbs))
                                                   (r_state (c2_rd t kbs))) < 2 ^ 63)
        by (unfold RC_FAILS in WR; lia).
      if_true_by (proj2 (Bool.negb_true_iff _) (c2d_bveqb_nz _ WRr W0)). step.
      assert (MM : c2_MM s kbs gbs =
        Mres (w_rc (write_model link_tab (Some t) (Some S_SERVED) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs))))
             (mk_names gbs)
             (w_reqs (write_model link_tab (Some t) (Some S_SERVED) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs))))
             (w_state (write_model link_tab (Some t) (Some S_SERVED) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs))))).
      { rewrite (c2d_MM_eq s kbs gbs t Hst Htn Hrc), V.
        destruct (Z.eqb_spec (w_rc (write_model link_tab (Some t) (Some S_SERVED) (r_reqs (c2_rd t kbs))
                                                (r_state (c2_rd t kbs)))) 0) as [E0|_]; [contradiction|].
        reflexivity. }
      eapply (c2d_post13 E i gp s m m2 F fc P N j0 j1 j2 kbs mbs' gbs);
        [reflexivity | reflexivity | rewrite MM; reflexivity | exact FRM | exact Hi | exact Hs | exact RST2 | exact MI2
        | exact TM2 | exact ST2 | exact MA2 | exact MW2 | rewrite MM; exact MRQ2
        | rewrite MM, MMK2; exact (eq_sym (proj2 MAR)) | exact MUc2 | exact WMc2].
  - (* V_OURS: bcmp (alias, "reac-pw:served", 15) *)
    rewrite V. unfold V_OURS, wz. c2d_ret.
    step. step. step. if_true. step. step. step. step. step.
    destruct (c2d_memcmp 15 (firstn 15 j2) (S_SERVED ++ [zb 0])
                ltac:(rewrite length_firstn, J2L; lia)
                ltac:(rewrite length_app; change (length S_SERVED) with 14%nat; cbn [length]; lia))
      as (v' & Hv' & Rv' & Iv').
    destruct (c2d_frame_j2 E P N j0 j1 j2 m1 FR1) as [J2B1 _].
    pose proof PO1 as (Q1 & Q2 & Q3 & Q4).
    eapply evt_cut.
    { eapply BCMP_OK with (ls := firstn 15 j2) (rs := S_SERVED ++ [zb 0]) (v := v').
      - rewrite unsigned_lit by c2d_lia LE. apply c2d_firstn_bytes. exact J2B1.
      - c2d_cl. exact (proj1 Q2).
      - c2d_cl. exact Hv'.
      - exact MI1. }
    intros ms' (t0x & t1x & t2x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & mb & -> &
                MUb & WMb & MIb & _ & _).
    assert (Emb : mb = m1) by (apply functional_extensionality; intros x; exact (MUb x I)). subst mb.
    c2d_ret.
    step.
    rewrite firstn_firstn, Nat.min_id in Iv'.
    change (firstn 15 (S_SERVED ++ [zb 0])) with (S_SERVED ++ [zb 0]) in Iv'.
    pose proof (c2d_served _ j2 NNa PF ltac:(rewrite J2L; lia)) as SRV.
    destruct (Z.eq_dec v' 0) as [V0|V0].
    + (* the alias is "reac-pw:served": 0x140d4, model_remember next *)
      subst v'. if_true.
      assert (BL : bl_eqb (r_alias (c2_rd t kbs)) S_SERVED = true)
        by (apply bl_eqb_iff; apply SRV; apply Iv'; reflexivity).
      pose proof (c2d_MM_served s kbs gbs t Hst Htn Hrc V BL) as MM.
      eapply (c2d_post14 E i gp s m m1 F fc P N j0 j1 j2 kbs mbs gbs t);
        [reflexivity | reflexivity | rewrite MM; reflexivity | exact FRM | exact Hi | exact Hs | exact Hst | exact Htn
        | exact RST1 | exact MI1 | exact TM1 | exact ST1 | exact MA1 | exact MW | exact MAR | rewrite MM; exact MRQ
        | rewrite MM; reflexivity | exact MUc1 | exact WM1].
    + (* another alias: 0x140cc li s3, 1; j 0x13da4 *)
      if_false_by (c2d_bveqb_nz v' ltac:(lia) V0). step. step.
      assert (BL : bl_eqb (r_alias (c2_rd t kbs)) S_SERVED = false).
      { destruct (bl_eqb (r_alias (c2_rd t kbs)) S_SERVED) eqn:Eb; [|reflexivity].
        exfalso. apply V0. apply Iv'. apply SRV. apply bl_eqb_iff. exact Eb. }
      assert (MM : c2_MM s kbs gbs = Mres V_OURS (mk_names gbs) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs))).
      { apply (c2d_MM_leave s kbs gbs t V_OURS Hst Htn Hrc V); [unfold V_OURS, V_MARK; lia | right; exact BL]. }
      eapply (c2d_post13 E i gp s m m1 F fc P N j0 j1 j2 kbs mbs gbs);
        [reflexivity | reflexivity | rewrite MM; reflexivity | exact FRM | exact Hi | exact Hs | exact RST1 | exact MI1
        | exact TM1 | exact ST1 | exact MA1 | exact MW | rewrite MM; exact MRQ
        | rewrite MM; exact (eq_sym (proj2 MAR)) | exact MUc1 | exact WM1].
  - (* V_LEAVE_VLAN: 0x14094 bnez s3, 0x13da4 *)
    rewrite V. unfold V_LEAVE_VLAN, wz. c2d_ret.
    step. step. step. if_false. step. if_true.
    assert (MM : c2_MM s kbs gbs = Mres V_LEAVE_VLAN (mk_names gbs) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs))).
    { apply (c2d_MM_leave s kbs gbs t V_LEAVE_VLAN Hst Htn Hrc V);
        [unfold V_LEAVE_VLAN, V_MARK; lia | left; unfold V_LEAVE_VLAN, V_OURS; lia]. }
    eapply (c2d_post13 E i gp s m m1 F fc P N j0 j1 j2 kbs mbs gbs);
      [reflexivity | reflexivity | rewrite MM; reflexivity | exact FRM | exact Hi | exact Hs | exact RST1 | exact MI1
      | exact TM1 | exact ST1 | exact MA1 | exact MW | rewrite MM; exact MRQ
      | rewrite MM; exact (eq_sym (proj2 MAR)) | exact MUc1 | exact WM1].
  - (* V_LEAVE_HOST: 0x14094 bnez s3, 0x13da4 *)
    rewrite V. unfold V_LEAVE_HOST, wz. c2d_ret.
    step. step. step. if_false. step. if_true.
    assert (MM : c2_MM s kbs gbs = Mres V_LEAVE_HOST (mk_names gbs) (r_reqs (c2_rd t kbs)) (r_state (c2_rd t kbs))).
    { apply (c2d_MM_leave s kbs gbs t V_LEAVE_HOST Hst Htn Hrc V);
        [unfold V_LEAVE_HOST, V_MARK; lia | left; unfold V_LEAVE_HOST, V_OURS; lia]. }
    eapply (c2d_post13 E i gp s m m1 F fc P N j0 j1 j2 kbs mbs gbs);
      [reflexivity | reflexivity | rewrite MM; reflexivity | exact FRM | exact Hi | exact Hs | exact RST1 | exact MI1
      | exact TM1 | exact ST1 | exact MA1 | exact MW | rewrite MM; exact MRQ
      | rewrite MM; exact (eq_sym (proj2 MAR)) | exact MUc1 | exact WM1].
Qed.
End D.
