(* Piece READ of arm c2 (op_mark) of the slot, plain image: from c2_13d70 (0x13d70) to c2_13da4 (model_mark
   answered -EINVAL or the failed read's code) or c2_1407c (model_read answered 0).
     0x13d70  s3 = -22
     0x13d74  beqz s2 -> 0x13da4          (NULL name)
     0x13d78  lbu a0, 0(s2); beqz a0 -> 0x13da4   (empty name)
     0x13d80  a2 = sp + 0x50, a3 = 32, a4 = sp + 0x78, a5 = 256, a0 = s0, a1 = s2
     0x13d98  jal model_read (0x14ffc), ra = 0x13d9c
     0x13d9c  beqz a0 -> 0x1407c
     0x13da0  s3 = a0, then 0x13da4.
   The facts it uses are in LC2ReadL.v. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem model_read_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC2Defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import mk_leaf printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LC2ReadL.
Local Open Scope Z_scope.

(* the registers at the jal to model_read (0x13d98), and after it (the callee-saved words kept) *)
Definition c2r_R0 (E : lenv) (gp : word) (s i : Z) (t0 t1 t2 a6 a7 s4 t3 t4 t5 t6 : word) : bvmap 5 word :=
  mkR (Z_to_bv 64 81308) (Z_to_bv 64 (e_S E - SLOT_FRAME)) gp (Z_to_bv 64 A_TP) t0 t1 t2
      (Z_to_bv 64 (e_md E)) (Z_to_bv 64 GNL40) (Z_to_bv 64 (e_md E)) (Z_to_bv 64 (sel_ptr s))
      (Z_to_bv 64 (e_S E - SLOT_FRAME + 80)) (Z_to_bv 64 32) (Z_to_bv 64 (e_S E - SLOT_FRAME + 120))
      (Z_to_bv 64 256) a6 a7 (Z_to_bv 64 (sel_ptr s)) (Z_to_bv 64 (-22)) s4 (Z_to_bv 64 46)
      (Z_to_bv 64 A_JT) (Z_to_bv 64 (e_mk E)) (Z_to_bv 64 171) (Z_to_bv 64 4)
      (Z_to_bv 64 (e_md E + MD_N_REQ)) (Z_to_bv 64 i) t3 t4 t5 t6.

Definition c2r_R1 (E : lenv) (gp : word) (s i : Z) (s4 : word)
    (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) : bvmap 5 word :=
  mkR ra' (Z_to_bv 64 (e_S E - SLOT_FRAME)) gp (Z_to_bv 64 A_TP) t0' t1' t2' (Z_to_bv 64 (e_md E))
      (Z_to_bv 64 GNL40) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (sel_ptr s)) (Z_to_bv 64 (-22)) s4
      (Z_to_bv 64 46) (Z_to_bv 64 A_JT) (Z_to_bv 64 (e_mk E)) (Z_to_bv 64 171) (Z_to_bv 64 4)
      (Z_to_bv 64 (e_md E + MD_N_REQ)) (Z_to_bv 64 i) t3' t4' t5' t6'.

(* the two end cuts, from their facts *)
Lemma c2r_13da4_intro : forall E i gp s (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2w s3w s4 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pcw : word) P N j0 j1 j2 kbs mbs gbs,
  s2w = wz (sel_ptr s) -> s3w = wz (m_rc (c2_MM s kbs gbs)) -> pcw = wz 0x13da4 ->
  frm0 fc -> 0 <= i <= 47 -> 0 <= s <= 255 ->
  c2_frame E P N j0 j1 j2 m -> c2_fix E m -> cursor_ok m (e_p0 E) (e_pl E) P N -> c2_name_ok m s ->
  c2_kern i kbs m -> c2_marks E gbs m -> model_at m (e_md E) mbs -> model_wf mbs ->
  md_reqs mbs = m_reqs (c2_MM s kbs gbs) -> md_marks mbs = m_marks (c2_MM s kbs gbs) ->
  c2_13da4 E i gp s (MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                          a0 a1 a2 a3 a4 a5 a6 a7 s2w s3w s4 (wz 46) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4)
                          (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
                      F pcw fc None m (seg_rom rsegs)).
Proof.
  intros E i gp s ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2w s3w s4 t3 t4 t5 t6 F fc m pcw P N j0 j1 j2 kbs mbs gbs
    E2 E3 EP H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.
  subst s2w s3w pcw. unfold c2_13da4.
  exists ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s4, t3, t4, t5, t6, F, fc, m, P, N, j0, j1, j2, kbs, mbs, gbs.
  split; [reflexivity|]. repeat (split; [assumption|]). assumption.
Qed.

Lemma c2r_1407c_intro : forall E i gp s (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2w s3 s4 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pcw : word) P N j0 j1 j2 kbs mbs gbs t,
  s2w = wz (sel_ptr s) -> pcw = wz 0x1407c ->
  frm0 fc -> 0 <= i <= 47 -> 0 <= s <= 255 -> sel_name s = Some t -> t <> [] ->
  c2_frame E P N j0 j1 j2 m -> c2_fix E m -> cursor_ok m (e_p0 E) (e_pl E) P N -> c2_name_ok m s ->
  c2_kern i kbs m -> c2_marks E gbs m -> r_rc (c2_rd t kbs) = 0 ->
  model_at m (e_md E) mbs -> model_wf mbs -> marks_are gbs mbs ->
  md_kstate mbs kbs = r_state (c2_rd t kbs) -> md_reqs mbs = r_reqs (c2_rd t kbs) ->
  cstr_at m (e_S E - SLOT_FRAME + FO_B40) (r_kind (c2_rd t kbs)) ->
  cstr_at m (e_S E - SLOT_FRAME + FO_B256) (r_alias (c2_rd t kbs)) ->
  c2_1407c E i gp s (MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                          a0 a1 a2 a3 a4 a5 a6 a7 s2w s3 s4 (wz 46) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4)
                          (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
                      F pcw fc None m (seg_rom rsegs)).
Proof.
  intros E i gp s ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2w s3 s4 t3 t4 t5 t6 F fc m pcw P N j0 j1 j2 kbs mbs gbs t
    E2 EP H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19.
  subst s2w pcw. unfold c2_1407c.
  exists ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s3, s4, t3, t4, t5, t6, F, fc, m, P, N, j0, j1, j2,
    kbs, mbs, gbs, t.
  split; [reflexivity|]. repeat (split; [assumption|]). assumption.
Qed.

(* model_read's Pre at the jal *)
Lemma c2r_pre_ok : forall E s m P N j0 j1 j2 i kbs mbs t
   (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  lenv_ok E -> bv_unsigned sp = e_S E - SLOT_FRAME -> bv_unsigned a0 = e_md E -> bv_unsigned a1 = sel_ptr s ->
  bv_unsigned a2 = e_S E - SLOT_FRAME + 80 -> bv_unsigned a3 = 32 -> bv_unsigned a4 = e_S E - SLOT_FRAME + 120 ->
  bv_unsigned a5 = 256 -> sel_name s = Some t ->
  c2_frame E P N j0 j1 j2 m -> c2_fix E m -> c2_name_ok m s -> c2_kern i kbs m ->
  model_at m (e_md E) mbs -> model_wf mbs ->
  c2r_mr_pre (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m.
Proof.
  intros E s m P N j0 j1 j2 i kbs mbs t ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
    s10 s11 t3 t4 t5 t6 HE Esp E0 E1 E2 E3 E4 E5 EN HF HX HNm HK HMd HMw.
  pose proof HE as (L1 & L2 & L3 & (BM1 & BM2 & BM3) & _).
  pose proof (c2r_img_free (e_md E) MD_SIZE ltac:(lia) ltac:(unfold MD_SIZE; lia) BM3) as IFm.
  destruct (c2r_frame_split E P N j0 j1 j2 m HF) as (_ & H32 & _ & H256).
  destruct HX as (_ & _ & _ & _ & _ & _ & IP & _).
  destruct HK as (K1 & K2 & K3 & _).
  destruct HNm as [SA NB]. rewrite EN in SA.
  destruct (NB t EN) as (Lt & Pl & _).
  assert (NP : 0x10000 <= sel_ptr s /\ sel_ptr s + Z.of_nat (length t) + 1 <= 0x74400).
  { destruct Pl as [(P1 & P2) | (k & Hk & Ek & L4)];
      [unfold A_RO_LO, A_RO_END in *; lia | rewrite Ek; unfold A_G_NAMES; lia]. }
  unfold c2r_mr_pre. cbv beta.
  rewrite mkR_a0, mkR_a1, mkR_a2, mkR_a3, mkR_a4, mkR_a5.
  unfold frame_apart_gnl, apart_frame. rewrite !mkR_sp.
  rewrite E0, E1, E2, E3, E4, E5, Esp.
  exists mbs, kbs, link_tab, (Some t).
  unfold SLOT_FRAME, MD_SIZE, SLOT_STACK_Z in *.
  split; [exact HMd|]. split; [exact HMw|]. split; [exact K1|].
  split; [unfold apart_gnl, A_G_NL, NK_SIZE; lia|].
  split; [exact K2|]. split; [exact K3|]. split; [exact SA|].
  split; [intros _ _; exists (firstn 32 j1); exact H32|].
  split; [intros _ _; exists j2; exact H256|].
  split; [unfold apart_gnl, A_G_NL, NK_SIZE; lia|].
  split; [lia|].
  split; [intros _ s0' Es0; injection Es0 as Es0'; subst s0'; lia|].
  split; [intros _; lia|].
  split; [intros _; lia|].
  split; [intros i0 n2 ix p Ei Up; destruct (c2r_ifp m i0 n2 ix p IP Ei Up) as (d & -> & B1 & B2); lia|].
  split; [intros s0' Es0; injection Es0 as Es0'; subst s0'; split; intros _ _; unfold apart; lia|].
  split.
  { intros _ _. split; [unfold apart_gnl, A_G_NL, NK_SIZE; lia|]. split; [unfold apart; lia|].
    intros i0 n2 ix p Ei Up. destruct (c2r_ifp m i0 n2 ix p IP Ei Up) as (d & -> & B1 & B2). unfold apart. lia. }
  split.
  { intros _ _. split; [unfold apart_gnl, A_G_NL, NK_SIZE; lia|]. split; [unfold apart; lia|].
    intros i0 n2 ix p Ei Up. destruct (c2r_ifp m i0 n2 ix p IP Ei Up) as (d & -> & B1 & B2). unfold apart. lia. }
  intros _ _ _ _. unfold apart. lia.
Qed.

(* from model_read's return (0x13d9c) to 0x1407c or 0x13da4 *)
Lemma c2r_after : forall E i gp s m P N j0 j1 j2 kbs mbs gbs t
    (t0 t1 t2 a6 a7 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
  lenv_ok E -> frm0 fc -> 0 <= i <= 47 -> 0 <= s <= 255 -> sel_name s = Some t -> t <> [] ->
  c2_frame E P N j0 j1 j2 m -> c2_fix E m -> cursor_ok m (e_p0 E) (e_pl E) P N -> c2_name_ok m s ->
  c2_kern i kbs m -> c2_marks E gbs m -> model_at m (e_md E) mbs -> model_wf mbs -> marks_are gbs mbs ->
  md_kstate mbs kbs = nk_kstate kbs -> md_n_req mbs = 0 ->
  (exists regs' : bvmap 5 word,
     (forall r, getr regs' r =
        getr (c2r_R1 E gp s i s4 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') r) /\
     c2r_mr_post (c2r_R0 E gp s i t0 t1 t2 a6 a7 s4 t3 t4 t5 t6) m regs' m') ->
  munch ((bv_unsigned (Z_to_bv 64 (e_S E - SLOT_FRAME)) - 240, bv_unsigned (Z_to_bv 64 (e_S E - SLOT_FRAME)))
         :: c2r_mr_wr (c2r_R0 E gp s i t0 t1 t2 a6 a7 s4 t3 t4 t5 t6) m) m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' ->
  stk rsegs m' (e_S E - SLOT_STACK_Z) (bv_unsigned (Z_to_bv 64 (e_S E - SLOT_FRAME))) ->
  evt rsegs (eqv_cl (fun c => (c2_13da4 E i gp s c \/ c2_1407c E i gp s c) /\
                              seg_fp (e_S E) (c2_hp E) m (ms_mem c)))
    (MS (c2r_R1 E gp s i s4 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6')
        F (ret_pc (Z_to_bv 64 81308)) fc None m' (seg_rom rsegs)).
Proof.
  intros E i gp s m P N j0 j1 j2 kbs mbs gbs t t0 t1 t2 a6 a7 s4 t3 t4 t5 t6 F fc
    ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m'
    HE FRM Hi Hs EN NE HF HX HC HNm HK HMk HMd HMw HMa HKs HNr (regs' & EG & PO) MU WM MI' ST'.
  pose proof HE as (L1 & L2 & L3 & (BM1 & BM2 & BM3) & _).
  unfold SLOT_STACK_Z in L1.
  assert (Rsp : bv_unsigned (Z_to_bv 64 (e_S E - SLOT_FRAME)) = e_S E - SLOT_FRAME)
    by (apply unsigned_lit; unfold SLOT_FRAME; lia).
  rewrite Rsp in MU, ST'.
  pose proof HNm as [SA NB]. rewrite EN in SA. destruct SA as [NZ HCs].
  destruct (NB t EN) as (Lt & Pl & _).
  assert (NP : 0x10000 <= sel_ptr s /\ sel_ptr s + Z.of_nat (length t) + 1 <= 0x74400).
  { destruct Pl as [(P1 & P2) | (k & Hk & Ek & L4)];
      [unfold A_RO_LO, A_RO_END in *; lia | rewrite Ek; unfold A_G_NAMES; lia]. }
  pose proof HK as (K1 & K2 & K3 & _).
  unfold c2r_R0, c2r_R1 in *.
  assert (U0 : bv_unsigned (Z_to_bv 64 (e_md E)) = e_md E)
    by (apply unsigned_lit; unfold MD_SIZE, SLOT_STACK_Z in *; lia).
  assert (U1 : bv_unsigned (Z_to_bv 64 (sel_ptr s)) = sel_ptr s) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 (e_S E - SLOT_FRAME + 80)) = e_S E - SLOT_FRAME + 80)
    by (apply unsigned_lit; unfold SLOT_FRAME; lia).
  assert (U3 : bv_unsigned (Z_to_bv 64 32) = 32) by reflexivity.
  assert (U4 : bv_unsigned (Z_to_bv 64 (e_S E - SLOT_FRAME + 120)) = e_S E - SLOT_FRAME + 120)
    by (apply unsigned_lit; unfold SLOT_FRAME; lia).
  assert (U5 : bv_unsigned (Z_to_bv 64 256) = 256) by reflexivity.
  (* model_read's Post at this call *)
  unfold c2r_mr_post in PO. cbv beta in PO.
  rewrite mkR_a0, mkR_a1, mkR_a2, mkR_a3, mkR_a4, mkR_a5 in PO.
  rewrite U0, U1, U2, U3, U4, U5 in PO.
  specialize (PO mbs kbs link_tab (Some t) HMd K1 K3 (conj NZ HCs)).
  cbv zeta in PO.
  rewrite (c2r_reqs_nil mbs HNr), HKs in PO.
  change (read_model link_tab (Some t) 32 256 [] (nk_kstate kbs)) with (c2_rd t kbs) in PO.
  destruct PO as (EA0 & (mbs' & HMd' & HMw' & Enx & Eso & Ese & Erq & Enr & Enm & Emk) & HK1 & HK2 & HB1 & HB2).
  specialize (HK1 ltac:(unfold SLOT_FRAME; lia) ltac:(lia)).
  specialize (HK2 ltac:(unfold SLOT_FRAME; lia) ltac:(lia)).
  destruct (HB1 ltac:(unfold SLOT_FRAME; lia) ltac:(lia)) as [jk HJK].
  destruct (HB2 ltac:(unfold SLOT_FRAME; lia) ltac:(lia)) as [jal HJA].
  unfold wz in EA0.
  assert (A0 : a0' = Z_to_bv 64 (r_rc (c2_rd t kbs))) by (rewrite <- EA0, EG; reflexivity).
  subst a0'.
  (* what model_read wrote *)
  assert (MU' : munch (c2r_W E) m m').
  { eapply munch_weaken; [|exact MU]. intros x Hx.
    unfold c2r_mr_wr. cbv beta. rewrite mkR_a0, mkR_a2, mkR_a3, mkR_a4, mkR_a5, U0, U2, U3, U4, U5.
    unfold c2r_W in Hx. cbn [outside] in Hx |- *.
    destruct (Z.eqb_spec (e_S E - SLOT_FRAME + 80) 0) as [Z1|Z1]; [unfold SLOT_FRAME in Z1; lia|].
    destruct (Z.eqb_spec (e_S E - SLOT_FRAME + 120) 0) as [Z2|Z2]; [unfold SLOT_FRAME in Z2; lia|].
    unfold SLOT_FRAME, MD_SIZE in *. repeat split; try exact I; lia. }
  assert (MV : c2r_mv E m m') by (split; [exact HE | split; assumption]).
  destruct (c2r_frame_split E P N j0 j1 j2 m HF) as (F0 & _ & F8 & _).
  destruct (c2r_keep E i s m m' P N j0 kbs gbs (skipn 32 j1) MV MI' ST' HX HC HNm HK HMk F0 F8)
    as (HX' & HC' & HNm' & HK' & HMk' & F0' & F8' & SEG).
  assert (HF' : c2_frame E P N j0 (jk ++ skipn 32 j1) jal m') by (apply c2r_frame_join; assumption).
  rewrite (ret_pc_even 81308) by (first [lia | reflexivity]).
  step.
  if_cases HC2.
  - (* rc = 0: 0x1407c *)
    apply c2r_eqb0 in HC2.
    assert (RC0 : r_rc (c2_rd t kbs) = 0) by (apply c2r_rc_zero; [exact K2 | exact HC2]).
    apply c2r_fin; [right | cbn [ms_mem]; exact SEG].
    eapply c2r_1407c_intro with (P := P) (N := N) (j0 := j0) (j1 := jk ++ skipn 32 j1) (j2 := jal) (kbs := kbs)
      (mbs := mbs') (gbs := gbs) (t := t); try eassumption.
    all: first [ reflexivity
               | (split; [rewrite Enm; exact (proj1 HMa) | rewrite Emk; exact (proj2 HMa)])
               | (apply c2r_kstate; assumption) ].
  - (* rc <> 0: s3 = rc, 0x13da4 *)
    apply c2r_neqb0 in HC2.
    assert (RCn : r_rc (c2_rd t kbs) <> 0) by (intros E0; apply HC2; rewrite E0; reflexivity).
    destruct (c2r_mm_read s kbs gbs t EN NE RCn) as (R1 & R2 & R3).
    step.
    apply c2r_fin; [left | cbn [ms_mem]; exact SEG].
    eapply c2r_13da4_intro with (P := P) (N := N) (j0 := j0) (j1 := jk ++ skipn 32 j1) (j2 := jal) (kbs := kbs)
      (mbs := mbs') (gbs := gbs); try eassumption.
    all: first [ reflexivity
               | (rewrite R1; unfold wz; rewrite ?Z.add_0_r; reflexivity)
               | (rewrite R2; exact Erq)
               | (rewrite R3, Emk; symmetry; exact (proj2 HMa)) ].
Qed.

Section R.
Hypothesis MODEL_READ_OK : model_read_contract.

Lemma c2_read : forall (E : lenv) (i : Z) (gp : word) (s : Z) (ms : machine_state),
  lenv_ok E -> c2_13d70 E i gp s ms ->
  evt rsegs (c2_post E (ms_mem ms) (fun c => c2_13da4 E i gp s c \/ c2_1407c E i gp s c)) ms.
Proof.
  intros E i gp s ms HE H.
  destruct H as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 &
    F & fc & m & P & N & j0 & j1 & j2 & kbs & mbs & gbs & Hms & FRM & Hi & Hs & HFr & HFx & HCur & HNm & HKn &
    HMk & HMd & HMwf & HMa & HKs & HNr).
  subst ms. cbn [ms_mem].
  pose proof HE as (L1 & L2 & L3 & (BM1 & BM2 & BM3) & _).
  pose proof HFx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _ & ST).
  pose proof HNm as [SA NB].
  assert (Rp : 0 <= sel_ptr s < 2 ^ 64).
  { revert SA. destruct (sel_name s) as [t|]; intros SA.
    - destruct SA as [_ [(B1 & B2 & _) _]]. rewrite length_app in B2. cbn [length] in B2. lia.
    - rewrite SA. lia. }
  unfold wz.
  step. step.
  if_cases HC1.
  - (* NULL name: 0x13da4, model_mark answers -EINVAL *)
    apply c2r_eqb0 in HC1. rewrite unsigned_lit in HC1 by exact Rp.
    assert (EN : sel_name s = None).
    { revert SA. destruct (sel_name s) as [t|]; intros SA; [destruct SA as [NZ _]; contradiction | reflexivity]. }
    destruct (c2r_mm_none s kbs gbs EN) as (R1 & R2 & R3).
    unfold c2_post. cbv beta.
    apply c2r_fin; [left | cbn [ms_mem]; apply c2_seg_fp_refl].
    eapply c2r_13da4_intro with (P := P) (N := N) (j0 := j0) (j1 := j1) (j2 := j2) (kbs := kbs) (mbs := mbs)
      (gbs := gbs); try eassumption.
    all: first [ reflexivity | (rewrite R1; reflexivity) | (rewrite R2; apply c2r_reqs_nil; exact HNr)
               | (rewrite R3; symmetry; exact (proj2 HMa)) ].
  - apply c2r_neqb0 in HC1. rewrite unsigned_lit in HC1 by exact Rp.
    revert SA. destruct (sel_name s) as [t|] eqn:EN; intros SA; [|exfalso; exact (HC1 SA)].
    destruct SA as [NZ HCs]. pose proof HCs as [HCb HCn].
    destruct t as [|b0 t'].
    + (* empty name: 0x13da4, model_mark answers -EINVAL *)
      assert (HB1 : ro_cells rsegs m (sel_ptr s) [CB 1 [zb 0]]) by exact (conj (conj eq_refl I) HCb).
      step. step. if_cases HC2.
      * destruct (c2r_mm_empty s kbs gbs EN) as (R1 & R2 & R3).
        unfold c2_post. cbv beta.
        apply c2r_fin; [left | cbn [ms_mem]; apply c2_seg_fp_refl].
        eapply c2r_13da4_intro with (P := P) (N := N) (j0 := j0) (j1 := j1) (j2 := j2) (kbs := kbs) (mbs := mbs)
          (gbs := gbs); try eassumption.
        all: first [ reflexivity | (rewrite R1; reflexivity) | (rewrite R2; apply c2r_reqs_nil; exact HNr)
                   | (rewrite R3; symmetry; exact (proj2 HMa)) ].
      * exfalso. vm_compute in HC2. discriminate HC2.
    + (* a name: the call of model_read *)
      assert (HB1 : ro_cells rsegs m (sel_ptr s) [CB 1 [b0]])
        by exact (conj (conj eq_refl I)
                       (proj1 (proj1 (bytes_at_app rsegs m (sel_ptr s) [b0] (t' ++ [zb 0])) HCb))).
      step. step. if_cases HC2.
      * exfalso. apply c2r_zxb_zero in HC2. apply HCn. left. exact HC2.
      * step. step. step. step. step. step. step.
        unfold c2_post. cbv beta.
        eapply (c2r_call 86012 240 c2r_mr_pre c2r_mr_wr c2r_mr_post) with (lo := e_S E - SLOT_STACK_Z).
        -- exact MODEL_READ_OK.
        -- eapply c2r_pre_ok with (P := P) (N := N) (j0 := j0) (j1 := j1) (j2 := j2) (i := i) (kbs := kbs)
             (mbs := mbs) (t := b0 :: t'); try eassumption;
             apply unsigned_lit; unfold SLOT_FRAME, SLOT_STACK_Z, MD_SIZE in *; lia.
        -- exact MI.
        -- rewrite unsigned_lit by (unfold SLOT_FRAME, SLOT_STACK_Z in *; lia). exact ST.
        -- rewrite unsigned_lit by (unfold SLOT_FRAME, SLOT_STACK_Z in *; lia). unfold SLOT_FRAME, SLOT_STACK_Z in *. lia.
        -- rewrite unsigned_lit by (unfold SLOT_FRAME, SLOT_STACK_Z in *; lia). unfold SLOT_FRAME, SLOT_STACK_Z in *. lia.
        -- intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' HPO MU WM MI' ST'.
           eapply c2r_after with (t := b0 :: t'); try eassumption. discriminate.
Qed.

End R.
