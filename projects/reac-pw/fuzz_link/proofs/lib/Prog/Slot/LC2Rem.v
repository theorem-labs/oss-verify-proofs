From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem printf_facts_c strcmp_c snprintf_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC2Defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LC2RemLib.
Local Open Scope Z_scope.

(* Arm c2 (op_mark), piece REMEMBER: 0x140d4 -> 0x13da4, the inlined model_remember (fuzz_link.c:433-440).
     0x140d4  lw s5, 0x204(s10); ld s4, 0x10(sp); mv s6, s5; blez s5 -> 0x14108
     0x140e4  the strcmp loop over the n marks (c2m_loop): a match -> 0x14130, none -> 0x14100
     0x14100  n > 31 -> 0x14130 (the list is full)
     0x14108  n + 1 -> m->n_mark; snprintf (m->mark[n], 16, "%s", name) (c2m_ins)
     0x14130  s5 = 46; s6 = the jump table; j 0x13da4 (c2m_fin) *)

Lemma c2m_pf_t0 : forall t : list byte, pf_bytes (map bz t ++ [0]) = t ++ [zb 0].
Proof.
  intros t. unfold pf_bytes. rewrite map_app, map_map. f_equal.
  transitivity (map (fun b : byte => b) t); [|apply map_id].
  apply map_ext. intros b. unfold bz. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  apply bv_unsigned_in_range.
Qed.

Lemma c2m_img_free_sub : forall a n k len, pf_img_free a n -> 0 <= k -> k + len <= n -> pf_img_free (a + k) len.
Proof.
  intros a n k len H Hk Hl i Hi sg Hs. replace (a + k + i) with (a + (k + i)) by lia. apply H; [lia | exact Hs].
Qed.

(* snprintf's argument: the name, its NUL and its slack, in the image, apart from the stack and from md *)
Lemma c2m_args : forall (E : lenv) (m : word -> option byte) (s : Z) (t : list byte) (D n : Z) (a4 a5 a6 a7 : word),
  lenv_ok E -> sel_name s = Some t -> c2_name_ok m s -> e_md E <= D -> D + n <= e_md E + MD_SIZE ->
  pf_args_ok m (e_S E - SLOT_FRAME) (e_S E - SLOT_STACK_Z) D n [Z_to_bv 64 (sel_ptr s); a4; a5; a6; a7]
    [APtr (map bz t)].
Proof.
  intros E m s t D n a4 a5 a6 a7 HE Hsn [HA HN] H1 H2.
  rewrite Hsn in HA. destruct HA as [Hp0 [HB HB0]].
  destruct (HN t Hsn) as (Hl & Hloc & (slack & HS & HSL)).
  pose proof (c2m_md_img E HE) as Hm.
  pose proof (bytes_at_bound rsegs m _ _ HB) as [Hb0 _].
  pose proof (Z.mod_pos_bound (- (sel_ptr s + Z.of_nat (length t) + 1)) 8 ltac:(lia)) as Hmod.
  assert (Hend : sel_ptr s + Z.of_nat (length t) + 1 + Z.of_nat (length slack) <= 0x960e0 /\ 0x10000 <= sel_ptr s)
    by (destruct Hloc as [(L1 & L2) | (k & Hk & Ek & Hl4)]; unfold A_RO_LO, A_RO_END, A_G_NAMES in *; lia).
  pose proof HE as (HS1 & HS2 & _).
  cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split.
  - apply Forall_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as (b & <- & Hb).
    pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
    unfold bz. split; [|lia].
    destruct (Z.eq_dec (bv_unsigned b) 0) as [E0|E0]; [|lia].
    exfalso. apply HB0. replace (zb 0) with b; [exact Hb|]. apply c2m_zb0. exact E0.
  - exists slack. rewrite unsigned_lit by lia. rewrite length_map.
    split; [|split; [lia|split; [lia|split]]].
    + rewrite c2m_pf_t0. apply bytes_at_app. split; [exact HB|].
      replace (sel_ptr s + Z.of_nat (length (t ++ [zb 0]))) with (sel_ptr s + Z.of_nat (length t) + 1)
        by (rewrite length_app; cbn [length]; lia).
      exact HS.
    + left. lia.
    + destruct Hm as [Hm|Hm]; [right | left]; lia.
Qed.

Section M.
Hypothesis STRCMP_OK : strcmp_contract.
Hypothesis SNPRINTF_OK : snprintf_contract.

(* the loop 0x140e4 - 0x140fc at slot k < n: s4 = base + 16 k, s6 = n - k, no slot before k holds t *)
Lemma c2m_loop : forall (rem : nat) (sl : Z -> list byte) (t : list byte) (base n k : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop),
  Z.of_nat rem = n - k -> 0 <= k -> k < n -> n <= 32 -> 0 <= base -> base + 16 * n <= 2^64 ->
  s4 = Z_to_bv 64 (base + 16 * k) -> s6 = Z_to_bv 64 (n - k) ->
  (forall j, k <= j < n -> bytes_at rsegs m (base + 16 * j) (sl j ++ [zb 0]) /\ ~ In (zb 0) (sl j)) ->
  bytes_at rsegs m (bv_unsigned s2) (t ++ [zb 0]) -> ~ In (zb 0) t ->
  (forall j, 0 <= j < k -> sl j <> t) ->
  (forall ra' a0' a1' a2' a3' s4' s6', (exists j, 0 <= j < n /\ sl j = t) ->
     evt rsegs Q (MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 s3 s4' (Z_to_bv 64 n) s6'
                          s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14130) fc None m (seg_rom rsegs))) ->
  (forall ra' a0' a1' a2' a3' s4' s6', (forall j, 0 <= j < n -> sl j <> t) ->
     evt rsegs Q (MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 s3 s4' (Z_to_bv 64 n) s6'
                          s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14100) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 n) s6
                       s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x140e4) fc None m (seg_rom rsegs)).
Proof.
  induction rem as [|rem IH];
    intros sl t base n k ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11
      t3 t4 t5 t6 F fc m Q Hrem Hk Hkn Hn Hb0 Hb1 Es4 Es6 HSL HT HT0 HINV KF KN; [lia|].
  subst s4 s6.
  step. step. step.
  destruct (HSL k ltac:(lia)) as [HB HB0].
  eapply evt_cut.
  { eapply STRCMP_OK with (sx := sl k) (sy := t).
    - rewrite unsigned_lit by lia. exact HB.
    - exact HB0.
    - exact HT.
    - exact HT0. }
  intros ms' (r & x11 & x12 & x13 & -> & Hr).
  rewrite ret_pc_even by (first [lia | reflexivity]).
  step.
  if_cases Hc; zify_cond Hc.
  - assert (Er : r = Z_to_bv 64 0) by (apply bv_eq; rewrite Hc; reflexivity).
    apply KF. exists k. split; [lia | apply Hr; exact Er].
  - assert (Ne : sl k <> t) by (intro Ek; apply Hr in Ek; rewrite Ek in Hc; apply Hc; reflexivity).
    step. step. step.
    destruct rem as [|rem'].
    + c2m_br false. apply KN. intros j Hj.
      destruct (Z.eq_dec j k) as [->|Hjk]; [exact Ne | apply HINV; lia].
    + c2m_br true.
      eapply IH with (k := k + 1).
      * lia.
      * lia.
      * lia.
      * exact Hn.
      * exact Hb0.
      * exact Hb1.
      * f_equal. lia.
      * f_equal. lia.
      * intros j Hj. apply HSL. lia.
      * exact HT.
      * exact HT0.
      * intros j Hj. destruct (Z.eq_dec j k) as [->|Hjk]; [exact Ne | apply HINV; lia].
      * exact KF.
      * exact KN.
Qed.

(* 0x14130 - 0x14138: s5 = 46, s6 = A_JT from the frame, j 0x13da4; the cut holds of the block mbs *)
Lemma c2m_fin : forall (E : lenv) (i : Z) (gp : word) (s : Z)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (P N : Z) (j0 j1 j2 kbs mbs gbs : list byte),
  frm0 fc -> 0 <= i <= 47 -> 0 <= s <= 255 ->
  c2_frame E P N j0 j1 j2 m -> c2_fix E m -> cursor_ok m (e_p0 E) (e_pl E) P N -> c2_name_ok m s ->
  c2_kern i kbs m -> c2_marks E gbs m -> model_at m (e_md E) mbs -> model_wf mbs ->
  md_reqs mbs = m_reqs (c2_MM s kbs gbs) -> md_marks mbs = m_marks (c2_MM s kbs gbs) ->
  seg_fp (e_S E) (c2_hp E) m0 m ->
  evt rsegs (c2_post E m0 (c2_13da4 E i gp s))
    (MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
             a0 a1 a2 a3 a4 a5 a6 a7
             (wz (sel_ptr s)) (wz (m_rc (c2_MM s kbs gbs))) s4 s5 s6 (wz (e_mk E))
             (wz 0xab) (wz 4) (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
        F (wz 0x14130) fc None m (seg_rom rsegs)).
Proof.
  intros E i gp s ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 F fc m0 m P N j0 j1 j2 kbs mbs gbs
    HFC Hi Hs HFR HFX HCU HNM HKN HMK HMD HWF HRQ HMQ HFP.
  pose proof HFR as HFRc. unfold c2_frame, lh_cells in HFRc. unfold wz in HFRc |- *.
  step. step. step.
  match goal with |- evt _ _ ?st => apply evt_done; exists st end.
  split; [split; [|exact HFP] | apply c2_ms_eqv_refl].
  unfold c2_13da4. do 17 eexists. exists F, fc, m, P, N, j0, j1, j2, kbs, mbs, gbs.
  split; [reflexivity|].
  split; [exact HFC|]. split; [exact Hi|]. split; [exact Hs|]. split; [exact HFR|]. split; [exact HFX|].
  split; [exact HCU|]. split; [exact HNM|]. split; [exact HKN|]. split; [exact HMK|]. split; [exact HMD|].
  split; [exact HWF|]. split; [exact HRQ | exact HMQ].
Qed.

(* 0x14108 - 0x1412c and snprintf: n < 32 and no mark is t; then m->n_mark = n + 1, m->mark[n] = t *)
Lemma c2m_ins : forall (E : lenv) (i : Z) (gp : word) (s n : Z)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (P N : Z) (j0 j1 j2 kbs mbs gbs t : list byte),
  lenv_ok E -> frm0 fc -> 0 <= i <= 47 -> 0 <= s <= 255 -> sel_name s = Some t ->
  c2_frame E P N j0 j1 j2 m -> c2_fix E m -> cursor_ok m (e_p0 E) (e_pl E) P N -> c2_name_ok m s ->
  c2_kern i kbs m -> c2_marks E gbs m -> model_at m (e_md E) mbs -> model_wf mbs -> marks_are gbs mbs ->
  md_reqs mbs = m_reqs (c2_MM s kbs gbs) -> m_marks (c2_MM s kbs gbs) = remember (mk_names gbs) t ->
  md_n_mark mbs = n -> n < 32 -> (forall j, 0 <= j < n -> c2m_slot mbs j <> t) ->
  evt rsegs (c2_post E m (c2_13da4 E i gp s))
    (MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
             a0 a1 a2 a3 a4 a5 a6 a7
             (wz (sel_ptr s)) (wz (m_rc (c2_MM s kbs gbs))) s4 (wz n) s6 (wz (e_mk E))
             (wz 0xab) (wz 4) (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
        F (wz 0x14108) fc None m (seg_rom rsegs)).
Proof.
  intros E i gp s n ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 F fc m P N j0 j1 j2 kbs mbs gbs t
    HE HFC Hi Hs Hsn HFR HFX HCU HNM HKN HMK HMD HWF HMA HRQ HMM En Hn32 NF.
  (* the facts the walk reads *)
  pose proof HE as (HS1 & HS2 & HS3 & (Hmd0 & Hmd1 & HmdF) & _).
  pose proof HWF as (_ & _ & _ & _ & _ & (Hm & _)).
  assert (Hn : 0 <= n < 32) by (rewrite <- En; unfold MARKS_MAX in Hm; lia).
  pose proof HMD as [[HB HW] HL].
  pose proof HNM as [HA HNL]. rewrite Hsn in HA. destruct HA as [Hp0 HTc].
  destruct (HNL t Hsn) as (Hl11 & _ & _).
  pose proof HTc as [_ HT0].
  pose proof HFX as (_ & _ & _ & _ & _ & _ & HIF & _ & _ & MI & TM & ST).
  assert (HS : store_ok rsegs m (wa (e_md E + MD_N_REQ + 516)) 4 = true).
  { replace (e_md E + MD_N_REQ + 516) with (e_md E + MD_N_MARK) by (unfold MD_N_REQ, MD_N_MARK; lia).
    apply (wr_at_store_ok rsegs m (e_md E) _ MD_N_MARK 4 HW); c2m_lia. }
  pose proof HFR as HFRc. unfold c2_frame, lh_cells in HFRc. unfold wz in HFRc |- *.
  (* 0x14108 addi a0, s5, 1; slli s5, s5, 4; sw a0, 0x204(s10) *)
  step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m ?a _) _) =>
    replace a with (wa (e_md E + MD_N_MARK)) by (unfold wa; f_equal; unfold MD_N_REQ, MD_N_MARK; lia) end.
  remember (write_to_mem m (wa (e_md E + MD_N_MARK)) (le4 (Z_to_bv 64 (n + 1)))) as m1 eqn:Em1.
  (* what the store keeps and makes *)
  assert (MU1 : munch [(e_md E + MD_N_MARK, e_md E + MD_N_MARK + 4)] m m1).
  { subst m1. pose proof (c2m_munch_write m (e_md E + MD_N_MARK) (le4 (Z_to_bv 64 (n + 1)))
      ltac:(c2m_lia) ltac:(rewrite length_le4; c2m_lia)) as H. rewrite length_le4 in H. exact H. }
  assert (MUW1 : munch (c2m_W E) m m1)
    by (eapply munch_weaken; [|exact MU1]; apply c2m_sub_md; c2m_lia).
  assert (WM1 : wmono rsegs m m1) by (subst m1; apply wmono_write, wmono_refl).
  assert (MI1 : mem_inv rsegs m1).
  { subst m1. apply mem_inv_store; [exact MI|]. rewrite length_le4.
    replace (e_md E + MD_N_MARK) with (e_md E + MD_N_REQ + 516) by (unfold MD_N_REQ, MD_N_MARK; lia). exact HS. }
  assert (TM1 : MemNorm.task_mem rsegs m1)
    by (subst m1; apply c2m_task_write; [exact TM | c2m_lia | rewrite length_le4; unfold TASK_SIZE; c2m_lia]).
  assert (ST1 : stk rsegs m1 (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME))
    by (subst m1; apply stk_write; [exact ST | c2m_lia | rewrite length_le4; c2m_lia]).
  assert (HMD1 : model_at m1 (e_md E) (c2m_mbs1 mbs n)).
  { split; [split|].
    - unfold c2m_mbs1. eapply c2m_bytes_upd; [exact HB | exact MU1 | | rewrite length_le4; c2m_lia |].
      + rewrite Z2Nat.id by c2m_lia. subst m1. apply bytes_at_write_same; [c2m_lia | rewrite length_le4; c2m_lia].
      + intros k Hk Hk2. rewrite length_le4 in Hk2. cbn [outside]. split; [c2m_lia | exact I].
    - rewrite c2m_len1 by exact HL. exact (wr_at_transport rsegs m m1 _ _ HW WM1).
    - rewrite c2m_len1 by exact HL. exact HL. }
  assert (HFR1 : c2_frame E P N j0 j1 j2 m1) by (apply (c2m_frame E m m1); assumption).
  assert (HFX1 : c2_fix E m1) by (apply (c2m_fix E m m1); assumption).
  assert (HNM1 : c2_name_ok m1 s) by (apply (c2m_name E m m1); assumption).
  pose proof HFR1 as HFRc1. unfold c2_frame, lh_cells, wz in HFRc1.
  (* 0x14114 ld a0, 0x10(sp); add a0, a0, s5; auipc; addi a2; addi a1, 16; mv a3, s2; jal snprintf *)
  step. step.
  rewrite (c2m_shl4 n) by lia.
  step. step. step. step. step.
  (* snprintf's premises *)
  pose proof HFX1 as (_ & _ & _ & _ & _ & _ & _ & _ & (HG1 & (cn & HG2)) & _).
  pose proof HNM1 as [HA1 HNL1]. rewrite Hsn in HA1. destruct HA1 as [_ HTc1].
  assert (HJ : rw_cells rsegs m1 (e_md E + MD_MARK + 16 * n)
                 [CB 16 (firstn 16 (skipn (Z.to_nat (c2m_D n)) (c2m_mbs1 mbs n)))]).
  { replace (e_md E + MD_MARK + 16 * n) with (e_md E + Z.of_nat (Z.to_nat (c2m_D n)))
      by (rewrite Z2Nat.id by (unfold c2m_D; c2m_lia); unfold c2m_D, MARK_LEN; lia).
    pose proof HMD1 as [HU1 HL1]. apply c2m_rw_sub; [exact HU1 | rewrite c2m_len1 by exact HL; unfold c2m_D; c2m_lia]. }
  eapply evt_cut.
  { eapply SNPRINTF_OK with (lo := e_S E - SLOT_STACK_Z) (canary := cn) (fmt := [37; 115]) (ps := [Ps])
      (args := [APtr (map bz t)]) (T := map bz t ++ [])
      (junk := firstn 16 (skipn (Z.to_nat (c2m_D n)) (c2m_mbs1 mbs n))).
    - rewrite unsigned_lit by lia. apply ro_bytes_at; [exact MI1 | lia | |].
      { change (Z.of_nat (length (pf_bytes ([37; 115] ++ [0])))) with 3. lia. }
      apply ro_bytes_b_sound. vm_compute. reflexivity.
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END. cbn [length]. lia.
    - reflexivity.
    - rewrite !unsigned_lit by c2m_lia. apply c2m_args; [exact HE | exact Hsn | exact HNM1 | c2m_lia | c2m_lia].
    - reflexivity.
    - rewrite !unsigned_lit by c2m_lia. exact HJ.
    - rewrite unsigned_lit by lia. lia.
    - rewrite app_nil_r, length_map. lia.
    - rewrite unsigned_lit by c2m_lia. c2m_lia.
    - rewrite !unsigned_lit by c2m_lia. left. c2m_lia.
    - rewrite !unsigned_lit by c2m_lia.
      replace (e_md E + MD_MARK + 16 * n) with (e_md E + (MD_MARK + 16 * n)) by lia.
      apply (c2m_img_free_sub _ MD_SIZE); [exact HmdF | c2m_lia | c2m_lia].
    - rewrite unsigned_lit by c2m_lia. exact ST1.
    - rewrite unsigned_lit by c2m_lia. unfold SNPRINTF_K. c2m_lia.
    - unfold IMG_END. c2m_lia.
    - rewrite unsigned_lit by c2m_lia. c2m_lia.
    - exact HFC.
    - exact MI1.
    - exact TM1.
    - exact HG1.
    - exact HG2. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc'
    & m2 & -> & MU2 & WM2 & MI2 & TM2 & FC2 & FK & ST2 & BT).
  rewrite ret_pc_even by (first [lia | reflexivity]).
  (* the memory after snprintf *)
  assert (ED : bv_unsigned (Z_to_bv 64 (e_md E + MD_MARK + 16 * n)) = e_md E + MD_MARK + 16 * n)
    by (apply unsigned_lit; c2m_lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (e_S E - SLOT_FRAME)) = e_S E - SLOT_FRAME) by (apply unsigned_lit; c2m_lia).
  assert (E16 : bv_unsigned (Z_to_bv 64 16) = 16) by reflexivity.
  assert (ELT : Z.of_nat (length (firstn (Z.to_nat (16 - 1)) (map bz t ++ []))) = Z.of_nat (length t))
    by (rewrite length_firstn, app_nil_r, length_map; lia).
  rewrite ED, ESP, E16, ELT in MU2. rewrite ED, E16 in BT. rewrite ESP in ST2.
  rewrite c2m_pf_t in BT by lia.
  assert (MUW2 : munch (c2m_W E) m1 m2)
    by (eapply munch_weaken; [|exact MU2]; apply c2m_sub_pf; [reflexivity | reflexivity | c2m_lia | c2m_lia]).
  assert (MUW : munch (c2m_W E) m m2) by exact (munch_trans _ _ _ _ MUW1 MUW2).
  assert (WM : wmono rsegs m m2) by exact (wmono_trans rsegs _ _ _ WM1 WM2).
  assert (HMD2 : model_at m2 (e_md E) (c2m_mbs2 mbs n t)).
  { destruct HMD1 as [[HB1 HW1] HL1]. split; [split|].
    - unfold c2m_mbs2. eapply c2m_bytes_upd; [exact HB1 | exact MU2 | | |].
      + rewrite Z2Nat.id by (unfold c2m_D; c2m_lia). replace (e_md E + c2m_D n) with (e_md E + MD_MARK + 16 * n)
          by (unfold c2m_D, MARK_LEN; lia). exact BT.
      + rewrite c2m_len1 by exact HL. rewrite c2m_lenT. unfold c2m_D. c2m_lia.
      + intros k Hk Hk2. rewrite c2m_len1 in Hk by exact HL. rewrite c2m_lenT in Hk2.
        cbn [outside]. unfold c2m_D in Hk2. split; [c2m_lia | split; [c2m_lia | exact I]].
    - rewrite (c2m_len2 mbs n t HL Hn Hl11). rewrite <- (c2m_len1 mbs n HL). exact (wr_at_transport rsegs m1 m2 _ _ HW1 WM2).
    - rewrite (c2m_len2 mbs n t HL Hn Hl11). exact HL. }
  eapply c2m_fin with (m0 := m) (mbs := c2m_mbs2 mbs n t).
  - exact FC2.
  - exact Hi.
  - exact Hs.
  - eapply (c2m_frame E m m2); eassumption.
  - eapply (c2m_fix E m m2); eassumption.
  - eapply (c2m_cursor E m m2); eassumption.
  - eapply (c2m_name E m m2); eassumption.
  - eapply (c2m_kern E m m2); eassumption.
  - eapply (c2m_marks E m m2); eassumption.
  - exact HMD2.
  - apply c2m_wf2; [exact HL | symmetry; exact En | exact Hn | exact Hl11 | exact HT0 | exact HWF].
  - rewrite (c2m_reqs2 mbs n t HL Hn Hl11 HWF). exact HRQ.
  - rewrite HMM. destruct HMA as [_ HMA]. rewrite HMA.
    rewrite (c2m_marks2 mbs n t HL (eq_sym En) Hn Hl11 HT0).
    rewrite c2m_rem_new; [reflexivity | lia | lia | rewrite En; exact NF].
  - exact (c2m_segfp E m m2 MUW WM).
Qed.

Lemma c2_rem : forall (E : lenv) (i : Z) (gp : word) (s : Z) (ms : machine_state),
  lenv_ok E -> c2_140d4 E i gp s ms ->
  evt rsegs (c2_post E (ms_mem ms) (c2_13da4 E i gp s)) ms.
Proof.
  intros E i gp s ms HE H.
  destruct H as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & t3 & t4 & t5 & t6 & F & fc & m
    & P & N & j0 & j1 & j2 & kbs & mbs & gbs & t & -> & HFC & Hi & Hs & Hsn & Htn & HFR & HFX & HCU & HNM & HKN
    & HMK & HMD & HWF & HMA & HRQ & HMM).
  change (ms_mem (MS _ _ _ _ _ m _)) with m.
  pose proof HE as (HS1 & HS2 & HS3 & (Hmd0 & Hmd1 & HmdF) & _).
  pose proof HWF as (_ & _ & _ & _ & _ & (Hm & _)).
  assert (Hn : 0 <= md_n_mark mbs <= 32) by (unfold MARKS_MAX in Hm; lia).
  pose proof HMD as [[HB HW] HL].
  pose proof HNM as [HA HNL]. rewrite Hsn in HA. destruct HA as [Hp0 [HTb HT0]].
  destruct (HNL t Hsn) as (Hl11 & _ & _).
  pose proof (bytes_at_bound rsegs m _ _ HTb) as HTbb. rewrite length_app in HTbb. cbn [length] in HTbb.
  assert (HMQ : remember (md_marks mbs) t = m_marks (c2_MM s kbs gbs))
    by (rewrite HMM; destruct HMA as [_ HMA]; rewrite HMA; reflexivity).
  assert (HR : ov_read_bytes rsegs m (wa (e_md E + MD_N_REQ + 516)) 4 = Some (slice mbs MD_N_MARK 4)).
  { replace (e_md E + MD_N_REQ + 516) with (e_md E + MD_N_MARK) by (unfold MD_N_REQ, MD_N_MARK; lia).
    unfold slice. rewrite (bytes_at_read rsegs m (e_md E) mbs MD_N_MARK 4 HB) by c2m_lia. reflexivity. }
  pose proof HFR as HFRc. unfold c2_frame, lh_cells in HFRc. unfold wz in HFRc |- *.
  (* 0x140d4 lw s5, 0x204(s10); ld s4, 0x10(sp); mv s6, s5 *)
  step. step. step.
  rewrite c2m_lw_val by (change (bytes_le_to_Z (slice mbs MD_N_MARK 4)) with (md_n_mark mbs); lia).
  change (bytes_le_to_Z (slice mbs MD_N_MARK 4)) with (md_n_mark mbs).
  (* blez s5 *)
  step.
  destruct (Z.eq_dec (md_n_mark mbs) 0) as [Hn0|Hn0].
  - c2m_br true.
    eapply c2m_ins; try eassumption; [reflexivity | lia | intros j Hj; exfalso; lia].
  - c2m_br false.
    eapply c2m_loop with (rem := Z.to_nat (md_n_mark mbs)) (k := 0) (base := e_md E + MD_MARK)
                         (sl := c2m_slot mbs) (t := t).
    + lia.
    + lia.
    + lia.
    + lia.
    + c2m_lia.
    + c2m_lia.
    + f_equal. lia.
    + f_equal. lia.
    + intros j Hj. exact (c2m_slot_at m (e_md E) mbs j HMD HWF Hj).
    + rewrite unsigned_lit by c2m_lia. exact HTb.
    + exact HT0.
    + intros j Hj. exfalso. lia.
    + (* a mark is t: the list stays *)
      intros ra' a0' a1' a2' a3' s4' s6' Hin.
      eapply c2m_fin with (m0 := m) (mbs := mbs); try eassumption.
      * rewrite <- HMQ. rewrite c2m_rem_in by (first [lia | exact Hin]); reflexivity.
      * apply c2_seg_fp_refl.
    + (* no mark is t *)
      intros ra' a0' a1' a2' a3' s4' s6' NF.
      step. step.
      destruct (Z.eq_dec (md_n_mark mbs) 32) as [H32|H32].
      * c2m_br true.
        eapply c2m_fin with (m0 := m) (mbs := mbs); try eassumption.
        -- rewrite <- HMQ. rewrite c2m_rem_full by exact H32; reflexivity.
        -- apply c2_seg_fp_refl.
      * c2m_br false.
        eapply c2m_ins; try eassumption; [reflexivity | lia].
Qed.

End M.
