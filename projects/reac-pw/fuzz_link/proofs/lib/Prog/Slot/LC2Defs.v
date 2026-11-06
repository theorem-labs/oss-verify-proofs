(* op_mark (fuzz_link.c:720-731), arm 2 of the slot's operation loop, plain image: the cut predicates of
   its two evt segments, and the answer the inlined model_mark (fuzz_link.c:442-460) computes.

   Segment A (LC2A.v): lh_ms with op 2 -> c2_15d88, the call of mark_quietly at 0x13dac (ra 0x13db0).
   Segment B (LC2B.v): c2_13db0, mark_quietly's Post at its return -> lh_ms (i + 1) or ex_ms.
   The inner cuts of segment A, each at the pc of its name:
     c2_13d70  name_of, kernel and model_begin are done (0x13afc - 0x13d6c);
     c2_1407c  model_read answered 0 (0x13d70 - 0x13d9c);
     c2_140d4  model_remember is next (the MARK and the OURS-and-served arms, 0x1407c - 0x140d0);
     c2_13da4  model_mark is done (s3 = its answer; 0x13da4 then moves marks and the name to a0 / a1).
   The code: link/ct/dis/plain/LLVMFuzzerTestOneInput.s. Registers at every cut of this arm: s0 = the
   model block, s1 = g_nl + 0x40000, s2 = the name name_of answered, s5 = 46, s6 = the jump table,
   s7 = the marks block, s8 = 0xab, s9 = 4, s10 = &m->n_req, s11 = i. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs.
Local Open Scope Z_scope.

(* ==========================================================================
   1. What the model answers
   ========================================================================== *)

(* model_mark as the slot's inlined code computes it (0x13d70 - 0x14138): the codes of the read and the
   write are model_read's and model_write's, which normalise them (read_model / write_model); the verdict
   v is answered as it is (fuzz_link.c:459), so this is NOT link_spec's mark_model, which normalises v too. *)
Definition mmark (tab : list (list byte * Z)) (nm : option (list byte))
    (marks reqs : list (list byte)) (K : kstate) : mres :=
  match nm with
  | None => Mres (- E_INVAL) marks reqs K
  | Some s =>
      if Nat.eqb (length s) 0 then Mres (- E_INVAL) marks reqs K
      else
        let r := read_model tab nm KIND_CAP ALIAS_MAX reqs K in
        if negb (r_rc r =? 0) then Mres (r_rc r) marks (r_reqs r) (r_state r)
        else
          let v := decide (Some (r_kind r)) (Some (r_alias r)) in
          if v =? V_MARK
          then
            let w := write_model tab nm (Some S_SERVED) (r_reqs r) (r_state r) in
            if negb (w_rc w =? 0) then Mres (w_rc w) marks (w_reqs w) (w_state w)
            else Mres v (remember marks s) (w_reqs w) (w_state w)
          else if (v =? V_OURS) && bl_eqb (r_alias r) S_SERVED
          then Mres v (remember marks s) (r_reqs r) (r_state r)
          else Mres v marks (r_reqs r) (r_state r)
  end.

(* the model's answer in operation i: the name of selector s, the marks the model holds (= the library's,
   marks_are), no request owed yet and the kernel state after model_begin (= the library's) *)
Definition c2_MM (s : Z) (kbs gbs : list byte) : mres :=
  mmark link_tab (sel_name s) (mk_names gbs) [] (nk_kstate kbs).

(* the library's answer, as mark_quietly_c.v's Post states it (M, at tab = link_tab) *)
Definition c2_ML (s : Z) (kbs gbs : list byte) : mres :=
  mark_lib link_tab (sel_name s) (mk_names gbs) (nk_sent kbs) (nk_kstate kbs).

(* the read model_mark makes of a non-empty name t: kind[32] at sp+0x50, alias[256] at sp+0x78 *)
Definition c2_rd (t kbs : list byte) : rres :=
  read_model link_tab (Some t) KIND_CAP ALIAS_MAX [] (nk_kstate kbs).

(* ==========================================================================
   2. The pieces of a cut's memory
   ========================================================================== *)

(* the frame: lh_cells with the cursor cells exact (P at sp+0x40, N at sp+0x48) *)
Definition c2_frame (E : lenv) (P N : Z) (j0 j1 j2 : list byte) (m : word -> option byte) : Prop :=
  rw_cells rsegs m (e_S E - SLOT_FRAME) (lh_cells (e_md E) (e_mk E) P N j0 j1 j2).

(* what no step of the arm changes (or gives back as it was): the saved registers, the image's tables and
   strings, long_alias, errno, the guard words, and the three whole-memory facts *)
Definition c2_fix (E : lenv) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (e_S E - 104) (e_saved E) /\
  gnames_at m /\ odd_at m /\ policy_ro m /\ la_ok m /\ texts_at m /\ ifptrs_at m /\
  wr_at rsegs m A_ERRNO 4 /\ guard_m m /\
  mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\
  stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME).

(* the fake kernel after kernel and model_begin (nk_next = 0 from kernel, n_sent = 0 from model_begin) *)
Definition c2_kern (i : Z) (kbs : list byte) (m : word -> option byte) : Prop :=
  nlk_at m kbs /\ nlk_wf kbs /\ iftab_at m kbs link_tab /\
  nk_open kbs = 0 /\ nk_misuse kbs = 0 /\ nk_opened kbs = nk_closed kbs /\ nk_opened kbs <= 64 * i /\
  nk_next kbs = 0 /\ nk_n_sent kbs = 0.

(* the marks block, untouched until mark_quietly *)
Definition c2_marks (E : lenv) (gbs : list byte) (m : word -> option byte) : Prop :=
  marks_at m (e_mk E) gbs /\ marks_wf gbs.

(* the name name_of answered for selector s (fuzz_link.c:102-110): NULL, or a C string of at most 11
   bytes that is a g_names slot (at most 4 bytes) or an `odd` string in the read-only image, with the
   bytes up to the next multiple of 8 after its NUL (the slack snprintf's %s and strlen read) *)
Definition c2_name_ok (m : word -> option byte) (s : Z) : Prop :=
  str_arg m (sel_ptr s) (sel_name s) /\
  forall t, sel_name s = Some t ->
    (length t <= 11)%nat /\
    ((A_RO_LO <= sel_ptr s /\ sel_ptr s + 16 <= A_RO_END) \/
     (exists k, 0 <= k < 64 /\ sel_ptr s = A_G_NAMES + 8 * k /\ (length t <= 4)%nat)) /\
    (exists slack, bytes_at rsegs m (sel_ptr s + Z.of_nat (length t) + 1) slack /\
       Z.of_nat (length slack) = (- (sel_ptr s + Z.of_nat (length t) + 1)) mod 8).

(* ==========================================================================
   3. The cuts of segment A
   ========================================================================== *)

(* 0x13d70: name_of, kernel and model_begin done. The model starts from the kernel's own state with no
   request owed, and holds the marks the library holds. *)
Definition c2_13d70 (E : lenv) (i : Z) (gp : word) (s : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (j0 j1 j2 kbs mbs gbs : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr s)) s3 s4 (wz 46) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz 0x13d70) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= s <= 255 /\
    c2_frame E P N j0 j1 j2 m /\ c2_fix E m /\ cursor_ok m (e_p0 E) (e_pl E) P N /\ c2_name_ok m s /\
    c2_kern i kbs m /\ c2_marks E gbs m /\
    model_at m (e_md E) mbs /\ model_wf mbs /\ marks_are gbs mbs /\
    md_kstate mbs kbs = nk_kstate kbs /\ md_n_req mbs = 0.

(* 0x1407c: model_read (0x13d98) answered 0 for the non-empty name t; kind[32] (sp+0x50) and alias[256]
   (sp+0x78) hold its two C strings, and the model block its requests and its state after the exchange *)
Definition c2_1407c (E : lenv) (i : Z) (gp : word) (s : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (j0 j1 j2 kbs mbs gbs t : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr s)) s3 s4 (wz 46) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz 0x1407c) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= s <= 255 /\
    sel_name s = Some t /\ t <> [] /\
    c2_frame E P N j0 j1 j2 m /\ c2_fix E m /\ cursor_ok m (e_p0 E) (e_pl E) P N /\ c2_name_ok m s /\
    c2_kern i kbs m /\ c2_marks E gbs m /\
    r_rc (c2_rd t kbs) = 0 /\
    model_at m (e_md E) mbs /\ model_wf mbs /\ marks_are gbs mbs /\
    md_kstate mbs kbs = r_state (c2_rd t kbs) /\ md_reqs mbs = r_reqs (c2_rd t kbs) /\
    cstr_at m (e_S E - SLOT_FRAME + FO_B40) (r_kind (c2_rd t kbs)) /\
    cstr_at m (e_S E - SLOT_FRAME + FO_B256) (r_alias (c2_rd t kbs)).

(* 0x140d4: model_remember(m, name) is next (s3 = the verdict). The model's answer is the verdict, its
   marks are `remember` of the marks it holds, and the block holds every request it owes. *)
Definition c2_140d4 (E : lenv) (i : Z) (gp : word) (s : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (j0 j1 j2 kbs mbs gbs t : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr s)) (wz (m_rc (c2_MM s kbs gbs))) s4 (wz 46) (wz A_JT) (wz (e_mk E))
                 (wz 0xab) (wz 4) (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz 0x140d4) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= s <= 255 /\
    sel_name s = Some t /\ t <> [] /\
    c2_frame E P N j0 j1 j2 m /\ c2_fix E m /\ cursor_ok m (e_p0 E) (e_pl E) P N /\ c2_name_ok m s /\
    c2_kern i kbs m /\ c2_marks E gbs m /\
    model_at m (e_md E) mbs /\ model_wf mbs /\ marks_are gbs mbs /\
    md_reqs mbs = m_reqs (c2_MM s kbs gbs) /\
    m_marks (c2_MM s kbs gbs) = remember (mk_names gbs) t.

(* 0x13da4: model_mark is done; s3 = its answer, the model block holds the requests and the marks it
   owes. The marks block and the fake kernel are as model_begin left them. *)
Definition c2_13da4 (E : lenv) (i : Z) (gp : word) (s : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (j0 j1 j2 kbs mbs gbs : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr s)) (wz (m_rc (c2_MM s kbs gbs))) s4 (wz 46) (wz A_JT) (wz (e_mk E))
                 (wz 0xab) (wz 4) (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz 0x13da4) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= s <= 255 /\
    c2_frame E P N j0 j1 j2 m /\ c2_fix E m /\ cursor_ok m (e_p0 E) (e_pl E) P N /\ c2_name_ok m s /\
    c2_kern i kbs m /\ c2_marks E gbs m /\
    model_at m (e_md E) mbs /\ model_wf mbs /\
    md_reqs mbs = m_reqs (c2_MM s kbs gbs) /\ md_marks mbs = m_marks (c2_MM s kbs gbs).

(* ==========================================================================
   4. The two SR cuts: the call of mark_quietly and its return
   ========================================================================== *)

(* 0x15d88 = mark_quietly's entry, ra = 0x13db0, a0 = marks, a1 = name (jal at 0x13dac). What its Pre
   asks of the slot's registers and memory: the fake kernel (c2_kern: nlk_at, nlk_wf, iftab_at link_tab,
   open = 0, the counters), the name (c2_name_ok: str_arg, at most 11 <= 15 bytes, its place and slack),
   the marks block (c2_marks), errno writable and the guard words (c2_fix); the rest is what the code after
   the call needs. *)
Definition c2_15d88 (E : lenv) (i : Z) (gp : word) (s : Z) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (j0 j1 j2 kbs mbs gbs : list byte),
    ms = MS (mkR (wz 0x13db0) (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 (wz (e_mk E)) (wz (sel_ptr s)) a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr s)) (wz (m_rc (c2_MM s kbs gbs))) s4 (wz 46) (wz A_JT) (wz (e_mk E))
                 (wz 0xab) (wz 4) (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz P_mark_quietly) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= s <= 255 /\
    c2_frame E P N j0 j1 j2 m /\ c2_fix E m /\ cursor_ok m (e_p0 E) (e_pl E) P N /\ c2_name_ok m s /\
    c2_kern i kbs m /\ c2_marks E gbs m /\
    model_at m (e_md E) mbs /\ model_wf mbs /\
    md_reqs mbs = m_reqs (c2_MM s kbs gbs) /\ md_marks mbs = m_marks (c2_MM s kbs gbs).

(* 0x13db0, mark_quietly's return: its Post (mark_quietly_c.v, the `getr regs 10 <> 0` arm, at tab =
   link_tab, nm = sel_name s, the kbs and gbs of the call) over the new memory, the callee-saved
   registers of the call (regs_preserved), a0 = its answer, and the call cut's facts over the regions
   mark_quietly does not write (the frame, the model block, the image's tables, long_alias, errno, the
   payload). kbs / gbs are the kernel and the marks AT THE CALL; only their scalars are kept. *)
Definition c2_13db0 (E : lenv) (i : Z) (gp : word) (s : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (j0 j1 j2 kbs mbs gbs : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 (Z_to_bv 64 (m_rc (c2_ML s kbs gbs))) a1 a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr s)) (wz (m_rc (c2_MM s kbs gbs))) s4 (wz 46) (wz A_JT) (wz (e_mk E))
                 (wz 0xab) (wz 4) (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz 0x13db0) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= s <= 255 /\
    (* kept across the call *)
    c2_frame E P N j0 j1 j2 m /\ c2_fix E m /\ cursor_ok m (e_p0 E) (e_pl E) P N /\
    model_at m (e_md E) mbs /\ model_wf mbs /\
    md_reqs mbs = m_reqs (c2_MM s kbs gbs) /\ md_marks mbs = m_marks (c2_MM s kbs gbs) /\
    (* the scalars of the kernel and the marks at the call *)
    nlk_wf kbs /\ nk_open kbs = 0 /\ nk_misuse kbs = 0 /\ nk_opened kbs = nk_closed kbs /\
    nk_opened kbs <= 64 * i /\ nk_next kbs = 0 /\ nk_n_sent kbs = 0 /\ marks_wf gbs /\
    (* mark_quietly's Post *)
    (exists gbs', marks_at m (e_mk E) gbs' /\ marks_wf gbs'
       /\ mk_names gbs' = m_marks (c2_ML s kbs gbs)
       /\ mk_n gbs' = Z.of_nat (length (m_marks (c2_ML s kbs gbs)))) /\
    (exists kbs', nlk_at m kbs' /\ nlk_wf kbs'
       /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
       /\ nk_n_if kbs' = nk_n_if kbs /\ iftab_at m kbs' link_tab
       /\ nk_next kbs' = Z.of_nat (k_next (m_state (c2_ML s kbs gbs)))
       /\ nk_sent kbs' = m_reqs (c2_ML s kbs gbs)
       /\ nk_n_sent kbs' = Z.of_nat (length (m_reqs (c2_ML s kbs gbs)))
       /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
       /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
       /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 2).

(* ==========================================================================
   5. Gluing evt pieces: posts hold up to ms_eqv (LDefs eqv_cl) and carry the footprint seg_fp against
      the piece's start memory, with the two heap blocks the arm holds
   ========================================================================== *)

Definition c2_hp (E : lenv) : list (Z * Z) := [(e_md E, MD_SIZE); (e_mk E, MK_SIZE)].

(* the post every piece of the arm ends in: Q up to ms_eqv, and only the arm's own regions written
   since the piece's start memory m0 *)
Definition c2_post (E : lenv) (m0 : word -> option byte) (Q : machine_state -> Prop) : machine_state -> Prop :=
  eqv_cl (fun c => Q c /\ seg_fp (e_S E) (c2_hp E) m0 (ms_mem c)).

Lemma c2_xregs_eqv_trans : forall R1 R2 R3, xregs_eqv R1 R2 -> xregs_eqv R2 R3 -> xregs_eqv R1 R3.
Proof. intros R1 R2 R3 H1 H2 r Hr. rewrite (H1 r Hr). exact (H2 r Hr). Qed.

Lemma c2_ms_eqv_trans : forall a b c, ms_eqv a b -> ms_eqv b c -> ms_eqv a c.
Proof.
  intros a b c (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8).
  split; [exact (c2_xregs_eqv_trans _ _ _ H1 K1)|].
  repeat split; congruence.
Qed.

Lemma c2_ms_eqv_refl : forall a, ms_eqv a a.
Proof. intros a. split; [intros r _; reflexivity|]. repeat split. Qed.

Lemma c2_outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma c2_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_le_gt_dec lo x) as [L|L]; destruct (Z_lt_ge_dec x hi) as [U|U].
  - right. intros [Hn _]. apply Hn. lia.
  - left. split; [lia | exact H].
  - left. split; [lia | exact H].
  - left. split; [lia | exact H].
Qed.

Lemma c2_seg_fp_refl : forall S hp m, seg_fp S hp m m.
Proof.
  intros S hp m. exists []. split; [apply munch_refl|]. split; [apply wmono_refl|].
  intros x _ H. exfalso. apply H. exact I.
Qed.

Lemma c2_seg_fp_trans : forall S hp m1 m2 m3, seg_fp S hp m1 m2 -> seg_fp S hp m2 m3 -> seg_fp S hp m1 m3.
Proof.
  intros S hp m1 m2 m3 (W1 & M1 & V1 & O1) (W2 & M2 & V2 & O2).
  exists (W1 ++ W2). split; [|split].
  - intros x Hx. apply c2_outside_app in Hx. destruct Hx as [H1 H2]. rewrite (M2 x H2). exact (M1 x H1).
  - exact (wmono_trans _ _ _ _ V1 V2).
  - intros x Hx Hn. destruct (c2_outside_dec W1 x) as [H1|H1]; [|exact (O1 x Hx H1)].
    destruct (c2_outside_dec W2 x) as [H2|H2]; [|exact (O2 x Hx H2)].
    exfalso. apply Hn. apply c2_outside_app. split; assumption.
Qed.

Lemma c2_post_done : forall E (Q : machine_state -> Prop) ms, Q ms -> evt rsegs (c2_post E (ms_mem ms) Q) ms.
Proof.
  intros E Q ms H. apply evt_done. exists ms. split; [split; [exact H | apply c2_seg_fp_refl] | apply c2_ms_eqv_refl].
Qed.

(* run to Q, then from every Q state to R: R, with the two footprints joined *)
Lemma c2_post_seq : forall E (Q R : machine_state -> Prop) ms,
  evt rsegs (c2_post E (ms_mem ms) Q) ms ->
  (forall c, Q c -> evt rsegs (c2_post E (ms_mem c) R) c) ->
  evt rsegs (c2_post E (ms_mem ms) R) ms.
Proof.
  intros E Q R ms H K. eapply evt_cut; [exact H|]. intros ms1 (c & (HQ & F1) & HE).
  pose proof (evt_register_transport rsegs _ c ms1 HE (K c HQ)) as H2.
  eapply evt_mono; [exact H2|]. intros a (c' & (c'' & (HR & F2) & E1) & E2).
  exists c''. split; [split; [exact HR|] | exact (c2_ms_eqv_trans _ _ _ E1 E2)].
  exact (c2_seg_fp_trans _ _ _ _ _ F1 F2).
Qed.

Lemma c2_post_mono : forall E m0 (Q R : machine_state -> Prop) ms,
  evt rsegs (c2_post E m0 Q) ms -> (forall c, Q c -> R c) -> evt rsegs (c2_post E m0 R) ms.
Proof.
  intros E m0 Q R ms H K. eapply evt_mono; [exact H|]. intros a (c & (HQ & F) & E1).
  exists c. split; [split; [exact (K c HQ) | exact F] | exact E1].
Qed.
