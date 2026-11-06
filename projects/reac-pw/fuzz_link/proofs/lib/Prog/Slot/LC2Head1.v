(* Arm c2 (op_mark), piece HEAD, first segment: the loop head with op 2 (lh_ms, lh_op 2) -> the call of
   kernel at 0x13d48 (c2h_13d48).
   0x13a1c - 0x13a64: the dispatch (op = b mod 6 = 2, the jump table of the image, jr 0x13afc);
   0x13afc - 0x13d44: op_mark's inlined fuzz_u8 and name_of (fuzz_link.c:102-110, :720-722): the selector
   s (0 for an empty input), s2 = the name's pointer (LDefs.sel_ptr s), the cursor advanced by 1 or 2.
   The only writes are the two cursor cells of the frame (sp + 0x40, sp + 0x48). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC2Defs LC2HeadA LC2HeadB.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Glue: the post of a piece, footprints, task_mem
   ========================================================================== *)

Lemma c2h_post_intro : forall E m0 (Q : machine_state -> Prop) ms,
  Q ms -> seg_fp (e_S E) (c2_hp E) m0 (ms_mem ms) -> c2_post E m0 Q ms.
Proof. intros E m0 Q ms HQ HF. exists ms. split; [split; assumption | apply c2_ms_eqv_refl]. Qed.

Lemma c2h_not_outside : forall W x, ~ outside W x -> exists lo hi, In (lo, hi) W /\ lo <= x < hi.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn in H; [exfalso; exact (H I)|].
  destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
  - exists lo, hi. split; [left; reflexivity | lia].
  - destruct (IH x) as (l & h & Hin & Hx).
    + intros HO. apply H. split; [lia | exact HO].
    + exists l, h. split; [right; exact Hin | exact Hx].
  - destruct (IH x) as (l & h & Hin & Hx).
    + intros HO. apply H. split; [lia | exact HO].
    + exists l, h. split; [right; exact Hin | exact Hx].
Qed.

Lemma c2h_task_size : TASK_SIZE = 2 ^ 47.
Proof. vm_compute. reflexivity. Qed.

Lemma c2h_task_mem_munch : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> x < 2 ^ 47) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' HT MU HW a b Ha. pose proof (bv_unsigned_in_range 64 a) as Ra.
  change (bv_modulus 64) with (2 ^ 64) in Ra.
  destruct (c2_outside_dec W (bv_unsigned a)) as [HO|HO].
  - rewrite (MU a HO) in Ha. exact (HT a b Ha).
  - right. rewrite c2h_task_size. exact (HW _ Ra HO).
Qed.

Lemma c2h_u64_read : forall m a v, u64_at m a v -> ov_read_bytes rsegs m (Z_to_bv 64 a) 8 = Some (le8 (wz v)).
Proof.
  intros m a v H. unfold u64_at in H.
  pose proof (bytes_at_ov_read rsegs m a _ 0 8 H ltac:(rewrite length_le8; lia)) as R.
  unfold wa in R. change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r in R. rewrite R.
  rewrite firstn_all2 by (rewrite length_skipn, length_le8; lia). reflexivity.
Qed.

(* the cursor cell sp + 0x40 that lh_op reads is the frame's P *)
Lemma c2h_P_eq : forall m A md mk P N j0 j1 j2 P',
  rw_cells rsegs m A (lh_cells md mk P N j0 j1 j2) -> bytes_at rsegs m (A + FO_P) (le8 (wz P')) ->
  0 <= P < 2 ^ 64 -> 0 <= P' < 2 ^ 64 -> P' = P.
Proof.
  intros m A md mk P N j0 j1 j2 P' HC HP R1 R2.
  destruct (c2h_frame_split _ _ _ _ _ _ _ _ _ HC) as (_ & H2 & _).
  destruct (c2h_cells2_bytes _ _ _ _ H2) as [B _].
  change (A + FO_P) with (A + 64) in HP.
  pose proof (c2h_bytes_at_unique _ _ _ _ HP B ltac:(rewrite !length_le8; reflexivity)) as E.
  apply c2h_le8_inj in E. apply (f_equal bv_unsigned) in E. unfold wz in E.
  rewrite !unsigned_lit in E by lia. exact E.
Qed.

Ltac c2h_dj :=
  cbn [disjoint_from e_S e_md e_mk e_p0 e_pl e_saved];
  unfold c2h_img_lo, c2h_if_lo, c2h_if_n, A_G_NL, NK_IF_NAME, NK_N_IF, NK_SIZE, NK_OPEN, NK_N_SENT,
    A_G_NAMES, A_GUARD_S, MK_SIZE, MD_SIZE, A_LONG_ALIAS, LONG_ALIAS_SIZE, SLOT_STACK_Z, SLOT_FRAME,
    MD_N_REQ in *;
  lia.

(* ==========================================================================
   2. The end of the segment, in every branch of name_of
   ========================================================================== *)

Lemma c2h_h1_fin : forall (S md mk p0 : Z) (pl sv : list byte) (i : Z) (gp : word) (s : Z)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (P N : Z) (j0 j1 j2 kbs mbs gbs : list byte),
  lenv_ok (LEnv S md mk p0 pl sv) ->
  c2h_keep (LEnv S md mk p0 pl sv) gbs m0 ->
  nlk_at m0 kbs -> c2h_kfacts i kbs -> iftab_at m0 kbs link_tab -> la_ok m0 ->
  model_at m0 md mbs -> model_wf mbs -> marks_wf gbs -> marks_are gbs mbs ->
  MemNorm.task_mem rsegs m0 ->
  munch [(S - 416, S - 400)] m0 m -> wmono rsegs m0 m ->
  mem_inv rsegs m -> stk rsegs m (S - 65536) (S - 480) ->
  c2_frame (LEnv S md mk p0 pl sv) P N j0 j1 j2 m ->
  c2h_cur (LEnv S md mk p0 pl sv) P N ->
  frm0 fc -> 0 <= i <= 47 -> 0 <= s <= 255 ->
  c2_post (LEnv S md mk p0 pl sv) m0 (fun c => exists s, c2h_13d48 (LEnv S md mk p0 pl sv) i gp s c)
    (MS (mkR ra (wz (S - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz md) (wz GNL40) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (sel_ptr s)) s3 s4 (wz 46) (wz A_JT) (wz mk) (wz 0xab) (wz 4) (wz (md + MD_N_REQ)) (wz i)
             t3 t4 t5 t6)
        F (wz 0x13d48) fc None m (seg_rom rsegs)).
Proof.
  intros S md mk p0 pl sv i gp s ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 F fc m0 m P N
    j0 j1 j2 kbs mbs gbs HE K HNK KF HIF HLA HMD HMDwf HMKwf HMA TM MU WM MI ST HC HCUR FRM Hi Hs.
  pose proof HE as HE'. unfold lenv_ok, blk_out in HE'. cbn [e_S e_md e_mk e_p0 e_pl e_saved] in HE'.
  destruct HE' as (HS1 & HS2 & HS3 & (Hmd1 & Hmd2 & Hmd3) & (Hmk1 & Hmk2 & Hmk3) & Hmd16 & Hmk16 & Hmdmk & Hpl1
                   & (Hp01 & Hp02 & Hp03) & Hplmd & Hplmk & Hsv).
  assert (HIFP : ifptrs_at m0) by (destruct K as (_ & _ & _ & _ & _ & X & _); exact X).
  apply c2h_post_intro.
  - exists s. unfold c2h_13d48. do 18 eexists. exists F, fc, m, P, N, j0, j1, j2, kbs, mbs, gbs.
    split; [reflexivity|].
    split; [exact FRM|]. split; [exact Hi|]. split; [exact Hs|]. split; [exact HC|].
    split.
    { eapply c2h_keep_munch; [exact Hsv | exact K | exact MU | exact WM | c2h_dj ..]. }
    split; [exact HCUR|].
    split.
    { destruct HNK as [U L]. split; [|exact L]. eapply c2h_blk_keep; [exact U | exact MU | exact WM |].
      rewrite L. c2h_dj. }
    split; [exact KF|].
    split.
    { eapply c2h_iftab_keep; [exact HIF | exact HIFP | reflexivity | exact MU | c2h_dj ..]. }
    split.
    { eapply c2h_la_keep; [exact HLA | exact MU | exact WM | c2h_dj]. }
    split.
    { destruct HMD as [U L]. split; [|exact L]. eapply c2h_blk_keep; [exact U | exact MU | exact WM |].
      rewrite L. c2h_dj. }
    split; [exact HMDwf|]. split; [exact HMKwf|]. split; [exact HMA|]. split; [exact MI|].
    split; [|exact ST].
    eapply c2h_task_mem_munch; [exact TM | exact MU |].
    intros x Hx HO. destruct (c2h_not_outside _ _ HO) as (lo & hi & Hin & Hr).
    cbn [In] in Hin. destruct Hin as [Ein|[]]. injection Ein as <- <-. lia.
  - exists [(S - 416, S - 400)]. split; [exact MU|]. split; [exact WM|].
    intros x Hx HO. destruct (c2h_not_outside _ _ HO) as (lo & hi & Hin & Hr).
    cbn [In] in Hin. destruct Hin as [Ein|[]]. injection Ein as <- <-.
    unfold own_w. left. cbn [e_S]. unfold SLOT_STACK_Z. lia.
Qed.

(* ==========================================================================
   3. The segment
   ========================================================================== *)

Lemma c2h_head1 : forall (E : lenv) (i : Z) (gp : word) (ms : machine_state),
  lenv_ok E -> lh_ms E i gp ms -> lh_op E ms 2 ->
  evt rsegs (c2_post E (ms_mem ms) (fun c => exists s, c2h_13d48 E i gp s c)) ms.
Proof.
  intros [S md mk p0 pl sv] i gp ms HE HL HO.
  destruct HO as (P' & b & HP' & Hb & Hb6).
  destruct HL as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 & F & fc
                  & m & P & N & kbs & mbs & gbs & Ems & FRM & Hi & HN & HM & MI & TM & ST).
  assert (Em : ms_mem ms = m) by (rewrite Ems; reflexivity).
  rewrite Em in HP', Hb |- *. subst ms.
  destruct HM as ((j0 & j1 & j2 & nc & HC) & HSV & HNK & HNKwf & HIF & Hopen & Hmis & Hoc & Hop & HGN & HODD
                  & HPOL & HLA & HTX & HIFP & HMD & HMDwf & HMK & HMKwf & HMA & HCUR & HERR & HGU).
  cbn [e_S e_md e_mk e_p0 e_pl e_saved] in *.
  destruct HCUR as [HPL (k & Hk & EP & EN)].
  pose proof HE as HE'. unfold lenv_ok, blk_out in HE'. cbn [e_S e_md e_mk e_p0 e_pl e_saved] in HE'.
  destruct HE' as (HS1 & HS2 & HS3 & (Hmd1 & Hmd2 & Hmd3) & (Hmk1 & Hmk2 & Hmk3) & Hmd16 & Hmk16 & Hmdmk & Hpl1
                   & (Hp01 & Hp02 & Hp03) & Hplmd & Hplmk & Hsv).
  unfold SLOT_STACK_Z, MD_SIZE, MK_SIZE in Hmd2, Hmk2, Hp02, Hplmd, Hplmk, Hmdmk.
  (* P is the cursor cell's word *)
  assert (EP' : P' = P).
  { pose proof (bytes_at_bound _ _ _ _ Hb) as BB. cbn [length] in BB.
    eapply c2h_P_eq; [exact HC | exact HP' | subst P; lia | lia]. }
  subst P'. clear HP'.
  pose proof (c2h_read_byte m P [b] 0 b Hb eq_refl) as HB. change (Z.of_nat 0) with 0 in HB.
  rewrite Z.add_0_r in HB.
  (* the facts no write of the segment touches, against the start memory m *)
  assert (K0 : c2h_keep (LEnv S md mk p0 pl sv) gbs m).
  { destruct HLA as (la & sl & _ & HSL & HSL3).
    refine (conj HSV (conj HGN (conj HODD (conj HPOL (conj HTX (conj HIFP (conj HGU (conj HERR _)))))))).
    refine (conj HMK (conj HPL _)). exists sl. exact (conj HSL HSL3). }
  assert (KF : c2h_kfacts i kbs) by exact (conj HNKwf (conj Hopen (conj Hmis (conj Hoc Hop)))).
  clear Hb HSV HERR HNKwf Hopen Hmis Hoc Hop.
  pose proof (munch_refl [(S - 416, S - 400)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold lh_cells, wz, SLOT_FRAME, SLOT_STACK_Z, L_LH, A_TP, GNL40, GNL42, A_JT, A_G_NL, MD_N_REQ, A_ODD,
    A_EMPTY, A_G_NAMES, MD_MARK in HC, ST |- *.
  (* the dispatch: 0x13a1c - 0x13a64 *)
  do 13 step.
  match goal with |- context [Z.land ?e 255] =>
    replace (Z.land e 255) with 2 by (first [apply c2h_disp_mod6 | symmetry; apply c2h_disp_mod6]; exact Hb6)
  end.
  step. if_false. do 5 step.
  (* op_mark: 0x13afc beqz a1 (in.n - 1 = 0) *)
  step. if_cases HC0.
  - (* an empty input: fuzz_u8 answers 0, s2 = g_names *)
    zify_cond HC0. try rewrite Z.mod_small in HC0 by lia.
    do 6 step.
    apply evt_done.
    eapply (c2h_h1_fin S md mk p0 pl sv i gp 0);
      [exact HE | exact K0 | exact HNK | exact KF | exact HIF | exact HLA | exact HMD | exact HMDwf
      | exact HMKwf | exact HMA | exact TM | exact MU | exact WM | exact MI | exact ST | exact HC | | exact FRM
      | exact Hi | lia].
    exists (k + 1). cbn [e_p0 e_pl]. lia.
  - zify_cond HC0. try rewrite Z.mod_small in HC0 by lia.
    (* the selector byte at P + 1 *)
    destruct (nth_error pl (Z.to_nat k + 1)) as [c|] eqn:Ec.
    2:{ exfalso. apply nth_error_None in Ec. lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with HPLm : bytes_at rsegs mm p0 pl |- _ =>
        pose proof (c2h_read_byte mm p0 pl (Z.to_nat k + 1) c HPLm Ec) as HB2
      end
    end.
    replace (p0 + Z.of_nat (Z.to_nat k + 1)) with (P + 1) in HB2 by lia.
    do 7 step.
    if_cases HC1.
    + (* s <> 255 *)
      zify_cond HC1. try rewrite (unsigned_lit (bv_unsigned c)) in HC1 by (pose proof (c2h_byte_range c); lia).
      step. step. if_cases HC2.
      * (* s > 63: odd[s % 6] *)
        zify_cond HC2. try rewrite (unsigned_lit (bv_unsigned c)) in HC2 by (pose proof (c2h_byte_range c); lia).
        do 10 step.
        (* a0 = odd + 8 (s mod 6): the mulhu by 0x2aaaaaaaaaaaaaab is s / 6 *)
        lazymatch goal with |- context [Z_to_bv 64 (133056 + ?e)] =>
          assert (EQa : e = 8 * (bz c mod 6)); [|rewrite EQa]
        end.
        { clear - HC2. rewrite !c2h_zxb. pose proof (c2h_byte_range c). unfold bz in *. c2h_zsolve. }
        assert (Hj : (Z.to_nat (bz c mod 6) < 6)%nat) by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; cbn; lia).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (HR : ov_read_bytes rsegs mm (Z_to_bv 64 (133056 + 8 * (bz c mod 6))) 8
                       = Some (le8 (Z_to_bv 64 (nth (Z.to_nat (bz c mod 6)) odd_ptrs 0))))
        end.
        { destruct (c2h_odd_keep _ _ _ HODD MU ltac:(c2h_dj) _ Hj) as [U _].
          pose proof (c2h_u64_read _ _ _ U) as R. rewrite Z2Nat.id in R by lia. exact R. }
        step.
        rewrite <- (c2h_sel_ptr_hi (bz c)) by (unfold bz; lia).
        apply evt_done.
        eapply (c2h_h1_fin S md mk p0 pl sv i gp (bz c));
          [exact HE | exact K0 | exact HNK | exact KF | exact HIF | exact HLA | exact HMD | exact HMDwf
          | exact HMKwf | exact HMA | exact TM | exact MU | exact WM | exact MI | exact ST | exact HC | | exact FRM
          | exact Hi | pose proof (c2h_byte_range c); unfold bz; lia].
        exists (k + 2). cbn [e_p0 e_pl]. lia.
      * (* s <= 63: g_names + 8 s *)
        zify_cond HC2. try rewrite (unsigned_lit (bv_unsigned c)) in HC2 by (pose proof (c2h_byte_range c); lia).
        do 4 step.
        match goal with |- context [Z_to_bv 64 (475640 + ?e)] =>
          assert (EQs : Z_to_bv 64 (475640 + e) = Z_to_bv 64 (sel_ptr (bz c)))
            by (rewrite (c2h_sel_ptr_lo (bz c)) by (unfold bz; pose proof (c2h_byte_range c); lia);
                f_equal; clear - HC2; rewrite c2h_zxb; unfold bz, A_G_NAMES in *;
                rewrite Z.shiftl_mul_pow2 by lia; lia);
          rewrite EQs
        end.
        apply evt_done.
        eapply (c2h_h1_fin S md mk p0 pl sv i gp (bz c));
          [exact HE | exact K0 | exact HNK | exact KF | exact HIF | exact HLA | exact HMD | exact HMDwf
          | exact HMKwf | exact HMA | exact TM | exact MU | exact WM | exact MI | exact ST | exact HC | | exact FRM
          | exact Hi | pose proof (c2h_byte_range c); unfold bz; lia].
        exists (k + 2). cbn [e_p0 e_pl]. lia.
    + (* s = 255: NULL *)
      do 2 step.
      apply evt_done.
      eapply (c2h_h1_fin S md mk p0 pl sv i gp 255);
        [exact HE | exact K0 | exact HNK | exact KF | exact HIF | exact HLA | exact HMD | exact HMDwf
        | exact HMKwf | exact HMA | exact TM | exact MU | exact WM | exact MI | exact ST | exact HC | | exact FRM
        | exact Hi | lia].
      exists (k + 2). cbn [e_p0 e_pl]. lia.
Qed.
