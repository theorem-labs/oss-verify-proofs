(* remember (reac_served_mark.c:38-47), PLAIN build: the walk of its contract (lib/Prog/remember_c.v).

   0x166b4, 48 instructions. Frame 48 (ra, s0..s4). n = m->n (lw at +0x20). If n <= 0, or after a
   strcmp loop over the n kept names (+0x34..+0x4c) found no match and n <= 31, it stores n + 1 into
   m->n (+0x94), restores the frame and TAIL-CALLS snprintf(&m->name[n], 16, "%s", ifname) (+0xb8);
   a match, or n = 32, returns at +0x58 with only the frame written. The callees are taken by their
   contracts: strcmp_contract (lib/Prog/strcmp_c.v) and snprintf_contract (lib/Prog/snprintf_c.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_leaf_fp mk_str mk_marks
  remember_aux remember_c strcmp_c printf_facts_c snprintf_c snprintf strcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemNorm.
Local Open Scope Z_scope.

Definition rem_pre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists gbs nm,
    marks_at m (arg regs 0) gbs /\ marks_wf gbs
    /\ arg regs 1 <> 0 /\ cstr_at m (arg regs 1) nm
    /\ (length nm <= 15)%nat
    /\ cstr_at m A_FMT_S (map (Z_to_bv 8) [37; 115])
    /\ (arg regs 1 + Z.of_nat (length nm) + 8 <= arg regs 0
        \/ arg regs 0 + MK_SIZE <= arg regs 1)
    /\ pf_img_free (arg regs 0) MK_SIZE
    /\ (exists slack, bytes_at rsegs m (arg regs 1 + Z.of_nat (length nm) + 1) slack
          /\ Z.of_nat (length slack) = (- (arg regs 1 + Z.of_nat (length nm) + 1)) mod 8)
    /\ apart_frame regs 6400 (arg regs 0) MK_SIZE
    /\ apart_frame regs 6400 (arg regs 1) (Z.of_nat (length nm) + 8).

Definition rem_post (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall gbs nm,
    marks_at m (arg regs 0) gbs -> cstr_at m (arg regs 1) nm ->
    exists gbs', marks_at m' (arg regs 0) gbs' /\ marks_wf gbs'
    /\ mk_names gbs' = remember (mk_names gbs) nm
    /\ mk_n gbs' = Z.of_nat (length (remember (mk_names gbs) nm)).

Lemma rem_pre_ext : pre_ext rem_pre.
Proof. intros r1 r2 m E H. unfold rem_pre, apart_frame, arg, spZ in *. rewrite <- !E. exact H. Qed.

Lemma rem_post_ext : post_ext rem_post.
Proof.
  intros r1 r2 m q1 q2 m' E1 E2 H gbs nm Hg Hn. unfold rem_post, arg in *.
  rewrite <- !E1 in Hg, Hn |- *. apply H; assumption.
Qed.

Lemma img_pages_hi : 0x960e0 <= IMG_PAGES.
Proof. exact c_pages. Qed.

Theorem remember_walk : strcmp_contract -> snprintf_contract ->
  leaf_fp_walk REMEMBER 6400 rem_pre (fun regs m => [(arg regs 0, arg regs 0 + MK_SIZE)]) rem_post.
Proof.
  intros HSC HSN. unfold leaf_fp_walk, REMEMBER, rem_pre, rem_post.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  cbv zeta. intros (gbs & nm & [Hmk Hlg] & Hwf & Ha1 & [Hnm Nnm] & Hlen & _ & Hsep & Himg & (slack & Hsl & Lsl)
    & Fa0 & Fa1) MI TM ST LO SP FRM ITOP GG [canary GQ].
  unfold apart_frame in Fa0, Fa1. rewrite ?mkR_sp, ?mkR_a0, ?mkR_a1 in *.
  unfold MK_SIZE, A_IMG_TOP in *.
  assert (Hlg' : length gbs = 516%nat) by lia.
  pose proof (marks_n_range gbs Hwf) as Hn.
  destruct Hmk as [Bmk Wmk].
  pose proof (bytes_at_bound _ _ _ _ Bmk) as Bnd. rewrite Hlg' in Bnd.
  pose proof (bytes_at_bound _ _ _ _ Hnm) as Bnm. rewrite length_app in Bnm. cbn [length] in Bnm.
  assert (Lslack : (length slack <= 7)%nat).
  { pose proof (Z.mod_pos_bound (- (bv_unsigned a1 + Z.of_nat (length nm) + 1)) 8 ltac:(lia)). lia. }
  pose proof (img_free_bound (bv_unsigned a0) 516 ltac:(lia) ltac:(lia) Himg) as IFB.
  pose proof img_pages_hi as IPH.
  (* the whole run writes inside these two windows, and each byte of them is readable at entry *)
  assert (RD : forall x : word,
             ~ outside [(bv_unsigned sp - 6400, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 516)]
               (bv_unsigned x) -> exists b, mrd rsegs m x = Some b).
  { intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
    destruct (Z_le_gt_dec (bv_unsigned sp - 6400) (bv_unsigned x)), (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp)).
    - destruct ST as (_ & _ & H). destruct (H (bv_unsigned x) ltac:(lia)) as [_ [b Hb]].
      exists b. unfold wa in Hb. rewrite Z_to_bv_bv_unsigned in Hb. exact Hb.
    - destruct (Z_le_gt_dec (bv_unsigned a0) (bv_unsigned x)), (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned a0 + 516));
        [|exfalso; apply Hx; cbn [outside]; lia..].
      destruct Bmk as (_ & _ & H). specialize (H (Z.to_nat (bv_unsigned x - bv_unsigned a0)) ltac:(lia)).
      rewrite Z2Nat.id in H by lia. replace (bv_unsigned a0 + (bv_unsigned x - bv_unsigned a0)) with (bv_unsigned x) in H by lia.
      unfold wa in H. rewrite Z_to_bv_bv_unsigned in H. rewrite H.
      destruct (nth_error gbs _) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
    - destruct (Z_le_gt_dec (bv_unsigned a0) (bv_unsigned x)), (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned a0 + 516));
        [|exfalso; apply Hx; cbn [outside]; lia..].
      destruct Bmk as (_ & _ & H). specialize (H (Z.to_nat (bv_unsigned x - bv_unsigned a0)) ltac:(lia)).
      rewrite Z2Nat.id in H by lia. replace (bv_unsigned a0 + (bv_unsigned x - bv_unsigned a0)) with (bv_unsigned x) in H by lia.
      unfold wa in H. rewrite Z_to_bv_bv_unsigned in H. rewrite H.
      destruct (nth_error gbs _) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
    - destruct (Z_le_gt_dec (bv_unsigned a0) (bv_unsigned x)), (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned a0 + 516));
        [|exfalso; apply Hx; cbn [outside]; lia..].
      destruct Bmk as (_ & _ & H). specialize (H (Z.to_nat (bv_unsigned x - bv_unsigned a0)) ltac:(lia)).
      rewrite Z2Nat.id in H by lia. replace (bv_unsigned a0 + (bv_unsigned x - bv_unsigned a0)) with (bv_unsigned x) in H by lia.
      unfold wa in H. rewrite Z_to_bv_bv_unsigned in H. rewrite H.
      destruct (nth_error gbs _) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia. }
  pose proof (remember_aux.rw_cells_of_u8arr m (bv_unsigned a0) gbs (conj Bmk Wmk)) as MK. rewrite Hlg' in MK.
  pose proof (munch_refl [(bv_unsigned sp - 6400, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 516)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof ST as ST0.
  (* copies the store tactics leave alone (they rewrite `bytes_at` hypotheses in place) *)
  pose proof (conj Bmk I) as Bmk0. pose proof (conj Hnm I) as Hnm0. pose proof (conj Hsl I) as Hsl0.
  pose proof (conj GG I) as GG0. pose proof (conj GQ I) as GQ0. pose proof (conj Wmk I) as Wmk0.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MUf.
  carve_frame 48%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. zstep.
  assert (L4 : length (firstn 4 (skipn 0 gbs)) = 4%nat) by (rewrite length_firstn, length_skipn; lia).
  rewrite (lw_val _ L4) by (rewrite <- mk_n_slice; lia). rewrite <- mk_n_slice.
  set (n := mk_n gbs) in *.
  zstep.
  (* facts carried to the frame-stored memory m1 *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (Bmk1 : bytes_at rsegs m1 (bv_unsigned a0) gbs).
  { eapply bytes_at_transport; [exact (proj1 Bmk0) | exact MUf |]. cbn [disjoint_from]. rewrite Hlg'. lia. }
  assert (Hnm1 : bytes_at rsegs m1 (bv_unsigned a1) (nm ++ [zb 0])).
  { eapply bytes_at_transport; [exact (proj1 Hnm0) | exact MUf |]. cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
  assert (Hsl1 : bytes_at rsegs m1 (bv_unsigned a1 + Z.of_nat (length nm) + 1) slack).
  { eapply bytes_at_transport; [exact (proj1 Hsl0) | exact MUf |]. cbn [disjoint_from]. lia. }
  assert (GG1 : bytes_at rsegs m1 A_GOT_GUARD (le8 (wz A_GUARD))).
  { eapply bytes_at_transport; [exact (proj1 GG0) | exact MUf |]. cbn [disjoint_from]. rewrite length_le8. unfold A_GOT_GUARD. lia. }
  assert (GQ1 : bytes_at rsegs m1 A_GUARD (le8 canary)).
  { eapply bytes_at_transport; [exact (proj1 GQ0) | exact MUf |]. cbn [disjoint_from]. rewrite length_le8. unfold A_GUARD. lia. }
  match goal with |- evt _ ?Q _ => set (QQ := Q) end.
  (* ---- the early return at +0x58: only the frame was written ---- *)
  assert (RET : forall ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6',
    remember (mk_names gbs) nm = mk_names gbs ->
    evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5'
                           a6' a7' s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 91916) fc None m1 (seg_rom rsegs))).
  { intros ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6' HR.
    zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp). zstep. zstep.
    apply evt_done. unfold QQ. do 4 eexists. split; [reflexivity|].
    split; [exact FRM|]. split; [intros; reflexivity|].
    split; [eapply regs_preserved_mkR|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact (task_mem_frame _ _ _ TM MU RD)|]. split; [exact ST|].
    intros gbs0 nm0 [B0 L0'] H0. rewrite ?mkR_a0 in B0. rewrite ?mkR_a1 in H0.
    assert (E0 : gbs0 = gbs) by (apply (bytes_at_unique m (bv_unsigned a0)); [exact (proj1 B0) | exact (proj1 Bmk0) | unfold MK_SIZE in L0'; lia]).
    assert (E1 : nm0 = nm) by exact (cstr_at_unique m nm0 (bv_unsigned a1) nm H0 (conj (proj1 Hnm0) Nnm)).
    subst gbs0 nm0. exists gbs. rewrite HR. split; [split; [split; [exact Bmk1 | exact (wr_at_transport _ _ _ _ _ (proj1 Wmk0) WM)] | unfold MK_SIZE; lia]|].
    split; [exact Hwf|]. split; [reflexivity|]. rewrite mk_names_length. fold n. lia. }
  (* ---- the store path at +0x78 ---- *)
  assert (WRITE : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s4' t3' t4' t5' t6',
    existsb (fun y => bl_eqb y nm) (mk_names gbs) = false -> n <= 31 ->
    evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' a1 a0 a0' a1' a2' a3' a4' a5'
                           a6' a7' s2' (Z_to_bv 64 n) s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 91948) fc None m1 (seg_rom rsegs))).
  { intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s4' t3' t4' t5' t6' Ex Hn31. clear MUf.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof (rw_cells_split_CB rsegs m1 (bv_unsigned a0) [] 516 gbs [] [4%nat; 512%nat] MK eq_refl) as MK'.
    cbn [app mk_CB_cells] in MK'. clear MK. rename MK' into MK.
    assert (HS : store_ok rsegs m1 a0 4 = true).
    { eapply (rw_cells_store_ok_at rsegs m1 (bv_unsigned a0) _ 0 (CB 4 (firstn 4 gbs)) 4 a0 MK);
        [reflexivity | reflexivity |]. symmetry. apply wa_of_var. lia. }
    pose proof (conj Hnm1 I) as Hnm1c. pose proof (conj Hsl1 I) as Hsl1c.
    pose proof (conj GG1 I) as GG1c. pose proof (conj GQ1 I) as GQ1c.
    pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + 4)] m1) as MUs.
    step.
    replace (write_to_mem m1 a0) with (write_to_mem m1 (wa (bv_unsigned a0 + Z.of_nat 0)))
      by (f_equal; first [apply wa_of_var; lia | symmetry; apply wa_of_var; lia]).
    mem_after_store. zsimp.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp). zstep.
    replace (Z_to_bv 64 (bv_unsigned a0 + n ≪ 4 + 4)) with (Z_to_bv 64 (bv_unsigned a0 + 4 + 16 * n))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    set (D := bv_unsigned a0 + 4 + 16 * n).
    pose proof (rw_cells_bytes _ _ _ MK) as [BK WK]. cbn [cells_bytes cbytes cells_size csize] in BK, WK.
    rewrite app_nil_r in BK.
    assert (LK : length (le4 (Z_to_bv 64 (n + 1)) ++ firstn 512 (skipn 4 gbs)) = 516%nat)
      by (rewrite length_app, length_le4, length_firstn, length_skipn; lia).
    pose proof (rw_cells_slice m2 (bv_unsigned a0) _ (4 + 16 * n) 16 BK ltac:(rewrite LK; exact WK) ltac:(lia) ltac:(lia)
                  ltac:(rewrite LK; lia)) as DSTc.
    replace (bv_unsigned a0 + (4 + 16 * n)) with D in DSTc by (unfold D; lia).
    assert (Hnm2 : bytes_at rsegs m2 (bv_unsigned a1) (nm ++ [zb 0])).
    { eapply bytes_at_transport; [exact (proj1 Hnm1c) | exact MUs |]. cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
    assert (Hsl2 : bytes_at rsegs m2 (bv_unsigned a1 + Z.of_nat (length nm) + 1) slack).
    { eapply bytes_at_transport; [exact (proj1 Hsl1c) | exact MUs |]. cbn [disjoint_from]. lia. }
    assert (GG2 : bytes_at rsegs m2 A_GOT_GUARD (le8 (wz A_GUARD))).
    { eapply bytes_at_transport; [exact (proj1 GG1c) | exact MUs |]. cbn [disjoint_from]. rewrite length_le8. unfold A_GOT_GUARD. lia. }
    assert (GQ2 : bytes_at rsegs m2 A_GUARD (le8 canary)).
    { eapply bytes_at_transport; [exact (proj1 GQ1c) | exact MUs |]. cbn [disjoint_from]. rewrite length_le8. unfold A_GUARD. lia. }
    assert (DU : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; unfold D; lia).
    assert (U16 : bv_unsigned (Z_to_bv 64 16) = 16) by reflexivity.
    assert (ULEN : (length (map bv_unsigned nm) <= 15)%nat) by (rewrite length_map; exact Hlen).
    eapply evt_cut.
    { eapply HSN with (fmt := [37; 115]) (ps := [Ps]) (args := [APtr (map bv_unsigned nm)])
                      (T := map bv_unsigned nm ++ []) (lo := bv_unsigned sp - 6400) (canary := canary)
                      (junk := slice (le4 (Z_to_bv 64 (n + 1)) ++ firstn 512 (skipn 4 gbs)) (4 + 16 * n) 16).
      - rewrite unsigned_lit by lia. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
        vm_compute. repeat split; reflexivity.
      - rewrite unsigned_lit by lia. unfold RO_LO. lia.
      - rewrite unsigned_lit by lia. unfold RO_END. cbn [length]. lia.
      - reflexivity.
      - rewrite DU, U16. cbn [pf_args_ok]. split; [|exact I]. cbn [pf_arg_ok].
        split; [exact (name_bytes_ok nm Nnm)|]. exists slack.
        rewrite length_map. split; [rewrite pf_bytes_name; apply bytes_at_app; split; [exact Hnm2|];
                                    rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add;
                                    replace (bv_unsigned a1 + (Z.of_nat (length nm) + Z.of_nat 1)) with (bv_unsigned a1 + Z.of_nat (length nm) + 1) by lia; exact Hsl2|].
        split; [lia|]. split; [lia|]. split; [lia|]. unfold D. lia.
      - reflexivity.
      - rewrite DU, U16. exact DSTc.
      - rewrite U16. lia.
      - rewrite length_app, length_map. cbn [length]. lia.
      - rewrite DU. unfold D. lia.
      - rewrite DU, U16. unfold D. lia.
      - rewrite DU, U16. unfold D. replace (bv_unsigned a0 + 4 + 16 * n) with (bv_unsigned a0 + (4 + 16 * n)) by lia.
        apply (pf_img_free_sub (bv_unsigned a0) 516); [exact Himg | lia | lia].
      - exact (proj2 (stk_split rsegs m2 lo (bv_unsigned sp - 6400) (bv_unsigned sp) ST ltac:(lia))).
      - unfold SNPRINTF_K. lia.
      - unfold IMG_END. lia.
      - exact SP.
      - exact FRM.
      - exact MI.
      - exact (task_mem_frame _ _ _ TM MU RD).
      - exact GG2.
      - exact GQ2. }
    intros ms' (t0x & t1x & t2x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & Ft & fc' & m3
                & -> & MU3 & WM3 & MI3 & TM3 & FRM3 & FK & ST3 & DST).
    rewrite DU, U16 in MU3, DST.
    replace (firstn (Z.to_nat (16 - 1)) (map bv_unsigned nm ++ [])) with (map bv_unsigned nm) in MU3, DST
      by (rewrite app_nil_r; rewrite firstn_all2 by (rewrite length_map; lia); reflexivity).
    rewrite pf_bytes_name in DST. rewrite length_map in MU3.
    assert (STlo : stk rsegs m3 lo (bv_unsigned sp - 6400)).
    { apply (stk_rebuild m2 m3 _ lo (bv_unsigned sp - 6400)
               (proj1 (stk_split rsegs m2 lo (bv_unsigned sp - 6400) (bv_unsigned sp) ST ltac:(lia))) MU3 WM3).
      intros x Hx. destruct (Z_le_gt_dec D x), (Z_lt_ge_dec x (D + Z.of_nat (length nm) + 1)).
      - right. destruct DST as (_ & _ & HD). specialize (HD (Z.to_nat (x - D)) ltac:(rewrite length_app; cbn [length]; lia)).
        rewrite Z2Nat.id in HD by lia. replace (D + (x - D)) with x in HD by lia. rewrite HD.
        destruct (nth_error _ _) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E.
        rewrite length_app in E. cbn [length] in E. lia.
      - left. cbn [outside]. lia.
      - left. cbn [outside]. lia.
      - left. cbn [outside]. lia. }
    apply evt_done. unfold QQ.
    exists (mkR ra sp gp tp t0x t1x t2x s0 s1 (Z_to_bv 64 (Z.of_nat (length (map bv_unsigned nm ++ []))))
                a1x a2x a3x a4x a5x a6x a7x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6x), Ft, fc', m3.
    split; [reflexivity|]. split; [exact FRM3|]. split; [exact FK|].
    split; [eapply regs_preserved_mkR|].
    split.
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU3].
      intros x Hx. cbn [outside] in *. unfold D. repeat split; try exact I; lia. }
    split; [exact (wmono_trans _ _ _ _ WM WM3)|]. split; [exact MI3|]. split; [exact TM3|].
    split; [exact (stk_merge rsegs m3 lo (bv_unsigned sp - 6400) (bv_unsigned sp) STlo ST3 ltac:(lia))|].
    intros gbs0 nm0 B0 H0. rewrite ?mkR_a0 in B0 |- *. rewrite ?mkR_a1 in H0.
    destruct B0 as [B0 L0'].
    assert (E0 : gbs0 = gbs) by (apply (bytes_at_unique m (bv_unsigned a0)); [exact (proj1 B0) | exact (proj1 Bmk0) | unfold MK_SIZE in L0'; lia]).
    assert (E1 : nm0 = nm) by exact (cstr_at_unique m nm0 (bv_unsigned a1) nm H0 (conj (proj1 Hnm0) Nnm)).
    subst gbs0 nm0.
    destruct (rem_marks_after gbs nm n Hlg' Hwf eq_refl ltac:(lia) Nnm Hlen Ex) as (Lg' & Wf' & Nm' & Nn').
    eexists. split; [|split; [exact Wf' | split; [exact Nm' | exact Nn']]].
    split; [|unfold MK_SIZE; rewrite Lg'; reflexivity].
    split.
    - apply (bytes_at_patch m2 m3 (bv_unsigned a0) _ _ (Z.to_nat (4 + 16 * n)) (nm ++ [zb 0]) BK MU3).
      + rewrite Z2Nat.id by lia. replace (bv_unsigned a0 + (4 + 16 * n)) with D by (unfold D; lia). exact DST.
      + rewrite LK, length_app. cbn [length]. lia.
      + intros x Hx Hn'. rewrite LK in Hx. rewrite Z2Nat.id in Hn' by lia. rewrite length_app in Hn'. cbn [length] in Hn'.
        cbn [outside]. unfold D. repeat split; try exact I; lia.
    - rewrite Lg'. eapply wr_at_transport; [|exact WM3]. exact WK. }
  (* ---- the strcmp loop at +0x34 ---- *)
  assert (LOOP : forall d i ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2w s4w t3' t4' t5' t6',
    (i + S d = Z.to_nat n)%nat ->
    (forall j, (j < i)%nat -> nth_error (mk_names gbs) j <> Some nm) ->
    s2w = Z_to_bv 64 (bv_unsigned a0 + 4 + 16 * Z.of_nat i) -> s4w = Z_to_bv 64 (n - Z.of_nat i) ->
    evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' a1 a0 a0' a1' a2' a3' a4' a5'
                           a6' a7' s2w (Z_to_bv 64 n) s4w s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 91880) fc None m1 (seg_rom rsegs))).
  { induction d as [|d IH]; intros i ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2w s4w t3' t4' t5' t6'
      Hd Hj E2 E4; subst s2w s4w.
    all: assert (Hi : (i < Z.to_nat n)%nat) by lia.
    all: pose proof (slot_cstr m1 (bv_unsigned a0) gbs (Z.of_nat i) Bmk1 Hlg Hwf ltac:(lia)) as [Bs Ns].
    all: pose proof (mk_names_nth gbs i ltac:(fold n; lia)) as NTH.
    all: zstep; zstep; zstep.
    all: eapply evt_cut; [eapply HSC with (sx := cstr (slice gbs (4 + 16 * Z.of_nat i) 16)) (sy := nm);
           [ rewrite unsigned_lit by lia;
             replace (bv_unsigned a0 + 4 + 16 * Z.of_nat i) with (bv_unsigned a0 + (4 + 16 * Z.of_nat i)) by lia;
             exact Bs
           | exact Ns | exact Hnm1 | exact Nnm ] |].
    all: intros ms' (r & x11 & x12 & x13 & -> & Hr).
    all: rewrite ret_pc_even by (lia || reflexivity).
    all: zstep.
    all: case_eq (bv_eqb r (Z_to_bv 64 0)); intros Er; cbv iota.
    - apply bv_eqb_true in Er. apply Hr in Er. rewrite Er in NTH.
      apply RET. unfold remember. rewrite (existsb_some _ nm i NTH). reflexivity.
    - zstep. zstep. zstep.
      rewrite bv_eqb_lit by lia. replace (n - Z.of_nat i + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      cbv [negb]. cbv iota. zstep. zstep. rewrite bv_lts_lit by lia.
      assert (EXF : existsb (fun y => bl_eqb y nm) (mk_names gbs) = false).
      { apply existsb_none. intros j Hj'. rewrite mk_names_length in Hj'. fold n in Hj'.
        destruct (Nat.lt_ge_cases j i) as [Hl|Hge]; [exact (Hj j Hl)|].
        assert (j = i) by lia. subst j. rewrite NTH. intros E. injection E as E. apply Hr in E.
        rewrite E, bv_eqb_refl in Er. discriminate. }
      destruct (Z.ltb_spec 31 n) as [H32|H31].
      + cbv [negb]. cbv iota. apply RET. unfold remember. rewrite EXF, mk_names_length. fold n.
        replace (Z.of_nat (Z.to_nat n) <? MARKS_MAX) with false
          by (symmetry; apply Z.ltb_ge; unfold MARKS_MAX; lia). reflexivity.
      + cbv [negb]. cbv iota. apply WRITE; [exact EXF | lia].
    - apply bv_eqb_true in Er. apply Hr in Er. rewrite Er in NTH.
      apply RET. unfold remember. rewrite (existsb_some _ nm i NTH). reflexivity.
    - zstep. zstep. zstep.
      rewrite bv_eqb_lit by lia. replace (n - Z.of_nat i + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbv [negb]. cbv iota.
      eapply (IH (S i)); [lia | | f_equal; lia | f_equal; lia].
      intros j Hj'. destruct (Nat.lt_ge_cases j i) as [Hl|Hge]; [exact (Hj j Hl)|].
      assert (j = i) by lia. subst j. rewrite NTH. intros E. injection E as E. apply Hr in E.
      rewrite E, bv_eqb_refl in Er. discriminate. }
  zstep. rewrite bv_lts_lit by lia.
  destruct (Z.ltb_spec 0 n) as [Hpos|Hz].
  - cbv [negb]. cbv iota. zstep. zstep.
    eapply (LOOP (Z.to_nat n - 1)%nat 0%nat); [lia | intros j Hj; lia | f_equal; lia | f_equal; lia].
  - cbv [negb]. cbv iota. apply WRITE; [| lia].
    assert (Z0 : n = 0) by lia. unfold mk_names. fold n. rewrite Z0. reflexivity.
Qed.

Theorem remember_holds : strcmp_contract -> snprintf_contract -> remember_contract.
Proof.
  intros HSC HSN. unfold remember_contract. apply leaf_fp_intro.
  - exact rem_pre_ext.
  - intros r1 r2 m E. unfold arg. rewrite <- !E. reflexivity.
  - exact rem_post_ext.
  - exact (remember_walk HSC HSN).
Qed.

(* closed: strcmp and snprintf by their released walks (lib/Prog/strcmp.v, lib/Prog/snprintf.v) *)
Theorem remember_closed : remember_contract.
Proof. exact (remember_holds strcmp_holds snprintf_holds). Qed.
