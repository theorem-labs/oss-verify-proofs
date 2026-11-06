(** The pod's write in the pod loop of the UBSan builder of reac-pw/fuzz_rate's LLVMFuzzerTestOneInput,
    0x13ee4 -> 0x13f48 (pod.h:428-432), proved against [Cut.S_write] with the contracts of pod_write_ent and memcpy
    as premises: the stop test of pod.h:428 (0x13ee4-0x13eec `ld a0,0(s11)`, `addi a1,a0,0x70`, `bltu s6,a1` with
    s6 = 0x4000; never taken), s10 = t1 (the bytes left, saved across the calls), pod_write_ent(pp, e) (0x13efc,
    a0 = s8 = pp, a1 = sp + 0xe8; through [PweFacts]), and, inside the first SPA_PROP_params Struct (the cell
    `first` at sp + 0xe0), n_ent++ (the cell 0x98 = &pp->n_ent) and the copy of e's 104 bytes to ent[n_ent] (the
    cells 0x90 = ~&ent[0], 0x88 = &ent[0], memcpy 0x13f44; its three UBSan checks 0x13f14, 0x13f20, 0x13f30 not
    taken). Ported from reac-pw/fuzz_role's U/Prog/RoleBuild/Write.v (its
    0x13c48 -> 0x13cac), re-walked at rate's registers and cells. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c
  pod_write_ent_c memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import Facts Cut Close PweFacts.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** ** Words *)
Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.

Lemma signed_small : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt z (2^63))) by lia. reflexivity.
Qed.

(** n + 1 <s n is false for the small n of n_ent++ (pod.h:432, its overflow check). *)
Lemma lts_succ_false : forall x, 0 <= x < 2^62 -> bv_lts (Z_to_bv 64 (x + 1)) (Z_to_bv 64 x) = false.
Proof. intros x Hx. unfold bv_lts. rewrite !signed_small by lia. apply Z.ltb_ge. lia. Qed.

(** ** The record copy *)
(** Two overwrites of disjoint ranges commute. *)
Lemma overwrite_comm : forall (I x y : list byte) (p q : nat), (p + length x <= q)%nat ->
  (q + length y <= length I)%nat ->
  overwrite (overwrite I p x) q y = overwrite (overwrite I q y) p x.
Proof.
  intros I x y p q Hpq Hq.
  rewrite <- (upd_overwrite I p x), <- (upd_overwrite I q y), <- (upd_overwrite (upd_bytes I p x) q y),
    <- (upd_overwrite (upd_bytes I q y) p x).
  assert (L1 : length (upd_bytes I p x) = length I) by (apply upd_bytes_length; lia).
  assert (L2 : length (upd_bytes I q y) = length I) by (apply upd_bytes_length; lia).
  assert (L3 : length (upd_bytes (upd_bytes I p x) q y) = length I) by (rewrite upd_bytes_length; lia).
  assert (L4 : length (upd_bytes (upd_bytes I q y) p x) = length I) by (rewrite upd_bytes_length; lia).
  apply nth_error_ext. intros j.
  destruct (Nat.lt_ge_cases j (length I)) as [Hj|Hj].
  - rewrite (upd_bytes_nth (upd_bytes I p x) q y j) by lia.
    rewrite (upd_bytes_nth (upd_bytes I q y) p x j) by lia.
    rewrite (upd_bytes_nth I p x j) by lia. rewrite (upd_bytes_nth I q y j) by lia.
    destruct (Nat.leb q j && Nat.ltb j (q + length y))%bool eqn:E1;
      destruct (Nat.leb p j && Nat.ltb j (p + length x))%bool eqn:E2; try reflexivity.
    exfalso. apply andb_true_iff in E1 as [E1a _]. apply andb_true_iff in E2 as [_ E2b].
    apply Nat.leb_le in E1a. apply Nat.ltb_lt in E2b. lia.
  - rewrite (proj2 (nth_error_None (upd_bytes (upd_bytes I p x) q y) j)) by lia.
    rewrite (proj2 (nth_error_None (upd_bytes (upd_bytes I q y) p x) j)) by lia. reflexivity.
Qed.

(** pp->ent[pp->n_ent++] = e as the code does it: n_ent first (0x13f18), then the entry (memcpy, 0x13f44). *)
Lemma pp_image_ent_code : forall b isp hasp pst es e corr,
  Z.of_nat (length b) <= POD_BUF_MAX -> (length es < 32)%nat ->
  Forall (fun e => (length (e_body e) <= 96)%nat) (es ++ [e]) ->
  overwrite (overwrite (pp_image b isp hasp pst es corr) (Z.to_nat OFF_N_ENT) (le32 (Z.of_nat (length es) + 1)))
    (Z.to_nat (OFF_ENT + ENT_SIZE * Z.of_nat (length es))) (ent_mem e)
  = pp_image b isp hasp pst (es ++ [e]) corr.
Proof.
  intros b isp hasp pst es e corr Hb Hl Hs.
  rewrite (pp_image_ent b isp hasp pst es e corr Hb Hl Hs). symmetry.
  pose proof Hs as Hs'. apply Forall_app in Hs' as [Hs1 He]. apply Forall_inv in He.
  apply overwrite_comm.
  - rewrite length_ent_mem by exact He. unfold OFF_ENT, ENT_SIZE, OFF_N_ENT. lia.
  - rewrite length_le32. pose proof (length_pp_image b isp hasp pst es corr Hb ltac:(lia) Hs1) as HL.
    unfold PP_SIZE, OFF_N_ENT in *. lia.
Qed.

Lemma bodies96 : forall es, Forall ent_wf es -> Forall (fun e => (length (e_body e) <= 96)%nat) es.
Proof. intros es H. eapply Forall_impl; [|exact H]. intros x (_ & Hx & Hz). lia. Qed.

(** The block after the record copy inside the first params Struct. *)
Lemma rec_image : forall sh ps es e bsN (o : Z),
  first_params ps = None -> Forall ent_wf es -> ent_wf e -> (length es < 32)%nat ->
  Z.of_nat (length (pc_buf (PbCut sh ps (Some (es ++ [e]))))) <= POD_BUF_MAX ->
  bsN = le32 (Z.of_nat (length es) + 1) -> o = OFF_ENT + ENT_SIZE * Z.of_nat (length es) ->
  overwrite (overwrite (pp_image (pc_buf (PbCut sh ps (Some (es ++ [e])))) (is_props (PodRec sh ps None))
      (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) es false) (Z.to_nat OFF_N_ENT) bsN)
    (Z.to_nat o) (ent_mem e)
  = pc_image (PbCut sh ps (Some (es ++ [e]))).
Proof.
  intros sh ps es e bsN o HN Hes He Hl Hb -> ->.
  unfold pc_image. cbn [pc_shape pc_props].
  assert (E1 : pc_ents (PbCut sh ps (Some (es ++ [e]))) = es ++ [e])
    by (unfold pc_ents; cbn [pc_props pc_open]; rewrite HN; reflexivity).
  rewrite E1. apply pp_image_ent_code; [exact Hb | exact Hl |].
  apply bodies96. apply Forall_app. split; [exact Hes | constructor; [exact He | constructor]].
Qed.

(** ** The record at this cut *)
Lemma write_lengths : forall sh ps es e, pc_wf sh ps -> Forall ent_wf es -> ent_wf e -> (length ps <= 2)%nat ->
  (length es <= 31)%nat ->
  Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) + 112 <= 16384 /\
  Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) mod 8 = 0 /\
  Z.of_nat (length (enc_pod e)) <= 56 /\
  Z.of_nat (length (pc_buf (PbCut sh ps (Some (es ++ [e])))))
    = Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) + Z.of_nat (length (enc_pod e)).
Proof.
  intros sh ps es e (_ & Hkv & He & _) Hes HEe Hp Hk.
  assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps)
    by (eapply Forall_impl; [|exact Hkv]; intros kv [_ H]; exact H).
  pose proof (pc_stop_never sh ps es Hv He Hes Hp Hk) as H1.
  destruct (pc_buf_len_open sh ps es Hv He Hes) as [_ H2].
  destruct (enc_pod_len_bound e HEe) as [H3 _].
  split; [lia|]. split; [apply (proj2 (Z.mod_divide _ 8 ltac:(lia))); exact H2|]. split; [exact H3|].
  rewrite <- pc_buf_pod, length_app. lia.
Qed.

(** The frame's cells this piece reads back (the preheader's, the Struct's) and the pod e at sp + 0xe8. *)
Definition FWR (sp : word) (pp fl : Z) (Hd : hdr) (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (e : ent)
    (m1 : word -> option byte) : Prop :=
  CFIX sp pp m1 /\ CVAR sp fl pp Hd sh np ps i cnt m1 /\ bytes_at rsegs m1 (bv_unsigned sp + 0xe8) (ent_mem e).

Lemma FWR_frame : forall sp pp fl Hd sh np ps i cnt e, (length (e_body e) <= 96)%nat ->
  frame_only sp (FWR sp pp fl Hd sh np ps i cnt e).
Proof.
  intros sp pp fl Hd sh np ps i cnt e Hb W m1 m2 MU HW (CF & CV & HE).
  split; [exact (CFIX_above sp W m1 m2 MU HW pp CF)|].
  split; [exact (CVAR_above sp W m1 m2 MU HW fl pp Hd sh np ps i cnt CV)|].
  apply (bytes_above sp W m1 m2 MU HW); [lia | rewrite length_ent_mem by exact Hb; unfold FRAME_LOCALS; lia | exact HE].
Qed.

Ltac fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

(** ** The proof *)
Theorem write_holds : pod_write_ent_c.pod_write_ent_contract -> memcpy_c.memcpy_contract ->
  forall sp gp tp F fc m rest fl src pp lo H, S_write sp gp tp F fc m rest fl src pp lo H.
Proof.
  intros PWE MCPY sp gp tp F fc m rest fl src pp lo Hd HOK HPPA HSPA sh np ps i cnt es k e r ms
    (ra & t0 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s7 & s10 & t3 & t4 & t5 & t6 & m1 & -> &
     MB & CF & CV & HE & HEW & CP & Hk & Hcnt & Hkc).
  pose proof HOK as (HS0 & HS1 & HP1 & _ & HM1 & HL0 & HSP & HPP & _ & HSROM).
  unfold POD_PROPS, MID_STACK, FRAME_LOCALS in HP1, HM1, HSP, HSROM.
  pose proof CP as (Hsuf & Hwf & Hsh & Hnp & Hi & Hinp & Hes).
  assert (Hps2 : (length ps <= 2)%nat) by lia.
  assert (Hk31 : (length es <= 31)%nat) by lia.
  destruct (write_lengths sh ps es e Hwf Hes HEW Hps2 Hk31) as (HL & HL8 & Hn & Hb1).
  pose proof HEW as (Hty & Hbody & Hsz).
  assert (HEL : length (ent_mem e) = 104%nat) by (apply length_ent_mem; lia).
  pose proof (bv_unsigned_in_range 64 sp) as Hsp. unfold bv_modulus in Hsp. change (2 ^ Z.of_N 64) with (2^64) in Hsp.
  change (pc_image (PbCut sh ps (Some es)))
    with (pp_image (pc_buf (PbCut sh ps (Some es))) (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
            (params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps (Some es))) false) in MB.
  assert (FK : FWR sp pp fl Hd sh np ps i cnt e m1) by (split; [exact CF | split; [exact CV | exact HE]]).
  pose proof (FWR_frame sp pp fl Hd sh np ps i cnt e ltac:(lia)) as KP.
  clear CF CV.
  pose proof (MBr_len_load sp m rest src pp lo _ _ _ _ _ _ m1 MB ltac:(unfold POD_BUF_MAX; lia)) as RL.
  unfold CNT_JOIN, POD_BUF_MAX.
  (* 0x13ee4 ld a0,0(s11) *)
  zstep. clear RL.
  (* 0x13ee8 addi a1,a0,0x70; 0x13eec bltu s6,a1 (s6 = 0x4000): pod.h:428's stop (-> 0x14048), never taken *)
  zstep. zstep. if_cases T0; [exfalso; zify_cond T0; lia|].
  (* 0x13ef0 mv s10,t1; 0x13ef4 addi a1,sp,0xe8; 0x13ef8 mv a0,s8; 0x13efc jal pod_write_ent *)
  zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply PWE with (e := e) (len := Z.of_nat (length (pc_buf (PbCut sh ps (Some es))))) (lo := lo).
    - rewrite unsigned_lit by lia. apply mod_16_8. exact HPPA.
    - rewrite unsigned_lit by lia. unfold PWE_LEN.
      apply (MBr_len_cell sp m rest src pp lo _ _ _ _ _ _ m1 MB). unfold POD_BUF_MAX. lia.
    - lia.
    - exact HL8.
    - unfold PWE_LEN. lia.
    - rewrite unsigned_lit by lia.
      apply (MBr_buf_cells sp m rest src pp lo _ _ _ _ _ _ m1 _ MB). unfold POD_BUF_MAX. lia.
    - rewrite unsigned_lit by lia. apply mod_16_add4; [exact HSPA | reflexivity].
    - rewrite unsigned_lit by lia. exact HE.
    - rewrite Hbody. lia.
    - unfold PWE_BODY. lia.
    - left. rewrite !unsigned_lit by lia. unfold PWE_REC. lia.
    - exact (MBr_stk_sp sp m rest src pp lo HOK _ m1 MB).
    - unfold PWE_STACK. lia.
    - intros a Ha. apply HSROM. lia.
    - left. rewrite unsigned_lit by lia. unfold PWE_REC. lia.
    - right. rewrite !unsigned_lit by lia. lia.
    - exact (MBr_mem_inv sp m rest src pp lo _ m1 MB). }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> &
              MU2 & WM2 & MI2 & ST2 & HX2 & HY2).
  fix_ret.
  rewrite (unsigned_lit pp) in MU2, HX2, HY2 by lia.
  unfold PWE_STACK, PWE_LEN in MU2, HY2.
  pose proof (MBr_pwe_post sp m rest src pp lo HOK _ _ _ _ _ _ (enc_pod e) m1 m2 MB MU2 WM2 MI2 ST2 HX2 HY2
                ltac:(unfold POD_BUF_MAX; lia)) as MB2.
  rewrite pc_buf_pod in MB2.
  assert (HW2 : forall x, bv_unsigned sp <= x < bv_unsigned sp + FRAME_LOCALS ->
             outside [(bv_unsigned sp - 32, bv_unsigned sp);
                      (pp + Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))),
                       pp + Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) + Z.of_nat (length (enc_pod e)));
                      (pp + 16384, pp + 16384 + 8)] x)
    by (intros x Hx; cbn [outside]; unfold FRAME_LOCALS in Hx; split; [lia | split; [lia | split; [lia | exact I]]]).
  pose proof (KP _ m1 m2 MU2 HW2 FK) as FK2.
  clear MB FK MU2 WM2 MI2 ST2 HX2 HY2 HW2.
  pose proof (MBr_bounds sp m rest src pp lo _ m2 MB2) as (_ & _ & HIL2). unfold POD_PROPS in HIL2.
  pose proof FK2 as (_ & CV2 & _). pose proof CV2 as (_ & _ & _ & _ & _ & _ & CE0). clear CV2.
  destruct (first_of ps) eqn:EF.
  - (* the first params Struct: the pod is recorded in ent[n_ent++] *)
    assert (HN : first_params ps = None)
      by (apply first_params_none; unfold first_of in EF; apply negb_true_iff in EF; exact EF).
    assert (E0 : pc_ents (PbCut sh ps (Some es)) = es)
      by (unfold pc_ents; cbn [pc_props pc_open]; rewrite HN; reflexivity).
    rewrite E0 in MB2.
    change (Z.b2z true) with 1 in CE0.
    pose proof (cell8_read _ _ _ CE0) as RE0. clear CE0.
    (* 0x13f00 ld a0,0xe0(sp); 0x13f04 beqz a0 *)
    zstep. clear RE0.
    zstep. if_cases T1; [exfalso; zify_cond T1; lia|].
    (* 0x13f08 ld a2,0x98(sp) *)
    pose proof FK2 as (CF2 & _).
    pose proof CF2 as (_ & _ & _ & _ & _ & _ & _ & C98 & _). unfold POD_NENT_OFF in C98.
    pose proof (cell8_read _ _ _ C98) as R98. clear C98 CF2.
    zstep. clear R98.
    (* 0x13f0c lw a0,0(a2): n_ent = k *)
    assert (RN : ov_read_bytes rsegs m2 (wa (pp + 19732)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat k)))).
    { rewrite le4_le32. erewrite MBr_read; [ | exact MB2 | lia | rewrite E0 in HIL2; lia ].
      change (Z.to_nat 19732) with (Z.to_nat OFF_N_ENT).
      rewrite pp_image_slice_nent; [rewrite Hk; reflexivity | unfold POD_BUF_MAX; lia | lia | apply bodies96; exact Hes]. }
    zstep. clear RN.
    rewrite sx32_small by lia.
    (* 0x13f10 addiw a1,a0,1; 0x13f14 blt a1,a0: the n_ent++ overflow trap, not taken *)
    zstep. rewrite swrap32_small by lia.
    zstep. if_cases T2; [exfalso; rewrite lts_succ_false in T2 by lia; discriminate T2|].
    (* 0x13f18 sw a1,0(a2) *)
    blk_step HOK MB2 FK2 KP pp 19732 4%nat.
    (* 0x13f1c addi a1,zero,0x21; 0x13f20 bgeu a0,a1: n_ent >= 33 traps, not taken *)
    zstep. zstep. if_cases T3; [exfalso; zify_cond T3; lia|].
    (* 0x13f24 addi a1,zero,0x68; 0x13f28 mul a0,a0,a1 *)
    zstep. zstep.
    (* 0x13f2c ld a1,0x90(sp); 0x13f30 bltu a1,a0: &ent[n] wraps, trap not taken *)
    pose proof FK2 as (CF3 & _ & HE3).
    pose proof CF3 as (_ & _ & _ & _ & _ & C88 & C90 & _). unfold OFF_ENT in C88, C90. clear CF3.
    pose proof (cell8_read _ _ _ C90) as R90.
    zstep. clear R90.
    zstep. if_cases T4; [exfalso; rewrite lnot_ltu_false in T4 by lia; discriminate T4|].
    (* 0x13f34 ld a1,0x88(sp); 0x13f38 add a0,a1,a0 *)
    pose proof (cell8_read _ _ _ C88) as R88.
    zstep. clear R88. zstep.
    (* 0x13f3c addi a1,sp,0xe8; 0x13f40 addi a2,zero,0x68; 0x13f44 jal memcpy *)
    zstep. zstep. zstep.
    pose proof (MBr_bounds sp m rest src pp lo _ _ MB2) as (_ & _ & HIL3). unfold POD_PROPS in HIL3.
    eapply evt_cut.
    { eapply MCPY with (src := ent_mem e).
      - rewrite unsigned_lit by lia. exact HE3.
      - rewrite (unsigned_lit 104) by lia. rewrite HEL. reflexivity.
      - rewrite !unsigned_lit by lia. change (Z.to_nat 104) with 104%nat.
        replace (pp + 16404 + Z.of_nat k * 104) with (pp + (16404 + Z.of_nat k * 104)) by lia.
        apply (MBr_pp_cells sp m rest src pp lo _ _ (16404 + Z.of_nat k * 104) 104 MB2); lia.
      - rewrite !unsigned_lit by lia. right. lia.
      - exact (MBr_mem_inv sp m rest src pp lo _ _ MB2). }
    intros ms' Hpost. unfold memcpy_post in Hpost.
    destruct Hpost as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m4 & -> &
                       MU4 & WM4 & MI4 & CB4 & _).
    fix_ret.
    rewrite !unsigned_lit in MU4, CB4 by lia.
    change (Z.to_nat 104) with 104%nat in CB4.
    assert (EA : pp + 16404 + Z.of_nat k * 104 = pp + (16404 + Z.of_nat k * 104)) by lia.
    rewrite EA in MU4, CB4.
    pose proof (MBr_call_pp sp m rest src pp lo HOK _ _ m4 (16404 + Z.of_nat k * 104) 104 (ent_mem e) MB2 MU4 WM4 MI4
                  (rw_cells_CB_bytes _ _ _ _ CB4) ltac:(rewrite HEL; reflexivity) ltac:(lia)
                  ltac:(unfold POD_PROPS; lia)) as MB4.
    assert (HW4 : forall x, bv_unsigned sp <= x < bv_unsigned sp + FRAME_LOCALS ->
               outside [(pp + (16404 + Z.of_nat k * 104), pp + (16404 + Z.of_nat k * 104) + 104)] x)
      by (intros x Hx; apply (below_misses sp); [lia | exact Hx]).
    pose proof (KP _ _ m4 MU4 HW4 FK2) as FK4.
    pose proof FK4 as (CF4 & CV4 & _).
    (* 0x13f48 *)
    apply evt_done. unfold CNTL. do 18 eexists.
    split; [reflexivity|].
    split.
    { eapply MBr_ext; [exact MB4|].
      apply rec_image; [exact HN | exact Hes | exact HEW | lia | unfold POD_BUF_MAX; lia | |].
      - rewrite le4_le32. f_equal. lia.
      - unfold OFF_ENT, ENT_SIZE. lia. }
    split; [exact CF4|]. split; [exact CV4|].
    split.
    { unfold CNTP. refine (conj Hsuf (conj Hwf (conj Hsh (conj Hnp (conj Hi (conj Hinp _)))))).
      apply Forall_app. split; [exact Hes | constructor; [exact HEW | constructor]]. }
    split; [exact Hk|]. split; [exact Hcnt | exact Hkc].
  - (* a later params Struct: nothing is recorded *)
    assert (EF' : pc_first (PbCut sh ps (Some es)) = false) by exact EF.
    change (Z.b2z false) with 0 in CE0.
    pose proof (cell8_read _ _ _ CE0) as RE0. clear CE0.
    (* 0x13f00 ld a0,0xe0(sp); 0x13f04 beqz a0 -> 0x13f48 *)
    zstep. clear RE0.
    zstep. if_cases T1; [|exfalso; zify_cond T1; lia].
    pose proof FK2 as (CF3 & CV3 & _).
    apply evt_done. unfold CNTL. do 18 eexists.
    split; [reflexivity|].
    split.
    { eapply MBr_ext; [exact MB2|]. unfold pc_image. cbn [pc_shape pc_props].
      rewrite (pc_ents_pod_other sh ps es e EF'). reflexivity. }
    split; [exact CF3|]. split; [exact CV3|].
    split.
    { unfold CNTP. refine (conj Hsuf (conj Hwf (conj Hsh (conj Hnp (conj Hi (conj Hinp _)))))).
      apply Forall_app. split; [exact Hes | constructor; [exact HEW | constructor]]. }
    split; [exact Hk|]. split; [exact Hcnt | exact Hkc].
Qed.
