(** One property of an object that is not a Struct, its Int-7 value (pod.h:410-419) in the UBSan builder,
    0x13268 -> 0x13e00, proved from Key.v's cut [PKEY] (key and flags put) when sel & 3 = 0 (SPA_PROP_volume) or
    bit 4 of sel is set: seen_params and `first` into their cells (0x13268-0x13284), memset(e->body + 4, 0, 92),
    e = Ent 4 4 (le32 7) (pod.h:413-415), pod_write_ent(pp, e) (0x13d6c), has_params := 1 when this is the first
    SPA_PROP_params (pod.h:417-418), then s5 = seen_params at the latch. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c
  memset_c pod_write_ent_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.RoleBuild Require Import Facts Cut Close PweFacts UTac Key
  Shape7.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** ** The record after an Int-7 property *)
(** pod.h:409's `first`: this property is SPA_PROP_params and none before it was. *)
Definition first7 (ps : list (Z * pval)) (sel : Z) : bool := negb (seen_of ps) && (key_of sel =? POD_PROP_PARAMS).

Lemma fp_int7_keep : forall ps sel, first7 ps sel = false ->
  first_params (ps ++ [(key_of sel, PInt 7)]) = first_params ps.
Proof.
  intros ps sel H. rewrite first_params_app. unfold first7 in H.
  destruct (seen_of ps) eqn:ES.
  - destruct (first_params_some ps ES) as [v Hv]. rewrite Hv. reflexivity.
  - cbn [negb andb] in H. rewrite (first_params_none ps ES). cbn [fst]. rewrite H. reflexivity.
Qed.

Lemma fp_int7_first : forall ps sel, first7 ps sel = true ->
  first_params ps = None /\ first_params (ps ++ [(key_of sel, PInt 7)]) = Some (PInt 7).
Proof.
  intros ps sel H. unfold first7 in H. apply andb_true_iff in H as [H1 H2].
  apply negb_true_iff in H1. pose proof (first_params_none ps H1) as HN.
  split; [exact HN|]. rewrite first_params_app, HN. cbn [fst snd]. rewrite H2. reflexivity.
Qed.

Lemma seen_app_params : forall ps v, seen_of (ps ++ [(POD_PROP_PARAMS, v)]) = true.
Proof.
  intros ps v. unfold seen_of. rewrite existsb_app. cbn [existsb fst]. rewrite Z.eqb_refl.
  rewrite orb_true_r. reflexivity.
Qed.

(** The property's bytes: key, flags, then the Int pod 7 (Model.prop_bytes, enc_val (PInt 7)). *)
Lemma int7_buf : forall sh ps sel, sh <> 7 ->
  pc_buf (PbCut sh (ps ++ [(key_of sel, PInt 7)]) None)
  = (pc_buf (PbCut sh ps None) ++ le32 (key_of sel) ++ le32 0) ++ enc_pod (Ent 4 4 (le32 7)).
Proof.
  intros sh ps sel Hsh. rewrite <- pc_buf_prop. unfold prop_bytes. rewrite (proj2 (Z.eqb_neq sh 7) Hsh).
  cbn [fst snd]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma int7_image_keep : forall sh ps sel, sh <> 7 -> first7 ps sel = false ->
  pp_image ((pc_buf (PbCut sh ps None) ++ le32 (key_of sel) ++ le32 0) ++ enc_pod (Ent 4 4 (le32 7)))
    (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))
    (pc_ents (PbCut sh ps None)) false
  = pc_image (PbCut sh (ps ++ [(key_of sel, PInt 7)]) None).
Proof.
  intros sh ps sel Hsh HF. rewrite <- (int7_buf sh ps sel Hsh).
  unfold pc_image. cbn [pc_shape pc_props].
  unfold has_params, params_struct, pc_ents. cbn [p_props pc_props pc_open].
  rewrite (fp_int7_keep ps sel HF). reflexivity.
Qed.

Lemma int7_image_first : forall sh ps sel bsH, sh <> 7 -> first7 ps sel = true ->
  Z.of_nat (length (pc_buf (PbCut sh ps None))) + 24 <= POD_BUF_MAX -> bsH = le32 1 ->
  overwrite (pp_image ((pc_buf (PbCut sh ps None) ++ le32 (key_of sel) ++ le32 0) ++ enc_pod (Ent 4 4 (le32 7)))
               (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))
               (pc_ents (PbCut sh ps None)) false) (Z.to_nat OFF_HAS_PARAMS) bsH
  = pc_image (PbCut sh (ps ++ [(key_of sel, PInt 7)]) None).
Proof.
  intros sh ps sel bsH Hsh HF Hb ->.
  destruct (fp_int7_first ps sel HF) as [HN HN'].
  assert (E0 : pc_ents (PbCut sh ps None) = []) by (unfold pc_ents; cbn [pc_props pc_open]; rewrite HN; reflexivity).
  assert (H0 : has_params (PodRec sh ps None) = false) by (unfold has_params; cbn [p_props]; rewrite HN; reflexivity).
  assert (P0 : params_struct (PodRec sh ps None) = false)
    by (unfold params_struct; cbn [p_props]; rewrite HN; reflexivity).
  assert (H1 : has_params (PodRec sh (ps ++ [(key_of sel, PInt 7)]) None) = true)
    by (unfold has_params; cbn [p_props]; rewrite HN'; reflexivity).
  assert (P1 : params_struct (PodRec sh (ps ++ [(key_of sel, PInt 7)]) None) = false)
    by (unfold params_struct; cbn [p_props]; rewrite HN'; reflexivity).
  assert (E1 : pc_ents (PbCut sh (ps ++ [(key_of sel, PInt 7)]) None) = [])
    by (unfold pc_ents; cbn [pc_props pc_open]; rewrite HN'; reflexivity).
  assert (HL : Z.of_nat (length ((pc_buf (PbCut sh ps None) ++ le32 (key_of sel) ++ le32 0)
                                 ++ enc_pod (Ent 4 4 (le32 7)))) <= POD_BUF_MAX).
  { rewrite !length_app, !length_le32.
    replace (length (enc_pod (Ent 4 4 (le32 7)))) with 16%nat by (vm_compute; reflexivity).
    unfold POD_BUF_MAX in *. lia. }
  rewrite E0, H0, P0.
  change (le32 1) with (le32 (Z.b2z true)).
  rewrite pp_image_has_params by first [exact HL | cbn [length]; lia | constructor].
  rewrite <- (int7_buf sh ps sel Hsh).
  unfold pc_image. cbn [pc_shape pc_props]. rewrite H1, P1, E1. reflexivity.
Qed.

Lemma ent47_wf : ent_wf (Ent 4 4 (le32 7)).
Proof. unfold ent_wf. cbn [e_type e_size e_body]. split; [lia | split; [reflexivity | lia]]. Qed.

Lemma testbit4_land : forall sel, Z.testbit sel 4 = true -> Z.land sel 16 <> 0.
Proof.
  intros sel H E. assert (X : Z.testbit (Z.land sel 16) 4 = true) by (rewrite Z.land_spec, H; reflexivity).
  rewrite E in X. discriminate X.
Qed.

Lemma key_range : forall sel, 0 <= key_of sel < 2^32.
Proof. intros sel. unfold key_of. destruct (sel mod 4 =? 0); unfold POD_PROP_VOLUME, POD_PROP_PARAMS; lia. Qed.

(** ** Frame cells *)
(** The preheader's and the object's cells stay through the two cell stores of 0x13274 / 0x13284 (sp + 0x88 and
    sp + 0xb0 hold none of them). *)
Lemma FS_write : forall sp pp fl sh np m1 (w : word) a bs, FS sp pp fl sh np m1 -> w = wa a -> 0 <= a ->
  a + Z.of_nat (length bs) <= 2^64 ->
  (bv_unsigned sp + 0x88 <= a /\ a + Z.of_nat (length bs) <= bv_unsigned sp + 0x90 \/ bv_unsigned sp + 0xa8 <= a) ->
  FS sp pp fl sh np (write_to_mem m1 w bs).
Proof.
  intros sp pp fl sh np m1 w a bs (CF & CP) -> Ha Hb Hd. unfold FS, CFIX, CPROP, cell8 in *.
  destruct CF as (C08 & C20 & C28 & C48 & C50 & C58 & C60 & C68 & C70 & C78 & C80 & C98 & CA0).
  destruct CP as (C10 & C18 & C90).
  repeat match goal with |- _ /\ _ => split end;
  (apply bytes_at_write_other; [assumption | lia | lia | rewrite length_le8; lia]).
Qed.

(** From 0x13d44: those cells, seen_params' and `first`. *)
Definition FT (sp : word) (pp fl sh np v88 vb0 : Z) (m1 : word -> option byte) : Prop :=
  CFIX sp pp m1 /\ CPROP sp fl sh np m1 /\ cell8 m1 (bv_unsigned sp + 0x88) v88 /\
  cell8 m1 (bv_unsigned sp + 0xb0) vb0.

Lemma FT_kept : forall sp pp fl sh np v88 vb0, kept_on sp (FT sp pp fl sh np v88 vb0).
Proof.
  intros sp pp fl sh np v88 vb0 W m1 m2 MU HW (CF & CP & C88 & CB0).
  split; [exact (CFIX_kept sp pp W m1 m2 MU HW CF)|].
  split; [exact (CPROP_kept sp fl sh np W m1 m2 MU HW CP)|].
  split; (apply (cell8_kept _ _ _ _ _ _ MU HW); [lia | lia | assumption]).
Qed.

Lemma bytes_at_cat4 : forall m1 A B C D x y z u, bytes_at rsegs m1 A x -> bytes_at rsegs m1 B y ->
  bytes_at rsegs m1 C z -> bytes_at rsegs m1 D u ->
  B = A + Z.of_nat (length x) -> C = B + Z.of_nat (length y) -> D = C + Z.of_nat (length z) ->
  bytes_at rsegs m1 A (x ++ y ++ z ++ u).
Proof.
  intros m1 A B C D x y z u HX HY HZ HU -> -> ->. apply bytes_at_app. split; [exact HX|].
  apply bytes_at_app. split; [exact HY|]. apply bytes_at_app. split; [exact HZ | exact HU].
Qed.

(** ** The walk *)
Section Int7.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl src pp lo : Z).
Hypothesis HOK : BOK sp rest src pp lo.
Hypothesis HPPA : pp mod 16 = 0.
Hypothesis HSPA : bv_unsigned sp mod 16 = 0.
Hypothesis MSET : memset_c.memset_contract.
Hypothesis PWE : pod_write_ent_c.pod_write_ent_contract.

(** 0x13d44 -> 0x13e00: memset(e->body + 4), e = Ent 4 4 (le32 7), pod_write_ent, has_params when `first`. *)
Lemma int7_tail : forall sh np ps r sel (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 s5 t3 t4 t5 t6 : word) m1,
  sh <> 7 -> 0 <= sel < 256 -> suffix rest r -> pc_wf sh ps -> 0 <= np < 4 -> (length ps < Z.to_nat np)%nat ->
  MBr sp m rest src pp lo (kimg sh ps sel) m1 -> CFIX sp pp m1 -> CPROP sp fl sh np m1 ->
  cell8 m1 (bv_unsigned sp + 0x88) (Z.b2z (seen_of (ps ++ [(key_of sel, PInt 7)]))) ->
  cell8 m1 (bv_unsigned sp + 0xb0) (Z.b2z (first7 ps sel)) ->
  evt rsegs (PROPL sp gp tp F fc m rest fl src pp lo sh np (length ps) (ps ++ [(key_of sel, PInt 7)]) r)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 S0V) (Z_to_bv 64 (Z.of_nat (length r)))
             a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (Z.of_nat (length ps)))
             (Z_to_bv 64 MULT10) (Z_to_bv 64 4) (Z_to_bv 64 (Z.lnot pp)) s5
             (Z_to_bv 64 (cur rest src r)) (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) (Z_to_bv 64 7)
             (Z_to_bv 64 (bv_unsigned sp + 0x158)) (Z_to_bv 64 np) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d44) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh np ps r sel ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 s5 t3 t4 t5 t6 m1 Hsh Hsel Hsuf Hwf Hnp Hlt MB CF CP C88 CB0.
  pose proof HOK as (HS0 & HS1 & HP1 & _ & HM1 & HL0 & HSP & HPP & _ & _).
  unfold POD_PROPS, MID_STACK, FRAME_LOCALS in HP1, HM1, HSP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with 18446744073709551616 in SPR.
  destruct (pc_buf_cap sh ps Hwf ltac:(lia)) as [HB8 HD8].
  unfold kimg in MB.
  assert (FK : FT sp pp fl sh np (Z.b2z (seen_of (ps ++ [(key_of sel, PInt 7)]))) (Z.b2z (first7 ps sel)) m1)
    by exact (conj CF (conj CP (conj C88 CB0))).
  pose proof (FT_kept sp pp fl sh np (Z.b2z (seen_of (ps ++ [(key_of sel, PInt 7)]))) (Z.b2z (first7 ps sel)))
    as KP.
  clear CF CP C88 CB0.
  unfold POD_LEN_OFF.
  (* 0x13d44 mv s5,a7; addi a2,zero,0x5c; addi a0,sp,0xc4; mv a1,zero; 0x13d54 jal memset *)
  zstep. zstep. zstep. zstep. zstep.
  eapply (mset_at sp gp tp F fc m rest src pp lo HOK MSET) with (o := 196) (n := 92%nat).
  { exact KP. } { exact FK. } { exact MB. }
  { rewrite unsigned_lit by lia. reflexivity. }
  { first [reflexivity | rewrite unsigned_lit by lia; reflexivity]. }
  { first [reflexivity | rewrite unsigned_lit by lia; reflexivity]. }
  { lia. } { unfold FRAME_LOCALS. lia. }
  intros u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m2 MB2 FK2 HZ.
  fix_ret.
  (* 0x13d58 sw s3,0xb8(sp); sw s3,0xbc(sp); sw s9,0xc0(sp) *)
  fr_step HOK MB2 FK2 (kept_write _ _ KP) (bv_unsigned sp + 184) 4%nat.
  fr_step HOK MB2 FK2 (kept_write _ _ KP) (bv_unsigned sp + 188) 4%nat.
  fr_step HOK MB2 FK2 (kept_write _ _ KP) (bv_unsigned sp + 192) 4%nat.
  (* e = Ent 4 4 (le32 7) at sp + 0xb8 *)
  lazymatch goal with
  | S1 : bytes_at rsegs ?mm (bv_unsigned sp + 184) ?x, S2 : bytes_at rsegs ?mm (bv_unsigned sp + 188) ?y,
    S3 : bytes_at rsegs ?mm (bv_unsigned sp + 192) ?z, S4 : bytes_at rsegs ?mm (bv_unsigned sp + 196) ?u
    |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HE : bytes_at rsegs mm (bv_unsigned sp + 184) (ent_mem (Ent 4 4 (le32 7))))
        by (eapply bytes_at_ext; [apply (bytes_at_cat4 mm _ _ _ _ x y z u S1 S2 S3 S4); lenlia
                                 | vm_compute; reflexivity]);
      clear S1 S2 S3 S4
  end.
  (* 0x13d64 addi a1,sp,0xb8; mv a0,s8; 0x13d6c jal pod_write_ent *)
  zstep. zstep. zstep.
  eapply (pwe_at sp gp tp F fc m rest src pp lo HOK HPPA HSPA PWE).
  { exact (kept_frame _ _ KP). } { exact FK2. } { exact MB2. } { exact HE. } { exact ent47_wf. }
  { destruct HD8 as [c Hc]. rewrite !length_app, !length_le32.
    replace (Z.of_nat (length (pc_buf (PbCut sh ps None)) + (4 + 4))) with ((c + 1) * 8) by lia.
    apply Z.mod_mul. lia. }
  { rewrite !length_app, !length_le32.
    replace (length (enc_pod (Ent 4 4 (le32 7)))) with 16%nat by (vm_compute; reflexivity).
    unfold POD_BUF_MAX. lia. }
  { rewrite unsigned_lit by lia. reflexivity. }
  { rewrite unsigned_lit by lia. reflexivity. }
  intros v0 v1 v2 va0 va1 va2 va3 va4 va5 va6 va7 v3 v4 v5 v6 mw MB3 FK3.
  fix_ret.
  (* 0x13d70 ld a0,0xb0(sp); 0x13d74 beqz a0 *)
  destruct (first7 ps sel) eqn:EF.
  - (* the first SPA_PROP_params: has_params := 1 (pod.h:418) *)
    pose proof FK3 as (_ & _ & _ & CB). change (Z.b2z true) with 1 in CB.
    pose proof (cell8_read _ _ _ CB) as RB. clear CB.
    zstep. clear RB. zstep. if_cases T; [exfalso; zify_cond T; lia|].
    (* 0x13d78 addi a0,zero,1; 0x13d7c sw a0,0xc(s7) *)
    zstep.
    blk_step HOK MB3 FK3 (kept_frame _ _ KP) pp 16396 4%nat.
    (* 0x13d80 mv a7,s5; j 0x13dfc; 0x13dfc ld s5,0x88(sp) *)
    pose proof FK3 as (CF4 & CP4 & C884 & _).
    zstep. zstep. pose proof (cell8_read _ _ _ C884) as R88. zstep. clear R88.
    apply evt_done. unfold PROPL. do 16 eexists.
    split; [reflexivity|].
    split.
    { eapply MBr_ext; [exact MB3|].
      apply int7_image_first; [exact Hsh | exact EF | unfold POD_BUF_MAX; lia | apply le4_le32]. }
    split; [exact CF4|]. split; [exact CP4|]. split; [exact Hsuf|].
    split; [apply pc_wf_int; [exact Hwf | apply key_range | lia]|]. split; [exact Hnp|].
    rewrite length_app. cbn [length]. split; lia.
  - (* not the first: has_params stays *)
    pose proof FK3 as (CF4 & CP4 & C884 & CB). change (Z.b2z false) with 0 in CB.
    pose proof (cell8_read _ _ _ CB) as RB. clear CB.
    zstep. clear RB. zstep. if_cases T; [|exfalso; zify_cond T; lia].
    (* 0x13d80 mv a7,s5; j 0x13dfc; 0x13dfc ld s5,0x88(sp) *)
    zstep. zstep. pose proof (cell8_read _ _ _ C884) as R88. zstep. clear R88.
    apply evt_done. unfold PROPL. do 16 eexists.
    split; [reflexivity|].
    split; [rewrite <- (int7_image_keep sh ps sel Hsh EF); exact MB3|].
    split; [exact CF4|]. split; [exact CP4|]. split; [exact Hsuf|].
    split; [apply pc_wf_int; [exact Hwf | apply key_range | lia]|]. split; [exact Hnp|].
    rewrite length_app. cbn [length]. split; lia.
Qed.

(** 0x13268 -> 0x13d44: seen_params' and `first` into their cells, the branches of pod.h:412 to the Int-7 value. *)
Lemma int7_walk : forall sh np ps r sel ms, PKEY sp gp tp F fc m rest fl src pp lo sh np ps r sel ms ->
  (sel mod 4 = 0 \/ Z.testbit sel 4 = true) ->
  evt rsegs (PROPL sp gp tp F fc m rest fl src pp lo sh np (length ps) (ps ++ [(key_of sel, PInt 7)]) r) ms.
Proof.
  intros sh np ps r sel ms
    (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & t3 & t4 & t5 & t6 & m1 & -> & -> & -> & -> &
     MB & CF & CP & Hsuf & Hwf & Hnp & Hlt & Hsh & Hsel) Hcase.
  pose proof HOK as (HS0 & HS1 & HP1 & _ & HM1 & HL0 & HSP & HPP & _ & _).
  unfold POD_PROPS, MID_STACK, FRAME_LOCALS in HP1, HM1, HSP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with 18446744073709551616 in SPR.
  assert (FK : FS sp pp fl sh np m1) by (split; assumption).
  clear CF CP.
  rewrite land3.
  destruct (Z.eq_dec (sel mod 4) 0) as [HA|HA].
  - (* sel & 3 = 0: SPA_PROP_volume *)
    rewrite HA.
    (* 0x13268 mv a2,s5; 0x1326c beqz a1 (taken) *)
    zstep. zstep. if_cases T0; [|exfalso; zify_cond T0; lia].
    (* 0x13274 sd a2,0x88(sp) *)
    fr_step HOK MB FK (FS_write sp pp fl sh np) (bv_unsigned sp + 136) 8%nat.
    (* 0x13278 snez a2,a1; seqz a3,s5; and a2,a2,a3; 0x13284 sd a2,0xb0(sp) *)
    zstep. zstep. zstep.
    fr_step HOK MB FK (FS_write sp pp fl sh np) (bv_unsigned sp + 176) 8%nat.
    (* 0x13288 beqz a1 (taken) -> 0x13d44 *)
    zstep. if_cases T1; [|exfalso; zify_cond T1; lia].
    destruct FK as (CF2 & CP2).
    assert (HK : key_of sel = POD_PROP_VOLUME) by (unfold key_of; rewrite HA; reflexivity).
    eapply int7_tail; try eassumption.
    + unfold cell8. rewrite HK, seen_app_other by (unfold POD_PROP_VOLUME, POD_PROP_PARAMS; lia). exact ST.
    + unfold cell8. eapply bytes_at_ext; [exact ST0|]. unfold first7. rewrite HK.
      destruct (seen_of ps); vm_compute; reflexivity.
  - (* sel & 3 <> 0: SPA_PROP_params, bit 4 set *)
    destruct Hcase as [Hc|Hbit]; [lia|].
    (* 0x13268 mv a2,s5; 0x1326c beqz a1 (not taken); 0x13270 addi a2,zero,1 *)
    zstep. zstep. if_cases T0; [exfalso; zify_cond T0; lia|]. zstep.
    (* 0x13274 sd a2,0x88(sp) *)
    fr_step HOK MB FK (FS_write sp pp fl sh np) (bv_unsigned sp + 136) 8%nat.
    (* 0x13278 snez a2,a1; seqz a3,s5; and a2,a2,a3; 0x13284 sd a2,0xb0(sp) *)
    zstep. zstep. zstep.
    fr_step HOK MB FK (FS_write sp pp fl sh np) (bv_unsigned sp + 176) 8%nat.
    (* 0x13288 beqz a1 (not taken); 0x1328c andi a0,a0,0x10; 0x13290 bnez a0 (taken: bit 4) -> 0x13d44 *)
    zstep. if_cases T1; [exfalso; zify_cond T1; lia|].
    zstep. zstep. if_cases T2; [|exfalso; zify_cond T2; apply (testbit4_land sel Hbit); lia].
    destruct FK as (CF2 & CP2).
    assert (HK : key_of sel = POD_PROP_PARAMS)
      by (unfold key_of; rewrite (proj2 (Z.eqb_neq (sel mod 4) 0) HA); reflexivity).
    eapply int7_tail; try eassumption.
    + unfold cell8. rewrite HK, seen_app_params. exact ST.
    + unfold cell8. eapply bytes_at_ext; [exact ST0|]. unfold first7. rewrite HK, Z.eqb_refl.
      rewrite (proj2 (Z.ltb_lt 0 (sel mod 4))) by lia. destruct (seen_of ps); vm_compute; reflexivity.
Qed.

End Int7.

Theorem int7_holds : memset_c.memset_contract -> pod_write_ent_c.pod_write_ent_contract ->
  forall sp gp tp F fc m rest fl src pp lo, BOK sp rest src pp lo -> pp mod 16 = 0 -> bv_unsigned sp mod 16 = 0 ->
  forall sh np ps r sel ms, PKEY sp gp tp F fc m rest fl src pp lo sh np ps r sel ms ->
  (sel mod 4 = 0 \/ Z.testbit sel 4 = true) ->
  evt rsegs (PROPL sp gp tp F fc m rest fl src pp lo sh np (length ps) (ps ++ [(key_of sel, PInt 7)]) r) ms.
Proof.
  intros MSET PWE sp gp tp F fc m rest fl src pp lo HOK HPPA HSPA.
  exact (int7_walk sp gp tp F fc m rest fl src pp lo HOK HPPA HSPA MSET PWE).
Qed.
