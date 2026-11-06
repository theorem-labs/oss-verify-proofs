(** One property of an object that is not a Struct, its Int-7 value (pod.h:410-419), in the UBSan builder of
    reac-pw/fuzz_rate's LLVMFuzzerTestOneInput, 0x13450 -> 0x140c8, proved from the cut [Cut.PKEY] (key and flags
    put) when sel & 3 = 0 (SPA_PROP_volume) or bit 4 of sel is set: seen_params' into s9 (0x13450-0x13458) and
    `first` into its cell sp + 0xe0 (0x1345c-0x13468), the branches of pod.h:412 (0x1346c, 0x13474) to 0x13fe0;
    there s10 = t1 and s3 = a7 saved across the calls, memset(e->body + 4 = sp + 0xf4, 0, 92) (0x13ff4),
    e = Ent 4 4 (le32 7) (`sw s1` 0x13ff8, 0x13ffc; `sw a0` 0x14004 with a0 = 7), pod_write_ent(pp, e = sp + 0xe8)
    (0x14010), has_params := 1 at s11 + 0xc when this is the first SPA_PROP_params (0x14014-0x14020, pod.h:417-418),
    then a7, t1 restored (0x14024, 0x14028) and the latch 0x140c8. Ported from reac-pw/fuzz_role's
    U/Prog/RoleBuild/Int7.v (its 0x13268 -> 0x13e00), re-walked at rate's
    registers, cells and addresses: rate keeps seen_params in s9, not in a cell. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c
  memset_c pod_write_ent_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import Facts Cut Close PweFacts UTac Kit
  Shape7.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
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

Lemma enc47_len : length (enc_pod (Ent 4 4 (le32 7))) = 16%nat.
Proof. unfold enc_pod. cbn [e_type e_size e_body]. rewrite !length_app, !length_le32, length_zeros. reflexivity. Qed.

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
  { rewrite !length_app, !length_le32, enc47_len. unfold POD_BUF_MAX in *. lia. }
  rewrite E0, H0, P0.
  change (le32 1) with (le32 (Z.b2z true)).
  rewrite pp_image_has_params by first [exact HL | cbn [length]; lia | constructor].
  rewrite <- (int7_buf sh ps sel Hsh).
  unfold pc_image. cbn [pc_shape pc_props]. rewrite H1, P1, E1. reflexivity.
Qed.

Lemma ent47_wf : ent_wf (Ent 4 4 (le32 7)).
Proof. unfold ent_wf. cbn [e_type e_size e_body]. split; [lia | split; [reflexivity | lia]]. Qed.

(** e = Ent 4 4 (le32 7) from its stores: type and size 4 (`sw s1`), the body word 7 (`sw a0`), the other 92
    body bytes the memset zeroed. *)
Lemma ent47_mem : forall x y z u, x = le4 (Z_to_bv 64 4) -> y = le4 (Z_to_bv 64 4) -> z = le4 (Z_to_bv 64 7) ->
  u = zeros 92 -> x ++ y ++ z ++ u = ent_mem (Ent 4 4 (le32 7)).
Proof.
  intros x y z u -> -> -> ->. rewrite !le4_le32. unfold ent_mem. cbn [e_type e_size e_body]. rewrite length_le32.
  reflexivity.
Qed.

Lemma testbit4_land : forall sel, Z.testbit sel 4 = true -> Z.land sel 16 <> 0.
Proof.
  intros sel H E. assert (X : Z.testbit (Z.land sel 16) 4 = true) by (rewrite Z.land_spec, H; reflexivity).
  rewrite E in X. discriminate X.
Qed.

Lemma key_range : forall sel, 0 <= key_of sel < 2^32.
Proof. intros sel. unfold key_of. destruct (sel mod 4 =? 0); unfold POD_PROP_VOLUME, POD_PROP_PARAMS; lia. Qed.

(** ** Frame cells *)
(** The preheader's and the object's cells (all below sp + 0xe0) stay through the store of `first` at sp + 0xe0
    (0x13468). *)
Lemma FS_write : forall sp pp fl Hd sh np m1 (w : word) a bs, FS sp pp fl Hd sh np m1 -> w = wa a -> 0 <= a ->
  a + Z.of_nat (length bs) <= 2^64 -> bv_unsigned sp + 0xe0 <= a ->
  FS sp pp fl Hd sh np (write_to_mem m1 w bs).
Proof.
  intros sp pp fl Hd sh np m1 w a bs (CF & CP) -> Ha Hb Hd0. unfold FS, CFIX, CPROP, CHDR, cell8 in *.
  destruct CF as (C00 & C50 & C58 & C78 & C80 & C88 & C90 & C98 & CA0 & CB8 & CC0 & CC8 & CD8).
  destruct CP as (C38 & CA8 & CB0 & C08 & C10 & C18 & C20 & C28 & C30).
  repeat match goal with |- _ /\ _ => split end;
  (apply bytes_at_write_other; [assumption | lia | lia | rewrite length_le8; lia]).
Qed.

(** From 0x13fe0: those cells and `first`. *)
Definition FT (sp : word) (pp fl : Z) (Hd : hdr) (sh np ve0 : Z) (m1 : word -> option byte) : Prop :=
  CFIX sp pp m1 /\ CPROP sp fl Hd sh np m1 /\ cell8 m1 (bv_unsigned sp + 0xe0) ve0.

Lemma FT_kept : forall sp pp fl Hd sh np ve0, kept_on sp (FT sp pp fl Hd sh np ve0).
Proof.
  intros sp pp fl Hd sh np ve0 W m1 m2 MU HW (CF & CP & CE0).
  split; [exact (CFIX_kept sp pp W m1 m2 MU HW CF)|].
  split; [exact (CPROP_kept sp fl Hd sh np W m1 m2 MU HW CP)|].
  apply (cell8_kept _ _ _ _ _ _ MU HW); [lia | lia | assumption].
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
Variables (rest : list byte) (fl src pp lo : Z) (Hd : hdr).
Hypothesis HOK : BOK sp rest src pp lo.
Hypothesis HPPA : pp mod 16 = 0.
Hypothesis HSPA : bv_unsigned sp mod 16 = 0.
Hypothesis MSET : memset_c.memset_contract.
Hypothesis PWE : pod_write_ent_c.pod_write_ent_contract.

(** 0x13fe0 -> 0x140c8: memset(e->body + 4), e = Ent 4 4 (le32 7), pod_write_ent, has_params when `first`. *)
Lemma int7_tail : forall sh np ps r sel (ra t0 t2 a0 a1 a2 a3 a4 a5 a6 s3 s10 t3 t4 t5 t6 : word) m1,
  sh <> 7 -> 0 <= sel < 256 -> suffix rest r -> pc_wf sh ps -> 0 <= np < 4 -> (length ps < Z.to_nat np)%nat ->
  MBr sp m rest src pp lo (kimg sh ps sel) m1 -> CFIX sp pp m1 -> CPROP sp fl Hd sh np m1 ->
  cell8 m1 (bv_unsigned sp + 0xe0) (Z.b2z (first7 ps sel)) ->
  evt rsegs (PROPL sp gp tp F fc m rest fl src pp lo Hd sh np (length ps) (ps ++ [(key_of sel, PInt 7)]) r)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 (Z.of_nat (length r))) t2
             (Z_to_bv 64 (bv_unsigned sp + T_OFF)) (Z_to_bv 64 4)
             a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (Z.of_nat (length ps)))
             (Z_to_bv 64 S2V) s3 (Z_to_bv 64 MULT10) (Z_to_bv 64 10)
             (Z_to_bv 64 (Z.lnot pp)) (Z_to_bv 64 (cur rest src r)) (Z_to_bv 64 pp)
             (Z_to_bv 64 (Z.b2z (seen_of (ps ++ [(key_of sel, PInt 7)])))) s10
             (Z_to_bv 64 (pp + POD_LEN_OFF)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13fe0) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh np ps r sel ra t0 t2 a0 a1 a2 a3 a4 a5 a6 s3 s10 t3 t4 t5 t6 m1 Hsh Hsel Hsuf Hwf Hnp Hlt MB CF CP CE0.
  pose proof HOK as (HS0 & HS1 & HP1 & _ & HM1 & HL0 & HSP & HPP & _ & _).
  unfold POD_PROPS, MID_STACK, FRAME_LOCALS in HP1, HM1, HSP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with 18446744073709551616 in SPR.
  destruct (pc_buf_cap sh ps Hwf ltac:(lia)) as [HB8 HD8].
  unfold kimg in MB.
  assert (FK : FT sp pp fl Hd sh np (Z.b2z (first7 ps sel)) m1) by exact (conj CF (conj CP CE0)).
  pose proof (FT_kept sp pp fl Hd sh np (Z.b2z (first7 ps sel))) as KP.
  clear CF CP CE0.
  unfold POD_LEN_OFF.
  (* 0x13fe0 mv s10,t1; mv s3,a7; addi a2,zero,0x5c; addi a0,sp,0xf4; mv a1,zero; 0x13ff4 jal memset *)
  zstep. zstep. zstep. zstep. zstep. zstep.
  eapply (mset_at sp gp tp F fc m rest src pp lo HOK MSET) with (o := 244) (n := 92%nat).
  { exact KP. } { exact FK. } { exact MB. }
  { rewrite unsigned_lit by lia. reflexivity. }
  { first [reflexivity | rewrite unsigned_lit by lia; reflexivity]. }
  { first [reflexivity | rewrite unsigned_lit by lia; reflexivity]. }
  { lia. } { unfold FRAME_LOCALS. lia. }
  intros u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m2 MB2 FK2 HZ.
  fix_ret.
  (* 0x13ff8 sw s1,0xe8(sp); 0x13ffc sw s1,0xec(sp); 0x14000 addi a0,zero,7; 0x14004 sw a0,0xf0(sp) *)
  fr_step HOK MB2 FK2 (kept_write _ _ KP) (bv_unsigned sp + 232) 4%nat.
  fr_step HOK MB2 FK2 (kept_write _ _ KP) (bv_unsigned sp + 236) 4%nat.
  zstep.
  fr_step HOK MB2 FK2 (kept_write _ _ KP) (bv_unsigned sp + 240) 4%nat.
  (* e = Ent 4 4 (le32 7) at sp + 0xe8 *)
  lazymatch goal with
  | S1 : bytes_at rsegs ?mm (bv_unsigned sp + 232) ?x, S2 : bytes_at rsegs ?mm (bv_unsigned sp + 236) ?y,
    S3 : bytes_at rsegs ?mm (bv_unsigned sp + 240) ?z, S4 : bytes_at rsegs ?mm (bv_unsigned sp + 244) ?u
    |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HE : bytes_at rsegs mm (bv_unsigned sp + 232) (ent_mem (Ent 4 4 (le32 7))))
        by (eapply bytes_at_ext; [apply (bytes_at_cat4 mm _ _ _ _ x y z u S1 S2 S3 S4); lenlia
                                 | apply ent47_mem; reflexivity]);
      clear S1 S2 S3 S4
  end.
  (* 0x14008 addi a1,sp,0xe8; 0x1400c mv a0,s8; 0x14010 jal pod_write_ent *)
  zstep. zstep. zstep.
  eapply (pwe_at sp gp tp F fc m rest src pp lo HOK HPPA HSPA PWE).
  { exact (kept_frame _ _ KP). } { exact FK2. } { exact MB2. } { exact HE. } { exact ent47_wf. }
  { destruct HD8 as [c Hc]. rewrite !length_app, !length_le32.
    replace (Z.of_nat (length (pc_buf (PbCut sh ps None)) + (4 + 4))) with ((c + 1) * 8) by lia.
    apply Z.mod_mul. lia. }
  { rewrite !length_app, !length_le32, enc47_len. unfold POD_BUF_MAX. lia. }
  { rewrite unsigned_lit by lia. reflexivity. }
  { rewrite unsigned_lit by lia. reflexivity. }
  intros v0 v1 v2 va0 va1 va2 va3 va4 va5 va6 va7 v3 v4 v5 v6 mw MB3 FK3.
  fix_ret.
  (* 0x14014 ld a0,0xe0(sp); 0x14018 beqz a0 -> 0x14024 *)
  destruct (first7 ps sel) eqn:EF.
  - (* the first SPA_PROP_params: has_params := 1 (pod.h:418) *)
    pose proof FK3 as (_ & _ & CB). change (Z.b2z true) with 1 in CB.
    pose proof (cell8_read _ _ _ CB) as RB. clear CB.
    zstep. clear RB. zstep. if_cases T; [exfalso; zify_cond T; lia|].
    (* 0x1401c addi a0,zero,1; 0x14020 sw a0,0xc(s11) *)
    zstep.
    blk_step HOK MB3 FK3 (kept_frame _ _ KP) pp 16396 4%nat.
    (* 0x14024 mv a7,s3; 0x14028 mv t1,s10; 0x1402c j 0x140c8 *)
    pose proof FK3 as (CF4 & CP4 & _).
    zstep. zstep. zstep.
    apply evt_done. unfold PROPL. do 17 eexists.
    split; [reflexivity|].
    split.
    { eapply MBr_ext; [exact MB3|].
      apply int7_image_first; [exact Hsh | exact EF | unfold POD_BUF_MAX; lia | apply le4_le32]. }
    split; [exact CF4|]. split; [exact CP4|]. split; [exact Hsuf|].
    split; [apply pc_wf_int; [exact Hwf | apply key_range | lia]|]. split; [exact Hnp|].
    rewrite length_app. cbn [length]. split; lia.
  - (* not the first: has_params stays *)
    pose proof FK3 as (CF4 & CP4 & CB). change (Z.b2z false) with 0 in CB.
    pose proof (cell8_read _ _ _ CB) as RB. clear CB.
    zstep. clear RB. zstep. if_cases T; [|exfalso; zify_cond T; lia].
    (* 0x14024 mv a7,s3; 0x14028 mv t1,s10; 0x1402c j 0x140c8 *)
    zstep. zstep. zstep.
    apply evt_done. unfold PROPL. do 17 eexists.
    split; [reflexivity|].
    split; [rewrite <- (int7_image_keep sh ps sel Hsh EF); exact MB3|].
    split; [exact CF4|]. split; [exact CP4|]. split; [exact Hsuf|].
    split; [apply pc_wf_int; [exact Hwf | apply key_range | lia]|]. split; [exact Hnp|].
    rewrite length_app. cbn [length]. split; lia.
Qed.

(** 0x13450 -> 0x13fe0: seen_params' into s9 and `first` into its cell, the branches of pod.h:412 to the Int-7
    value. *)
Lemma int7_walk : forall sh np ps r sel ms, PKEY sp gp tp F fc m rest fl src pp lo Hd sh np ps r sel ms ->
  (sel mod 4 = 0 \/ Z.testbit sel 4 = true) ->
  evt rsegs (PROPL sp gp tp F fc m rest fl src pp lo Hd sh np (length ps) (ps ++ [(key_of sel, PInt 7)]) r) ms.
Proof.
  intros sh np ps r sel ms
    (ra & t0 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & s9 & s10 & t3 & t4 & t5 & t6 & m1 & -> & -> & -> & -> &
     MB & CF & CP & Hsuf & Hwf & Hnp & Hlt & Hsh & Hsel) Hcase.
  pose proof HOK as (HS0 & HS1 & HP1 & _ & HM1 & HL0 & HSP & HPP & _ & _).
  unfold POD_PROPS, MID_STACK, FRAME_LOCALS in HP1, HM1, HSP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with 18446744073709551616 in SPR.
  assert (FK : FS sp pp fl Hd sh np m1) by (split; assumption).
  clear CF CP.
  rewrite land3.
  unfold PROP_KEY.
  destruct (Z.eq_dec (sel mod 4) 0) as [HA|HA].
  - (* sel & 3 = 0: SPA_PROP_volume *)
    rewrite HA.
    assert (HK : key_of sel = POD_PROP_VOLUME) by (unfold key_of; rewrite HA; reflexivity).
    (* 0x13450 mv s9,s3; 0x13454 beqz a1 -> 0x1345c (taken) *)
    zstep. zstep. if_cases T0; [|exfalso; zify_cond T0; lia].
    (* 0x1345c snez a2,a1; 0x13460 seqz a3,s3; 0x13464 and a2,a2,a3; 0x13468 sd a2,0xe0(sp) *)
    zstep. zstep. zstep.
    fr_step HOK MB FK (FS_write sp pp fl Hd sh np) (bv_unsigned sp + 224) 8%nat.
    (* 0x1346c beqz a1 -> 0x13fe0 (taken) *)
    zstep. if_cases T1; [|exfalso; zify_cond T1; lia].
    destruct FK as (CF2 & CP2).
    replace (Z_to_bv 64 (Z.b2z (seen_of ps)))
      with (Z_to_bv 64 (Z.b2z (seen_of (ps ++ [(key_of sel, PInt 7)]))))
      by (rewrite HK, seen_app_other by (unfold POD_PROP_VOLUME, POD_PROP_PARAMS; lia); reflexivity).
    eapply int7_tail; try eassumption.
    unfold cell8. eapply bytes_at_ext; [exact ST|]. f_equal. f_equal. unfold first7. rewrite HK.
    destruct (seen_of ps); reflexivity.
  - (* sel & 3 <> 0: SPA_PROP_params, bit 4 set *)
    destruct Hcase as [Hc|Hbit]; [lia|].
    assert (HK : key_of sel = POD_PROP_PARAMS)
      by (unfold key_of; rewrite (proj2 (Z.eqb_neq (sel mod 4) 0) HA); reflexivity).
    (* 0x13450 mv s9,s3; 0x13454 beqz a1 (not taken); 0x13458 addi s9,zero,1 *)
    zstep. zstep. if_cases T0; [exfalso; zify_cond T0; lia|]. zstep.
    (* 0x1345c snez a2,a1; 0x13460 seqz a3,s3; 0x13464 and a2,a2,a3; 0x13468 sd a2,0xe0(sp) *)
    zstep. zstep. zstep.
    fr_step HOK MB FK (FS_write sp pp fl Hd sh np) (bv_unsigned sp + 224) 8%nat.
    (* 0x1346c beqz a1 (not taken); 0x13470 andi a0,a0,0x10; 0x13474 bnez a0 -> 0x13fe0 (taken: bit 4) *)
    zstep. if_cases T1; [exfalso; zify_cond T1; lia|].
    zstep. zstep. if_cases T2; [|exfalso; zify_cond T2; apply (testbit4_land sel Hbit); lia].
    destruct FK as (CF2 & CP2).
    replace (Z_to_bv 64 1) with (Z_to_bv 64 (Z.b2z (seen_of (ps ++ [(key_of sel, PInt 7)]))))
      by (rewrite HK, seen_app_params; reflexivity).
    eapply int7_tail; try eassumption.
    unfold cell8. eapply bytes_at_ext; [exact ST|]. f_equal. f_equal. unfold first7. rewrite HK, Z.eqb_refl.
    rewrite (proj2 (Z.ltb_lt 0 (sel mod 4))) by lia. destruct (seen_of ps); reflexivity.
Qed.

End Int7.

Theorem int7_holds : memset_c.memset_contract -> pod_write_ent_c.pod_write_ent_contract ->
  forall sp gp tp F fc m rest fl src pp lo H, BOK sp rest src pp lo -> pp mod 16 = 0 -> bv_unsigned sp mod 16 = 0 ->
  forall sh np ps r sel ms, PKEY sp gp tp F fc m rest fl src pp lo H sh np ps r sel ms ->
  (sel mod 4 = 0 \/ Z.testbit sel 4 = true) ->
  evt rsegs (PROPL sp gp tp F fc m rest fl src pp lo H sh np (length ps) (ps ++ [(key_of sel, PInt 7)]) r) ms.
Proof.
  intros MSET PWE sp gp tp F fc m rest fl src pp lo Hd HOK HPPA HSPA.
  exact (int7_walk sp gp tp F fc m rest fl src pp lo Hd HOK HPPA HSPA MSET PWE).
Qed.
