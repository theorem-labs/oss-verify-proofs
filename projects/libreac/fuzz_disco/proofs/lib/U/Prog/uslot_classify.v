From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcModel RcLeaf RcKind RcParse CtrlParsed.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c disco_table.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_classify_c SightModel SightLib GateModel.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import classify_core_c reac_disco_classify_c reac_disco_classify_on_segment_c check_sighting_c reac_disco_gate_should_push_c bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib uslot_frame uslot_observe.
Import ListNotations.
Open Scope Z_scope.

Lemma sc_cm_ret0 : forall F len U L O, cm_ret F len U L = 0 ->
  dkind F len <> 0 /\ bytes_eqb (src F) U = false /\ (dkind F len = 1 \/ fsum F = 0) /\
  cm_out F len U L O = sight F len.
Proof.
  intros F len U L O. unfold cm_ret, cm_out, classify_model.
  generalize (dkind F len) as k. generalize (bytes_eqb (src F) U) as e. generalize (fsum F) as s. intros s e k H.
  destruct (Z.eqb_spec k 0) as [E1|E1]; [cbn [fst snd] in H; lia|].
  destruct e; [cbn [fst snd] in H; lia|].
  destruct (Z.eqb_spec k 1) as [E3|E3]; destruct (Z.eqb_spec s 0) as [E5|E5]; cbn [negb andb] in *;
    try (cbn [fst snd] in H; lia);
    (destruct L as [Lb|];
     [ destruct (negb (lv Lb =? 0) && negb (bytes_eqb (lm Lb) (src F))); cbn [fst snd] in *; try lia | cbn [fst snd] in * ]);
    repeat split; auto.
Qed.

Lemma sc_cm_lock : forall F len U Lb, length F = 50%nat -> length Lb = 12%nat ->
  exists Lb', cm_lock F len U (Some Lb) = Some Lb' /\ length Lb' = 12%nat.
Proof.
  intros F len U Lb LF HL. unfold cm_lock, classify_model.
  generalize (dkind F len) as k. intros k.
  assert (HT : length (latch F Lb) = 12%nat).
  { unfold latch, src, fld, le4. rewrite !length_app, length_Z_to_le_bytes, !length_firstn, !length_skipn, LF, HL.
    reflexivity. }
  destruct (k =? 0); [eexists; split; [reflexivity | exact HL]|].
  destruct (bytes_eqb (src F) U); [eexists; split; [reflexivity | exact HL]|].
  destruct (negb (k =? 1) && negb (fsum F =? 0)); [eexists; split; [reflexivity | exact HL]|].
  destruct ((k =? 1) && negb (lv Lb =? 0) && negb (bytes_eqb (lm Lb) (src F)));
    [eexists; split; [reflexivity | exact HL]|].
  destruct (negb (k =? 1) && (lv Lb =? 0)); eexists; split; [reflexivity | exact HT | reflexivity | exact HL].
Qed.

Lemma sc_dkind_len : forall F len, dkind F len <> 0 -> 50 <= len.
Proof.
  intros F len H. unfold dkind, ctrlparse in H. destruct (cp_hdr len F) eqn:E; [|cbn in H; lia].
  unfold cp_hdr in E. apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply Z.leb_le in E. exact E.
Qed.

Lemma sc_dkind_1 : forall F len, dkind F len = 1 -> fb F 16 = 0 /\ fb F 17 = 0.
Proof.
  intros F len H. unfold dkind, ctrlparse in H. destruct (cp_hdr len F); cbn [fst] in H; [|discriminate].
  unfold cp_kind in H. destruct (cp_type F 0 0) eqn:E.
  - unfold cp_type in E. apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1, E2. exact (conj E1 E2).
  - unfold KL1 in H.
    repeat match type of H with context [if ?c then _ else _] => destruct c end; discriminate.
Qed.

Lemma sc_role : forall F k, 0 <= role F k <= 2.
Proof.
  intros F k. unfold role.
  destruct (k =? 1); [destruct (cp_bcast F); lia|].
  destruct ((k =? 2) || (k =? 3) || (k =? 4) || (k =? 6)); [lia|].
  destruct ((k =? 7) || (k =? 9)); [lia|].
  destruct (k =? 5); [|lia].
  destruct ((fb F 22 =? 0) && ((tag F =? 256) || (tag F =? 770) || (tag F =? 1280))); lia.
Qed.

Lemma sc_cnt_nonneg : forall f bs k, 0 <= cnt f bs k.
Proof. intros f bs k. induction k as [|k IH]; cbn [cnt]; [lia|]. destruct (f _); lia. Qed.

Lemma sc_bytes_eqb_refl : forall a, bytes_eqb a a = true.
Proof. intros a. unfold bytes_eqb. destruct (list_eq_dec Z.eq_dec _ _) as [_|N]; [reflexivity | exfalso; apply N; reflexivity]. Qed.

Lemma sc_le4_val : forall z, 0 <= z < 2 ^ 32 -> bytes_le_to_Z (le4 (Z_to_bv 64 z)) = z.
Proof.
  intros z Hz. rewrite bytes_le_to_Z_le4. rewrite unsigned_lit by lia. apply Z.mod_small. lia.
Qed.

Lemma sc_zb_small : forall i, 0 <= i < 256 -> bv_unsigned (zb i) = i.
Proof. intros i Hi. unfold zb. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hi. Qed.

Lemma sc_le4_len : forall v, length (le4 v) = 4%nat.
Proof. intros v. unfold le4. apply length_Z_to_le_bytes. Qed.

Lemma sc_ble1 : forall b : byte, bytes_le_to_Z [b] = bv_unsigned b.
Proof. intros b. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity. Qed.

Lemma sc_sdecl_core : forall (d : bool) (a b i o : Z), 0 <= a -> 0 <= b ->
  (if d && (4 * a <=? 40) && (4 * b <=? 40) then Some (4 * a, 4 * b) else None) = Some (i, o) ->
  0 <= i <= 40 /\ 0 <= o <= 40.
Proof.
  intros d a b i o N1 N2 E.
  destruct (d && (4 * a <=? 40) && (4 * b <=? 40)) eqn:C; [|discriminate].
  injection E as <- <-. apply andb_prop in C as [C C3]. apply andb_prop in C as [_ C2].
  apply Z.leb_le in C2, C3. lia.
Qed.

Lemma sc_nin : forall P, 0 <= n_in P.
Proof. intros P. unfold n_in. apply sc_cnt_nonneg. Qed.

Lemma sc_nout : forall P, 0 <= n_out P.
Proof. intros P. unfold n_out. apply sc_cnt_nonneg. Qed.

Lemma sc_sdecl : forall F i o, sdecl F = Some (i, o) -> 0 <= i <= 40 /\ 0 <= o <= 40.
Proof.
  intros F i o E.
  exact (sc_sdecl_core (decl (fld F 18 20)) (n_in (fld F 18 20)) (n_out (fld F 18 20)) i o
    (sc_nin (fld F 18 20)) (sc_nout (fld F 18 20)) E).
Qed.

Lemma sc_sight : forall F len U L, length F = 50%nat -> cm_ret F len U L = 0 ->
  sighting_facts (sight F len) F U len 0 /\ length (sight F len) = 24%nat /\
  sighting_S1 (sight F len) /\ sighting_S2 (sight F len).
Proof.
  intros F len U L LF H. destruct (sc_cm_ret0 F len U L [] H) as (K0 & NE & K1 & _).
  pose proof (sc_dkind_len F len K0) as L50.
  assert (K1' : (fb F 16 = 0 /\ fb F 17 = 0) \/ fsum F = 0).
  { destruct K1 as [K1|K1]; [left; apply sc_dkind_1 with (len := len); exact K1 | right; exact K1]. }
  clear K1 H.
  assert (LS : length (src F) = 6%nat) by (unfold src, fld; rewrite length_firstn, length_skipn; lia).
  pose proof (sc_role F (dkind F len)) as HR.
  pose proof (geo_range len) as HG.
  pose proof (sc_sdecl F) as HD.
  unfold sighting_facts, sighting_S1, sighting_S2, s_role, s_hd, s_din, s_dout, s32_at, u_at, disco_classify_c.sighting_ok.
  change (fld F 6 6) with (src F). unfold sight.
  revert HR. generalize (role F (dkind F len)) as r. intros r HR.
  generalize (slots F) as sl. intros sl.
  pose proof (sc_le4_val r ltac:(lia)) as VR. pose proof (sc_le4_len (Z_to_bv 64 r)) as LR.
  pose proof (sc_le4_val (geo len) HG) as VG. pose proof (sc_le4_len (Z_to_bv 64 (geo len))) as LG.
  destruct (le4 (Z_to_bv 64 r)) as [|c0 [|c1 [|c2 [|c3 [|? ?]]]]]; cbn [length] in LR; try lia.
  destruct (le4 (Z_to_bv 64 (geo len))) as [|g0 [|g1 [|g2 [|g3 [|? ?]]]]]; cbn [length] in LG; try lia.
  destruct (src F) as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 l]]]]]]]; cbn [length] in LS; try lia.
  destruct (sdecl F) as [[i o]|]; [destruct (HD i o eq_refl) as [Hi Ho] | ]; clear HD;
    cbn [app length]; unfold fb, fu, fld, sub;
    change (Z.to_nat 8) with 8%nat; change (Z.to_nat 12) with 12%nat; change (Z.to_nat 13) with 13%nat;
    change (Z.to_nat 14) with 14%nat; cbn [skipn firstn nth];
    rewrite ?VR, ?VG, ?sc_ble1; rewrite ?sc_zb_small by lia; rewrite ?swrap32_id by lia;
    unfold s32; replace (r <? 2 ^ 31) with true by (symmetry; apply Z.ltb_lt; lia);
    repeat split; try lia; try apply sc_bytes_eqb_refl; try exact NE; try exact K1'.
Qed.

Lemma gm_push : forall G S now, snd (gate_model G S now) = 0 \/ snd (gate_model G S now) = 1.
Proof.
  intros G S now. unfold gate_model.
  destruct (gfind G (fld S 0 6) 0 (Z.to_nat (gn G))) as [i|].
  - destruct (gedge G S i); [right; reflexivity|].
    destruct ((now <? fu G (32 * i + 24) 8) || (RF <=? now - fu G (32 * i + 24) 8)); [right | left]; reflexivity.
  - destruct (8 <=? gn G); [left | right]; reflexivity.
Qed.

Lemma cm_lock_none : forall F len U, cm_lock F len U None = None.
Proof.
  intros F len U. unfold cm_lock, classify_model. generalize (dkind F len) as k. intros k.
  destruct (k =? 0); [reflexivity|]. destruct (bytes_eqb (src F) U); [reflexivity|].
  destruct (negb (k =? 1) && negb (fsum F =? 0)); reflexivity.
Qed.

Lemma sc_cm_ret_cases : forall F len U L, cm_ret F len U L = -1 \/ cm_ret F len U L = 0.
Proof.
  intros F len U L. unfold cm_ret, classify_model. generalize (dkind F len) as k. intros k.
  destruct (k =? 0); [left; reflexivity|]. destruct (bytes_eqb (src F) U); [left; reflexivity|].
  destruct (negb (k =? 1) && negb (fsum F =? 0)); [left; reflexivity|].
  destruct L as [Lb|]; [|right; reflexivity].
  destruct ((k =? 1) && negb (lv Lb =? 0) && negb (bytes_eqb (lm Lb) (src F))); [left | right]; reflexivity.
Qed.

Definition R19A : Z := 0x13d64.
Definition R19B : Z := 0x13d7c.
Definition R19R : Z := 0x13d94.

Definition fb50 (Rb : list byte) : list byte := firstn 50 (Rb ++ repeat (Z_to_bv 8 0) 50).

Lemma fb50_len : forall Rb, length (fb50 Rb) = 50%nat.
Proof. intros Rb. unfold fb50. rewrite length_firstn, length_app, repeat_length. lia. Qed.

Lemma fb50_at : forall m f Rb, bytes_at rsegs m f Rb -> (50 <= length Rb)%nat -> bytes_at rsegs m f (fb50 Rb).
Proof.
  intros m f Rb H L. unfold fb50. rewrite firstn_app. replace (50 - length Rb)%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r. change (firstn 50 Rb) with (sub Rb 0 50).
  rewrite <- (Z.add_0_r f). apply bytes_at_sub; [exact H | lia | lia].
Qed.


Definition cls_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (X lo len : Z) (FB U OB : list byte) (L : option (list byte)) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (cm_ret FB len U L)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 R19R) fc None m' (seg_rom rsegs) /\
    munch [(lo, X); (X + 268, X + 280); (X + 1056, X + 1080)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X /\
    rw_cells rsegs m' (X + 1056) [CB 24 (cm_out FB len U L OB)] /\
    exists Lb', rw_cells rsegs m' (X + 268) [CB 12 Lb'].

Lemma uslot_R19_cls0 : reac_disco_classify_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X lo f len : Z) (Rb U OB Lb : list byte),
  sp = Z_to_bv 64 X -> s7 = Z_to_bv 64 f -> s3 = Z_to_bv 64 len ->
  0 < X -> X mod 16 = 0 -> X + 2624 < 2 ^ 63 -> 0 < f -> f + len <= lo -> 0 <= len < 2 ^ 16 ->
  bytes_at rsegs m f Rb -> Z.of_nat (length Rb) = len ->
  length U = 6%nat -> bytes_at rsegs m (X + 946) U ->
  rw_cells rsegs m (X + 1056) [CB 24 OB] -> rw_cells rsegs m (X + 268) [CB 12 Lb] ->
  mem_inv rsegs m -> stk rsegs m lo X -> lo + CLASSIFY_CORE_K <= X ->
  evt rsegs (cls_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m X lo len (fb50 Rb) U OB None)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R19A) fc None m (seg_rom rsegs)).
Proof.
  intros CC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X lo f len Rb U OB Lb Esp Es7 Es3 HX0 HX16 HX1 Hf0 Hflo Hlen HR LR LU HU RO RL MI ST HLO.
  subst sp s7 s3. unfold R19A, cls_post. unfold CLASSIFY_CORE_K in HLO.
  pose proof (munch_refl [(lo, X); (X + 268, X + 280); (X + 1056, X + 1080)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step. step.
  eapply evt_cut.
  { eapply CC with (lo := lo) (f := f) (len := len) (u := X + 946) (o := X + 1056) (FB := fb50 Rb) (U := U) (OB := OB);
      try reflexivity.
    unfold classify_core_pre, disj, CLASSIFY_CORE_K. rewrite (unsigned_lit X) by lia.
    split; [lia|]. split; [exact ST|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [apply fb50_len|].
    split; [intros H50; split; [lia|]; split; [apply fb50_at; [exact HR | lia] | lia]|].
    split; [exact LU|]. split; [exact HU|]. split; [lia|].
    split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [exact RO|]. split; [lia|].
    split; [lia|]. split; [reflexivity|]. exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              Eq & MUc & WMc & MI2 & ST2 & RO2 & LK2).
  subst ms'. cbn [app] in MUc.
  rewrite (unsigned_lit X) in MUc, ST2 by lia. unfold CLASSIFY_CORE_K in MUc.
  transport_after_call rsegs m m2 MUc WMc. clear MUc WMc MI.
  rewrite (ret_pc_even 0x13d78) by (first [lia | reflexivity]).
  step.
  apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact RO2|]. exists Lb. exact RL.
Qed.

Lemma uslot_R19_cls1 : reac_disco_classify_on_segment_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X lo f len : Z) (Rb U OB Lb : list byte),
  sp = Z_to_bv 64 X -> s7 = Z_to_bv 64 f -> s3 = Z_to_bv 64 len ->
  0 < X -> X mod 16 = 0 -> X + 2624 < 2 ^ 63 -> 0 < f -> f + len <= lo -> 0 <= len < 2 ^ 16 ->
  bytes_at rsegs m f Rb -> Z.of_nat (length Rb) = len ->
  length U = 6%nat -> bytes_at rsegs m (X + 946) U ->
  rw_cells rsegs m (X + 1056) [CB 24 OB] -> rw_cells rsegs m (X + 268) [CB 12 Lb] ->
  mem_inv rsegs m -> stk rsegs m lo X -> lo + CLASSIFY_CORE_K <= X ->
  evt rsegs (cls_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m X lo len (fb50 Rb) U OB (Some Lb))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R19B) fc None m (seg_rom rsegs)).
Proof.
  intros CC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X lo f len Rb U OB Lb Esp Es7 Es3 HX0 HX16 HX1 Hf0 Hflo Hlen HR LR LU HU RO RL MI ST HLO.
  pose proof (rwc_len _ _ _ _ RL) as LL.
  subst sp s7 s3. unfold R19B, cls_post. unfold CLASSIFY_CORE_K in HLO.
  pose proof (munch_refl [(lo, X); (X + 268, X + 280); (X + 1056, X + 1080)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step. step. step.
  eapply evt_cut.
  { eapply CC with (lo := lo) (lk := X + 268) (f := f) (len := len) (u := X + 946) (o := X + 1056)
      (FB := fb50 Rb) (U := U) (OB := OB) (L := Some Lb); try reflexivity.
    unfold classify_core_pre, disj, CLASSIFY_CORE_K. rewrite (unsigned_lit X) by lia.
    split; [lia|]. split; [exact ST|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [apply fb50_len|].
    split; [intros H50; split; [lia|]; split; [apply fb50_at; [exact HR | lia] | lia]|].
    split; [exact LU|]. split; [exact HU|]. split; [lia|].
    split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [exact RO|]. split; [lia|].
    split; [lia|]. split; [split; [lia|]; split; [Z.div_mod_to_equations; lia|]; split; [exact RL|]; lia|]. exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              Eq & MUc & WMc & MI2 & ST2 & RO2 & LK2).
  subst ms'. cbn [app] in MUc.
  rewrite (unsigned_lit X) in MUc, ST2 by lia. unfold CLASSIFY_CORE_K in MUc.
  transport_after_call rsegs m m2 MUc WMc. clear MUc WMc MI.
  rewrite (ret_pc_even 0x13d94) by (first [lia | reflexivity]).
  apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact RO2|].
  destruct (sc_cm_lock (fb50 Rb) len U Lb (fb50_len Rb) LL) as (Lb' & ELb & _). rewrite ELb in LK2.
  exists Lb'. exact LK2.
Qed.

Ltac ccl :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.

Lemma uslot_R19_out :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 (-1) ->
  evt rsegs (fun ms' => exists a1' a2' : word,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 R27) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R19R) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Ea0.
  subst a0. unfold R19R, R27.
  step. step. step. ccl. step. ccl.
  apply evt_done. do 2 eexists. reflexivity.
Qed.

Definition R20 : Z := 0x13de0.

Lemma uslot_R19_sight : check_sighting_contract -> reac_disco_gate_should_push_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X lo f len rem now : Z) (FB U S G : list byte)
    (j208 j232 : word),
  sp = Z_to_bv 64 X -> a0 = Z_to_bv 64 0 -> s3 = Z_to_bv 64 len -> s4 = Z_to_bv 64 rem ->
  0 < X -> X mod 16 = 0 -> X + 2624 < 2 ^ 63 -> 0 < f -> f + len <= lo -> 0 <= len < 2 ^ 16 ->
  0 <= now < 2 ^ 64 ->
  sighting_facts S FB U len 0 -> length S = 24%nat ->
  length FB = 50%nat -> bytes_at rsegs m f FB ->
  length U = 6%nat -> bytes_at rsegs m (X + 946) U ->
  rw_cells rsegs m (X + 208) [C8 j208] -> rw_cells rsegs m (X + 224) [C8 (Z_to_bv 64 now)] ->
  rw_cells rsegs m (X + 232) [C8 j232] -> rw_cells rsegs m (X + 248) [C8 (Z_to_bv 64 f)] ->
  rw_cells rsegs m (X + 1056) [CB 24 S] ->
  rw_cells rsegs m (X + 280) [CB 264 G] -> gate_ok G ->
  mem_inv rsegs m -> stk rsegs m lo X -> lo + REAC_DISCO_GATE_SHOULD_PUSH_K <= X ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (m' : word -> option byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 (Z_to_bv 64 (snd (gate_model G S now))) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 R20) fc None m' (seg_rom rsegs) /\
       munch [(lo, X); (X + 208, X + 216); (X + 232, X + 240); (X + 280, X + 544)] m m' /\
       wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X /\
       rw_cells rsegs m' (X + 208) [C8 s9] /\ rw_cells rsegs m' (X + 232) [C8 (Z_to_bv 64 rem)] /\
       rw_cells rsegs m' (X + 280) [CB 264 (fst (gate_model G S now))] /\ gate_ok (fst (gate_model G S now)) /\
       rw_cells rsegs m' (X + 1056) [CB 24 S])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R19R) fc None m (seg_rom rsegs)).
Proof.
  intros CSC GSC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X lo f len rem now FB U S G j208 j232 Esp Ea0 Es3 Es4 HX0 HX16 HX1 Hf0 Hflo Hlen Hnow
    SF LS LFB HFB LU HU R208 R224 R232 R248 RS RG GOK MI ST HLO.
  subst sp a0 s3 s4. unfold R19R, R20. unfold REAC_DISCO_GATE_SHOULD_PUSH_K in HLO.
  pose proof (munch_refl [(lo, X); (X + 208, X + 216); (X + 232, X + 240); (X + 280, X + 544)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof SF as SF'. destruct SF' as (L50 & _).
  pose proof (rwc_split _ _ _ _ RS) as (_ & HS & _).
  step. step. step. ccl. step. ccl.
  step. step. step. step. step. step.
  eapply evt_cut.
  { eapply CSC with (lo := lo) (s := X + 1056) (f := f) (len := len) (u := X + 946) (st := 0) (S := S) (FB := FB) (U := U);
      try reflexivity; rewrite ?(unsigned_lit X) by lia; try eassumption; try unfold CHECK_SIGHTING_K; try lia;
      Z.div_mod_to_equations; lia. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              Eq & MUc & WMc & MI2 & ST2).
  subst ms'.
  rewrite (unsigned_lit X) in MUc, ST2 by lia. unfold CHECK_SIGHTING_K in MUc.
  transport_after_call rsegs m m2 MUc WMc. clear MUc WMc MI.
  rewrite (ret_pc_even 0x13dbc) by (first [lia | reflexivity]).
  step. step. step. step.
  eapply evt_cut.
  { eapply GSC with (lo := lo) (g := X + 280) (s := X + 1056) (now := now) (G := G) (S := S);
      try reflexivity; rewrite ?(unsigned_lit X) by lia; try eassumption; try unfold REAC_DISCO_GATE_SHOULD_PUSH_K;
      try lia; Z.div_mod_to_equations; lia. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 &
              Eq & MUc & WMc & MI3 & ST3 & RG3 & GOK3 & HS3).
  subst ms'.
  rewrite (unsigned_lit X) in MUc, ST3 by lia. unfold REAC_DISCO_GATE_SHOULD_PUSH_K in MUc.
  transport_after_call rsegs m2 m3 MUc WMc. clear MUc WMc MI2.
  rewrite (ret_pc_even 0x13dcc) by (first [lia | reflexivity]).
  pose proof (gm_push G S now) as HP.
  step. step. step. rewrite ltu_lit by lia.
  replace (1 <? snd (gate_model G S now)) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step. step.
  apply evt_done. do 17 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.


Definition R21 : Z := 0x13e50.

Lemma cw_add : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
  intros x c. rewrite unsigned_lit_wrap.
  rewrite <- (Z_to_bv_mod64 (x mod 2 ^ 64 + c)), <- (Z_to_bv_mod64 (x + c)).
  f_equal. apply Zplus_mod_idemp_l.
Qed.

Ltac weq := first [ reflexivity
                  | (apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; rewrite ?Z.shiftl_mul_pow2 by lia;
                     try change (2 ^ 5) with 32; Z.div_mod_to_equations; lia) ].

Lemma uslot_R20 : bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X : Z) (G : list byte),
  sp = Z_to_bv 64 X -> 0 < X -> X + 2624 < 2 ^ 63 ->
  rw_cells rsegs m (X + 280) [CB 264 G] -> gate_ok G ->
  rw_cells rsegs m (X + 256) [C8 (Z_to_bv 64 (nt (X + 280)))] -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s9' s11' t3' t4' t5' t6' : word)
                       (m' : word -> option byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1' a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4' s5 s6' s7' s8 s9' s10 s11' t3' t4' t5' t6')
                F (Z_to_bv 64 R21) fc None m' (seg_rom rsegs) /\
       munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R20) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X G Esp HX0 HX1 RG GOK R256 MI.
  subst sp. unfold R20, R21.
  pose proof GOK as (LG & HN & HD).
  pose proof (rw_CB_read rsegs m (X + 280) 264 G 256 4 RG ltac:(lia)) as RN.
  change (X + 280 + Z.of_nat 256) with (X + 280 + 256) in RN.
  step. change (firstn 4 (skipn 256 G)) with (fld G 256 4).
  rewrite GateModel.lw_val by (apply length_fld; lia). change (s32 (bytes_le_to_Z (fld G 256 4))) with (gn G).
  clear RN.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  step. step. rewrite ltu_lit by lia. replace (8 <? gn G) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step. rewrite GateModel.eqb_lit by lia.
  destruct (Z.eqb_spec (gn G) 0) as [N0|N0]; cbv iota.
  - apply evt_done. unfold QQ. do 22 eexists. exists m. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. exact MI.
  - assert (OUTER : forall k i (m2 : word -> option byte)
        (ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x28 x29 x30 x31 w1 w9 w11 : word),
        Z.of_nat k = gn G - i -> 0 <= i < gn G ->
        w1 = Z_to_bv 64 (32 * (i + 1)) -> w9 = Z_to_bv 64 (32 * gn G) -> w11 = Z_to_bv 64 i ->
        munch [] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 -> rw_cells rsegs m2 (X + 280) [CB 264 G] ->
        rw_cells rsegs m2 (X + 256) [C8 (Z_to_bv 64 (nt (X + 280)))] ->
        evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 X) gp tp x5 x6 x7 s0 w1
                              x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 x20 s5 x22 (Z_to_bv 64 (gn G)) s8 w9
                              s10 w11 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x13dfc) fc None m2 (seg_rom rsegs))).
    { induction k as [|k IH];
        intros i m2 ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x28 x29 x30 x31 w1 w9 w11
          Hk Hi E1 E9 E11 MU2 WM2 MI2 RG2 R2562;
        [lia|]. subst w1 w9 w11.
      step. step. rewrite ?cw_add. step. rewrite ltu_lit by lia.
      destruct (Z.ltb_spec (i + 1) (gn G)) as [Hj|Hj]; cbn [negb].
      - step. step. step. step.
        assert (INNER : forall k' j (m3 : word -> option byte)
            (ra'' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 w4 w6 w11 : word),
            w4 = Z_to_bv 64 (32 * j) -> w6 = Z_to_bv 64 (X + 280 + 32 * i) -> w11 = Z_to_bv 64 (i + 1) ->
            Z.of_nat k' = gn G - j -> i < j < gn G ->
            munch [] m m3 -> wmono rsegs m m3 -> mem_inv rsegs m3 -> rw_cells rsegs m3 (X + 280) [CB 264 G] ->
            rw_cells rsegs m3 (X + 256) [C8 (Z_to_bv 64 (nt (X + 280)))] ->
            evt rsegs QQ (MS (mkR ra'' (Z_to_bv 64 X) gp tp y5 y6 y7 s0 (Z_to_bv 64 (32 * (i + 1)))
                                  y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 w4 s5 w6 (Z_to_bv 64 (gn G)) s8
                                  (Z_to_bv 64 (32 * gn G)) s10 w11 y28 y29 y30 y31)
                             F (Z_to_bv 64 0x13e18) fc None m3 (seg_rom rsegs))).
        { induction k' as [|k' IH'];
            intros j m3 ra'' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 w4 w6 w11
              Ew4 Ew6 Ew11 Hk' Hjj MU3 WM3 MI3 RG3 R2563;
            [lia|]. subst w4 w6 w11.
          step. step. rewrite eqb_lit by lia. replace (32 * j =? 256) with false by (symmetry; apply Z.eqb_neq; lia).
          cbv iota.
          step. step. rewrite ltu_lit by (unfold nt; lia).
          replace (nt (X + 280) <? 32 * j) with false by (symmetry; apply Z.ltb_ge; unfold nt; lia). cbv iota.
          step. step. step. step. step.
          assert (LM : forall q : nat, (q < 8)%nat -> length (gmac G q) = 6%nat)
            by (intros q Hq; unfold gmac; apply length_fld; lia).
          destruct (memcmp6 (gmac G (Z.to_nat i)) (gmac G (Z.to_nat j)) (LM (Z.to_nat i) ltac:(lia)) (LM (Z.to_nat j) ltac:(lia)))
            as (v & Hv & Veq & Vr).
          assert (NE : gmac G (Z.to_nat i) <> gmac G (Z.to_nat j)).
          { intros E. pose proof (HD (Z.to_nat i) (Z.to_nat j) ltac:(lia) ltac:(lia)) as HF.
            apply bytes_eqb_false in HF. apply HF. rewrite E. reflexivity. }
          assert (V0 : v <> 0) by (intros E; apply NE; apply Veq; exact E).
          pose proof (rwc_bytes _ _ _ _ RG3) as HG3.
          eapply evt_cut.
          { eapply BC with (ls := gmac G (Z.to_nat i)) (rs := gmac G (Z.to_nat j)) (v := v).
            - rewrite !unsigned_lit by lia.
              match goal with |- bytes_at _ _ ?A _ => replace A with (X + 280 + Z.of_nat (32 * Z.to_nat i)) by lia end.
              unfold gmac. apply GateModel.bytes_at_fld; [exact HG3 | lia].
            - rewrite !unsigned_lit by lia.
              match goal with |- bytes_at _ _ ?A _ => replace A with (X + 280 + Z.of_nat (32 * Z.to_nat j)) by lia end.
              unfold gmac. apply GateModel.bytes_at_fld; [exact HG3 | lia].
            - rewrite (unsigned_lit 6) by lia. exact Hv.
            - exact MI3. }
          intros ms' PO. unfold memcmp_post in PO.
          destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m4 &
                          Eq & MUc & WMc & MI4 & B1 & B2).
          subst ms'. clear B1 B2.
          transport_after_call rsegs m3 m4 MUc WMc. clear MUc WMc MI3.
          rewrite (ret_pc_even 0x13e3c) by (first [lia | reflexivity]).
          step. rewrite eqb_small by exact Vr. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; exact V0).
          cbv iota.
          step. rewrite ?cw_add. step. rewrite eqb_lit by lia.
          destruct (Z.eqb_spec (32 * gn G) (32 * j + 32)) as [J0|J0]; cbn [negb].
          + step. rewrite ?cw_add. step. rewrite eqb_lit by lia.
            replace (i + 1 =? gn G) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
            apply (IH (i + 1)); try assumption; try weq; lia.
          + apply (IH' (j + 1)); try assumption; try weq; lia. }
        apply (INNER (Z.to_nat (gn G - (i + 1))) (i + 1)); try assumption; try weq; lia.
      - step. rewrite ?cw_add. step. rewrite eqb_lit by lia.
        replace (i + 1 =? gn G) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
        apply evt_done. unfold QQ. do 22 eexists. exists m2. split; [reflexivity|].
        split; [exact MU2|]. split; [exact WM2|]. exact MI2. }
    step. step. step.
    apply (OUTER (Z.to_nat (gn G)) 0); try assumption; try weq; try lia; try apply munch_refl; try apply wmono_refl.
Qed.

Lemma land_bit : forall a k, 0 <= k -> Z.land a (2 ^ k) = if Z.testbit a k then 2 ^ k else 0.
Proof.
  intros a k Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, (Z.pow2_bits_eqb k n Hk).
  destruct (Z.testbit a k) eqn:E.
  - rewrite (Z.pow2_bits_eqb k n Hk). destruct (Z.eqb_spec k n) as [<-|N]; [rewrite E; reflexivity | apply andb_false_r].
  - rewrite Z.bits_0. destruct (Z.eqb_spec k n) as [<-|N]; [rewrite E; reflexivity | apply andb_false_r].
Qed.

Lemma fam_val : forall ob : byte,
  bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (sxb ob)) 57))) 62)) =
  (bv_unsigned ob / 32) mod 4.
Proof.
  intros ob. pose proof (byte_range ob) as Hb. rewrite sxb_unsigned.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite (unsigned_lit_wrap (_ * 2 ^ 57)).
  change (2 ^ 64) with (128 * 2 ^ 57). rewrite Z.mul_mod_distr_r by lia.
  replace (2 ^ 62) with (2 ^ 57 * 32) by reflexivity. rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia.
  rewrite unsigned_lit; [|pose proof (Z.mod_pos_bound (if bv_unsigned ob <? 128 then bv_unsigned ob else bv_unsigned ob - 256 + 128 * 2 ^ 57) 128); split; [apply Z.div_pos; lia | apply (Z.lt_le_trans _ 128); [apply Z.div_lt_upper_bound; lia | lia]]].
  destruct (Z.ltb_spec (bv_unsigned ob) 128); Z.div_mod_to_equations; lia.
Qed.

Definition fam_upd (op : Z) (S : list byte) : list byte :=
  if Z.testbit op 4 then upd_bytes S 15 [Z_to_bv 8 ((op / 32) mod 4)] else S.

Definition R21T : Z := 0x13e68.

Lemma uslot_R21 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X : Z) (ob : byte) (S : list byte),
  sp = Z_to_bv 64 X -> s0 = sxb ob -> 0 < X -> X + 2624 < 2 ^ 63 ->
  rw_cells rsegs m (X + 208) [C8 (Z_to_bv 64 (bv_unsigned ob))] ->
  rw_cells rsegs m (X + 1056) [CB 24 S] -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a0' s0' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' s1 a0' a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (bv_unsigned ob)) s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 R21T) fc None m' (seg_rom rsegs) /\
      munch [(X + 1056, X + 1080)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (X + 1056) [CB 24 (fam_upd (bv_unsigned ob) S)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R21) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X ob S Esp Es0 HX0 HX1 R208 RS MI.
  subst sp s0. unfold R21, R21T, fam_upd.
  pose proof (byte_range ob) as Hob.
  pose proof (rwc_len _ _ _ _ RS) as LS.
  step. step. rewrite (unsigned_lit (bv_unsigned ob)) by lia.
  change (Z.land (bv_unsigned ob) 16) with (Z.land (bv_unsigned ob) (2 ^ 4)). rewrite land_bit by lia.
  step.
  destruct (Z.testbit (bv_unsigned ob) 4) eqn:B4; ccl.
  - step. step. step.
    pose proof (rw_CB_store_ok rsegs m (X + 1056) 24 S 15 1 RS ltac:(lia)) as SO.
    pose proof (rw_CB_write rsegs m (X + 1056) 24 S 15
      (le1 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (sxb ob)) 57)) ≫ 62))) RS
      ltac:(unfold le1; rewrite length_Z_to_le_bytes; lia)) as RS2.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [apply munch_write; [apply munch_refl | lia | unfold le1; rewrite length_Z_to_le_bytes; lia |
                                 unfold le1; rewrite length_Z_to_le_bytes; cbn; lia]|].
    split; [apply wmono_write; apply wmono_refl|].
    split; [apply mem_inv_store; [exact MI | unfold le1; rewrite length_Z_to_le_bytes; exact SO]|].
    replace [Z_to_bv 8 ((bv_unsigned ob / 32) mod 4)]
      with (le1 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (sxb ob)) 57)) ≫ 62))).
    + exact RS2.
    + unfold le1. rewrite fam_val. cbn [Z_to_le_bytes]. reflexivity.
  - apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. exact RS.
Qed.

Lemma uslot_R21_tail :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X rem push op : Z),
  sp = Z_to_bv 64 X -> s9 = Z_to_bv 64 op -> s5 = Z_to_bv 64 push -> 0 < X -> X + 2624 < 2 ^ 63 ->
  0 <= op < 256 -> 0 <= push <= 1 ->
  rw_cells rsegs m (X + 232) [C8 (Z_to_bv 64 rem)] ->
  evt rsegs (fun ms' => exists (a0' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                    s2 s3 (Z_to_bv 64 rem) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 (if (push =? 0) && negb (Z.testbit op 2) then R27 else R22)) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R21T) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X rem push op Esp Es9 Es5 HX0 HX1 Hop Hpush R232.
  subst sp s9 s5. unfold R21T, R22, R27.
  step. rewrite (unsigned_lit op) by lia.
  change (Z.land op 4) with (Z.land op (2 ^ 2)). rewrite land_bit by lia.
  step. step. step.
  assert (HP : push = 0 \/ push = 1) by lia.
  destruct (Z.testbit op 2) eqn:B2; destruct HP as [-> | ->]; ccl; apply evt_done; eexists; reflexivity.
Qed.

Lemma fam_ok : forall op S, length S = 24%nat -> sighting_S1 S -> sighting_S2 S ->
  length (fam_upd op S) = 24%nat /\ sighting_S1 (fam_upd op S) /\ sighting_S2 (fam_upd op S).
Proof.
  intros op S LS S1 S2. unfold fam_upd. destruct (Z.testbit op 4); [|auto].
  change (upd_bytes S 15 [Z_to_bv 8 ((op / 32) mod 4)]) with (upd S 15 [Z_to_bv 8 ((op / 32) mod 4)]).
  unfold sighting_S1, sighting_S2, s_role, s_hd, s_din, s_dout, s32_at, u_at in *.
  rewrite !sub_upd_out by (cbn [length]; lia).
  split; [rewrite uslot_observe.length_upd by (cbn [length]; lia); exact LS | split; assumption].
Qed.

Definition r1921_post (ra sp gp tp s2 s3 s8 s10 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (X lo rem op : Z) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s7' s11' t3' t4' t5' t6' : word)
                    (m' : word -> option byte) (tgt : Z) (S' G' Lb' : list byte) (j208' j232' : word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 (Z_to_bv 64 rem) s5' s6' s7' s8 (Z_to_bv 64 op) s10 s11' t3' t4' t5' t6')
             F (Z_to_bv 64 tgt) fc None m' (seg_rom rsegs) /\
    munch [(lo, X); (X + 208, X + 216); (X + 232, X + 240); (X + 268, X + 544); (X + 1056, X + 1080)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X /\
    rw_cells rsegs m' (X + 208) [C8 j208'] /\ rw_cells rsegs m' (X + 232) [C8 j232'] /\
    rw_cells rsegs m' (X + 268) [CB 12 Lb'] /\ rw_cells rsegs m' (X + 280) [CB 264 G'] /\ gate_ok G' /\
    rw_cells rsegs m' (X + 1056) [CB 24 S'] /\
    (tgt = R27 \/ (tgt = R22 /\ length S' = 24%nat /\ sighting_S1 S' /\ sighting_S2 S' /\
                   j208' = Z_to_bv 64 op /\ j232' = Z_to_bv 64 rem)).

Lemma uslot_R19_cont : check_sighting_contract -> reac_disco_gate_should_push_contract -> bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X lo f len rem now r : Z) (ob : byte)
    (FB U S G Lb : list byte) (j208 j232 : word),
  sp = Z_to_bv 64 X -> a0 = Z_to_bv 64 r -> s3 = Z_to_bv 64 len -> s4 = Z_to_bv 64 rem ->
  s0 = sxb ob -> s9 = Z_to_bv 64 (bv_unsigned ob) ->
  0 < X -> X mod 16 = 0 -> X + 2624 < 2 ^ 63 -> 0 < f -> f + len <= lo -> 0 <= len < 2 ^ 16 ->
  0 <= now < 2 ^ 64 -> 0 <= rem < 2 ^ 64 ->
  (r = -1 \/ (r = 0 /\ sighting_facts S FB U len 0 /\ length S = 24%nat /\ sighting_S1 S /\ sighting_S2 S)) ->
  length FB = 50%nat -> (50 <= len -> bytes_at rsegs m f FB) ->
  length U = 6%nat -> bytes_at rsegs m (X + 946) U ->
  rw_cells rsegs m (X + 208) [C8 j208] -> rw_cells rsegs m (X + 224) [C8 (Z_to_bv 64 now)] ->
  rw_cells rsegs m (X + 232) [C8 j232] -> rw_cells rsegs m (X + 248) [C8 (Z_to_bv 64 f)] ->
  rw_cells rsegs m (X + 256) [C8 (Z_to_bv 64 (nt (X + 280)))] ->
  rw_cells rsegs m (X + 268) [CB 12 Lb] -> rw_cells rsegs m (X + 280) [CB 264 G] -> gate_ok G ->
  rw_cells rsegs m (X + 1056) [CB 24 S] ->
  mem_inv rsegs m -> stk rsegs m lo X -> lo + REAC_DISCO_GATE_SHOULD_PUSH_K <= X ->
  evt rsegs (r1921_post ra sp gp tp s2 s3 s8 s10 F fc m X lo rem (bv_unsigned ob))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R19R) fc None m (seg_rom rsegs)).
Proof.
  intros CSC GSC BC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X lo f len rem now r ob FB U S G Lb j208 j232 Esp Ea0 Es3 Es4 Es0 Es9
    HX0 HX16 HX1 Hf0 Hflo Hlen Hnow Hrem RC LFB HFB LU HU R208 R224 R232 R248 R256 RL RG GOK RS MI ST HLO.
  subst sp a0 s3 s4 s0 s9. unfold r1921_post.
  pose proof (munch_refl [(lo, X); (X + 208, X + 216); (X + 232, X + 240); (X + 268, X + 544); (X + 1056, X + 1080)] m)
    as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct RC as [-> | (-> & SF & LS & S1 & S2)].
  - eapply evt_mono; [apply uslot_R19_out; reflexivity|].
    intros ms' (a1' & a2' & ->).
    do 22 eexists. exists m, R27, S, G, Lb, j208, j232. split; [reflexivity|].
    repeat (split; [eassumption|]). left; reflexivity.
  - pose proof SF as SF'. destruct SF' as (L50 & _).
    specialize (HFB L50).
    eapply evt_cut.
    { eapply (uslot_R19_sight CSC GSC) with (lo := lo) (f := f) (now := now) (FB := FB) (U := U) (S := S) (G := G);
        try reflexivity; try eassumption; lia. }
    intros ms' (ra1 & t0a & t1a & t2a & a0a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m2 &
                Eq & MUc & WMc & MI2 & ST2 & R208' & R232' & RG2 & GOK2 & RS2).
    subst ms'.
    transport_after_call rsegs m m2 MUc WMc. clear MUc WMc MI.
    eapply evt_cut.
    { eapply (uslot_R20 BC) with (G := fst (gate_model G S now)); try reflexivity; try eassumption; lia. }
    intros ms' (ra2 & t0b & t1b & t2b & s1b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & s4b & s6b & s7b & s9b &
                s11b & t3b & t4b & t5b & t6b & m3 & Eq & MUc & WMc & MI3).
    subst ms'.
    transport_after_call rsegs m2 m3 MUc WMc. clear MUc WMc MI2.
    eapply evt_cut.
    { eapply uslot_R21 with (ob := ob) (S := S); try reflexivity; try eassumption; lia. }
    intros ms' (a0c & s0c & m4 & Eq & MUc & WMc & MI4 & RS4).
    subst ms'.
    transport_after_call rsegs m3 m4 MUc WMc. clear MUc WMc MI3.
    pose proof (gm_push G S now) as HP. pose proof (byte_range ob) as Hob.
    eapply evt_mono.
    { eapply uslot_R21_tail with (rem := rem) (push := snd (gate_model G S now)) (op := bv_unsigned ob);
        try reflexivity; try eassumption; lia. }
    intros ms' (a0d & ->).
    destruct (fam_ok (bv_unsigned ob) S LS S1 S2) as (LS' & S1' & S2').
    do 22 eexists. exists m4. eexists. exists (fam_upd (bv_unsigned ob) S), (fst (gate_model G S now)), Lb.
    do 2 eexists. split; [reflexivity|].
    repeat (split; [eassumption|]).
    destruct ((snd (gate_model G S now) =? 0) && negb (Z.testbit (bv_unsigned ob) 2)); [left; reflexivity|].
    right. split; [reflexivity|]. repeat (split; [eassumption|]). split; reflexivity.
Qed.

Lemma uslot_R19_R21 : reac_disco_classify_contract -> reac_disco_classify_on_segment_contract ->
  check_sighting_contract -> reac_disco_gate_should_push_contract -> bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X lo f len rem now k : Z) (ob : byte)
    (Rb U OB G Lb : list byte) (j208 j232 : word),
  sp = Z_to_bv 64 X -> s7 = Z_to_bv 64 f -> s3 = Z_to_bv 64 len -> s4 = Z_to_bv 64 rem ->
  s0 = sxb ob -> s9 = Z_to_bv 64 (bv_unsigned ob) ->
  0 < X -> X mod 16 = 0 -> X + 2624 < 2 ^ 63 -> 0 < f -> f + len <= lo -> 0 <= len < 2 ^ 16 ->
  0 <= now < 2 ^ 64 -> 0 <= rem < 2 ^ 64 -> k = 0 \/ k = 1 ->
  rw_cells rsegs m f [CB (Z.to_nat len) Rb] ->
  length U = 6%nat -> bytes_at rsegs m (X + 946) U ->
  rw_cells rsegs m (X + 208) [C8 j208] -> rw_cells rsegs m (X + 224) [C8 (Z_to_bv 64 now)] ->
  rw_cells rsegs m (X + 232) [C8 j232] -> rw_cells rsegs m (X + 248) [C8 (Z_to_bv 64 f)] ->
  rw_cells rsegs m (X + 256) [C8 (Z_to_bv 64 (nt (X + 280)))] ->
  rw_cells rsegs m (X + 268) [CB 12 Lb] -> rw_cells rsegs m (X + 280) [CB 264 G] -> gate_ok G ->
  rw_cells rsegs m (X + 1056) [CB 24 OB] ->
  mem_inv rsegs m -> stk rsegs m lo X -> lo + CLASSIFY_CORE_K <= X ->
  evt rsegs (r1921_post ra sp gp tp s2 s3 s8 s10 F fc m X lo rem (bv_unsigned ob))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (r17_exit k)) fc None m (seg_rom rsegs)).
Proof.
  intros CC0 CC1 CSC GSC BC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X lo f len rem now k ob Rb U OB G Lb j208 j232 Esp Es7 Es3 Es4 Es0 Es9
    HX0 HX16 HX1 Hf0 Hflo Hlen Hnow Hrem Hk RF LU HU R208 R224 R232 R248 R256 RL RG GOK RS MI ST HLO.
  apply rwc_split in RF. destruct RF as (LRb & HR & WR).
  assert (LR : Z.of_nat (length Rb) = len) by (rewrite LRb; lia).
  clear WR LRb.
  assert (CONT : forall L r S Lb2 (m2 : word -> option byte) (ra2 t0a t1a t2a a1a a2a a3a a4a a5a a6a a7a t3a t4a t5a t6a : word),
    munch [(lo, X); (X + 268, X + 280); (X + 1056, X + 1080)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
    stk rsegs m2 lo X ->
    r = cm_ret (fb50 Rb) len U L -> S = cm_out (fb50 Rb) len U L OB ->
    rw_cells rsegs m2 (X + 1056) [CB 24 S] -> rw_cells rsegs m2 (X + 268) [CB 12 Lb2] ->
    evt rsegs (r1921_post ra sp gp tp s2 s3 s8 s10 F fc m X lo rem (bv_unsigned ob))
      (MS (mkR ra2 sp gp tp t0a t1a t2a s0 s1 (Z_to_bv 64 r) a1a a2a a3a a4a a5a a6a a7a
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3a t4a t5a t6a)
          F (Z_to_bv 64 R19R) fc None m2 (seg_rom rsegs))).
  { intros L r S Lb2 m2 ra2 t0a t1a t2a a1a a2a a3a a4a a5a a6a a7a t3a t4a t5a t6a MU2 WM2 MI2 ST2 Er ES RS2 RL2.
    pose proof (munch_refl [(lo, X); (X + 268, X + 280); (X + 1056, X + 1080)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    subst sp s7 s3 s4 s0 s9.
    assert (HR2 : bytes_at rsegs m2 f Rb)
      by (eapply bytes_at_transport; [exact HR | exact MU2 | cbn [disjoint_from]; repeat split; try exact I;
          unfold CLASSIFY_CORE_K in HLO; lia]).
    transport_after_call rsegs m m2 MU2 WM2. clear MU2 WM2 MI.
    eapply evt_mono.
    { eapply (uslot_R19_cont CSC GSC BC) with (lo := lo) (f := f) (FB := fb50 Rb) (U := U) (S := S) (G := G) (Lb := Lb2)
        (r := r) (ob := ob) (now := now); try reflexivity; try eassumption; try (unfold REAC_DISCO_GATE_SHOULD_PUSH_K; unfold CLASSIFY_CORE_K in HLO; lia); try lia.
      - destruct (sc_cm_ret_cases (fb50 Rb) len U L) as [E|E]; rewrite <- Er in E; [left; exact E|].
        right. split; [exact E|].
        rewrite Er in E. destruct (sc_sight (fb50 Rb) len U L (fb50_len Rb) E) as (SF & LS & S1 & S2).
        destruct (sc_cm_ret0 (fb50 Rb) len U L OB E) as (_ & _ & _ & EO). rewrite ES, EO.
        split; [exact SF|]. split; [exact LS|]. split; [exact S1 | exact S2].
      - apply fb50_len.
      - intros H50. apply fb50_at; [exact HR2 | lia]. }
    intros ms' (ra' & t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s5' & s6' & s7' & s11' &
                t3' & t4' & t5' & t6' & m' & tgt & S' & G' & Lb' & j208' & j232' & Eq & MU' & WM' & PO).
    do 22 eexists. exists m', tgt, S', G', Lb', j208', j232'. split; [exact Eq|].
    split; [eapply munch_trans; [|exact MU']; eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [eapply wmono_trans; [exact WM | exact WM']|]. exact PO. }
  destruct Hk as [-> | ->]; unfold r17_exit; cbn [Z.eqb Pos.eqb].
  - eapply evt_cut.
    { eapply (uslot_R19_cls0 CC0) with (lo := lo) (f := f) (len := len) (Rb := Rb) (U := U) (OB := OB) (Lb := Lb);
        try eassumption; lia. }
    intros ms' (ra2 & t0a & t1a & t2a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m2 &
                Eq & MU2 & WM2 & MI2 & ST2 & RS2 & Lb2 & RL2).
    subst ms'.
    eapply (CONT None (cm_ret (fb50 Rb) len U None) (cm_out (fb50 Rb) len U None OB) Lb2 m2);
      try eassumption; reflexivity.
  - eapply evt_cut.
    { eapply (uslot_R19_cls1 CC1) with (lo := lo) (f := f) (len := len) (Rb := Rb) (U := U) (OB := OB) (Lb := Lb);
        try eassumption; lia. }
    intros ms' (ra2 & t0a & t1a & t2a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m2 &
                Eq & MU2 & WM2 & MI2 & ST2 & RS2 & Lb2 & RL2).
    subst ms'.
    eapply (CONT (Some Lb) (cm_ret (fb50 Rb) len U (Some Lb)) (cm_out (fb50 Rb) len U (Some Lb) OB) Lb2 m2);
      try eassumption; reflexivity.
Qed.
