From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib slot_ser_defs slot_ser_pure.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import printf_facts_c snprintf_c snprintf_stk_c jtok_is_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_table disco_json_text reac_disco_table_json_c tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model disco_json_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_tokb slot_ser_Pq slot_ser slot_ser_J1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_P1 slot_ser_P2 slot_ser_P3.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Lemma model_seg : reac_box_name_contract -> snprintf_stk_contract -> jtok_is_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F0 F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (canary : word)
    (X lo buf now count i0 p k kk : Z) (T : list byte) (os : list jobj) (vpad : list byte)
    (Q : machine_state -> Prop),
  p3ctx X lo buf now count T os vpad -> 0 <= k < count ->
  sp = Z_to_bv 64 X -> s4 = Z_to_bv 64 (X + 1024 + 144 * k) -> s7 = Z_to_bv 64 (X + 512 + 48 * k) ->
  pinv X lo buf now i0 p T os vpad canary m0 kk m -> MemNorm.task_mem rsegs m -> frm0 fc -> fl F0 F ->
  (forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
          (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y28 y29 y30 y31 : word),
     pinv X lo buf now i0 p T os vpad canary m0 kk m' -> MemNorm.task_mem rsegs m' -> frm0 fc' -> fl F0 F' ->
     evt rsegs Q (MS (mkR y1 sp gp tp y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17
                         s2 s3 s4 y21 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F' (Z_to_bv 64 0x14294) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x141f4) fc None m (seg_rom rsegs)).
Proof.
  intros BNC SNK JT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F0 F fc m0 m canary X lo buf now count i0 p k kk T os vpad Q CX Hk Esp Es4 Es7 PI TM FC FL K.
  destruct (p3_count X lo buf now count T os vpad CX) as (Ec & Hc & Los & L6 & IB & G33 & L969).
  pose proof CX as (HX0 & HX16 & HX1 & Hnow & Hb & LT & TOK & LV & JR & Hbl & HLO & HI).
  unfold SNPRINTF_K, IMG_END in HLO, HI.
  pose proof PI as (HT & _ & _ & _ & _ & C3 & _ & S2 & _ & _ & _ & _ & _ & MI & ST & _ & _).
  pose proof (rd_sub m (X + 512) T (48 * k + 12) 1 HT ltac:(lia) ltac:(rewrite LT; lia)) as R12.
  destruct (stk_rw m (X + 920) (X + 992) (X + 944) 8 S2 ltac:(lia) ltac:(lia)) as [jw CW].
  pose proof (munch_refl [(X + 944, X + 952)] m) as MUs. pose proof (wmono_refl rsegs m) as WMs.
  clear HT S2.
  subst sp s4 s7.
  step. rewrite lbu_val by (apply length_sub; rewrite ?LT; lia).
  change (bytes_le_to_Z (sub T (48 * k + 12) 1)) with (hd_of T k).
  step. step. step. step. step.
  pose proof (stk_of_rw_cells rsegs m1 (X + 944) _ CW) as SW. cbn [cells_size csize Nat.add] in SW.
  pose proof PI as (_ & _ & _ & _ & _ & _ & _ & S2m & _).
  pose proof (task_stk [(X + 944, X + 952)] m m1 (X + 920) (X + 992) TM MUs S2m
                ltac:(intros x _ O; cbn [outside] in O; intuition lia)) as TM1.
  assert (PI1 : pinv X lo buf now i0 p T os vpad canary m0 kk m1).
  { eapply pinv_tr; [exact LT | exact (objs_len_le buf vpad os count LV L6 Los Hc) | exact Hb | exact Hbl
      | unfold IMG_END; lia | lia | exact PI | exact MUs | exact WMs | exact MI | exact ST | sub_tac | rd_tac SW]. }
  assert (BW : bytes_at rsegs m1 (X + 944) (pf_bytes s_0x0 ++ Z_to_bv 8 0 :: skipn 4 jw)).
  { pose proof CW as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r, s0x0_bytes, <- app_assoc in B.
    exact B. }
  pose proof CW as CW2. apply (rw_cells_app m1 (X + 944) [C4 _] [CB 4 _]) in CW2 as [_ CW2].
  apply ser_cb in CW2 as (LS0 & _ & _).
  clear PI TM MUs WMs S2m SW R12.
  pose proof (u1_range T (48 * k + 12)) as Rhd. change (u_at T (48 * k + 12) 1) with (hd_of T k) in Rhd.
  rewrite eqb_lit by lia.
  pose proof TOK as (_ & _ & _ & T4). destruct (T4 k ltac:(lia)) as ([H0|H1] & _ & _).
  - rewrite H0. cbv iota.
    pose proof (nm_unknown m1 MI) as NU. unfold nm_at in NU.
    destruct (p3_obj X lo buf now count T os vpad k CX Hk) as (_ & _ & J2 & J3 & _).
    rewrite (model_hd0 T k H0) in J2, J3. cbn [fst snd] in J2, J3.
    eapply (mw_calls JT) with (MA := 0x1031b) (mt := s_unknown) (wt := s_0x0)
      (sl1 := img8 (0x1031b + Z.of_nat (length s_unknown) + 1)) (sl2 := skipn 4 jw) (kk := kk) (k := k)
      (X := X) (lo := lo) (buf := buf) (now := now) (count := count) (T := T) (os := os) (vpad := vpad) (m0 := m0)
      (canary := canary) (i0 := i0) (p := p);
      [ first [ exact CX | exact J2 | exact J3 | exact NU | exact BW | exact PI1 | exact TM1 | reflexivity
              | (unfold s_unknown, s_0x0; repeat (apply Forall_cons; [lia|]); apply Forall_nil)
              | (rewrite img8_len; mod8) | (rewrite LS0; unfold s_0x0; cbn [length]; lia)
              | (left; rewrite img8_len; unfold s_unknown; cbn [length]; lia) | lia ] .. |].
    intros m4 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 PI4 TM4.
    eapply K; [exact PI4 | exact TM4 | exact FC | exact FL].
  - rewrite H1. cbv iota.
    eapply (bn_seg BNC SNK JT) with (sl0 := skipn 4 jw) (kk := kk) (k := k)
      (X := X) (lo := lo) (buf := buf) (now := now) (count := count) (T := T) (os := os) (vpad := vpad) (m0 := m0)
      (canary := canary) (i0 := i0) (p := p) (F0 := F0);
      [ first [ exact CX | exact H1 | exact BW | exact LS0 | exact PI1 | exact TM1 | exact FC | exact FL
              | reflexivity | lia ] .. |].
    exact K.
Qed.

Lemma ld8_val : forall bs, length bs = 8%nat -> bv_extract 0 64 (le_bytes_to_word bs) = Z_to_bv 64 (bytes_le_to_Z bs).
Proof.
  intros bs L. apply bv_eq. rewrite extract_low_mod by lia. unfold le_bytes_to_word.
  pose proof (ble_range bs) as H. rewrite L in H. change (8 * Z.of_nat 8) with 64 in H.
  rewrite !unsigned_lit by lia. change (Z.of_N 64) with 64. apply Z.mod_small. lia.
Qed.

Lemma age_range : forall now ls, 0 <= now < 2 ^ 64 -> 0 <= ls < 2 ^ 64 -> 0 <= age_of now ls < 10 ^ 14.
Proof.
  intros now ls Hn Hl. unfold age_of. destruct (ls <? now) eqn:E; [|lia].
  apply Z.ltb_lt in E. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma llu_text : forall u, printf_facts_c.pf_text [Pllu] [AU64 u] = Some (pf_udec u).
Proof. intros u. cbn. rewrite ?app_nil_r. reflexivity. Qed.

Definition llu_fmt : list Z := [37; 108; 108; 117].

Lemma llu_fmt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10422 (pf_bytes (llu_fmt ++ [0])).
Proof. intros m MI. apply ro_at; [exact MI | vm_compute; reflexivity | lia | apply Z.leb_le; vm_compute; reflexivity]. Qed.

Lemma owned_ok : forall e, Forall (fun c => 0 < c < 256) (owned_text e) /\ (length (owned_text e) <= 5)%nat.
Proof.
  intros e. unfold owned_text, s_true, s_false. destruct (e_owned e =? 0); cbn [length]; split;
    try lia; repeat (apply Forall_cons; [lia|]); apply Forall_nil.
Qed.

Lemma age_seg : snprintf_stk_contract -> jtok_is_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F0 F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (canary : word)
    (X lo buf now count i0 p k kk : Z) (T : list byte) (os : list jobj) (vpad : list byte)
    (Q : machine_state -> Prop),
  p3ctx X lo buf now count T os vpad -> 0 <= k < count ->
  sp = Z_to_bv 64 X -> s1 = Z_to_bv 64 count -> s4 = Z_to_bv 64 (X + 1024 + 144 * k) -> s6 = Z_to_bv 64 k ->
  a3 = Z_to_bv 64 (age_of now (last_of T k)) ->
  pinv X lo buf now i0 p T os vpad canary m0 kk m -> MemNorm.task_mem rsegs m -> frm0 fc -> fl F0 F ->
  (forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
          (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     pinv X lo buf now i0 p T os vpad canary m0 kk m' -> MemNorm.task_mem rsegs m' -> frm0 fc' -> fl F0 F' ->
     evt rsegs Q (MS (mkR y1 sp gp tp y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17
                         s2 s3 s4 s5 (Z_to_bv 64 (k + 1)) s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F' (Z_to_bv 64 (if k + 1 =? count then 0x14314 else 0x140f0)) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x142e4) fc None m (seg_rom rsegs)).
Proof.
  intros SNK JT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F0 F fc m0 m canary X lo buf now count i0 p k kk T os vpad Q CX Hk Esp Es1 Es4 Es6 Ea3 PI TM FC FL K.
  destruct (p3_count X lo buf now count T os vpad CX) as (Ec & Hc & Los & L6 & IB & G33 & L969).
  pose proof CX as (HX0 & HX16 & HX1 & Hnow & Hb & LT & TOK & LV & JR & Hbl & HLO & HI).
  unfold SNPRINTF_K, IMG_END in HLO, HI.
  pose proof PI as (_ & _ & _ & _ & _ & _ & _ & S2 & _ & _ & _ & G1 & G2 & MI & ST & _ & _).
  set (age := age_of now (last_of T k)) in *.
  pose proof (ser_u_at_bound T (48 * k + 40) 8) as Rls. change (u_at T (48 * k + 40) 8) with (last_of T k) in Rls.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Rls.
  pose proof (age_range now (last_of T k) Hnow Rls) as Ha. fold age in Ha.
  destruct (dec_spec age ltac:(lia)) as (_ & _ & _ & DL). pose proof (DL 14 ltac:(lia) ltac:(lia)) as Lq.
  rewrite dec_udec in Lq by lia. change (Z.to_nat 14) with 14%nat in Lq.
  destruct (stk_rw m (X + 920) (X + 992) (X + 920) 24 S2 ltac:(lia) ltac:(lia)) as [ja CA].
  subst sp s1 s4 s6 a3.
  step. step. step. step. step.
  eapply (sn_call SNK) with (lo := lo) (S := X) (D := X + 920) (n := 24) (A := 0x10422) (canary := canary)
    (fmt := llu_fmt) (ps := [Pllu]) (args := [AU64 age]) (q := pf_udec age) (junk := ja) (xs := []);
    [ first [ reflexivity | exact (llu_fmt_at m MI) | exact CA | assumption | exact (llu_text _)
            | (unfold RO_LO; lia) | (apply Z.leb_le; vm_compute; reflexivity) | (apply ba_nil; lia)
            | (cbn [length]; lia) | lia
            | (cbn [pf_args_ok pf_arg_ok app]; split; [rewrite unsigned_lit by lia; reflexivity | exact I]) ] .. |].
  intros m1 Ft fc1 w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 MU1 WM1 MI1 TM1 FC1 FK1 ST1 BY1.
  rewrite (ret_pc_even 0x142f8) by (first [lia | reflexivity]).
  rewrite firstn_all2 in MU1, BY1 by lia.
  assert (LBq : Z.of_nat (length (pf_bytes (pf_udec age ++ [0]))) = Z.of_nat (length (pf_udec age)) + 1)
    by (rewrite length_pf_bytes, length_app; cbn [length]; lia).
  assert (PI1 : pinv X lo buf now i0 p T os vpad canary m0 kk m1).
  { eapply pinv_tr; [exact LT | exact (objs_len_le buf vpad os count LV L6 Los Hc) | exact Hb | exact Hbl
      | unfold IMG_END; lia | lia | exact PI | exact MU1 | exact WM1 | exact MI1 | exact ST1 | sub_tac | rdb_tac BY1]. }
  pose proof PI1 as (_ & _ & _ & _ & _ & _ & _ & S21 & _).
  destruct (stk_rw m1 (X + 920) (X + 992) (X + 920 + Z.of_nat (length (pf_udec age)) + 1) 8 S21 ltac:(lia) ltac:(lia))
    as [sl CS]. apply ser_cb in CS as (LS & BS & _).
  assert (BA : bytes_at rsegs m1 (X + 920) (pf_bytes (pf_udec age) ++ Z_to_bv 8 0 :: sl)).
  { replace (pf_bytes (pf_udec age) ++ Z_to_bv 8 0 :: sl) with (pf_bytes (pf_udec age ++ [0]) ++ sl)
      by (unfold pf_bytes; rewrite map_app, <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BY1|]. rewrite LBq. replace (X + 920 + (Z.of_nat (length (pf_udec age)) + 1))
      with (X + 920 + Z.of_nat (length (pf_udec age)) + 1) by lia. exact BS. }
  destruct (p3_obj X lo buf now count T os vpad k CX Hk) as (_ & _ & _ & _ & _ & J5).
  change (e_last_seen (tj_entry T k)) with (last_of T k) in J5. fold age in J5. rewrite dec_udec in J5 by lia.
  step. step. step. step.
  eapply (jt_true JT) with (k := k) (kk := kk) (s := 5%nat) (kind := 2) (TA := X + 920) (R := 0x14308)
    (text := pf_udec age) (slack := sl);
    [ first [ exact CX | exact J5 | exact BA | exact PI1 | exact TM1 | reflexivity | (f_equal; lia)
            | (rewrite <- dec_udec by lia; apply dec_ok; lia) | (rewrite LS; mod8) | (right; lia) | lia ] .. |].
  intros m2 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 MU2 PI2 TM2.
  step. if_lit. step. step.
  rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (k + 1) count) as [E|E]; cbn [negb]; cbv iota.
  - eapply K; [exact PI2 | exact TM2 | exact FC1 | exact (fl_trans F0 F Ft FL FK1)].
  - eapply K; [exact PI2 | exact TM2 | exact FC1 | exact (fl_trans F0 F Ft FL FK1)].
Qed.

Lemma own_seg : snprintf_stk_contract -> jtok_is_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F0 F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (canary : word)
    (X lo buf now count i0 p k kk TA : Z) (T : list byte) (os : list jobj) (vpad : list byte)
    (Q : machine_state -> Prop),
  p3ctx X lo buf now count T os vpad -> 0 <= k < count ->
  sp = Z_to_bv 64 X -> s1 = Z_to_bv 64 count -> s4 = Z_to_bv 64 (X + 1024 + 144 * k) -> s6 = Z_to_bv 64 k ->
  s7 = Z_to_bv 64 (X + 512 + 48 * k) -> s11 = Z_to_bv 64 now -> a2 = Z_to_bv 64 TA ->
  nm_at m TA (owned_text (tj_entry T k)) -> 0 <= TA -> TA + 16 <= 0x20000 ->
  pinv X lo buf now i0 p T os vpad canary m0 kk m -> MemNorm.task_mem rsegs m -> frm0 fc -> fl F0 F ->
  (forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
          (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     pinv X lo buf now i0 p T os vpad canary m0 kk m' -> MemNorm.task_mem rsegs m' -> frm0 fc' -> fl F0 F' ->
     evt rsegs Q (MS (mkR y1 sp gp tp y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17
                         s2 s3 s4 s5 (Z_to_bv 64 (k + 1)) s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F' (Z_to_bv 64 (if k + 1 =? count then 0x14314 else 0x140f0)) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x142b0) fc None m (seg_rom rsegs)).
Proof.
  intros SNK JT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F0 F fc m0 m canary X lo buf now count i0 p k kk TA T os vpad Q CX Hk Esp Es1 Es4 Es6 Es7 Es11 Ea2 N HT0 HT1
    PI TM FC FL K.
  destruct (p3_count X lo buf now count T os vpad CX) as (Ec & Hc & _).
  pose proof CX as (HX0 & HX16 & HX1 & Hnow & Hb & LT & TOK & LV & JR & Hbl & HLO & HI).
  unfold SNPRINTF_K, IMG_END in HLO, HI. unfold nm_at in N.
  destruct (p3_obj X lo buf now count T os vpad k CX Hk) as (_ & _ & _ & _ & J4 & _).
  destruct (owned_ok (tj_entry T k)) as [FO LO].
  subst sp s1 s4 s6 s7 s11 a2.
  step. step. step.
  eapply (jt_true JT) with (k := k) (kk := kk) (s := 4%nat) (kind := 3) (TA := TA) (R := 0x142bc)
    (text := owned_text (tj_entry T k)) (slack := img8 (TA + Z.of_nat (length (owned_text (tj_entry T k))) + 1));
    [ first [ exact CX | exact J4 | exact N | exact PI | exact TM | exact FO | reflexivity | (f_equal; lia)
            | (rewrite img8_len; mod8) | (left; rewrite img8_len; lia) | lia ] .. |].
  intros m1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 MU1 PI1 TM1.
  step. if_lit.
  pose proof PI1 as (HTm & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI1 & _).
  pose proof (rd_sub m1 (X + 512) T (48 * k + 40) 8 HTm ltac:(lia) ltac:(rewrite LT; lia)) as R40.
  pose proof (ser_u_at_bound T (48 * k + 40) 8) as Rls. change (u_at T (48 * k + 40) 8) with (last_of T k) in Rls.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Rls.
  step. rewrite ld8_val by (apply length_sub; rewrite ?LT; lia).
  change (bytes_le_to_Z (sub T (48 * k + 40) 8)) with (last_of T k).
  step. rewrite ltu_lit by lia.
  destruct (Z.ltb_spec (last_of T k) now) as [L|L]; cbn [negb]; cbv iota.
  - step. step. step. step. step.
    rewrite (unsigned_lit now), (unsigned_lit (last_of T k)) by lia.
    rewrite (unsigned_lit (now - last_of T k)) by lia.
    change 4835703278458516699 with KDv. rewrite tj_quot_mach by lia.
    step.
    eapply (age_seg SNK JT) with (k := k) (kk := kk) (X := X) (lo := lo) (buf := buf) (now := now) (count := count)
      (T := T) (os := os) (vpad := vpad) (m0 := m0) (canary := canary) (i0 := i0) (p := p) (F0 := F0);
      [ first [ exact CX | exact PI1 | exact TM1 | exact FC | exact FL | reflexivity | lia
              | (unfold age_of; replace (last_of T k <? now) with true by (symmetry; apply Z.ltb_lt; lia);
                 reflexivity) ] .. |].
    exact K.
  - step.
    eapply (age_seg SNK JT) with (k := k) (kk := kk) (X := X) (lo := lo) (buf := buf) (now := now) (count := count)
      (T := T) (os := os) (vpad := vpad) (m0 := m0) (canary := canary) (i0 := i0) (p := p) (F0 := F0);
      [ first [ exact CX | exact PI1 | exact TM1 | exact FC | exact FL | reflexivity | lia
              | (unfold age_of; replace (last_of T k <? now) with false by (symmetry; apply Z.ltb_ge; lia);
                 reflexivity) ] .. |].
    exact K.
Qed.

Lemma tail_seg : snprintf_stk_contract -> jtok_is_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F0 F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (canary : word)
    (X lo buf now count i0 p k kk : Z) (T : list byte) (os : list jobj) (vpad : list byte)
    (Q : machine_state -> Prop),
  p3ctx X lo buf now count T os vpad -> 0 <= k < count ->
  sp = Z_to_bv 64 X -> s1 = Z_to_bv 64 count -> s4 = Z_to_bv 64 (X + 1024 + 144 * k) -> s6 = Z_to_bv 64 k ->
  s7 = Z_to_bv 64 (X + 512 + 48 * k) -> s11 = Z_to_bv 64 now ->
  pinv X lo buf now i0 p T os vpad canary m0 kk m -> MemNorm.task_mem rsegs m -> frm0 fc -> fl F0 F ->
  (forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
          (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     pinv X lo buf now i0 p T os vpad canary m0 kk m' -> MemNorm.task_mem rsegs m' -> frm0 fc' -> fl F0 F' ->
     evt rsegs Q (MS (mkR y1 sp gp tp y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17
                         s2 s3 s4 s5 (Z_to_bv 64 (k + 1)) s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F' (Z_to_bv 64 (if k + 1 =? count then 0x14314 else 0x140f0)) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14294) fc None m (seg_rom rsegs)).
Proof.
  intros SNK JT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F0 F fc m0 m canary X lo buf now count i0 p k kk T os vpad Q CX Hk Esp Es1 Es4 Es6 Es7 Es11 PI TM FC FL K.
  destruct (p3_count X lo buf now count T os vpad CX) as (Ec & Hc & _).
  pose proof CX as (HX0 & HX16 & HX1 & Hnow & Hb & LT & TOK & LV & JR & Hbl & HLO & HI).
  pose proof PI as (HT & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _).
  pose proof (rd_sub m (X + 512) T (48 * k + 24) 4 HT ltac:(lia) ltac:(rewrite LT; lia)) as R24.
  subst sp s1 s4 s6 s7 s11.
  step. rewrite lw_val by (apply length_sub; rewrite ?LT; lia).
  change (bv_swrap 32 (bytes_le_to_Z (sub T (48 * k + 24) 4))) with (owned_of T k).
  step. pose proof TOK as (_ & _ & _ & T4). destruct (T4 k ltac:(lia)) as (_ & _ & [O0|O1]).
  - rewrite O0. if_lit. step. step.
    eapply (own_seg SNK JT) with (k := k) (kk := kk) (X := X) (lo := lo) (buf := buf) (now := now) (count := count)
      (T := T) (os := os) (vpad := vpad) (m0 := m0) (canary := canary) (i0 := i0) (p := p) (F0 := F0) (TA := 0x10298);
      [ first [ exact CX | exact PI | exact TM | exact FC | exact FL | reflexivity | lia
              | (unfold owned_text; change (e_owned (tj_entry T k)) with (owned_of T k); rewrite O0;
                 exact (nm_false m MI)) ] .. |].
    exact K.
  - rewrite O1. if_lit. step. step. step.
    eapply (own_seg SNK JT) with (k := k) (kk := kk) (X := X) (lo := lo) (buf := buf) (now := now) (count := count)
      (T := T) (os := os) (vpad := vpad) (m0 := m0) (canary := canary) (i0 := i0) (p := p) (F0 := F0) (TA := 0x103aa);
      [ first [ exact CX | exact PI | exact TM | exact FC | exact FL | reflexivity | lia
              | (unfold owned_text; change (e_owned (tj_entry T k)) with (owned_of T k); rewrite O1;
                 exact (nm_true m MI)) ] .. |].
    exact K.
Qed.
