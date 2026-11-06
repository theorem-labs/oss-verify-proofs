From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib slot_ser_defs slot_ser_pure.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import printf_facts_c snprintf_c snprintf_stk_c jtok_is_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_table disco_json_text reac_disco_table_json_c tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model disco_json_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_tokb slot_ser_Pq slot_ser slot_ser_J1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Definition fl (F0 F : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get F0 k.

Definition p3ctx (X lo buf now count : Z) (T : list byte) (os : list jobj) (vpad : list byte) : Prop :=
  0 < X /\ X mod 16 = 0 /\ X + 2592 < 2 ^ 63 /\ 0 <= now < 2 ^ 64 /\ 0 < buf /\
  length T = 400%nat /\ disco_table_c.table_ok T /\ length vpad = 4%nat /\
  json_read (tj_text T now) 9 = Some (count, os) /\
  buf + Z.of_nat (length (tj_text T now)) + 1 <= lo /\ lo + SNPRINTF_K <= X /\ IMG_END <= lo.

Lemma tj_nth : forall T k, 0 <= k < n_of T -> nth_error (tj_entries T) (Z.to_nat k) = Some (tj_entry T k).
Proof.
  intros T k Hk. unfold tj_entries. rewrite nth_error_map.
  rewrite (nth_error_nth' (seq 0 (Z.to_nat (n_of T))) 0%nat) by (rewrite length_seq; lia).
  rewrite seq_nth by lia. cbn [option_map]. f_equal. f_equal. lia.
Qed.

Lemma p3_count : forall X lo buf now count T os vpad, p3ctx X lo buf now count T os vpad ->
  count = n_of T /\ 0 <= count <= 8 /\ length os = Z.to_nat count /\ Forall (fun o => length o = 6%nat) os /\
  Forall (Forall (tok_inb (tj_text T now))) os /\ Forall (fun c => 33 <= c <= 255) (tj_text T now) /\
  (length (tj_text T now) <= 969)%nat.
Proof.
  intros X lo buf now count T os vpad (HX0 & HX16 & HX1 & Hnow & Hb & LT & TOK & LV & JR & Hbl & HLO & HI).
  pose proof (ser_tj_ok T LT TOK) as [TOK' WF].
  destruct (F1_2_json_read_table box_tok (tj_entries T) now ser_tok_ok TOK' WF Hnow) as (os' & JR' & F2).
  change (table_json_text box_tok (tj_entries T) now) with (tj_text T now) in JR'.
  rewrite JR in JR'. injection JR' as Ec Eo. subst os'.
  pose proof (ser_tj_len T) as LE. pose proof TOK as (T1 & _). unfold tbl_T1 in T1.
  pose proof (Forall2_length F2) as LF.
  split; [rewrite Ec, LE; lia|]. split; [rewrite Ec; destruct TOK' as (TL & _); lia|].
  split; [rewrite <- LF, Ec; lia|]. split.
  { clear -F2. induction F2 as [|e o E O V F IH]; constructor; [|exact IH].
    apply (f_equal (@length _)) in V. unfold obj_view in V. rewrite length_map in V. exact V. }
  split; [exact (json_read_inb _ _ _ _ JR)|]. split.
  { exact (ser_text_g33 box_tok (tj_entries T) now ser_tok_ok WF Hnow). }
  exact (C7_text_bound box_tok (tj_entries T) now ser_tok_ok TOK' WF Hnow).
Qed.

Lemma p3_obj : forall X lo buf now count T os vpad k, p3ctx X lo buf now count T os vpad -> 0 <= k < count ->
  (forall j, 0 <= j < count ->
     jtok_is (tj_text T now) (nth 0 (nth (Z.to_nat k) os []) tok_none) 1 (mac_text (e_mac (tj_entry T j))) = (j =? k)) /\
  jtok_is (tj_text T now) (nth 1 (nth (Z.to_nat k) os []) tok_none) 1 (rolename (e_role (tj_entry T k))) = true /\
  jtok_is (tj_text T now) (nth 2 (nth (Z.to_nat k) os []) tok_none) 1 (fst (model_of box_tok (tj_entry T k))) = true /\
  jtok_is (tj_text T now) (nth 3 (nth (Z.to_nat k) os []) tok_none) 1 (snd (model_of box_tok (tj_entry T k))) = true /\
  jtok_is (tj_text T now) (nth 4 (nth (Z.to_nat k) os []) tok_none) 3 (owned_text (tj_entry T k)) = true /\
  jtok_is (tj_text T now) (nth 5 (nth (Z.to_nat k) os []) tok_none) 2
    (dec (age_of now (e_last_seen (tj_entry T k)))) = true.
Proof.
  intros X lo buf now count T os vpad k CX Hk.
  destruct (p3_count X lo buf now count T os vpad CX) as (Ec & Hc & Los & _).
  pose proof CX as (HX0 & HX16 & HX1 & Hnow & Hb & LT & TOK & LV & JR & Hbl & HLO & HI).
  pose proof (ser_tj_ok T LT TOK) as [TOK' WF].
  assert (JR' : json_read (table_json_text box_tok (tj_entries T) now) 9 = Some (Z.of_nat (length (tj_entries T)), os)).
  { rewrite ser_tj_len, Z2Nat.id by lia. rewrite <- Ec. exact JR. }
  assert (Eo : nth_error os (Z.to_nat k) = Some (nth (Z.to_nat k) os [])) by (apply nth_error_nth'; lia).
  pose proof (tj_nth T k ltac:(lia)) as Ek.
  destruct (F1_3_serialise_finds box_tok (tj_entries T) now os ser_tok_ok TOK' WF Hnow JR' (Z.to_nat k) _ _ Eo Ek)
    as (M & R & Mo & W & O & A).
  split; [|exact (conj R (conj Mo (conj W (conj O A))))].
  intros j Hj. specialize (M (Z.to_nat j) (tj_entry T j) (tj_nth T j ltac:(lia))).
  destruct (Z.eqb_spec j k) as [->|N]; [apply M; reflexivity|].
  apply not_true_is_false. intros E. apply M in E. lia.
Qed.

Lemma jt_kind : forall B t kind text, jtok_is B t kind text = true -> tv_kind t = kind.
Proof.
  intros B t kind text H. unfold jtok_is in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  apply Z.eqb_eq. exact H.
Qed.

Lemma stk_rw : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists j, rw_cells rsegs m a [CB n j].
Proof.
  intros m lo hi a n S Ha Hn. destruct (stk_split rsegs m lo a hi S ltac:(lia)) as [_ S2].
  destruct (stk_split rsegs m a (a + Z.of_nat n) hi S2 ltac:(lia)) as [S3 _]. exact (stk_cb m a n S3).
Qed.

Lemma fl_trans : forall F0 F F', fl F0 F -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) ->
  fl F0 F'.
Proof. intros F0 F F' H1 H2 k Hk. rewrite H2 by exact Hk. apply H1. exact Hk. Qed.

Lemma task_stk : forall W m m' lo hi, MemNorm.task_mem rsegs m -> munch W m m' -> stk rsegs m lo hi ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> lo <= x < hi) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' lo hi TM MU S H. eapply task_of; [exact TM | exact MU |].
  intros x Hx O. eapply tsk_of_stk; [exact TM | exact S | apply H; assumption].
Qed.

Lemma mac_fmt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x103c8 (pf_bytes (mac_fmt ++ [0])).
Proof.
  intros m MI. apply ro_at; [exact MI | vm_compute; reflexivity | lia | apply Z.leb_le; vm_compute; reflexivity].
Qed.

Lemma arg_u1 : forall m S lo D n T k,
  pf_arg_ok m S lo D n (Z_to_bv 64 (bytes_le_to_Z (sub T k 1))) (AInt (u_at T k 1)).
Proof.
  intros m S lo D n T k. pose proof (u1_range T k) as H. unfold u_at in *. cbn [pf_arg_ok].
  rewrite unsigned_lit by lia. split; [lia | reflexivity].
Qed.

Lemma objs_len_le : forall buf vpad os count, length vpad = 4%nat -> Forall (fun o => length o = 6%nat) os ->
  length os = Z.to_nat count -> 0 <= count <= 8 -> Z.of_nat (length (objs_bytes buf vpad os)) <= 1296.
Proof. intros buf vpad os count L H Lo Hc. rewrite objs_len by assumption. lia. Qed.

Lemma mac_bytes_ok : forall T j, Forall (fun c => 0 < c < 256) (mac_text (map bv_unsigned (mac_of T j))).
Proof.
  intros T j. eapply Forall_impl; [|apply g33_mac]; [intros c Hc; unfold g33 in Hc; lia|].
  apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (b & <- & _). unfold byte_ok.
  pose proof (byte_range b). lia.
Qed.

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let c' := eval vm_compute in c in
      replace c with c' by (vm_compute; reflexivity); cbv iota
  end.

Ltac sub_tac := intros x Hx; cbn [outside] in *; intuition lia.
Ltac rd0_tac := intros x Hx; left; cbn [outside]; intuition lia.
Ltac rd_split := intros x Hx; lazymatch goal with |- outside ?W _ \/ _ =>
  let O := fresh "O" in destruct (outside_dec W x) as [O|O]; [left; exact O|right]; cbn [outside] in O end.
Ltac rd_tac S := rd_split; let SH := fresh "SH" in destruct S as (_ & _ & SH);
  lazymatch goal with |- exists _, mrd _ _ (wa ?y) = Some _ => apply (proj2 (SH y ltac:(intuition lia))) end.
Ltac rdb_tac BY := rd_split; eapply bytes_at_mrd; [exact BY|]; intuition lia.

Lemma mac_call : snprintf_stk_contract -> jtok_is_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F0 F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (canary : word)
    (X lo buf now count i0 p k j : Z) (T : list byte) (os : list jobj) (vpad : list byte) (Q : machine_state -> Prop),
  p3ctx X lo buf now count T os vpad -> 0 <= j < count -> 0 <= k < count ->
  sp = Z_to_bv 64 X -> s4 = Z_to_bv 64 (X + 1024 + 144 * k) -> s10 = Z_to_bv 64 (X + 514 + 48 * j) ->
  pinv X lo buf now i0 p T os vpad canary m0 k m -> MemNorm.task_mem rsegs m -> frm0 fc -> fl F0 F ->
  (forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
          (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     pinv X lo buf now i0 p T os vpad canary m0 k m' -> MemNorm.task_mem rsegs m' -> frm0 fc' -> fl F0 F' ->
     evt rsegs Q (MS (mkR y1 sp gp tp y5 y6 y7 s0 s1 (Z_to_bv 64 (Z.b2z (j =? k))) y11 y12 y13 y14 y15 y16 y17
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F' (Z_to_bv 64 0x14160) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14118) fc None m (seg_rom rsegs)).
Proof.
  intros SNK JT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F0 F fc m0 m canary X lo buf now count i0 p k j T os vpad Q CX Hj Hk Esp Es4 Es10 PI TM FC FL K.
  destruct (p3_count X lo buf now count T os vpad CX) as (Ec & Hc & Los & L6 & IB & G33 & L969).
  pose proof CX as (HX0 & HX16 & HX1 & Hnow & Hb & LT & TOK & LV & JR & Hbl & HLO & HI).
  unfold SNPRINTF_K, IMG_END in HLO, HI.
  pose proof PI as (HT & _ & _ & _ & _ & _ & S1 & _ & _ & S3 & _ & _ & _ & MI & ST & _ & _).
  pose proof (rd_sub m (X + 512) T (48 * j + 0) 1 HT ltac:(lia) ltac:(rewrite LT; lia)) as R0.
  pose proof (rd_sub m (X + 512) T (48 * j + 1) 1 HT ltac:(lia) ltac:(rewrite LT; lia)) as R1.
  pose proof (rd_sub m (X + 512) T (48 * j + 2) 1 HT ltac:(lia) ltac:(rewrite LT; lia)) as R2.
  pose proof (rd_sub m (X + 512) T (48 * j + 3) 1 HT ltac:(lia) ltac:(rewrite LT; lia)) as R3.
  pose proof (rd_sub m (X + 512) T (48 * j + 4) 1 HT ltac:(lia) ltac:(rewrite LT; lia)) as R4.
  pose proof (rd_sub m (X + 512) T (48 * j + 5) 1 HT ltac:(lia) ltac:(rewrite LT; lia)) as R5.
  destruct (stk_rw m X (X + 16) X 16 S1 ltac:(lia) ltac:(lia)) as [jx CX0].
  pose proof (munch_refl [(X, X + 16)] m) as MUs. pose proof (wmono_refl rsegs m) as WMs.
  clear HT S1 S3.
  subst sp s4 s10.
  step. step. step. step. step. step.
  rewrite !lbu_val by (apply length_sub; rewrite ?LT; lia).
  step. step. step. step. step. step.
  pose proof (stk_of_rw_cells rsegs m1 X _ CX0) as SX. cbn [cells_size csize Nat.add] in SX.
  pose proof PI as (_ & _ & _ & _ & _ & _ & S1m & _).
  pose proof (task_stk [(X, X + 16)] m m1 X (X + 16) TM MUs S1m ltac:(intros x _ O; cbn [outside] in O; intuition lia))
    as TM1.
  assert (PI1 : pinv X lo buf now i0 p T os vpad canary m0 k m1).
  { eapply pinv_tr; [exact LT | exact (objs_len_le buf vpad os count LV L6 Los Hc) | exact Hb | exact Hbl
      | unfold IMG_END; lia | lia | exact PI | exact MUs | exact WMs | exact MI | exact ST | sub_tac | rd_tac SX]. }
  clear PI TM MUs WMs S1m SX R0 R1 R2 R3 R4 R5.
  step.
  pose proof (mac_fmt_at m1 MI) as FMT.
  pose proof PI1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & S3 & _ & G1 & G2 & _).
  destruct (stk_rw m1 (X + 2320) (X + 2488) (X + 2344) 18 S3 ltac:(lia) ltac:(lia)) as [jd CD].
  assert (XS : bytes_at rsegs m1 X (u64s [Z_to_bv 64 (bytes_le_to_Z (sub T (48 * j + 5) 1))])).
  { cbn [u64s]. rewrite app_nil_r. pose proof CX0 as CA.
    apply (rw_cells_app m1 X [C8 _] [CB 8 _]) in CA as [CA _]. apply ser_c8 in CA. exact (ser_cb_bytes _ _ _ _ CA). }
  eapply (sn_call SNK) with (lo := lo) (S := X) (D := X + 2344) (n := 18) (A := 0x103c8) (canary := canary)
    (fmt := mac_fmt) (ps := mac_ps)
    (args := [AInt (u_at T (48 * j + 0) 1); AInt (u_at T (48 * j + 1) 1); AInt (u_at T (48 * j + 2) 1);
              AInt (u_at T (48 * j + 3) 1); AInt (u_at T (48 * j + 4) 1); AInt (u_at T (48 * j + 5) 1)])
    (q := mac_text (map bv_unsigned (mac_of T j))) (junk := jd)
    (xs := [Z_to_bv 64 (bytes_le_to_Z (sub T (48 * j + 5) 1))]);
    [ first [ reflexivity | exact FMT | exact XS | exact CD | assumption
            | (unfold RO_LO; lia) | (apply Z.leb_le; vm_compute; reflexivity)
            | (rewrite mac_text_len; lia) | (cbn [length]; lia) | lia
            | (apply mac_text_pf; [lia | rewrite LT; lia])
            | (cbn [pf_args_ok app]; repeat (apply conj; [apply arg_u1|]); exact I) ] .. |].
  intros m2 Ft fc2 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU2 WM2 MI2 TM2 FC2 FK2 ST2 BY2.
  rewrite (ret_pc_even 0x1414c) by (first [lia | reflexivity]).
  rewrite firstn_all2 in MU2, BY2 by (rewrite mac_text_len; lia). rewrite mac_text_len in MU2.
  assert (LBY2 : Z.of_nat (length (pf_bytes (mac_text (map bv_unsigned (mac_of T j)) ++ [0]))) = 18).
  { rewrite length_pf_bytes, length_app, mac_text_len. reflexivity. }
  assert (PI2 : pinv X lo buf now i0 p T os vpad canary m0 k m2).
  { eapply pinv_tr; [exact LT | exact (objs_len_le buf vpad os count LV L6 Los Hc) | exact Hb | exact Hbl
      | unfold IMG_END; lia | lia | exact PI1 | exact MU2 | exact WM2 | exact MI2 | exact ST2 | sub_tac | rdb_tac BY2]. }
  clear PI1 TM1 MU2 WM2 CD CX0 XS FMT S3 G1 G2 MI ST jd.
  pose proof PI2 as (_ & HO2 & HB2 & _ & _ & _ & _ & _ & _ & S32 & _).
  destruct (stk_rw m2 (X + 2320) (X + 2488) (X + 2362) 6 S32 ltac:(lia) ltac:(lia)) as [sl CS].
  pose proof CS as CSw. apply ser_cb in CSw as (LSL & BSL & _).
  assert (TB : bytes_at rsegs m2 (X + 2344)
                 (pf_bytes (mac_text (map bv_unsigned (mac_of T j))) ++ Z_to_bv 8 0 :: sl)).
  { replace (pf_bytes (mac_text (map bv_unsigned (mac_of T j))) ++ Z_to_bv 8 0 :: sl)
      with (pf_bytes (mac_text (map bv_unsigned (mac_of T j)) ++ [0]) ++ sl)
      by (unfold pf_bytes; rewrite map_app, <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BY2|]. rewrite LBY2. replace (X + 2344 + 18) with (X + 2362) by lia. exact BSL. }
  destruct (p3_obj X lo buf now count T os vpad k CX Hk) as (MJ & _).
  pose proof (MJ k Hk) as MK. rewrite Z.eqb_refl in MK. pose proof (jt_kind _ _ _ _ MK) as KK.
  assert (Hko : (Z.to_nat k < length os)%nat) by lia.
  pose proof (objs_slot_at m2 (X + 1024) buf vpad os (Z.to_nat k) 0 LV L6 Hko ltac:(lia) HO2) as SL0.
  replace (X + 1024 + 144 * Z.of_nat (Z.to_nat k) + 24 * Z.of_nat 0) with (X + 1024 + 144 * k) in SL0 by lia.
  assert (IB0 : tok_inb (tj_text T now) (nth 0 (nth (Z.to_nat k) os []) tok_none)).
  { rewrite Forall_forall in IB. specialize (IB _ (nth_In os [] Hko)). rewrite Forall_forall in IB. apply IB.
    apply nth_In. rewrite Forall_forall in L6. rewrite (L6 _ (nth_In os [] Hko)). lia. }
  assert (FB : Forall (fun c => 0 <= c < 256) (tj_text T now))
    by (eapply Forall_impl; [|exact G33]; intros c Hc'; cbv beta in Hc'; lia).
  step. step. step. step. step.
  eapply (jt_call JT) with (lo := lo) (S := X) (SA := X + 1024 + 144 * k) (TA := X + 2344) (buf := buf) (kind := 1)
    (B := tj_text T now) (text := mac_text (map bv_unsigned (mac_of T j)))
    (t := nth 0 (nth (Z.to_nat k) os []) tok_none) (vpad := vpad) (slack := sl);
    [ first [ reflexivity | exact IB0 | exact SL0 | exact HB2 | exact FB | exact (mac_bytes_ok T j) | exact TB
            | exact MI2 | exact ST2 | (rewrite KK; lia) | (right; lia) | (unfold JTOK_IS_K; lia)
            | (rewrite mac_text_len, LSL; lia) | lia ] .. |].
  intros m3 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 MU3 WM3 MI3 ST3.
  rewrite (ret_pc_even 0x14160) by (first [lia | reflexivity]). unfold JTOK_IS_K in MU3.
  change (map bv_unsigned (mac_of T j)) with (e_mac (tj_entry T j)). rewrite (MJ j Hj).
  assert (PI3 : pinv X lo buf now i0 p T os vpad canary m0 k m3).
  { eapply pinv_tr; [exact LT | exact (objs_len_le buf vpad os count LV L6 Los Hc) | exact Hb | exact Hbl
      | unfold IMG_END; lia | lia | exact PI2 | exact MU3 | exact WM3 | exact MI3 | exact ST3 | sub_tac | rd0_tac]. }
  pose proof (task_stk [(X - 32, X)] m2 m3 lo X TM2 MU3 ST2 ltac:(intros x _ O; cbn [outside] in O; intuition lia))
    as TM3.
  eapply K; [exact PI3 | exact TM3 | exact FC2 | exact (fl_trans F0 F Ft FL FK2)].
Qed.

Lemma mac_loop : snprintf_stk_contract -> jtok_is_contract ->
  forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F0 F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (canary : word)
    (X lo buf now count i0 p k j : Z) (T : list byte) (os : list jobj) (vpad : list byte) (Q : machine_state -> Prop),
  Z.of_nat n = k - j -> p3ctx X lo buf now count T os vpad -> 0 <= j <= k -> k < count ->
  sp = Z_to_bv 64 X -> s4 = Z_to_bv 64 (X + 1024 + 144 * k) -> s5 = Z_to_bv 64 (-1) -> s7 = Z_to_bv 64 j ->
  s9 = Z_to_bv 64 (j + 1) -> s10 = Z_to_bv 64 (X + 514 + 48 * j) ->
  pinv X lo buf now i0 p T os vpad canary m0 k m -> MemNorm.task_mem rsegs m -> frm0 fc -> fl F0 F ->
  (forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
          (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y23 y25 y26 y28 y29 y30 y31 : word),
     pinv X lo buf now i0 p T os vpad canary m0 k m' -> MemNorm.task_mem rsegs m' -> frm0 fc' -> fl F0 F' ->
     evt rsegs Q (MS (mkR y1 sp gp tp y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17
                         s2 s3 s4 (Z_to_bv 64 k) s6 y23 s8 y25 y26 s11 y28 y29 y30 y31)
                     F' (Z_to_bv 64 0x14180) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14118) fc None m (seg_rom rsegs)).
Proof.
  intros SNK JT n. induction n as [|n IH].
  all: intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F0 F fc m0 m canary X lo buf now count i0 p k j T os vpad Q En CX Hj Hk Esp Es4 Es5 Es7 Es9 Es10 PI TM FC FL K.
  all: destruct (p3_count X lo buf now count T os vpad CX) as (Ec & Hc & _).
  all: pose proof CX as (HX0 & HX16 & HX1 & Hnow & Hb & LT & _).
  all: subst s4 s10.
  all: eapply (mac_call SNK JT) with (j := j) (k := k) (X := X) (count := count) (lo := lo) (buf := buf) (now := now)
         (T := T) (os := os) (vpad := vpad) (m0 := m0) (F0 := F0) (canary := canary) (i0 := i0) (p := p);
       [ first [ exact CX | exact PI | exact TM | exact FC | exact FL | exact Esp | reflexivity | lia ] .. |].
  all: intros m1 F1 fc1 y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 PI1 TM1 FC1 FL1.
  all: pose proof PI1 as (HT1 & _).
  all: pose proof (rd_sub m1 (X + 512) T 384 4 HT1 ltac:(lia) ltac:(rewrite LT; lia)) as RN.
  all: subst sp s5 s7 s9.
  all: destruct (Z.eqb_spec j k) as [Ejk|Njk]; cbn [Z.b2z].
  2, 3: exfalso; lia.
  - subst j. step. if_lit. step. step.
    rewrite lw_val by (apply length_sub; rewrite ?LT; lia).
    change (bv_swrap 32 (bytes_le_to_Z (sub T 384 4))) with (n_of T). rewrite <- Ec.
    step. rewrite lts_lit by lia.
    destruct (Z.ltb_spec (k + 1) count) as [Lk|Lk]; cbn [negb]; cbv iota.
    + step. step. step. step. rewrite lts_lit by lia. replace (k <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      cbv iota. eapply K; [exact PI1 | exact TM1 | exact FC1 | exact FL1].
    + eapply K; [exact PI1 | exact TM1 | exact FC1 | exact FL1].
  - step. if_lit. step.
    rewrite lw_val by (apply length_sub; rewrite ?LT; lia).
    change (bv_swrap 32 (bytes_le_to_Z (sub T 384 4))) with (n_of T). rewrite <- Ec.
    step. rewrite lts_lit by lia. replace (j + 1 <? count) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [negb]; cbv iota.
    step. step. step. step. if_lit.
    eapply IH with (j := j + 1) (k := k) (X := X) (count := count) (lo := lo) (buf := buf) (now := now)
      (T := T) (os := os) (vpad := vpad) (m0 := m0) (F0 := F0) (canary := canary) (i0 := i0) (p := p);
      [ first [ exact CX | exact PI1 | exact TM1 | exact FC1 | exact FL1 | reflexivity | lia | (f_equal; lia)
              | (rewrite unsigned_lit by lia; rewrite swrap32_small by lia; reflexivity) ] .. | exact K].
Qed.
