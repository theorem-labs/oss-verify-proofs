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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_tokb slot_ser_Pq slot_ser slot_ser_J1 slot_ser_P1 slot_ser_P2.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Lemma mw_calls : jtok_is_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (canary : word)
    (X lo buf now count i0 p k kk MA : Z) (T : list byte) (os : list jobj) (vpad : list byte)
    (mt wt : list Z) (sl1 sl2 : list byte) (Q : machine_state -> Prop),
  p3ctx X lo buf now count T os vpad -> 0 <= k < count ->
  sp = Z_to_bv 64 X -> s4 = Z_to_bv 64 (X + 1024 + 144 * k) -> s5 = Z_to_bv 64 MA ->
  jtok_is (tj_text T now) (nth 2 (nth (Z.to_nat k) os []) tok_none) 1 mt = true ->
  jtok_is (tj_text T now) (nth 3 (nth (Z.to_nat k) os []) tok_none) 1 wt = true ->
  Forall (fun c => 0 < c < 256) mt -> Forall (fun c => 0 < c < 256) wt ->
  bytes_at rsegs m MA (pf_bytes mt ++ Z_to_bv 8 0 :: sl1) ->
  (- (MA + Z.of_nat (length mt) + 1)) mod 8 <= Z.of_nat (length sl1) ->
  (MA + Z.of_nat (length mt + 1 + length sl1) <= X - 32 \/ X <= MA) ->
  bytes_at rsegs m (X + 944) (pf_bytes wt ++ Z_to_bv 8 0 :: sl2) ->
  (- (X + 944 + Z.of_nat (length wt) + 1)) mod 8 <= Z.of_nat (length sl2) ->
  pinv X lo buf now i0 p T os vpad canary m0 kk m -> MemNorm.task_mem rsegs m ->
  (forall (m' : word -> option byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     pinv X lo buf now i0 p T os vpad canary m0 kk m' -> MemNorm.task_mem rsegs m' ->
     evt rsegs Q (MS (mkR y1 sp gp tp y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F (Z_to_bv 64 0x14294) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1426c) fc None m (seg_rom rsegs)).
Proof.
  intros JT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m canary X lo buf now count i0 p k kk MA T os vpad mt wt sl1 sl2 Q
    CX Hk Esp Es4 Es5 J2 J3 FM FW BM AM PM BW AW PI TM K.
  pose proof CX as (HX0 & HX16 & HX1 & Hnow & Hb & LT & TOK & LV & JR & Hbl & HLO & HI).
  subst sp s4 s5.
  step. step. step. step.
  eapply (jt_true JT) with (k := k) (kk := kk) (s := 2%nat) (kind := 1) (TA := MA) (R := 0x1427c) (text := mt)
    (slack := sl1);
    [ first [ exact CX | exact J2 | exact BM | exact AM | exact PM | exact FM | exact PI | exact TM | reflexivity
            | (f_equal; lia) | lia ] .. |].
  intros m1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU1 PI1 TM1.
  assert (BW1 : bytes_at rsegs m1 (X + 944) (pf_bytes wt ++ Z_to_bv 8 0 :: sl2)).
  { eapply bytes_tr; [exact BW | exact MU1 |]. intros x Hx. cbn [outside]. split; [lia | exact I]. }
  step. if_lit. step. step. step. step.
  eapply (jt_true JT) with (k := k) (kk := kk) (s := 3%nat) (kind := 1) (TA := X + 944) (R := 0x14290) (text := wt)
    (slack := sl2);
    [ first [ exact CX | exact J3 | exact BW1 | exact AW | exact PI1 | exact TM1 | exact FW | reflexivity
            | (f_equal; lia) | (right; lia) | lia ] .. |].
  intros m2 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 MU2 PI2 TM2.
  step. if_lit. eapply K; [exact PI2 | exact TM2].
Qed.

Lemma bn_accept_ret : forall f i o nm tk dp, nm <> 0 -> tk <> 0 -> dp <> 0 ->
  bn_accept f [] i o nm 24 tk 24 dp 48 = (bn_ret f [] i o =? 0).
Proof.
  intros f i o nm tk dp Hn Ht Hd. unfold bn_accept, bn_args_ok.
  replace (nm =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hn).
  replace (tk =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ht).
  replace (dp =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hd).
  change (24 =? 0) with false. change (48 =? 0) with false. cbn [negb andb].
  destruct (bn_ok i) eqn:Bi; destruct (bn_ok o) eqn:Bo; destruct ((i =? 0) && (o =? 0)) eqn:Bz; cbn [andb negb];
    try (rewrite bn_ret_refuse by (rewrite Bi, Bo, Bz; reflexivity); reflexivity).
  destruct (bn_c17 f i o Bi Bo Bz) as (R0 & L1 & L2 & L3 & _). rewrite R0.
  replace (Z.of_nat (length (bn_NM f [] i o)) <? 24) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (Z.of_nat (length (bn_TK (bn_NM f [] i o))) <? 24) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (Z.of_nat (length (bn_DP (bn_NM f [] i o) i o)) <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma ba_nil : forall m a, 0 <= a <= 2 ^ 64 -> bytes_at rsegs m a [].
Proof. intros m a H. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia. Qed.

Lemma model_hd0 : forall T k, hd_of T k = 0 -> model_of box_tok (tj_entry T k) = (s_unknown, s_0x0).
Proof. intros T k H. unfold model_of. cbn [e_has_decl tj_entry]. rewrite H. reflexivity. Qed.

Lemma model_nobn : forall T k, hd_of T k = 1 ->
  bn_ret (u_at T (48 * k + 15) 1) [] (din_of T k) (dout_of T k) <> 0 ->
  model_of box_tok (tj_entry T k) = (s_unknown, s_0x0).
Proof.
  intros T k H R. unfold model_of, box_tok. cbn [e_has_decl e_family e_decl_in e_decl_out tj_entry]. rewrite H.
  replace (bn_ret (u_at T (48 * k + 15) 1) [] (din_of T k) (dout_of T k) =? 0) with false
    by (symmetry; apply Z.eqb_neq; exact R).
  reflexivity.
Qed.

Lemma model_bn : forall T k, hd_of T k = 1 ->
  bn_ret (u_at T (48 * k + 15) 1) [] (din_of T k) (dout_of T k) = 0 ->
  model_of box_tok (tj_entry T k) =
    (bn_TK (bn_NM (u_at T (48 * k + 15) 1) [] (din_of T k) (dout_of T k)),
     dec (din_of T k) ++ [120] ++ dec (dout_of T k)).
Proof.
  intros T k H R. unfold model_of, box_tok. cbn [e_has_decl e_family e_decl_in e_decl_out tj_entry]. rewrite H.
  rewrite R. reflexivity.
Qed.

Lemma s0x0_bytes : le4 (Z_to_bv 64 W0X0) = pf_bytes s_0x0 ++ [Z_to_bv 8 0].
Proof. apply ser_map_unsigned_inj. vm_compute. reflexivity. Qed.

Lemma bn_ret0 : forall f sd i o, bn_ret f sd i o = 0 ->
  bn_ok i = true /\ bn_ok o = true /\ (i =? 0) && (o =? 0) = false.
Proof.
  intros f sd i o H. unfold bn_ret in H.
  destruct (bn_ok i), (bn_ok o), ((i =? 0) && (o =? 0)); cbn in H; try discriminate; repeat split; reflexivity.
Qed.

Lemma tk_ok : forall tk, Forall (fun c => bn_tok_char c = true) tk -> Forall (fun c => 0 < c < 256) tk.
Proof.
  intros tk F. eapply Forall_impl; [|exact F]. intros c H. cbv beta in H. unfold bn_tok_char in H.
  apply orb_true_iff in H as [H|H]; [apply orb_true_iff in H as [H|H]|].
  - apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
  - apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
  - apply Z.eqb_eq in H. lia.
Qed.

Lemma dec_ok : forall v, 0 <= v < 10 ^ 20 -> Forall (fun c => 0 < c < 256) (dec v).
Proof.
  intros v H. destruct (dec_spec v H) as (D & _). eapply Forall_impl; [|exact D]. intros c Hc. unfold digc in Hc. lia.
Qed.

Lemma task_regions : forall W m m' lo X, MemNorm.task_mem rsegs m -> munch W m m' -> stk rsegs m lo X ->
  stk rsegs m (X + 920) (X + 992) -> stk rsegs m (X + 2320) (X + 2488) ->
  (forall x, ~ outside W x -> lo <= x < X \/ X + 920 <= x < X + 992 \/ X + 2320 <= x < X + 2488) ->
  MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' lo X TM MU S1 S2 S3 H. eapply task_of; [exact TM | exact MU |].
  intros x Hx O. destruct (H x O) as [A|[A|A]].
  - exact (tsk_of_stk m _ _ x TM S1 A).
  - exact (tsk_of_stk m _ _ x TM S2 A).
  - exact (tsk_of_stk m _ _ x TM S3 A).
Qed.

Lemma wd_text : forall a b, printf_facts_c.pf_text [Pd; PLit 120; Pd] [AInt a; AInt b] = Some (pf_dec a ++ [120] ++ pf_dec b).
Proof. intros a b. cbn. rewrite ?app_nil_r. reflexivity. Qed.

Definition wd_fmt : list Z := [37; 100; 120; 37; 100].

Lemma wd_fmt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x102b9 (pf_bytes (wd_fmt ++ [0])).
Proof. intros m MI. apply ro_at; [exact MI | vm_compute; reflexivity | lia | apply Z.leb_le; vm_compute; reflexivity]. Qed.

Lemma dec_len_le2 : forall v, 0 <= v <= 40 -> (length (pf_dec v) <= 2)%nat.
Proof. intros v H. rewrite <- dec_pfdec by lia. pose proof (dec_len2 v H) as L. unfold jlen in L. lia. Qed.

Ltac mod8 := match goal with |- ?a mod 8 <= _ => pose proof (Z.mod_pos_bound a 8 ltac:(lia)); lia end.

Lemma bn_seg : reac_box_name_contract -> snprintf_stk_contract -> jtok_is_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F0 F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (canary : word)
    (X lo buf now count i0 p k kk : Z) (T : list byte) (os : list jobj) (vpad sl0 : list byte)
    (Q : machine_state -> Prop),
  p3ctx X lo buf now count T os vpad -> 0 <= k < count -> hd_of T k = 1 ->
  sp = Z_to_bv 64 X -> s4 = Z_to_bv 64 (X + 1024 + 144 * k) -> s5 = Z_to_bv 64 0x1031b ->
  s7 = Z_to_bv 64 (X + 512 + 48 * k) ->
  bytes_at rsegs m (X + 944) (pf_bytes s_0x0 ++ Z_to_bv 8 0 :: sl0) -> length sl0 = 4%nat ->
  pinv X lo buf now i0 p T os vpad canary m0 kk m -> MemNorm.task_mem rsegs m -> frm0 fc -> fl F0 F ->
  (forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
          (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y28 y29 y30 y31 : word),
     pinv X lo buf now i0 p T os vpad canary m0 kk m' -> MemNorm.task_mem rsegs m' -> frm0 fc' -> fl F0 F' ->
     evt rsegs Q (MS (mkR y1 sp gp tp y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17
                         s2 s3 s4 y21 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F' (Z_to_bv 64 0x14294) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1420c) fc None m (seg_rom rsegs)).
Proof.
  intros BNC SNK JT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F0 F fc m0 m canary X lo buf now count i0 p k kk T os vpad sl0 Q CX Hk Hhd Esp Es4 Es5 Es7 BW LS0 PI TM FC FL K.
  destruct (p3_count X lo buf now count T os vpad CX) as (Ec & Hc & Los & L6 & IB & G33 & L969).
  pose proof CX as (HX0 & HX16 & HX1 & Hnow & Hb & LT & TOK & LV & JR & Hbl & HLO & HI).
  unfold SNPRINTF_K, IMG_END in HLO, HI.
  pose proof PI as (HT & _ & _ & _ & _ & _ & S1 & _ & _ & _ & _ & _ & _ & MI & ST & _ & _).
  pose proof (rd_sub m (X + 512) T (48 * k + 13) 1 HT ltac:(lia) ltac:(rewrite LT; lia)) as R13.
  pose proof (rd_sub m (X + 512) T (48 * k + 14) 1 HT ltac:(lia) ltac:(rewrite LT; lia)) as R14.
  pose proof (rd_sub m (X + 512) T (48 * k + 15) 1 HT ltac:(lia) ltac:(rewrite LT; lia)) as R15.
  destruct (stk_rw m X (X + 16) X 16 S1 ltac:(lia) ltac:(lia)) as [jx CX0].
  pose proof (munch_refl [(X, X + 16)] m) as MUs. pose proof (wmono_refl rsegs m) as WMs.
  clear HT S1.
  subst sp s4 s5 s7.
  step. step. step. rewrite !lbu_val by (apply length_sub; rewrite ?LT; lia).
  change (bytes_le_to_Z (sub T (48 * k + 13) 1)) with (din_of T k).
  change (bytes_le_to_Z (sub T (48 * k + 14) 1)) with (dout_of T k).
  change (bytes_le_to_Z (sub T (48 * k + 15) 1)) with (u_at T (48 * k + 15) 1).
  pose proof TOK as (_ & _ & _ & T4). destruct (T4 k ltac:(lia)) as (_ & HD & _). destruct (HD Hhd) as [Hdi Hdo].
  pose proof (u1_range T (48 * k + 13)) as Rdi. pose proof (u1_range T (48 * k + 14)) as Rdo.
  pose proof (u1_range T (48 * k + 15)) as Rf.
  change (u_at T (48 * k + 13) 1) with (din_of T k) in Rdi. change (u_at T (48 * k + 14) 1) with (dout_of T k) in Rdo.
  step. step. step. step. step. step. step. step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (stk_of_rw_cells rsegs m1 X _ CX0) as SX. cbn [cells_size csize Nat.add] in SX.
  pose proof PI as (_ & _ & _ & _ & _ & _ & S1m & _).
  pose proof (task_stk [(X, X + 16)] m m1 X (X + 16) TM MUs S1m ltac:(intros x _ O; cbn [outside] in O; intuition lia))
    as TM1.
  assert (PI1 : pinv X lo buf now i0 p T os vpad canary m0 kk m1).
  { eapply pinv_tr; [exact LT | exact (objs_len_le buf vpad os count LV L6 Los Hc) | exact Hb | exact Hbl
      | unfold IMG_END; lia | lia | exact PI | exact MUs | exact WMs | exact MI | exact ST | sub_tac | rd_tac SX]. }
  clear PI TM MUs WMs S1m SX R13 R14 R15.
  pose proof PI1 as (_ & _ & _ & _ & _ & _ & _ & S2 & _ & S3 & BN & _).
  destruct (stk_rw m1 (X + 2320) (X + 2488) (X + 2320) 24 S3 ltac:(lia) ltac:(lia)) as [jn CN].
  destruct (stk_rw m1 (X + 2320) (X + 2488) (X + 2344) 48 S3 ltac:(lia) ltac:(lia)) as [jd CD].
  destruct (stk_rw m1 (X + 920) (X + 992) (X + 968) 24 S2 ltac:(lia) ltac:(lia)) as [jt CT].
  assert (DB : bytes_at rsegs m1 X (le8 (Z_to_bv 64 (X + 2344)) ++ le8 (Z_to_bv 64 48))).
  { pose proof CX0 as CA. apply (rw_cells_app m1 X [C8 _] [C8 _]) in CA as [CA CB].
    apply ser_c8 in CA. apply ser_c8 in CB. apply ser_cb_bytes in CA. apply ser_cb_bytes in CB.
    apply bytes_at_app. split; [exact CA|]. rewrite length_le8. exact CB. }
  eapply evt_cut.
  { eapply BNC with (lo := lo) (f := u_at T (48 * k + 15) 1) (i := din_of T k) (o := dout_of T k)
      (display := Z_to_bv 64 (X + 2344)) (display_len := Z_to_bv 64 48) (sd := []);
    rewrite ?(unsigned_lit X), ?(unsigned_lit (X + 2320)), ?(unsigned_lit (X + 968)), ?(unsigned_lit (X + 2344)),
      ?(unsigned_lit 24), ?(unsigned_lit 48), ?(unsigned_lit 0) by lia;
    [ first [ reflexivity | lia | exact DB | exact ST | assumption | (unfold BN_K; lia)
            | (apply bn_img; [assumption | exact BN | unfold BN_K; lia])
            | (intros _; split; [left; split; reflexivity|]; unfold bn_bufs;
               change (Z.min 24 24) with 24; change (Z.min 48 48) with 48;
               split; [exists jn; exact CN|]; split; [exists jt; exact CT|]; split; [exists jd; exact CD|];
               unfold BN_K; cbn [disjoint_from]; repeat split; try exact I; lia) ] .. ]. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              E & WM2 & MI2 & ST2 & BR).
  subst ms'.
  rewrite (unsigned_lit X) in ST2 by lia.
  rewrite (unsigned_lit (X + 2320)), (unsigned_lit (X + 968)), (unsigned_lit (X + 2344)), (unsigned_lit 24),
    (unsigned_lit 48) in BR by lia.
  rewrite bn_accept_ret in BR by lia.
  rewrite (ret_pc_even 0x14248) by (first [lia | reflexivity]).
  set (f := u_at T (48 * k + 15) 1) in *. set (NM := bn_NM f [] (din_of T k) (dout_of T k)) in *.
  destruct (Z.eqb_spec (bn_ret f [] (din_of T k) (dout_of T k)) 0) as [R0|R0].
  - destruct BR as (Ea & MU2 & BNM & BTK & BDP). subst a0'.
    rewrite (unsigned_lit X) in MU2 by lia. unfold BN_K in MU2.
    destruct (bn_ret0 _ _ _ _ R0) as (Bi & Bo & Bz).
    pose proof (bn_c17 f (din_of T k) (dout_of T k) Bi Bo Bz) as BC. cbv zeta in BC.
    change (bn_NM f [] (din_of T k) (dout_of T k)) with NM in BC. destruct BC as (_ & LNM & LTK & LDP & FTK).
    assert (LB1 : Z.of_nat (length (bn_bytes (NM ++ [0]))) = Z.of_nat (length NM) + 1)
      by (unfold bn_bytes; rewrite length_map, length_app; cbn [length]; lia).
    assert (LB2 : Z.of_nat (length (bn_bytes (bn_TK NM ++ [0]))) = Z.of_nat (length (bn_TK NM)) + 1)
      by (unfold bn_bytes; rewrite length_map, length_app; cbn [length]; lia).
    assert (LB3 : Z.of_nat (length (bn_bytes (bn_DP NM (din_of T k) (dout_of T k) ++ [0]))) =
                  Z.of_nat (length (bn_DP NM (din_of T k) (dout_of T k))) + 1)
      by (unfold bn_bytes; rewrite length_map, length_app; cbn [length]; lia).
    assert (PI2 : pinv X lo buf now i0 p T os vpad canary m0 kk m2).
    { eapply pinv_tr; [exact LT | exact (objs_len_le buf vpad os count LV L6 Los Hc) | exact Hb | exact Hbl
        | unfold IMG_END; lia | lia | exact PI1 | exact MU2 | exact WM2 | exact MI2 | exact ST2 | sub_tac | ].
      rd_split.
      assert (D : (X + 2320 <= x < X + 2320 + Z.of_nat (length NM) + 1) \/
                  (X + 968 <= x < X + 968 + Z.of_nat (length (bn_TK NM)) + 1) \/
                  (X + 2344 <= x < X + 2344 + Z.of_nat (length (bn_DP NM (din_of T k) (dout_of T k))) + 1)) by lia.
      destruct D as [D|[D|D]];
        [ eapply bytes_at_mrd; [exact BNM | rewrite LB1; lia]
        | eapply bytes_at_mrd; [exact BTK | rewrite LB2; lia]
        | eapply bytes_at_mrd; [exact BDP | rewrite LB3; lia] ]. }
    pose proof (task_regions _ m1 m2 lo X TM1 MU2 ST S2 S3 ltac:(intros x O; cbn [outside] in O; intuition lia))
      as TM2.
    step. if_lit.
    pose proof PI2 as (HT2 & _ & _ & _ & _ & _ & _ & S22 & _ & _ & _ & G1 & G2 & _).
    pose proof (rd_sub m2 (X + 512) T (48 * k + 13) 1 HT2 ltac:(lia) ltac:(rewrite LT; lia)) as R13.
    pose proof (rd_sub m2 (X + 512) T (48 * k + 14) 1 HT2 ltac:(lia) ltac:(rewrite LT; lia)) as R14.
    step. step. rewrite !lbu_val by (apply length_sub; rewrite ?LT; lia).
    change (bytes_le_to_Z (sub T (48 * k + 13) 1)) with (din_of T k).
    change (bytes_le_to_Z (sub T (48 * k + 14) 1)) with (dout_of T k).
    step. step. step. step. step.
    destruct (stk_rw m2 (X + 920) (X + 992) (X + 944) 24 S22 ltac:(lia) ltac:(lia)) as [jw CW].
    pose proof (dec_len_le2 (din_of T k) ltac:(lia)) as Ld1. pose proof (dec_len_le2 (dout_of T k) ltac:(lia)) as Ld2.
    set (q := pf_dec (din_of T k) ++ [120] ++ pf_dec (dout_of T k)) in *.
    assert (Lq : (length q <= 5)%nat) by (unfold q; rewrite !length_app; cbn [length]; lia).
    eapply (sn_call SNK) with (lo := lo) (S := X) (D := X + 944) (n := 24) (A := 0x102b9) (canary := canary)
      (fmt := wd_fmt) (ps := [Pd; PLit 120; Pd]) (args := [AInt (din_of T k); AInt (dout_of T k)]) (q := q)
      (junk := jw) (xs := []);
      [ first [ reflexivity | exact (wd_fmt_at m2 MI2) | exact CW | assumption | exact (wd_text _ _)
              | (unfold RO_LO; lia) | (apply Z.leb_le; vm_compute; reflexivity) | (apply ba_nil; lia)
              | (cbn [length]; lia) | lia
              | (cbn [pf_args_ok app]; repeat (apply conj; [apply arg_u1|]); exact I) ] .. |].
    intros m3 Ft fc3 w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 MU3 WM3 MI3 TM3 FC3 FK3 ST3 BY3.
    rewrite (ret_pc_even 0x14268) by (first [lia | reflexivity]).
    rewrite firstn_all2 in MU3, BY3 by lia.
    assert (LBq : Z.of_nat (length (pf_bytes (q ++ [0]))) = Z.of_nat (length q) + 1)
      by (rewrite length_pf_bytes, length_app; cbn [length]; lia).
    assert (PI3 : pinv X lo buf now i0 p T os vpad canary m0 kk m3).
    { eapply pinv_tr; [exact LT | exact (objs_len_le buf vpad os count LV L6 Los Hc) | exact Hb | exact Hbl
        | unfold IMG_END; lia | lia | exact PI2 | exact MU3 | exact WM3 | exact MI3 | exact ST3 | sub_tac | rdb_tac BY3]. }
    assert (BTK3 : bytes_at rsegs m3 (X + 968) (bn_bytes (bn_TK NM ++ [0]))).
    { eapply bytes_tr; [exact BTK | exact MU3 |]. rewrite LB2. intros x Hx. cbn [outside].
      repeat split; try exact I; lia. }
    step.
    pose proof PI3 as (_ & _ & _ & _ & _ & _ & _ & S23 & _).
    destruct (stk_rw m3 (X + 920) (X + 992) (X + 968 + Z.of_nat (length (bn_TK NM)) + 1) 8 S23 ltac:(lia) ltac:(lia))
      as [sl1 CS1].
    destruct (stk_rw m3 (X + 920) (X + 992) (X + 944 + Z.of_nat (length q) + 1) 8 S23 ltac:(lia) ltac:(lia))
      as [sl2 CS2].
    apply ser_cb in CS1 as (LS1 & BS1 & _). apply ser_cb in CS2 as (LS2 & BS2 & _).
    assert (BM : bytes_at rsegs m3 (X + 968) (pf_bytes (bn_TK NM) ++ Z_to_bv 8 0 :: sl1)).
    { replace (pf_bytes (bn_TK NM) ++ Z_to_bv 8 0 :: sl1) with (bn_bytes (bn_TK NM ++ [0]) ++ sl1)
        by (unfold bn_bytes, pf_bytes; rewrite map_app, <- app_assoc; reflexivity).
      apply bytes_at_app. split; [exact BTK3|]. rewrite LB2. replace (X + 968 + (Z.of_nat (length (bn_TK NM)) + 1))
        with (X + 968 + Z.of_nat (length (bn_TK NM)) + 1) by lia. exact BS1. }
    assert (BWd : bytes_at rsegs m3 (X + 944) (pf_bytes q ++ Z_to_bv 8 0 :: sl2)).
    { replace (pf_bytes q ++ Z_to_bv 8 0 :: sl2) with (pf_bytes (q ++ [0]) ++ sl2)
        by (unfold pf_bytes; rewrite map_app, <- app_assoc; reflexivity).
      apply bytes_at_app. split; [exact BY3|]. rewrite LBq. replace (X + 944 + (Z.of_nat (length q) + 1))
        with (X + 944 + Z.of_nat (length q) + 1) by lia. exact BS2. }
    destruct (p3_obj X lo buf now count T os vpad k CX Hk) as (_ & _ & J2 & J3 & _).
    rewrite (model_bn T k Hhd R0) in J2, J3. cbn [fst snd] in J2, J3. rewrite !dec_pfdec in J3 by lia.
    assert (FQ : Forall (fun c => 0 < c < 256) q).
    { unfold q. rewrite <- !dec_pfdec by lia. apply Forall_app. split; [apply dec_ok; lia|].
      apply Forall_app. split; [apply Forall_cons; [lia | apply Forall_nil] | apply dec_ok; lia]. }
    eapply (mw_calls JT) with (MA := X + 968) (mt := bn_TK NM) (wt := q) (sl1 := sl1) (sl2 := sl2) (kk := kk) (k := k)
      (X := X) (lo := lo) (buf := buf) (now := now) (count := count) (T := T) (os := os) (vpad := vpad) (m0 := m0)
      (canary := canary) (i0 := i0) (p := p);
      [ first [ exact CX | exact J2 | exact J3 | exact BM | exact BWd | exact PI3 | exact TM3 | exact FQ
              | exact (tk_ok _ FTK) | reflexivity | (rewrite LS1; mod8) | (rewrite LS2; mod8) | (right; lia) | lia ] .. |].
    intros m4 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 PI4 TM4.
    eapply K; [exact PI4 | exact TM4 | exact FC3 | exact (fl_trans F0 F Ft FL FK3)].
  - destruct BR as (Ea & MU2). subst a0'.
    rewrite (unsigned_lit X) in MU2 by lia. unfold BN_K in MU2.
    assert (PI2 : pinv X lo buf now i0 p T os vpad canary m0 kk m2).
    { eapply pinv_tr; [exact LT | exact (objs_len_le buf vpad os count LV L6 Los Hc) | exact Hb | exact Hbl
        | unfold IMG_END; lia | lia | exact PI1 | exact MU2 | exact WM2 | exact MI2 | exact ST2 | sub_tac | rd0_tac]. }
    pose proof (task_stk [(X - 288, X)] m1 m2 lo X TM1 MU2 ST ltac:(intros x _ O; cbn [outside] in O; intuition lia))
      as TM2.
    assert (BW2 : bytes_at rsegs m2 (X + 944) (pf_bytes s_0x0 ++ Z_to_bv 8 0 :: sl0)).
    { eapply bytes_tr; [exact BW | exact MU2 |]. intros x Hx. cbn [outside]. split; [lia | exact I]. }
    step. if_lit.
    pose proof (nm_unknown m2 MI2) as NU. unfold nm_at in NU.
    destruct (p3_obj X lo buf now count T os vpad k CX Hk) as (_ & _ & J2 & J3 & _).
    rewrite (model_nobn T k Hhd R0) in J2, J3. cbn [fst snd] in J2, J3.
    eapply (mw_calls JT) with (MA := 0x1031b) (mt := s_unknown) (wt := s_0x0)
      (sl1 := img8 (0x1031b + Z.of_nat (length s_unknown) + 1)) (sl2 := sl0) (kk := kk) (k := k)
      (X := X) (lo := lo) (buf := buf) (now := now) (count := count) (T := T) (os := os) (vpad := vpad) (m0 := m0)
      (canary := canary) (i0 := i0) (p := p);
      [ first [ exact CX | exact J2 | exact J3 | exact NU | exact BW2 | exact PI2 | exact TM2 | reflexivity
              | (unfold s_unknown, s_0x0; repeat (apply Forall_cons; [lia|]); apply Forall_nil)
              | (rewrite img8_len; mod8) | (rewrite LS0; unfold s_0x0; cbn [length]; lia)
              | (left; rewrite img8_len; unfold s_unknown; cbn [length]; lia) | lia ] .. |].
    intros m4 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 PI4 TM4.
    eapply K; [exact PI4 | exact TM4 | exact FC | exact FL].
Qed.
