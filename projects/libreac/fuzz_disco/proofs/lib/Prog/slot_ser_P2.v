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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_tokb slot_ser_Pq slot_ser slot_ser_J1 slot_ser_P1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Lemma used_upd : forall k, 0 <= k < 8 -> Arr.upd (used_ws k) (Z.to_nat k) (Z_to_bv 64 1) = used_ws (k + 1).
Proof.
  intros k Hk. assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  destruct E as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst k; vm_compute; reflexivity.
Qed.

Lemma pinv_used : forall X lo buf now i0 p T os vpad canary m0 k m,
  length T = 400%nat -> Z.of_nat (length (objs_bytes buf vpad os)) <= 1296 ->
  0 < buf -> buf + Z.of_nat (length (tj_text T now)) + 1 <= lo -> IMG_END <= lo -> lo <= X -> X + 2592 < 2 ^ 63 ->
  0 <= k < 8 ->
  pinv X lo buf now i0 p T os vpad canary m0 k m ->
  pinv X lo buf now i0 p T os vpad canary m0 (k + 1) (write_to_mem m (wa (X + 992 + 4 * k)) (le4 (Z_to_bv 64 1))).
Proof.
  intros X lo buf now i0 p T os vpad canary m0 k m LT LO Hb Hbl HI HX HX1 Hk
    (HT & HO & HB & C1 & C2 & C3 & S1 & S2 & U & S3 & BN & G1 & G2 & MI & ST & WM & MU).
  unfold IMG_END in HI.
  assert (SO : store_ok rsegs m (wa (X + 992 + 4 * k)) 4 = true).
  { eapply (u32arr_store_ok rsegs m (X + 992) (used_ws k) k); [exact U | rewrite len_used; lia | reflexivity]. }
  unfold pinv. rewrite ?length_le4.
  split; [apply bytes_at_write_other; rewrite ?length_le4; [exact HT | lia | lia | rewrite LT; lia]|].
  split; [apply bytes_at_write_other; rewrite ?length_le4; [exact HO | lia | lia | lia]|].
  split; [apply bytes_at_write_other; rewrite ?length_le4;
          [exact HB | lia | lia | rewrite length_pf_bytes, length_app; cbn [length]; lia]|].
  split; [apply rw_cells_frame; rewrite ?length_le4; [exact C1 | lia | lia | cbn [cells_size csize]; lia]|].
  split; [apply rw_cells_frame; rewrite ?length_le4; [exact C2 | lia | lia | cbn [cells_size csize]; lia]|].
  split; [apply rw_cells_frame; rewrite ?length_le4; [exact C3 | lia | lia | cbn [cells_size csize]; lia]|].
  split; [apply stk_write; rewrite ?length_le4; [exact S1 | lia | lia]|].
  split; [apply stk_write; rewrite ?length_le4; [exact S2 | lia | lia]|].
  split; [rewrite <- used_upd by lia; apply (u32arr_write rsegs m (X + 992) (used_ws k) k (Z_to_bv 64 1) U);
          rewrite len_used; lia|].
  split; [apply stk_write; rewrite ?length_le4; [exact S3 | lia | lia]|].
  split; [apply bytes_at_write_other; rewrite ?length_le4; [exact BN | lia | lia | rewrite len_bn_table; unfold BN_TS; lia]|].
  split; [apply bytes_at_write_other; rewrite ?length_le4;
          [exact G1 | lia | lia | rewrite length_le8; unfold GOT_GUARD; lia]|].
  split; [apply bytes_at_write_other; rewrite ?length_le4; [exact G2 | lia | lia | rewrite length_le8; unfold GUARD; lia]|].
  split; [apply mem_inv_store; [exact MI | rewrite length_le4; exact SO]|].
  split; [apply stk_write; rewrite ?length_le4; [exact ST | lia | lia]|].
  split; [apply wmono_write; exact WM|].
  apply munch_write; rewrite ?length_le4; [exact MU | lia | lia | cbn [inside]; lia].
Qed.

Lemma task_used : forall X lo buf now i0 p T os vpad canary m0 k m,
  0 <= k < 8 -> X + 2592 < 2 ^ 63 -> pinv X lo buf now i0 p T os vpad canary m0 k m -> MemNorm.task_mem rsegs m ->
  MemNorm.task_mem rsegs (write_to_mem m (wa (X + 992 + 4 * k)) (le4 (Z_to_bv 64 1))).
Proof.
  intros X lo buf now i0 p T os vpad canary m0 k m Hk HX PI TM.
  pose proof PI as (_ & _ & _ & _ & _ & _ & _ & _ & [UB _] & _).
  pose proof (bytes_at_bound rsegs m _ _ UB) as BU. rewrite u32s_length, len_used in BU.
  eapply task_of; [exact TM | apply munch_write; rewrite ?length_le4; [apply munch_refl | lia | lia |]|].
  - instantiate (1 := [(X + 992 + 4 * k, X + 992 + 4 * k + 4)]). cbn [inside]. lia.
  - intros x Hx O. cbn [outside] in O. destruct (bytes_at_mrd m _ _ x UB) as [b Hb].
    + rewrite u32s_length, len_used. lia.
    + eapply tsk_of_mrd; [exact TM | exact Hx | exact Hb].
Qed.

Lemma nm_box : forall m, mem_inv rsegs m -> nm_at m 0x102ad s_box. Proof. nm_tac. Qed.
Lemma nm_master : forall m, mem_inv rsegs m -> nm_at m 0x103e6 s_master. Proof. nm_tac. Qed.
Lemma nm_unknown : forall m, mem_inv rsegs m -> nm_at m 0x1031b s_unknown. Proof. nm_tac. Qed.
Lemma nm_true : forall m, mem_inv rsegs m -> nm_at m 0x103aa s_true. Proof. nm_tac. Qed.
Lemma nm_false : forall m, mem_inv rsegs m -> nm_at m 0x10298 s_false. Proof. nm_tac. Qed.

Lemma rolename_ok : forall r, Forall (fun c => 0 < c < 256) (rolename r).
Proof.
  intros r. unfold rolename, s_box, s_master, s_unknown.
  destruct (r =? 1); [|destruct (r =? 2)]; repeat (apply Forall_cons; [lia|]); apply Forall_nil.
Qed.

Lemma rolename_len : forall r, (length (rolename r) <= 7)%nat.
Proof. intros r. unfold rolename. destruct (r =? 1); [|destruct (r =? 2)]; cbn; lia. Qed.

Lemma jt_true : jtok_is_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (canary : word)
    (X lo buf now count i0 p k kk kind TA R : Z) (s : nat) (T : list byte) (os : list jobj) (vpad : list byte)
    (text : list Z) (slack : list byte) (Q : machine_state -> Prop),
  p3ctx X lo buf now count T os vpad -> 0 <= k < count -> (s < 6)%nat ->
  sp = Z_to_bv 64 X -> a0 = Z_to_bv 64 (X + 1024 + 144 * k + 24 * Z.of_nat s) -> a1 = Z_to_bv 64 kind ->
  a2 = Z_to_bv 64 TA -> ra = Z_to_bv 64 R -> 0 <= R < 2 ^ 64 -> R mod 2 = 0 ->
  jtok_is (tj_text T now) (nth s (nth (Z.to_nat k) os []) tok_none) kind text = true ->
  0 < kind < 2 ^ 31 -> Forall (fun c => 0 < c < 256) text ->
  bytes_at rsegs m TA (pf_bytes text ++ Z_to_bv 8 0 :: slack) ->
  (- (TA + Z.of_nat (length text) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (TA + Z.of_nat (length text + 1 + length slack) <= X - 32 \/ X <= TA) ->
  pinv X lo buf now i0 p T os vpad canary m0 kk m -> MemNorm.task_mem rsegs m ->
  (forall (m' : word -> option byte) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     munch [(X - 32, X)] m m' ->
     pinv X lo buf now i0 p T os vpad canary m0 kk m' -> MemNorm.task_mem rsegs m' ->
     evt rsegs Q (MS (mkR ra sp gp tp y5 y6 y7 s0 s1 (Z_to_bv 64 1) y11 y12 y13 y14 y15 y16 y17
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F (Z_to_bv 64 R) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 JTOK_IS) fc None m (seg_rom rsegs)).
Proof.
  intros JT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m canary X lo buf now count i0 p k kk kind TA R s T os vpad text slack Q
    CX Hk Hs Esp Ea0 Ea1 Ea2 Era HR HR2 JS Hkind FT TB Hal HTA PI TM K.
  destruct (p3_count X lo buf now count T os vpad CX) as (Ec & Hc & Los & L6 & IB & G33 & L969).
  pose proof CX as (HX0 & HX16 & HX1 & Hnow & Hb & LT & TOK & LV & JR & Hbl & HLO & HI).
  unfold SNPRINTF_K, IMG_END in HLO, HI.
  pose proof PI as (_ & HO & HB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & ST & _ & _).
  assert (Hko : (Z.to_nat k < length os)%nat) by lia.
  pose proof (objs_slot_at m (X + 1024) buf vpad os (Z.to_nat k) s LV L6 Hko Hs HO) as SL.
  replace (X + 1024 + 144 * Z.of_nat (Z.to_nat k) + 24 * Z.of_nat s) with (X + 1024 + 144 * k + 24 * Z.of_nat s)
    in SL by lia.
  assert (IBs : tok_inb (tj_text T now) (nth s (nth (Z.to_nat k) os []) tok_none)).
  { rewrite Forall_forall in IB. specialize (IB _ (nth_In os [] Hko)). rewrite Forall_forall in IB. apply IB.
    apply nth_In. rewrite Forall_forall in L6. rewrite (L6 _ (nth_In os [] Hko)). lia. }
  assert (FB : Forall (fun c => 0 <= c < 256) (tj_text T now))
    by (eapply Forall_impl; [|exact G33]; intros c Hc'; cbv beta in Hc'; lia).
  pose proof (jt_kind _ _ _ _ JS) as KK.
  eapply (jt_call JT) with (lo := lo) (S := X) (SA := X + 1024 + 144 * k + 24 * Z.of_nat s) (TA := TA) (buf := buf)
    (kind := kind) (B := tj_text T now) (text := text) (t := nth s (nth (Z.to_nat k) os []) tok_none)
    (vpad := vpad) (slack := slack);
    [ first [ exact Esp | exact Ea0 | exact Ea1 | exact Ea2 | exact IBs | exact SL | exact HB | exact FB | exact FT
            | exact TB | exact Hal | exact HTA | exact MI | exact ST | (rewrite KK; lia) | (right; lia)
            | (unfold JTOK_IS_K; lia) | lia ] .. |].
  intros m' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU WM MI' ST'.
  subst ra. rewrite (ret_pc_even R) by lia. rewrite JS. unfold JTOK_IS_K in MU.
  assert (PI' : pinv X lo buf now i0 p T os vpad canary m0 kk m').
  { eapply pinv_tr; [exact LT | exact (objs_len_le buf vpad os count LV L6 Los Hc) | exact Hb | exact Hbl
      | unfold IMG_END; lia | lia | exact PI | exact MU | exact WM | exact MI' | exact ST' | sub_tac | rd0_tac]. }
  pose proof (task_stk [(X - 32, X)] m m' lo X TM MU ST ltac:(intros x _ O; cbn [outside] in O; intuition lia))
    as TM'.
  apply K; [exact MU | exact PI' | exact TM'].
Qed.

Lemma role_seg : jtok_is_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (canary : word)
    (X lo buf now count i0 p k : Z) (T : list byte) (os : list jobj) (vpad : list byte) (Q : machine_state -> Prop),
  p3ctx X lo buf now count T os vpad -> 0 <= k < count ->
  sp = Z_to_bv 64 X -> s4 = Z_to_bv 64 (X + 1024 + 144 * k) -> s5 = Z_to_bv 64 k ->
  pinv X lo buf now i0 p T os vpad canary m0 k m -> MemNorm.task_mem rsegs m ->
  (forall (m' : word -> option byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y28 y29 y30 y31 : word),
     pinv X lo buf now i0 p T os vpad canary m0 (k + 1) m' -> MemNorm.task_mem rsegs m' ->
     evt rsegs Q (MS (mkR y1 sp gp tp y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17
                         s2 s3 s4 y21 s6 (Z_to_bv 64 (X + 512 + 48 * k)) s8 s9 s10 s11 y28 y29 y30 y31)
                     F (Z_to_bv 64 0x141f4) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14180) fc None m (seg_rom rsegs)).
Proof.
  intros JT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m canary X lo buf now count i0 p k T os vpad Q CX Hk Esp Es4 Es5 PI TM K.
  destruct (p3_count X lo buf now count T os vpad CX) as (Ec & Hc & Los & L6 & IB & G33 & L969).
  pose proof CX as (HX0 & HX16 & HX1 & Hnow & Hb & LT & TOK & LV & JR & Hbl & HLO & HI).
  unfold SNPRINTF_K, IMG_END in HLO, HI.
  pose proof PI as (HT & _ & _ & _ & _ & _ & _ & _ & U & _).
  assert (RU : ov_read_bytes rsegs m (wa (X + 992 + 4 * k)) 4 = Some (le4 (Z_to_bv 64 0))).
  { eapply (u32arr_read rsegs m (X + 992) (used_ws k) k); [exact U | | lia | reflexivity]. unfold used_ws.
    rewrite nth_error_map, (nth_error_nth' (seq 0 8) 0%nat) by (rewrite length_seq; lia).
    rewrite seq_nth by lia. cbn [option_map]. replace (Z.of_nat (0 + Z.to_nat k) <? k) with false
      by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  pose proof (rd_sub m (X + 512) T (48 * k + 8) 4 HT ltac:(lia) ltac:(rewrite LT; lia)) as RR.
  assert (SO : store_ok rsegs m (wa (X + 992 + 4 * k)) 4 = true)
    by (eapply (u32arr_store_ok rsegs m (X + 992) (used_ws k) k); [exact U | rewrite len_used; lia | reflexivity]).
  subst sp s4 s5.
  step. rewrite lts_lit by lia. replace (k <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step. step. step.
  replace (Z_to_bv 64 (X + 992 + Z.shiftl (bv_unsigned (Z_to_bv 64 k)) 2)) with (Z_to_bv 64 (X + 992 + 4 * k))
    by (rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).
  step. step. if_lit.
  step. step. step. rewrite mul48_lit by lia. step. step. step.
  rewrite lw_val by (apply length_sub; rewrite ?LT; lia).
  change (bv_swrap 32 (bytes_le_to_Z (sub T (48 * k + 8) 4))) with (role_of_e T k).
  step. step.
  pose proof (pinv_used X lo buf now i0 p T os vpad canary m0 k m LT (objs_len_le buf vpad os count LV L6 Los Hc)
                Hb Hbl ltac:(unfold IMG_END; lia) ltac:(lia) HX1 ltac:(lia) PI) as PI1.
  pose proof (task_used X lo buf now i0 p T os vpad canary m0 k m ltac:(lia) HX1 PI TM) as TM1.
  set (m1 := write_to_mem m (wa (X + 992 + 4 * k)) (le4 (Z_to_bv 64 1))) in PI1, TM1.
  change (write_to_mem m (Z_to_bv 64 (X + 992 + 4 * k)) (le4 (Z_to_bv 64 1))) with m1.
  pose proof PI1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI1 & _).
  destruct (p3_obj X lo buf now count T os vpad k CX Hk) as (_ & R1 & _).
  change (e_role (tj_entry T k)) with (role_of_e T k) in R1.
  assert (JR3 : forall (TA : Z) (w10 w11 : word), nm_at m1 TA (rolename (role_of_e T k)) -> 0 <= TA ->
    TA + 16 <= 0x20000 ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 X) gp tp t0 t1 t2 s0 s1 w10 w11 (Z_to_bv 64 TA) a3 a4 a5 a6 a7
                         s2 s3 (Z_to_bv 64 (X + 1024 + 144 * k)) (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 k)) 6))
                         s6 (Z_to_bv 64 (X + 512 + 48 * k)) s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x141e4) fc None m1 (seg_rom rsegs))).
  { intros TA w10 w11 N HTA0 HTA1. unfold nm_at in N.
    step. step. step.
    eapply (jt_true JT) with (k := k) (kk := k + 1) (s := 1%nat) (kind := 1) (TA := TA) (R := 0x141f0)
      (text := rolename (role_of_e T k)) (slack := img8 (TA + Z.of_nat (length (rolename (role_of_e T k))) + 1));
      [ first [ exact CX | exact R1 | exact N | exact PI1 | exact TM1 | reflexivity | (f_equal; lia) | lia
              | apply rolename_ok
              | (rewrite img8_len; match goal with |- ?a mod 8 <= _ => pose proof (Z.mod_pos_bound a 8 ltac:(lia)); lia end)
              | (left; rewrite img8_len; pose proof (rolename_len (role_of_e T k)); lia) ] .. |].
    intros m' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 _ PI' TM'.
    step. if_lit. eapply K; [exact PI' | exact TM']. }
  pose proof TOK as (_ & T2 & _). destruct (T2 k ltac:(lia)) as [Er|[Er|Er]]; rewrite Er.
  - step. step. if_lit. step. step. step. step. step. if_lit.
    apply JR3; [rewrite Er; exact (nm_unknown m1 MI1) | lia | lia].
  - step. step. if_lit. step. step. step. step. step. if_lit. step. step.
    apply JR3; [rewrite Er; exact (nm_box m1 MI1) | lia | lia].
  - step. step. if_lit. step. step. step. step. if_lit.
    apply JR3; [rewrite Er; exact (nm_master m1 MI1) | lia | lia].
Qed.
