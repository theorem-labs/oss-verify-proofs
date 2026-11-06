(** m_file (plain build, image 3776ca44d75c, 0x13fb4): the sub-piece S_MF_KMOD of Prog/mf_cuts.v, the "model" key
    of the inlined m_key: 0x144d4-0x145a0 with the joins 0x1473c-0x14748 and 0x14598-0x1459c.

    From KMODEL 0x144d4 (the key state of mf_cuts.H_MF_KAT with [S_role] already missed):
    - ieq(k, kl, "model" 0x10811) 0x144e4; 0 goes to KIGN 0x145a0 (the premise H_MF_KIGN n).
    - the hit: s7 := min(vl, 23) (0x144ec-0x144f4), s8 := 0x1ff (0x144f8), the inline fold of the value into
      low = sp + 0x28 (0x144fc-0x14534, the frame scratch [sp + 0x28, sp + 0x68)), NUL at low + s7; the bytes
      are SegModel.h_fold v 24.
    - fuzz_catalogue_row(low, s7) 0x14540: NULL (cat_row low = None) refuses at 0x14744 and joins 0x14598;
      else memcpy(cur + 0x24, low, s7 + 1) 0x14558 and model_set = 1 (0x14560), then 0x14598.
    - 0x14598 puts s7 back to 9 and joins the tail 0x143d4 (the premise H_MF_TAIL n). *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env seg_tok_bridge
  m_file_c mf_cuts mfu_facts mfp_facts mfp_mconf mf_common ieq_c fuzz_catalogue_row_c memcpy_c m_refuse_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Words and bytes *)
Lemma km_u8 : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  change (Z.of_N 8) with 8%Z. lia.
Qed.

Lemma km_eqb : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma km_ltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma km_le1 : forall y b, 0 <= b < 256 -> y mod 256 = b -> le1 (Z_to_bv 64 y) = [Z_to_bv 8 b].
Proof.
  intros y b Hb Hy. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (Z.of_N 8) with 8%Z. change (Z.of_N 64) with 64%Z.
  rewrite (mod_mod8_of_modw y 64) by lia. change (2 ^ 8)%Z with 256%Z.
  rewrite Hy, (Z.mod_small b 256) by lia. reflexivity.
Qed.

(** The fold's test `(c - 'A') <u 26`. *)
Lemma km_sub65 : forall x, 0 <= x < 256 -> (((x + -65) mod 2 ^ 64) <? 26) = true <-> 65 <= x <= 90.
Proof.
  intros x Hx. split.
  - intros HB. apply Z.ltb_lt in HB. destruct (Z_lt_le_dec x 65) as [Hlt|Hge].
    + exfalso. rewrite <- (Z_mod_plus_full (x + -65) 1 (2 ^ 64)) in HB.
      rewrite Z.mod_small in HB by lia. lia.
    + rewrite Z.mod_small in HB by lia. lia.
  - intros Hr. apply Z.ltb_lt. rewrite Z.mod_small by lia. lia.
Qed.

Lemma km_lower_hi : forall x, 0 <= x < 256 -> (((x + -65) mod 2 ^ 64) <? 26) = true ->
  (x + 32) mod 256 = lower x.
Proof.
  intros x Hx HB. apply (proj1 (km_sub65 x Hx)) in HB. unfold lower.
  rewrite (proj2 (Z.leb_le 65 x)) by lia. rewrite (proj2 (Z.leb_le x 90)) by lia. cbn [andb].
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma km_lower_lo : forall x, 0 <= x < 256 -> (((x + -65) mod 2 ^ 64) <? 26) = false ->
  x mod 256 = lower x.
Proof.
  intros x Hx HB. unfold lower.
  destruct (Z.leb_spec 65 x) as [H1|H1]; destruct (Z.leb_spec x 90) as [H2|H2]; cbn [andb];
    try (rewrite Z.mod_small by lia; reflexivity).
  exfalso. rewrite (proj2 (km_sub65 x Hx) ltac:(lia)) in HB. discriminate HB.
Qed.

(** ** Lists *)
Lemma km_map_len : forall {A B} (f : A -> B) (l : list A), length (map f l) = length l.
Proof. intros A B f. induction l as [|x l IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma km_zszb : forall l, Forall (fun x => 0 <= x < 256) l -> zs (zb l) = l.
Proof.
  unfold zs, zb. induction 1 as [|x l Hx Hl IH]; cbn [map]; [reflexivity|].
  f_equal; [apply km_u8; exact Hx | exact IH].
Qed.

Lemma km_in_firstn : forall {A} nn (l : list A) x, In x (firstn nn l) -> In x l.
Proof. intros A nn l x H. rewrite <- (firstn_skipn nn l). apply in_or_app. left. exact H. Qed.
Lemma km_in_skipn : forall {A} o (l : list A) x, In x (skipn o l) -> In x l.
Proof. intros A o l x H. rewrite <- (firstn_skipn o l). apply in_or_app. right. exact H. Qed.

Lemma km_forall_sub : forall (P : Z -> Prop) (l : list Z) o nn, Forall P l ->
  Forall P (firstn nn (skipn o l)).
Proof.
  intros P l o nn H. apply Forall_forall. intros x Hx. rewrite Forall_forall in H. apply H.
  apply (km_in_skipn o). apply (km_in_firstn nn). exact Hx.
Qed.

Lemma km_firstn_S : forall (l : list Z) i, (i < length l)%nat ->
  firstn (S i) l = firstn i l ++ [nth i l 0].
Proof.
  induction l as [|x l IH]; intros [|i] Hi; cbn [length] in Hi; try lia.
  - reflexivity.
  - cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.

Lemma km_nth_firstn : forall (l : list Z) nn i, (i < nn)%nat -> nth i (firstn nn l) 0 = nth i l 0.
Proof.
  induction l as [|x l IH]; intros nn i Hi.
  - destruct nn as [|nn]; [lia|]. cbn [firstn]. reflexivity.
  - destruct nn as [|nn]; [lia|]. destruct i as [|i]; cbn [firstn nth]; [reflexivity|].
    apply IH. lia.
Qed.

Lemma km_zb_nth : forall (l : list Z) i, (i < length l)%nat ->
  firstn 1 (skipn i (zb l)) = [Z_to_bv 8 (nth i l 0)].
Proof.
  unfold zb. induction l as [|x l IH]; intros [|i] Hi; cbn [map skipn firstn length nth] in *;
    try lia; [reflexivity|]. apply IH. lia.
Qed.

Lemma km_zb_app : forall l1 l2, zb (l1 ++ l2) = zb l1 ++ zb l2.
Proof. unfold zb. intros l1 l2. apply map_app. Qed.

Lemma km_zb_len : forall l, length (zb l) = length l.
Proof. intros l. apply km_map_len. Qed.

(** ** Memory *)
Lemma km_read_byte : forall m a (l : list Z) i, bytes_at rsegs m a (zb l) -> (i < length l)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat i)) 1 = Some [Z_to_bv 8 (nth i l 0)].
Proof.
  intros m a l i HB Hi.
  rewrite (bytes_at_ov_read rsegs m a (zb l) i 1 HB) by (rewrite km_zb_len; lia).
  f_equal. apply km_zb_nth. exact Hi.
Qed.

Lemma km_read_all : forall m a bs, bytes_at rsegs m a bs ->
  ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs HB.
  pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) HB ltac:(lia)) as R.
  rewrite Z.add_0_r in R. cbn [skipn] in R. rewrite firstn_all in R. exact R.
Qed.

Lemma km_wr_at : forall m L Hi a nx, stk rsegs m L Hi -> L <= a -> a + nx <= Hi -> 0 <= nx ->
  wr_at rsegs m a nx.
Proof.
  intros m L Hi a nx (H1 & H2 & H) HL HH Hn. split; [lia|]. split; [lia|].
  intros i Hi'. apply (proj1 (H (a + i) ltac:(lia))).
Qed.

(** ** The fold loop 0x14508-0x14528
    At 0x14508 with a0 = A + i, a1 = A + nn, s4 = V + i, s7 = nn: it stores lower(vv[i]) at A + i and
    goes on until A + i + 1 = A + nn, then falls through to 0x1452c. *)
Lemma km_fold_loop :
  forall (L Hi A V : Z) (nn : nat) (vv : list Z) (m0 : word -> option byte) (P : machine_state -> Prop)
         (F' : bvmap 5 word) (fc' : bv 32)
         (ra sp' gp' tp' t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  (nn <= 23)%nat -> (nn <= length vv)%nat -> Forall (fun x => 0 <= x < 256) vv ->
  0 <= L -> L <= A -> A + 24 <= Hi -> Hi <= 2 ^ 64 ->
  0 <= V -> V + Z.of_nat nn < 2 ^ 64 -> (V + Z.of_nat nn <= L \/ Hi <= V) ->
  (forall (m2 : word -> option byte) (x10 x11 x12 x13 : word),
     bytes_at rsegs m2 A (zb (map lower (firstn nn vv))) ->
     munch [(A, A + 24)] m0 m2 -> wmono rsegs m0 m2 -> stk rsegs m2 L Hi -> mem_inv rsegs m2 ->
     evt rsegs P
       (MS (mkR ra sp' gp' tp' t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2 s3
                (Z_to_bv 64 (V + Z.of_nat nn)) s5 s6 (Z_to_bv 64 (Z.of_nat nn)) s8 s9 s10 s11 t3 t4 t5 t6)
           F' (Z_to_bv 64 0x1452c) fc' None m2 (seg_rom rsegs))) ->
  forall (jj ii : nat) (m1 : word -> option byte) (a2 a3 : word),
  (ii + jj = nn)%nat -> (0 < jj)%nat ->
  bytes_at rsegs m1 A (zb (map lower (firstn ii vv))) ->
  bytes_at rsegs m1 V (zb (firstn nn vv)) ->
  munch [(A, A + 24)] m0 m1 -> wmono rsegs m0 m1 -> stk rsegs m1 L Hi -> mem_inv rsegs m1 ->
  evt rsegs P
    (MS (mkR ra sp' gp' tp' t0 t1 t2 s0 s1 (Z_to_bv 64 (A + Z.of_nat ii)) (Z_to_bv 64 (A + Z.of_nat nn))
             a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (V + Z.of_nat ii)) s5 s6 (Z_to_bv 64 (Z.of_nat nn))
             s8 s9 s10 s11 t3 t4 t5 t6)
        F' (Z_to_bv 64 0x14508) fc' None m1 (seg_rom rsegs)).
Proof.
  intros L Hi A V nn vv m0 P F' fc' ra sp' gp' tp' t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 s10 s11
    t3 t4 t5 t6 Hnn Hnv HFA HL0 HLA HAH HH HV0 HVn HVA K.
  assert (LV : length (zb (firstn nn vv)) = nn).
  { rewrite km_zb_len, firstn_length. lia. }
  induction jj as [|jj IH]; intros ii m1 a2 a3 Hij Hjj BA BV MU WM ST MI; [lia|].
  assert (Hin : (ii < nn)%nat) by lia.
  assert (Hiv : (ii < length vv)%nat) by lia.
  assert (Lpre : length (zb (map lower (firstn ii vv))) = ii).
  { rewrite km_zb_len, km_map_len, firstn_length. lia. }
  assert (Hx : 0 <= nth ii vv 0 < 256).
  { rewrite Forall_forall in HFA. apply HFA. apply nth_In. lia. }
  pose proof (km_read_byte m1 V (firstn nn vv) ii BV ltac:(rewrite firstn_length; lia)) as RD.
  rewrite (km_nth_firstn vv nn ii Hin) in RD.
  pose proof (km_wr_at m1 L Hi A 24 ST HLA ltac:(lia) ltac:(lia)) as WR.
  pose proof (wr_at_store_ok rsegs m1 A 24 (Z.of_nat ii) 1 WR ltac:(lia) ltac:(lia)) as SO.
  assert (CONT : forall (y : Z) (z3 : word), 0 <= y < 2 ^ 64 -> y mod 256 = lower (nth ii vv 0) ->
    evt rsegs P
      (MS (mkR ra sp' gp' tp' t0 t1 t2 s0 s1 (Z_to_bv 64 (A + Z.of_nat ii)) (Z_to_bv 64 (A + Z.of_nat nn))
               (Z_to_bv 64 y) z3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (V + Z.of_nat ii)) s5 s6
               (Z_to_bv 64 (Z.of_nat nn)) s8 s9 s10 s11 t3 t4 t5 t6)
          F' (Z_to_bv 64 0x1451c) fc' None m1 (seg_rom rsegs))).
  { intros y z3 Hy Hyl.
    pose proof (lower_byte (nth ii vv 0) Hx) as [HLB _].
    step.
    rewrite (km_le1 y (lower (nth ii vv 0)) ltac:(lia) Hyl).
    (* the three register steps and the back branch *)
    step. step. step.
    rewrite (km_eqb (A + Z.of_nat ii + 1) (A + Z.of_nat nn) ltac:(lia) ltac:(lia)).
    assert (BA' : bytes_at rsegs (write_to_mem m1 (wa (A + Z.of_nat ii)) [Z_to_bv 8 (lower (nth ii vv 0))])
                    A (zb (map lower (firstn (S ii) vv)))).
    { rewrite (km_firstn_S vv ii Hiv), map_app, km_zb_app. cbn [map zb].
      apply (proj2 (bytes_at_app rsegs _ A _ _)). rewrite Lpre. split.
      - apply (bytes_at_write_other rsegs m1 (A + Z.of_nat ii) _ A _ BA); cbn [length]; [lia|lia|].
        rewrite Lpre. lia.
      - apply bytes_at_write_same; cbn [length]; lia. }
    assert (BV' : bytes_at rsegs (write_to_mem m1 (wa (A + Z.of_nat ii)) [Z_to_bv 8 (lower (nth ii vv 0))])
                    V (zb (firstn nn vv))).
    { apply (bytes_at_write_other rsegs m1 (A + Z.of_nat ii) _ V _ BV); cbn [length]; [lia|lia|].
      rewrite LV. lia. }
    assert (MU' : munch [(A, A + 24)] m0 (write_to_mem m1 (wa (A + Z.of_nat ii))
                                            [Z_to_bv 8 (lower (nth ii vv 0))])).
    { apply (munch_write _ m0 m1 (A + Z.of_nat ii)); cbn [length inside]; [exact MU|lia|lia|].
      left. lia. }
    assert (WM' : wmono rsegs m0 (write_to_mem m1 (wa (A + Z.of_nat ii))
                                     [Z_to_bv 8 (lower (nth ii vv 0))])) by (apply wmono_write; exact WM).
    assert (ST' : stk rsegs (write_to_mem m1 (wa (A + Z.of_nat ii)) [Z_to_bv 8 (lower (nth ii vv 0))]) L Hi).
    { apply stk_write; cbn [length]; [exact ST|lia|lia]. }
    assert (MI' : mem_inv rsegs (write_to_mem m1 (wa (A + Z.of_nat ii))
                                    [Z_to_bv 8 (lower (nth ii vv 0))])).
    { apply mem_inv_store; [exact MI|]. cbn [length]. exact SO. }
    destruct (Z.eqb_spec (A + Z.of_nat ii + 1) (A + Z.of_nat nn)) as [EE|EE]; cbn [negb]; cbv iota.
    - assert (ESi : (S ii = nn)%nat) by lia.
      replace (A + Z.of_nat ii + 1) with (A + Z.of_nat nn) by lia.
      replace (V + Z.of_nat ii + 1) with (V + Z.of_nat nn) by lia.
      apply K; [rewrite <- ESi; exact BA' | exact MU' | exact WM' | exact ST' | exact MI'].
    - replace (A + Z.of_nat ii + 1) with (A + Z.of_nat (S ii)) by lia.
      replace (V + Z.of_nat ii + 1) with (V + Z.of_nat (S ii)) by lia.
      apply IH; [lia | lia | exact BA' | exact BV' | exact MU' | exact WM' | exact ST' | exact MI']. }
  (* 0x14508-0x14518: the byte, the fold, into a2 *)
  step.
  unfold zxb. rewrite (km_u8 (nth ii vv 0) Hx).
  step. step.
  unfold v_sltiu. rewrite unsigned_lit_wrap.
  replace (bv_wrap 64 26) with 26 by (vm_compute; reflexivity).
  destruct ((nth ii vv 0 + -65) mod 2 ^ 64 <? 26) eqn:EB.
  - step. step. apply CONT; [lia | apply km_lower_hi; assumption].
  - step. step. apply CONT; [lia | apply km_lower_lo; assumption].
Qed.

(** ** The literal "model" at 0x10811 (.rodata) *)
Definition km_model_slack : list byte :=
  match image_bytes rsegs 0x10817 1 with Some l => l | None => [] end.
Definition km_model_bytes : list byte := zb S_model ++ ZERO :: km_model_slack.

Lemma km_model_ro : ro_bytes_b rsegs 0x10811 km_model_bytes = true.
Proof. vm_compute. reflexivity. Qed.

Lemma km_model_blen : length km_model_bytes = 7%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma km_model_nul : ~ In 0 S_model.
Proof. intros H. vm_compute in H. repeat (destruct H as [H|H]; [discriminate H|]). exact H. Qed.

Lemma km_model_cstr : forall mm, mem_inv rsegs mm -> cstr_at rsegs mm 0x10811 S_model.
Proof.
  intros mm MI.
  pose proof (ro_cells_image rsegs mm 0x10811 km_model_bytes MI km_model_ro ltac:(lia)
                ltac:(rewrite km_model_blen; lia)) as RO.
  destruct RO as [_ HB]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  unfold km_model_bytes in HB.
  exists (zb S_model), km_model_slack.
  split; [exact HB|]. split; [vm_compute; reflexivity|]. split; [exact km_model_nul|].
  replace (Z.of_nat (length km_model_slack)) with 1 by (vm_compute; reflexivity).
  replace ((- (0x10811 + Z.of_nat (length S_model) + 1)) mod 8) with 1 by (vm_compute; reflexivity).
  lia.
Qed.

(** ** Sub-ranges of a byte block *)
Lemma km_bat_sub : forall (mm : word -> option byte) a (l : list byte) kk nx,
  bytes_at rsegs mm a l -> (kk + nx <= length l)%nat ->
  bytes_at rsegs mm (a + Z.of_nat kk) (firstn nx (skipn kk l)).
Proof.
  intros mm a l kk nx H Hk.
  rewrite <- (firstn_skipn kk l) in H. apply bytes_at_app in H as [_ H].
  rewrite <- (firstn_skipn nx (skipn kk l)) in H. apply bytes_at_app in H as [H _].
  rewrite firstn_length_le in H by lia. exact H.
Qed.

Lemma km_cells : forall (mm : word -> option byte) a (bs : list byte) off len nz,
  bytes_at rsegs mm a bs -> wr_at rsegs mm a nz -> (off + len <= length bs)%nat ->
  Z.of_nat (off + len) <= nz ->
  rw_cells rsegs mm (a + Z.of_nat off) [CB len (firstn len (skipn off bs))].
Proof.
  intros mm a bs off len nz HB HW Hoff Hnz. split.
  - split.
    + cbn [cells_wf cell_wf]. split; [rewrite firstn_length, skipn_length; lia | exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. apply km_bat_sub; [exact HB | lia].
  - cbn [cells_size csize]. rewrite Nat.add_0_r.
    destruct HW as (H1 & H2 & H3). split; [lia|]. split; [lia|].
    intros i Hi. replace (a + Z.of_nat off + i) with (a + (Z.of_nat off + i)) by lia. apply H3. lia.
Qed.

(** ** upd_nth of the same index twice *)
Lemma km_upd_nth2 : forall (l : list mseg) i (f1 f2 : mseg -> mseg),
  upd_nth i f2 (upd_nth i f1 l) = upd_nth i (fun g => f2 (f1 g)) l.
Proof.
  induction l as [|x l IH]; intros [|i] f1 f2; cbn [upd_nth]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma km_upd_nth_ext : forall (l : list mseg) i (f1 f2 : mseg -> mseg),
  (forall g, f1 g = f2 g) -> upd_nth i f1 l = upd_nth i f2 l.
Proof.
  induction l as [|x l IH]; intros [|i] f1 f2 HE; cbn [upd_nth]; try reflexivity.
  - rewrite HE. reflexivity.
  - rewrite (IH i f1 f2 HE). reflexivity.
Qed.

Lemma km_firstn_min : forall (l : list Z) kk, firstn kk l = firstn (Nat.min kk (length l)) l.
Proof.
  induction l as [|x l IH]; intros [|kk]; cbn [firstn length Nat.min]; try reflexivity.
  f_equal. apply IH.
Qed.

Lemma km_outside_app : forall W1 W2 x, outside (W1 ++ W2) x -> outside W1 x /\ outside W2 x.
Proof.
  induction W1 as [|[a b] W1 IH]; intros W2 x H; cbn [app outside] in *; [split; [exact I|exact H]|].
  destruct H as [H1 H2]. destruct (IH W2 x H2) as [H3 H4]. split; [split; assumption | exact H4].
Qed.
Lemma km_sub_app_l : forall W1 W2, sub_fp W1 (W1 ++ W2).
Proof. intros W1 W2 x H. apply (km_outside_app W1 W2 x H). Qed.
Lemma km_sub_app_r : forall W1 W2, sub_fp W2 (W1 ++ W2).
Proof. intros W1 W2 x H. apply (km_outside_app W1 W2 x H). Qed.

Lemma km_consts : M_FILE_FRAME = 208 /\ M_FILE_STACK = 6160 /\ M_REFUSE_STACK = 5952 /\
  PRINTF_K = 5936 /\ SEG_M_SIZE = 9236 /\ MSEG_SIZE = 256 /\ sa_img_end SA = 0x536e8 /\
  MS_MODEL = 36 /\ MS_MODEL_SET = 32 /\ IEQ_STACK = 32 /\ FCR_STACK = 48.
Proof. repeat split; reflexivity. Qed.

(** ** The walk *)
Section KMod.
Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
Variables (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 sp : word).
Variables (m : word -> option byte) (lo c p line : Z) (mc : mconf) (gi k0 : nat) (rest : list Z).
Variables (ok kl ov vl : nat) (k v : list Z) (n : nat).

Hypothesis HT : H_MF_TAIL n.
Hypothesis Hn : (length rest <= n)%nat.
Hypothesis Hne : rest <> [].
Hypothesis HCTX : mf_ctx m fc (bv_unsigned sp0) (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Hypothesis HTXT : mf_text m (bv_unsigned sp0) lo c p rest.
Hypothesis HSTT : mf_st m (bv_unsigned sp) c mc (Some gi) k0 line rest.
Hypothesis HKV : mk_kv rest ok kl ov vl k v.
Hypothesis HROLE : ieq k S_role = false.

Local Notation KP MF :=
  (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0 MF).
Local Notation KWF :=
  [(bv_unsigned sp - M_REFUSE_STACK, bv_unsigned sp); (bv_unsigned sp + 0x28, bv_unsigned sp + 0x68)].

(** The numbers the walk needs. *)
Lemma km_b : sa_img_end SA <= lo /\ lo + M_FILE_STACK <= bv_unsigned sp0 /\ bv_unsigned sp0 < 2 ^ 63 /\
  bv_unsigned sp0 mod 16 = 0 /\ bv_unsigned sp mod 16 = 0 /\
  (c + SEG_M_SIZE + 4 <= lo \/ bv_unsigned sp0 <= c) /\ 0 < c /\ c + SEG_M_SIZE + 8 <= 2 ^ 64.
Proof. eapply mf_ctx_bounds. exact HCTX. Qed.

Lemma km_t : ~ In 0 rest /\ Forall (fun x => 0 <= x < 256) rest /\ 0 < p /\
  p + cstr_span p rest <= 2 ^ 64 /\ cstr_span p rest <= Z.of_nat (length rest) + 8.
Proof. eapply mf_text_props. exact HTXT. Qed.

Lemma km_line_le : (length (mf_line rest) <= length rest)%nat.
Proof.
  destruct (mf_line_rest rest) as [[E _]|[E _]]; pose proof (f_equal (@length Z) E) as LE;
    rewrite ?length_app in LE; cbn [length] in LE; lia.
Qed.

Lemma km_span1 : Z.of_nat (length rest) + 1 <= cstr_span p rest.
Proof.
  unfold cstr_span.
  pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length rest) + 1)) 8 ltac:(lia)). lia.
Qed.

Lemma km_kv : (ok + kl <= length rest)%nat /\ (ov + vl <= length rest)%nat /\
  length k = kl /\ length v = vl /\
  Forall (fun x => 0 <= x < 256) k /\ Forall (fun x => 0 <= x < 256) v /\ ~ In 0 v.
Proof.
  destruct HKV as (H1 & H2 & H3 & H4). pose proof km_line_le as HL.
  destruct km_t as (Hnul & HF & _).
  assert (Lk : length k = kl) by (rewrite <- H3, firstn_length, skipn_length; lia).
  assert (Lv : length v = vl) by (rewrite <- H4, firstn_length, skipn_length; lia).
  split; [lia|]. split; [lia|]. split; [exact Lk|]. split; [exact Lv|].
  split; [rewrite <- H3; apply km_forall_sub; exact HF|].
  split; [rewrite <- H4; apply km_forall_sub; exact HF|].
  rewrite <- H4. intros Hin. apply Hnul. apply (km_in_skipn ov). apply (km_in_firstn vl). exact Hin.
Qed.

Lemma km_low_eq : h_fold v 24 = map lower (firstn (Nat.min vl 23) v).
Proof.
  destruct km_kv as (_ & _ & _ & Lv & _). unfold h_fold. cbn [Nat.sub].
  rewrite (km_firstn_min v 23), Lv, Nat.min_comm. reflexivity.
Qed.

Lemma km_low_len : length (h_fold v 24) = Nat.min vl 23.
Proof.
  destruct km_kv as (_ & _ & _ & Lv & _). rewrite h_fold_length, Lv. cbn [Nat.sub]. reflexivity.
Qed.

Lemma km_low_props : ~ In 0 (h_fold v 24) /\ Forall (fun x => 0 <= x < 256) (h_fold v 24).
Proof.
  destruct km_kv as (_ & _ & _ & _ & _ & HFv & Hv0). apply h_fold_props; assumption.
Qed.

(** The stack region a callee of depth d gets. *)
Lemma km_sok : forall (ma : word -> option byte) (d : Z), 0 <= d <= M_REFUSE_STACK ->
  stack_ok rsegs ma lo (bv_unsigned sp0) M_FILE_STACK -> stack_ok rsegs ma lo (bv_unsigned sp) d.
Proof.
  intros ma d Hd (ST & HK & HA & HR).
  destruct km_b as (_ & _ & _ & _ & Hm16 & _).
  pose proof HCTX as HC0. destruct HC0 as (HSP & _).
  destruct km_consts as (Ca & Cb & Cc & Cd & Ce & Cf & Cg & Ch & Ci & Cj & Ck).
  destruct (stk_split rsegs ma lo (bv_unsigned sp) (bv_unsigned sp0) ST ltac:(lia)) as [S1 _].
  split; [exact S1|]. split; [lia|]. split; [exact Hm16|]. intros a Ha. apply HR. lia.
Qed.

(** Transport of the loop facts across a write inside the frame or inside the block. *)
Lemma km_tr : forall (ma mb : word -> option byte) (fca fcb : bv 32) (pa : bool) (mca : mconf) (W : list ivl),
  mf_ctx ma fca (bv_unsigned sp0) (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mf_text ma (bv_unsigned sp0) lo c p rest ->
  cell8 ma (bv_unsigned sp + 0x20) (cur_ptr c (Some gi)) ->
  mconf_atp rsegs pa ma c mca ->
  munch W ma mb -> wmono rsegs ma mb -> mem_inv rsegs mb -> frm0 fcb ->
  stk rsegs mb lo (bv_unsigned sp0) ->
  sub_fp W [(lo, bv_unsigned sp); (bv_unsigned sp + 0x20, bv_unsigned sp + 0x68); (c, c + SEG_M_SIZE)] ->
  disjoint_from W (bv_unsigned sp + 0x20) 8 ->
  mf_ctx mb fcb (bv_unsigned sp0) (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 /\
  mf_text mb (bv_unsigned sp0) lo c p rest /\
  cell8 mb (bv_unsigned sp + 0x20) (cur_ptr c (Some gi)).
Proof.
  intros ma mb fca fcb pa mca W HC HX HE HM MU WM MI FR ST SUB DJ.
  pose proof HC as HC0.
  destruct HC0 as (HSP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSOKa & _).
  destruct HSOKa as (_ & HKd & _ & _).
  destruct km_consts as (Ca & Cb & Cc & Cd & Ce & Cf & Cg & Ch & Ci & Cj & Ck).
  assert (TM : MemNorm.task_mem rsegs mb) by (eapply mf_task_mem; [exact HC | exact HM | exact MU | exact SUB]).
  split.
  { eapply mf_ctx_transport;
      [exact HC | exact MU | exact WM | exact MI | exact TM | exact FR | exact ST | exact SUB]. }
  split.
  - eapply mf_text_transport; [exact HX | exact MU |].
    assert (Hlos : lo <= bv_unsigned sp) by lia.
    assert (Hsps : bv_unsigned sp + 0x68 <= bv_unsigned sp0) by lia.
    eapply sub_fp_trans; [exact SUB|]. unfold sub_fp. cbn [outside]. intros x (H1 & H2 & _).
    split; [intros HH; apply H1; lia|].
    split; [intros HH; apply H1; lia|].
    split; [exact H2 | exact I].
  - eapply cell8_transport; [exact HE | exact MU | exact DJ].
Qed.

(** The join 0x14598: s7 := 9, then the tail. *)
Lemma km_tail : forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32) (mc' : mconf)
  (W1 : list ivl) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31 : word),
  mf_ctx m' fc' (bv_unsigned sp0) (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mf_text m' (bv_unsigned sp0) lo c p rest ->
  mconf_at rsegs m' c mc' -> cell8 m' (bv_unsigned sp + 0x20) (cur_ptr c (Some gi)) ->
  (gi < length (mc_seg mc'))%nat -> (k0 <= length (mc_kept mc'))%nat ->
  mc_refused mc' <= mc_refused mc + 1 -> mc_overflow mc' <= mc_overflow mc + 1 ->
  munch W1 m m' -> wmono rsegs m m' ->
  sub_fp W1 (M_FILE_W (bv_unsigned sp0) c k0 (mf_fin (mc', Some gi) line rest)) ->
  (forall kk : reg, bv_unsigned kk <> 10 -> reg_get F' kk = reg_get F kk) ->
  evt rsegs (KP (mf_fin (mc', Some gi) line rest))
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 0x3b) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) x20 x21 x22 x23 (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x23) (Z_to_bv 64 0x20) x28 x29 x30 x31)
        F' (Z_to_bv 64 0x14598) fc' None m' (seg_rom rsegs)).
Proof.
  intros m' F' fc' mc' W1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31
    HC HX HM HE Hcur Hk0 Href Hovf MU WM SUB HRG.
  pose proof HSTT as HS0.
  destruct HS0 as (_ & _ & _ & _ & Hline0 & Hline1 & Href0 & Hovf0).
  step. step.
  eapply mf_post_back; [exact HRG | exact MU | exact WM | exact SUB |].
  eapply HT.
  - pose proof (mf_rest_lt rest Hne). lia.
  - eapply mf_tail_loop;
      [exact HC | exact HX | exact Hne | exact HM | exact HE | exact Hcur | exact Hk0 | lia | lia
      | eapply mf_cnt_next; [exact Hne | exact Href0 | lia]
      | eapply mf_cnt_next; [exact Hne | exact Hovf0 | lia]].
  - unfold m_file_regs. repeat split; reflexivity.
Qed.

(** The frame part of the write list is inside M_FILE_W. *)
Lemma km_sub_wf : forall MF, sub_fp [(bv_unsigned sp - M_REFUSE_STACK, bv_unsigned sp);
                                     (bv_unsigned sp + 0x28, bv_unsigned sp + 0x68)]
                              (M_FILE_W (bv_unsigned sp0) c k0 MF).
Proof.
  intros MF. pose proof HCTX as HC0. destruct HC0 as (HSP & _).
  unfold sub_fp, M_FILE_W. cbn [outside]. intros x (H1 & _).
  destruct km_consts as (Ca & Cb & Cc & Cd & Ce & Cf & Cg & Ch & Ci & Cj & Ck).
  split; [lia|]. split; [lia|exact I].
Qed.

(** The refusal 0x1473c-0x14748 and its join. *)
Lemma km_refuse_join : m_refuse_contract ->
  forall (ma : word -> option byte) (fca : bv 32)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31 : word),
  mf_ctx ma fca (bv_unsigned sp0) (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mf_text ma (bv_unsigned sp0) lo c p rest ->
  cell8 ma (bv_unsigned sp + 0x20) (cur_ptr c (Some gi)) ->
  mconf_at rsegs ma c mc ->
  munch KWF m ma -> wmono rsegs m ma ->
  mk_disp mc gi k v (line + 1) = m_refuse mc (line + 1) false ->
  evt rsegs (KP (mf_fin (mk_disp mc gi k v (line + 1), Some gi) line rest))
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 0x3b) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) x20 x21 x22 x23 (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x23) (Z_to_bv 64 0x20) x28 x29 x30 x31)
        F (Z_to_bv 64 0x1473c) fca None ma (seg_rom rsegs)).
Proof.
  intros HREF ma fca x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31
    HC HX HE HM MU WM EQR.
  destruct km_b as (Himg & Hdep & Hs63 & Hm160 & Hm16 & Hcap & Hc0 & Hcb).
  pose proof HCTX as HC0. destruct HC0 as (HSP & _).
  pose proof HSTT as HS0. destruct HS0 as (_ & _ & Hcur0 & Hkk0 & Hline0 & Hline1 & Href0 & Hovf0).
  assert (Hr1 : (1 <= length rest)%nat) by (destruct rest; [congruence|cbn [length]; lia]).
  destruct km_consts as (Ca & Cb & Cc & Cd & Ce & Cf & Cg & Ch & Ci & Cj & Ck).
  rewrite EQR.
  step. step. step.
  eapply (mf_refuse_call HREF 0x14744);
    [lia | lia | reflexivity | exact HC | exact HX | exact HE | exact HM | lia | lia |].
  intros m' F' fc' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 HC' HX' HE' HM' MU' WM' HRG'.
  step.
  pose proof (m_refuse_sizes mc (line + 1) false) as [ES EK].
  eapply (km_tail m' F' fc' (m_refuse mc (line + 1) false)
            (KWF ++ m_refuse_W (bv_unsigned sp) c mc));
    [exact HC' | exact HX' | exact HM' | exact HE' | rewrite ES; exact Hcur0 | lia
    | unfold m_refuse; cbv zeta; cbn [mc_refused]; lia
    | unfold m_refuse; cbv zeta; cbn [mc_overflow]; lia
    | eapply (munch_trans _ m ma m');
        [eapply munch_weaken; [apply km_sub_app_l | exact MU]
        |eapply munch_weaken; [apply km_sub_app_r | exact MU']]
    | eapply wmono_trans; [exact WM | exact WM']
    | apply sub_fp_app;
        [apply km_sub_wf
        |eapply (sub_fp_trans _ (M_FILE_W (bv_unsigned sp0) c k0 (m_refuse mc (line + 1) false)));
           [apply mf_W_refuse; [lia | lia | exact Hkk0]
           |apply (mf_W_fin (bv_unsigned sp0) c k0 (m_refuse mc (line + 1) false, Some gi) line rest);
            cbn [fst snd]; unfold mf_cur_ok; rewrite ES; exact Hcur0]]
    | exact HRG'].
Qed.

(** The two edits of entry gi are one. *)
Lemma km_model_upd : m_upd (m_upd mc gi (ms_set_model (h_fold v 24))) gi (ms_set_model_set true)
                   = m_upd mc gi (ms_with_model (h_fold v 24)).
Proof.
  unfold m_upd, m_set_segs. cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  f_equal. rewrite km_upd_nth2. apply km_upd_nth_ext. intros g. symmetry. apply ms_with_model_eq.
Qed.

(** The hit 0x14548-0x14564: memcpy of the model into cur, then model_set = 1. *)
Lemma km_hit_join : memcpy_contract ->
  forall (ma : word -> option byte) (fca : bv 32)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31 : word),
  mf_ctx ma fca (bv_unsigned sp0) (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mf_text ma (bv_unsigned sp0) lo c p rest ->
  cell8 ma (bv_unsigned sp + 0x20) (cur_ptr c (Some gi)) ->
  mconf_at rsegs ma c mc ->
  bytes_at rsegs ma (bv_unsigned sp + 40) (zb (h_fold v 24) ++ [ZERO]) ->
  munch KWF m ma -> wmono rsegs m ma ->
  mk_disp mc gi k v (line + 1) = m_upd mc gi (ms_with_model (h_fold v 24)) ->
  evt rsegs (KP (mf_fin (mk_disp mc gi k v (line + 1), Some gi) line rest))
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 0x3b) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) x20 x21 x22
             (Z_to_bv 64 (Z.of_nat (Nat.min vl 23))) (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x23) (Z_to_bv 64 0x20) x28 x29 x30 x31)
        F (Z_to_bv 64 0x14548) fca None ma (seg_rom rsegs)).
Proof.
  intros HCPY ma fca x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31
    HC HX HE HM HB MU WM EQH.
  destruct km_b as (Himg & Hdep & Hs63 & Hm160 & Hm16 & Hcap & Hc0 & Hcb).
  pose proof HCTX as HC0. destruct HC0 as (HSP & _).
  pose proof HSTT as HS0. destruct HS0 as (_ & _ & Hcur0 & Hkk0 & Hline0 & Hline1 & Href0 & Hovf0).
  destruct km_low_props as (Hlow0 & HlowF). pose proof km_low_len as LL.
  destruct km_consts as (Ca & Cb & Cc & Cd & Ce & Cf & Cg & Ch & Ci & Cj & Ck).
  pose proof HC as HCa.
  destruct HCa as (_ & _ & _ & _ & _ & _ & _ & _ & HWRa & _ & _ & HPEa & HCATa & _ & HSOKa & HMIa).
  destruct HPEa as (HFRMa & _). destruct HSOKa as (STa & HKa & HMa16 & HROMa).
  destruct (mconf_atp_bytes rsegs false ma c mc HM) as (bs & HBS & HENC & HLEN).
  destruct (mconf_enc_bounds false mc bs HENC) as (_ & Hn32 & _).
  assert (HLZ : Z.of_nat (length bs) = 9236) by (rewrite HLEN; vm_compute; reflexivity).
  assert (Hgib : (gi < 32)%nat) by (cbn [cur_ok] in Hcur0; lia).
  assert (Hga : c <= mseg_addr c gi /\ mseg_addr c gi + 256 <= c + 9236).
  { clear - Hgib Hc0. unfold mseg_addr, MSEG_SIZE. lia. }
  destruct Hga as (Hga0 & Hga1).
  rewrite EQH.
  pose proof (km_read_all ma (bv_unsigned sp + 0x20) (le8 (Z_to_bv 64 (mseg_addr c gi))) HE) as RD.
  rewrite length_le8 in RD.
  step. step. step. step. step.
  eapply evt_cut.
  { eapply HCPY with (src := zb (h_fold v 24) ++ [ZERO])
      (junk := firstn (Nat.min vl 23 + 1) (skipn (256 * gi + 36) bs)).
    - rewrite unsigned_lit by lia. exact HB.
    - rewrite unsigned_lit by lia. rewrite length_app, km_zb_len, LL. cbn [length]. lia.
    - rewrite !unsigned_lit by lia.
      replace (Z.to_nat (Z.of_nat (Nat.min vl 23) + 1)) with (Nat.min vl 23 + 1)%nat by lia.
      replace (mseg_addr c gi + 36) with (c + Z.of_nat (256 * gi + 36))
        by (unfold mseg_addr, MSEG_SIZE; lia).
      eapply (km_cells ma c bs (256 * gi + 36) (Nat.min vl 23 + 1) SEG_M_SIZE HBS HWRa);
        [clear - HLZ Hgib; lia | clear - Hgib; unfold SEG_M_SIZE; lia].
    - rewrite !unsigned_lit by lia.
      destruct Hcap as [Hcl|Hcr];
        [right; clear - Hga0 Hga1 Hcl Ce Hdep HSP Ca Cb Hc0
        |left; clear - Hga0 Hcr HSP Ca Hc0]; lia.
    - exact HMIa. }
  intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m4 & -> &
              MU4 & WM4 & MI4 & RW4 & BS4).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !unsigned_lit in MU4 by lia.
  assert (BD4 : bytes_at rsegs m4 (mseg_addr c gi + 36) (zb (h_fold v 24) ++ [ZERO])).
  { destruct RW4 as [[_ HBB] _]. cbn [cells_bytes cbytes] in HBB. rewrite app_nil_r in HBB.
    rewrite unsigned_lit in HBB by lia. exact HBB. }
  assert (LN : Z.of_nat (length (zb (h_fold v 24) ++ [ZERO])) = Z.of_nat (Nat.min vl 23) + 1).
  { rewrite length_app, km_zb_len, LL. cbn [length]. lia. }
  assert (HM4 : mconf_atp rsegs false m4 c (m_upd mc gi (ms_set_model (h_fold v 24)))).
  { eapply (mconf_atp_upd rsegs false false ma m4 c mc (m_upd mc gi (ms_set_model (h_fold v 24)))
              (mseg_addr c gi + 36) (zb (h_fold v 24) ++ [ZERO]));
      [exact HM | exact MU4 | | exact BD4 | lia | lia |].
    - intros x Hx Hnx. cbn [outside] in Hnx. rewrite LN.
      destruct (Z_le_gt_dec (mseg_addr c gi + 36) x) as [H1|H1];
        [|exfalso; apply Hnx; split; [lia|exact I]].
      destruct (Z_lt_ge_dec x (mseg_addr c gi + 36 + (Z.of_nat (Nat.min vl 23) + 1))) as [H2|H2];
        [lia|exfalso; apply Hnx; split; [lia|exact I]].
    - intros bs0 Hbs0.
      replace (Z.to_nat (mseg_addr c gi + 36 - c)) with (256 * gi + 36)%nat
        by (unfold mseg_addr, MSEG_SIZE; lia).
      apply (mconf_enc_seg false mc bs0 gi (ms_set_model (h_fold v 24)) 36
               (zb (h_fold v 24) ++ [ZERO]) Hbs0 Hcur0);
        [rewrite length_app, km_zb_len, LL; cbn [length]; lia|].
      intros fb Hfb. apply (mseg_enc_model _ fb (h_fold v 24) Hfb);
        [rewrite LL; lia | exact Hlow0 | exact HlowF]. }
  assert (WR4 : wr_at rsegs m4 c SEG_M_SIZE) by (eapply wr_at_transport; [exact HWRa | exact WM4]).
  assert (SOw : store_ok rsegs m4 (wa (mseg_addr c gi + 32)) 4 = true).
  { replace (mseg_addr c gi + 32) with (c + (256 * Z.of_nat gi + 32))
      by (unfold mseg_addr, MSEG_SIZE; lia).
    apply (wr_at_store_ok rsegs m4 c SEG_M_SIZE (256 * Z.of_nat gi + 32) 4 WR4);
      [lia | unfold SEG_M_SIZE; lia]. }
  step. step.
  assert (HM5 : mconf_atp rsegs false
                  (write_to_mem m4 (wa (mseg_addr c gi + 32)) (le4 (Z_to_bv 64 1))) c
                  (m_upd mc gi (ms_with_model (h_fold v 24)))).
  { rewrite <- km_model_upd.
    eapply (mconf_atp_store rsegs false false m4 c (m_upd mc gi (ms_set_model (h_fold v 24)))
              (m_upd (m_upd mc gi (ms_set_model (h_fold v 24))) gi (ms_set_model_set true))
              (mseg_addr c gi + 32) (le4 (Z_to_bv 64 1)));
      [exact HM4 | lia | rewrite length_le4; unfold SEG_M_SIZE; lia |].
    intros bs0 Hbs0.
    replace (Z.to_nat (mseg_addr c gi + 32 - c)) with (256 * gi + 32)%nat
      by (unfold mseg_addr, MSEG_SIZE; lia).
    apply (mconf_enc_seg false (m_upd mc gi (ms_set_model (h_fold v 24))) bs0 gi
             (ms_set_model_set true) 32 (le4 (Z_to_bv 64 1)) Hbs0);
      [unfold m_upd, m_set_segs; cbn [mc_seg]; rewrite upd_nth_length; exact Hcur0
      |rewrite length_le4; lia|].
    intros fb Hfb. exact (mseg_enc_model_set _ fb true Hfb). }
  assert (MUE : munch [(mseg_addr c gi + 0, mseg_addr c gi + 0 + 256)] ma
                  (write_to_mem m4 (wa (mseg_addr c gi + 32)) (le4 (Z_to_bv 64 1)))).
  { apply (munch_write _ ma m4 (mseg_addr c gi + 32));
      [eapply munch_weaken; [|exact MU4]; unfold sub_fp; cbn [outside]; intros y (Hy & _);
       split; [lia|exact I]
      |lia | rewrite length_le4; lia | cbn [inside]; rewrite length_le4; left; lia]. }
  assert (WME : wmono rsegs ma (write_to_mem m4 (wa (mseg_addr c gi + 32)) (le4 (Z_to_bv 64 1))))
    by (apply wmono_write; exact WM4).
  assert (MIE : mem_inv rsegs (write_to_mem m4 (wa (mseg_addr c gi + 32)) (le4 (Z_to_bv 64 1)))).
  { apply mem_inv_store; [exact MI4|]. rewrite length_le4. exact SOw. }
  assert (STE : stk rsegs (write_to_mem m4 (wa (mseg_addr c gi + 32)) (le4 (Z_to_bv 64 1))) lo
                  (bv_unsigned sp0)).
  { apply stk_write; [|lia|rewrite length_le4; lia].
    eapply stk_transport_disjoint; [exact STa | exact MU4 | exact WM4 |].
    cbn [disjoint_from]. split; [destruct Hcap as [Hcl|Hcr]; lia | exact I]. }
  destruct (km_tr ma _ fca fca false mc _ HC HX HE HM MUE WME MIE HFRMa STE
              ltac:(unfold sub_fp; cbn [outside]; intros y (_ & _ & Hy & _);
                    split; [lia | exact I])
              ltac:(cbn [disjoint_from]; split; [destruct Hcap as [Hcl|Hcr]; lia | exact I]))
    as (HCe & HXe & HEe).
  step.
  eapply (km_tail _ F fca (m_upd mc gi (ms_with_model (h_fold v 24)))
            (KWF ++ [(mseg_addr c gi + 0, mseg_addr c gi + 0 + 256)]));
    [exact HCe | exact HXe | exact HM5 | exact HEe
    | unfold m_upd, m_set_segs; cbn [mc_seg]; rewrite upd_nth_length; exact Hcur0
    | unfold m_upd, m_set_segs; cbn [mc_kept]; exact Hkk0
    | unfold m_upd, m_set_segs; cbn [mc_refused]; lia
    | unfold m_upd, m_set_segs; cbn [mc_overflow]; lia
    | eapply (munch_trans _ m ma _);
        [eapply munch_weaken; [apply km_sub_app_l | exact MU]
        |eapply munch_weaken; [apply km_sub_app_r | exact MUE]]
    | eapply wmono_trans; [exact WM | exact WME]
    | apply sub_fp_app;
        [apply km_sub_wf
        |eapply (sub_fp_trans _ (M_FILE_W (bv_unsigned sp0) c k0
                                   (m_upd mc gi (ms_with_model (h_fold v 24)))));
           [apply mf_W_seg;
              [unfold m_upd, m_set_segs; cbn [mc_seg]; rewrite upd_nth_length; exact Hcur0
              |lia | unfold MSEG_SIZE; lia]
           |apply (mf_W_fin (bv_unsigned sp0) c k0
                     (m_upd mc gi (ms_with_model (h_fold v 24)), Some gi) line rest);
            cbn [fst snd]; unfold mf_cur_ok, m_upd, m_set_segs; cbn [mc_seg];
            rewrite upd_nth_length; exact Hcur0]]
    | intros kk Hkk; reflexivity].
Qed.

(** fuzz_catalogue_row's answer on the folded value, in the spine's terms. *)
Lemma km_rowptr : row_ptr FUZZ_CATALOGUE (zb (h_fold v 24))
                = cat_ptr FUZZ_CATALOGUE (cat_row (h_fold v 24)).
Proof.
  destruct km_low_props as (Hn0 & HF0).
  rewrite (row_ptr_by_token FUZZ_CATALOGUE (zb (h_fold v 24)))
    by (rewrite (km_zszb _ HF0); exact Hn0).
  rewrite (km_zszb _ HF0). unfold by_token. rewrite (cut_nul_id _ Hn0). reflexivity.
Qed.

(** 0x1452c-0x14544: the NUL after the fold, fuzz_catalogue_row, and its two answers. *)
Lemma km_after_fold : fuzz_catalogue_row_contract -> memcpy_contract -> m_refuse_contract ->
  ieq k S_model = true ->
  forall (ma : word -> option byte) (fca : bv 32)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
  mf_ctx ma fca (bv_unsigned sp0) (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mf_text ma (bv_unsigned sp0) lo c p rest ->
  cell8 ma (bv_unsigned sp + 0x20) (cur_ptr c (Some gi)) ->
  mconf_at rsegs ma c mc ->
  bytes_at rsegs ma (bv_unsigned sp + 40) (zb (h_fold v 24)) ->
  munch KWF m ma -> wmono rsegs m ma ->
  evt rsegs (KP (mf_fin (mk_disp mc gi k v (line + 1), Some gi) line rest))
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 0x3b) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1))
             (Z_to_bv 64 (p + Z.of_nat ov + Z.of_nat (Nat.min vl 23))) x21 x22
             (Z_to_bv 64 (Z.of_nat (Nat.min vl 23))) (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x23) (Z_to_bv 64 0x20) x28 x29 x30 x31)
        F (Z_to_bv 64 0x1452c) fca None ma (seg_rom rsegs)).
Proof.
  intros HFCR HCPY HREF EM ma fca x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31
    HC HX HE HM HB MU WM.
  destruct km_b as (Himg & Hdep & Hs63 & Hm160 & Hm16 & Hcap & Hc0 & Hcb).
  destruct km_consts as (Ca & Cb & Cc & Cd & Ce & Cf & Cg & Ch & Ci & Cj & Ck).
  pose proof HCTX as HC0. destruct HC0 as (HSP & _).
  destruct km_low_props as (Hlow0 & HlowF). pose proof km_low_len as LL.
  assert (LZ : length (zb (h_fold v 24)) = Nat.min vl 23) by (rewrite km_zb_len; exact LL).
  pose proof HC as HCa.
  destruct HCa as (_ & _ & _ & _ & _ & _ & _ & _ & HWRa & _ & _ & HPEa & HCATa & _ & HSOKa & HMIa).
  pose proof HPEa as HPE1. destruct HPE1 as (HFRMa & _).
  pose proof HSOKa as HSOK1. destruct HSOK1 as (STa & HKa & HMa16 & HROMa).
  pose proof (km_wr_at ma lo (bv_unsigned sp0) (bv_unsigned sp + 40) 24 STa
                ltac:(lia) ltac:(lia) ltac:(lia)) as WRf.
  pose proof (wr_at_store_ok rsegs ma (bv_unsigned sp + 40) 24 (Z.of_nat (Nat.min vl 23)) 1 WRf
                ltac:(lia) ltac:(lia)) as SOf.
  step. step. step.
  rewrite (km_le1 0 0 ltac:(lia) ltac:(reflexivity)).
  assert (BA2 : bytes_at rsegs
                  (write_to_mem ma (wa (bv_unsigned sp + 40 + Z.of_nat (Nat.min vl 23))) [ZERO])
                  (bv_unsigned sp + 40) (zb (h_fold v 24) ++ [ZERO])).
  { apply (proj2 (bytes_at_app rsegs _ (bv_unsigned sp + 40) (zb (h_fold v 24)) [ZERO])).
    rewrite LZ. split.
    - eapply bytes_at_write_other;
        [exact HB | lia | cbn [length]; lia | cbn [length]; rewrite LZ; lia].
    - apply bytes_at_write_same; cbn [length]; lia. }
  assert (BA1 : bytes_at rsegs
                  (write_to_mem ma (wa (bv_unsigned sp + 40 + Z.of_nat (Nat.min vl 23))) [ZERO])
                  (bv_unsigned sp + 40) (zb (h_fold v 24)))
    by (apply (proj1 (proj1 (bytes_at_app rsegs _ (bv_unsigned sp + 40) (zb (h_fold v 24)) [ZERO]) BA2))).
  assert (MU2 : munch [(bv_unsigned sp + 0x28, bv_unsigned sp + 0x68)] ma
                  (write_to_mem ma (wa (bv_unsigned sp + 40 + Z.of_nat (Nat.min vl 23))) [ZERO])).
  { apply (munch_write _ ma ma (bv_unsigned sp + 40 + Z.of_nat (Nat.min vl 23)));
      [apply munch_refl | lia | cbn [length]; lia | cbn [inside length]; left; lia]. }
  assert (WM2 : wmono rsegs ma
                  (write_to_mem ma (wa (bv_unsigned sp + 40 + Z.of_nat (Nat.min vl 23))) [ZERO]))
    by (apply wmono_write; apply wmono_refl).
  assert (MI2 : mem_inv rsegs
                  (write_to_mem ma (wa (bv_unsigned sp + 40 + Z.of_nat (Nat.min vl 23))) [ZERO]))
    by (apply mem_inv_store; [exact HMIa | cbn [length]; exact SOf]).
  assert (ST2 : stk rsegs
                  (write_to_mem ma (wa (bv_unsigned sp + 40 + Z.of_nat (Nat.min vl 23))) [ZERO])
                  lo (bv_unsigned sp0))
    by (apply stk_write; [exact STa | lia | cbn [length]; lia]).
  assert (HM2 : mconf_atp rsegs false
                  (write_to_mem ma (wa (bv_unsigned sp + 40 + Z.of_nat (Nat.min vl 23))) [ZERO]) c mc).
  { eapply mconf_atp_transport;
      [exact HM | exact MU2
      |cbn [disjoint_from]; split; [clear - Hcap Ce Hdep HSP Ca Cb; lia | exact I]]. }
  destruct (km_tr ma _ fca fca false mc _ HC HX HE HM MU2 WM2 MI2 HFRMa ST2
              ltac:(unfold sub_fp; cbn [outside]; intros y (_ & Hy & _ & _);
                    split; [lia | exact I])
              ltac:(cbn [disjoint_from]; split; [lia | exact I])) as (HC2 & HX2 & HE2).
  pose proof HC2 as HC2a.
  destruct HC2a as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HCAT2 & _).
  step. step. step.
  eapply evt_cut.
  { eapply HFCR with (sb := zb (h_fold v 24)) (lo := lo).
    - rewrite unsigned_lit by lia. exact BA1.
    - rewrite unsigned_lit by lia. rewrite LZ. reflexivity.
    - destruct (stk_split rsegs _ lo (bv_unsigned sp) (bv_unsigned sp0) ST2 ltac:(lia)) as [S1 _].
      exact S1.
    - lia.
    - intros aa Haa. apply HROMa. lia.
    - rewrite unsigned_lit by lia. rewrite LZ. right. lia.
    - intros aa Haa. apply HCAT2. exact Haa.
    - exact MI2. }
  intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & -> &
              MU3 & WM3 & MI3 & ST3).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite km_rowptr.
  assert (MUa3 : munch KWF m m3).
  { eapply (munch_trans _ m ma m3); [exact MU|].
    eapply (munch_trans _ ma _ m3).
    - eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside].
      intros y (_ & Hy & _). split; [lia | exact I].
    - eapply munch_weaken; [|exact MU3]. unfold sub_fp. cbn [outside].
      intros y (Hy & _). split; [lia | exact I]. }
  assert (WMa3 : wmono rsegs m m3)
    by (eapply wmono_trans; [exact WM | eapply wmono_trans; [exact WM2 | exact WM3]]).
  assert (ST3' : stk rsegs m3 lo (bv_unsigned sp0)).
  { eapply mf_stk_after;
      [exact ST2 | exact MU3 | exact WM3 | exact ST3 | lia
      |cbn [disjoint_from]; split; [lia | exact I]]. }
  destruct (km_tr _ m3 fca fca false mc _ HC2 HX2 HE2 HM2 MU3 WM3 MI3 HFRMa ST3'
              ltac:(unfold sub_fp; cbn [outside]; intros y (Hy & _ & _ & _); split; [lia | exact I])
              ltac:(cbn [disjoint_from]; split; [lia | exact I])) as (HC3 & HX3 & HE3).
  assert (HM3 : mconf_atp rsegs false m3 c mc).
  { eapply mconf_atp_transport;
      [exact HM2 | exact MU3
      |cbn [disjoint_from]; split; [clear - Hcap Ce Hdep HSP Ca Cb Ck; lia | exact I]]. }
  destruct (cat_row (h_fold v 24)) as [ri|] eqn:ECR.
  - assert (Hri : (ri < CAT_N)%nat).
    { pose proof (stb_row_of (zb (h_fold v 24))) as SR.
      rewrite (km_zszb _ HlowF), ECR in SR.
      destruct (row_of_some _ _ SR) as (H1 & _). exact H1. }
    cbn [cat_ptr]. step.
    rewrite (km_eqb (FUZZ_CATALOGUE + CAT_ROW * Z.of_nat ri) 0)
      by (clear - Hri; unfold FUZZ_CATALOGUE, CAT_ROW, CAT_N in *; lia).
    replace (FUZZ_CATALOGUE + CAT_ROW * Z.of_nat ri =? 0) with false
      by (symmetry; apply Z.eqb_neq; clear - Hri; unfold FUZZ_CATALOGUE, CAT_ROW, CAT_N in *; lia).
    cbv iota.
    eapply km_hit_join;
      [exact HCPY | exact HC3 | exact HX3 | exact HE3 | exact HM3
      |eapply bytes_at_transport;
         [exact BA2 | exact MU3
         |cbn [disjoint_from]; rewrite length_app, LZ; cbn [length]; split; [lia | exact I]]
      | exact MUa3 | exact WMa3
      |unfold mk_disp; rewrite HROLE, EM; cbv zeta; rewrite ECR; reflexivity].
  - cbn [cat_ptr]. step. rewrite (km_eqb 0 0) by lia. cbn [Z.eqb]. cbv iota.
    eapply km_refuse_join;
      [exact HREF | exact HC3 | exact HX3 | exact HE3 | exact HM3 | exact MUa3 | exact WMa3
      |unfold mk_disp; rewrite HROLE, EM; cbv zeta; rewrite ECR; reflexivity].
Qed.

(** 0x144d4-0x14528: ieq "model", the clamp of the length, the fold. *)
Lemma km_body : ieq_contract -> fuzz_catalogue_row_contract -> memcpy_contract -> m_refuse_contract ->
  H_MF_KIGN n ->
  forall (ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word),
  evt rsegs (KP (mf_fin (mk_disp mc gi k v (line + 1), Some gi) line rest))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 0x3b) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) (Z_to_bv 64 (p + Z.of_nat ov))
             (Z_to_bv 64 (p + Z.of_nat ok)) (Z_to_bv 64 (p + Z.of_nat (ov + vl)))
             (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 (Z.of_nat kl)) (Z_to_bv 64 BLANK_MASK)
             (Z_to_bv 64 0x23) (Z_to_bv 64 0x20) t3 t4 t5 t6)
        F (Z_to_bv 64 MF_PC_KMODEL) fc None m (seg_rom rsegs)).
Proof.
  intros HIEQ HFCR HCPY HREF HKI ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6.
  destruct km_b as (Himg & Hdep & Hs63 & Hm160 & Hm16 & Hcap & Hc0 & Hcb).
  destruct km_consts as (Ca & Cb & Cc & Cd & Ce & Cf & Cg & Ch & Ci & Cj & Ck).
  destruct km_t as (Hnul & HFR & Hp0 & Hspan & Hspan8). pose proof km_span1 as Hsp1.
  destruct km_kv as (Hok & Hov & Lk & Lv & HFk & HFv & Hv0).
  pose proof HCTX as HC0.
  destruct HC0 as (HSP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPE0 & _ & _ & HSOK0 & HMI0).
  pose proof HPE0 as HPE1. destruct HPE1 as (HFRM0 & _).
  pose proof HSTT as HS0.
  destruct HS0 as (HMC0 & HCELL0 & Hcur0 & Hkk0 & Hline0 & Hline1 & Href0 & Hovf0).
  pose proof HTXT as HX0. destruct HX0 as (Hpne & _ & _ & HAPp & HAPc).
  pose proof HSOK0 as HSOK1. destruct HSOK1 as (ST0 & HK0 & HM016 & HROM0).
  unfold MF_PC_KMODEL.
  step. step. step. step. step.
  eapply evt_cut.
  { eapply HIEQ with (l := zb k) (w := S_model) (lo := lo).
    unfold ieq_pre. rewrite !unsigned_lit by lia.
    split; [lia|].
    split.
    { pose proof (mf_text_bytes m (bv_unsigned sp0) lo c p rest ok kl HTXT ltac:(lia)) as BK.
      destruct HKV as (_ & _ & Ek & _). rewrite Ek in BK. exact BK. }
    split; [rewrite km_zb_len, Lk; reflexivity|].
    split; [unfold apart in *; destruct HAPp as [Hl|Hr]; [left; lia | right; lia]|].
    split; [lia|].
    split; [apply km_model_cstr; exact HMI0|].
    split.
    { unfold apart. left.
      replace (Z.of_nat (length S_model)) with 5 by (vm_compute; reflexivity). lia. }
    split; [apply (km_sok m 32); [lia | exact HSOK0]|].
    exact HMI0. }
  intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> &
              MU1 & WM1 & MI1 & ST1 & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite (km_zszb k HFk).
  assert (ST1' : stk rsegs m1 lo (bv_unsigned sp0)).
  { eapply mf_stk_after;
      [exact ST0 | exact MU1 | exact WM1 | exact ST1 | lia
      |cbn [disjoint_from]; split; [lia | exact I]]. }
  assert (HM1 : mconf_atp rsegs false m1 c mc).
  { eapply mconf_atp_transport;
      [exact HMC0 | exact MU1
      |cbn [disjoint_from]; split; [clear - Hcap Ce Hdep HSP Ca Cb Cj; lia | exact I]]. }
  destruct (km_tr m m1 fc fc false mc _ HCTX HTXT HCELL0 HMC0 MU1 WM1 MI1 HFRM0 ST1'
              ltac:(unfold sub_fp; cbn [outside]; intros y (Hy & _ & _ & _); split; [lia | exact I])
              ltac:(cbn [disjoint_from]; split; [lia | exact I])) as (HC1 & HX1 & HE1).
  assert (MU1W : munch KWF m m1).
  { eapply munch_weaken; [|exact MU1]. unfold sub_fp. cbn [outside].
    intros y (Hy & _). split; [lia | exact I]. }
  step.
  destruct (ieq k S_model) eqn:EM.
  - cbn [b2z]. rewrite (km_eqb 1 0) by lia. cbn [Z.eqb]. cbv iota.
    assert (CONT : forall (y10 : word),
      evt rsegs (KP (mf_fin (mk_disp mc gi k v (line + 1), Some gi) line rest))
        (MS (mkR (Z_to_bv 64 0x144e8) sp gp tp u0 u1 u2 (Z_to_bv 64 c) (Z_to_bv 64 0x3b) y10 b1 b2 b3
                 b4 b5 b6 b7 (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1))
                 (Z_to_bv 64 (p + Z.of_nat ov)) (Z_to_bv 64 (p + Z.of_nat ok))
                 (Z_to_bv 64 (p + Z.of_nat (ov + vl))) (Z_to_bv 64 (Z.of_nat (Nat.min vl 23)))
                 (Z_to_bv 64 0x1ff) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x23) (Z_to_bv 64 0x20)
                 u3 u4 u5 u6)
            F (Z_to_bv 64 0x144fc) fc None m1 (seg_rom rsegs))).
    { intros y10.
      step.
      rewrite (km_eqb (p + Z.of_nat (ov + vl)) (p + Z.of_nat ov)) by lia.
      destruct (Z.eqb_spec (p + Z.of_nat (ov + vl)) (p + Z.of_nat ov)) as [E0|E0]; cbv iota.
      - assert (Hvl0 : vl = 0%nat) by lia.
        replace (Z_to_bv 64 (p + Z.of_nat ov)) with
          (Z_to_bv 64 (p + Z.of_nat ov + Z.of_nat (Nat.min vl 23))) by (f_equal; lia).
        eapply km_after_fold;
          [exact HFCR | exact HCPY | exact HREF | exact EM | exact HC1 | exact HX1 | exact HE1
          | exact HM1
          |rewrite km_low_eq, Hvl0; cbn [Nat.min firstn map]; unfold zb; cbn [map];
           apply bytes_at_nil; lia
          | exact MU1W | exact WM1].
      - step. step.
        replace (Z_to_bv 64 (bv_unsigned sp + 40)) with
          (Z_to_bv 64 (bv_unsigned sp + 40 + Z.of_nat 0)) by (f_equal; lia).
        replace (Z_to_bv 64 (p + Z.of_nat ov)) with
          (Z_to_bv 64 (p + Z.of_nat ov + Z.of_nat 0)) by (f_equal; lia).
        eapply (km_fold_loop lo (bv_unsigned sp0) (bv_unsigned sp + 40) (p + Z.of_nat ov)
                  (Nat.min vl 23) v m1);
          [lia | lia | exact HFv | lia | lia | lia | lia | lia | lia
          |destruct HAPp as [Hl|Hr]; [left; lia | right; lia]
          | | reflexivity | lia
          |cbn [firstn map]; unfold zb; cbn [map]; apply bytes_at_nil; lia
          | | apply munch_refl | apply wmono_refl | exact ST1' | exact MI1].
        + intros m2 y10' y11 y12 y13 BAf MUf WMf STf MIf.
          assert (HM2 : mconf_atp rsegs false m2 c mc).
          { eapply mconf_atp_transport;
              [exact HM1 | exact MUf
              |cbn [disjoint_from]; split; [clear - Hcap Ce Hdep HSP Ca Cb; lia | exact I]]. }
          destruct (km_tr m1 m2 fc fc false mc _ HC1 HX1 HE1 HM1 MUf WMf MIf HFRM0 STf
                      ltac:(unfold sub_fp; cbn [outside]; intros y (_ & Hy & _ & _);
                            split; [lia | exact I])
                      ltac:(cbn [disjoint_from]; split; [lia | exact I])) as (HC2 & HX2 & HE2).
          eapply km_after_fold;
            [exact HFCR | exact HCPY | exact HREF | exact EM | exact HC2 | exact HX2 | exact HE2
            | exact HM2 | rewrite km_low_eq; exact BAf
            |eapply (munch_trans _ m m1 m2);
               [exact MU1W
               |eapply munch_weaken; [|exact MUf]; unfold sub_fp; cbn [outside];
                intros y (_ & Hy & _); split; [lia | exact I]]
            |eapply wmono_trans; [exact WM1 | exact WMf]].
        + assert (EV : firstn (Nat.min vl 23) v = firstn (Nat.min vl 23) (skipn ov rest)).
          { destruct HKV as (_ & _ & _ & Ev). rewrite <- Ev, firstn_firstn. f_equal. lia. }
          rewrite EV.
          apply (mf_text_bytes m1 (bv_unsigned sp0) lo c p rest ov (Nat.min vl 23) HX1). lia. }
    step. step.
    rewrite (km_ltu (Z.of_nat vl) 23) by lia.
    destruct (Z.ltb_spec (Z.of_nat vl) 23) as [HV|HV]; cbv iota.
    + step. replace (Z.of_nat vl) with (Z.of_nat (Nat.min vl 23)) by lia. apply CONT.
    + step. step.
      replace (Z_to_bv 64 23) with (Z_to_bv 64 (Z.of_nat (Nat.min vl 23))) by (f_equal; lia).
      apply CONT.
  - cbn [b2z]. rewrite (km_eqb 0 0) by lia. cbn [Z.eqb]. cbv iota.
    eapply mf_post_back with (F1 := F) (m1 := m1)
      (W1 := [(bv_unsigned sp - IEQ_STACK, bv_unsigned sp)]);
      [intros kk Hkk; reflexivity | exact MU1 | exact WM1 | apply mf_W_frame; lia |].
    eapply HKI;
      [exact Hn | exact Hne
      |apply (proj2 (mf_loop_iff m1 fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc (Some gi) line k0
                       rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11));
       split; [exact HC1 | split; [exact HX1 |
         split; [exact HM1 | split; [exact HE1 | split; [exact Hcur0 | split; [exact Hkk0 |
         split; [exact Hline0 | split; [exact Hline1 | split; [exact Href0 | exact Hovf0]]]]]]]]]
      |unfold mk_regs; repeat split; reflexivity
      |exact HKV
      |repeat constructor; assumption].
Qed.

End KMod.

(** The sub-piece: KMODEL -> KIGN or TAIL. *)
Lemma mf_kmod_holds :
  ieq_contract -> fuzz_catalogue_row_contract -> memcpy_contract -> m_refuse_contract -> S_MF_KMOD.
Proof.
  intros HI HF HC HR n HT HKI.
  unfold H_MF_KMODEL, H_MF_KAT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m lo ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc gi k0 rest
    ok kl ov vl k v Hn Hne HL HRG HKV HM.
  apply (proj1 (mf_loop_iff m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc (Some gi) line k0 rest
                  ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)) in HL.
  destruct HL as (HCTX & HTXT & HSTT).
  destruct HRG as (E0 & E1 & E2 & E3 & E9 & E10 & E11 & E5 & E8 & E4 & E7 & E6).
  subst s0 s1 s2 s3 s9 s10 s11 s5 s8 s4 s7 s6.
  eapply km_body; try eassumption.
  exact (Forall_inv HM).
Qed.
