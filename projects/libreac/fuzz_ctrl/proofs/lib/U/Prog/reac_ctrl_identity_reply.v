From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcKind RcParse RcParseLib RcReply RcReplyLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import reac_ctrl_identity_reply_c reac_ctrl_parse_c
  reac_ctrl_record_cksum_verify_c.
Import ListNotations.
Open Scope Z_scope.

Ltac mem_after_store_opt ::=
  try rewrite rc_le1_zxb;
  try fix_lit_store;
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

(* The UBSan pointer-overflow tests compare against 2^64 - c (the literal -c). *)
Lemma u_ltu_negr : forall x y, 0 <= x -> -2^64 < y < 0 -> x < 2^64 + y ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof.
  intros x y Hx Hy Hxy. unfold bv_ltu. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  apply Z.ltb_lt. change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma u_ltu_negl : forall x y, 0 <= x -> -2^64 < y < 0 -> x <= 2^64 + y ->
  bv_ltu (Z_to_bv 64 y) (Z_to_bv 64 x) = false.
Proof.
  intros x y Hx Hy Hxy. unfold bv_ltu. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  apply Z.ltb_ge. change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma u_land1 : forall x, x mod 2 = 0 -> 0 <= x < 2^64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 x)) 1) = Z_to_bv 64 0.
Proof.
  intros x H R. rewrite unsigned_lit by lia. change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
  change (2^1) with 2. rewrite H. reflexivity.
Qed.

Lemma u_land7 : forall x, x mod 8 = 0 -> 0 <= x < 2^64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 x)) 7) = Z_to_bv 64 0.
Proof.
  intros x H R. rewrite unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia.
  change (2^3) with 8. rewrite H. reflexivity.
Qed.

Lemma u_eqb_m1 : bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0) = false.
Proof. unfold bv_eqb. rewrite !unsigned_lit_wrap. reflexivity. Qed.

(* The block sum loop 0x14c68 .. 0x14c7c: a2 and a3 both walk from A to A + c (a1); a0 sums the bytes. *)
Lemma loopU : forall (Q : machine_state -> Prop)
  (r1 r2 r3 r4 r5 r6 r7 r8 r9 e r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word)
  (Ff : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A : Z) (bs : list byte) (c : nat),
  bytes_at rsegs m A bs -> length bs = c -> 0 < A -> A + Z.of_nat c <= 2^64 ->
  e = Z_to_bv 64 (A + Z.of_nat c) ->
  (forall x4, evt rsegs Q
     (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 (Z_to_bv 64 (psum bs c)) e (Z_to_bv 64 (A + Z.of_nat c))
              (Z_to_bv 64 (A + Z.of_nat c)) x4 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
         Ff (Z_to_bv 64 0x14c80) fc None m (seg_rom rsegs))) ->
  forall n i p s x4, (i + n = c)%nat -> (0 < n)%nat -> p = A + Z.of_nat i -> s = psum bs i ->
  evt rsegs Q
     (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 (Z_to_bv 64 s) e (Z_to_bv 64 p) (Z_to_bv 64 p) x4
              r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
         Ff (Z_to_bv 64 0x14c68) fc None m (seg_rom rsegs)).
Proof.
  intros Q r1 r2 r3 r4 r5 r6 r7 r8 r9 e r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31
    Ff fc m A bs c HB Hl HA HAc He HK.
  subst e.
  induction n as [|n IH]; intros i p s x4 Hin Hn Hp Hs; [lia|]. subst p s.
  pose proof (rd_byte rsegs m A bs i HB ltac:(lia)) as RD.
  pose proof (psum_range bs i) as PR.
  step.
  rewrite (rc_beq0_false (A + Z.of_nat i)) by lia. cbv iota.
  do 5 step.
  rewrite psum_S_zxb.
  rewrite (eqb_le64 (A + Z.of_nat i + 1) (A + Z.of_nat c)) by lia.
  destruct n as [|n].
  - replace (A + Z.of_nat i + 1 =? A + Z.of_nat c) with true by (symmetry; apply Z.eqb_eq; lia).
    cbn [negb]. replace (A + Z.of_nat i + 1) with (A + Z.of_nat c) by lia.
    replace (S i) with c by lia. apply HK.
  - replace (A + Z.of_nat i + 1 =? A + Z.of_nat c) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [negb]. apply (IH (S i)); lia.
Qed.

Section P.
Hypothesis PARSE : reac_ctrl_parse_contract.
Hypothesis CKV : reac_ctrl_record_cksum_verify_contract.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Ff : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (fr len pa pp pn S : Z) (g : list byte).
Hypothesis Hfr : 0 <= fr < 2^64.
Hypothesis Hlen : 0 <= len < 2^64.
Hypothesis Hpa : 0 <= pa < 2^64.
Hypothesis Hpp : 0 <= pp < 2^64.
Hypothesis Hpn : 0 <= pn < 2^64.
Hypothesis HS : 176 <= S < 2^64.
Hypothesis HS16 : S mod 16 = 0.
Hypothesis Hg : length g = 50%nat.

Ltac parse_post :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO; destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  let STc := fresh "STc" in let HOc := fresh "HOc" in
  destruct PO as [E [MUc [WMc [MIc [STc HOc]]]]]; subst ms';
  lazymatch type of MUc with
  | munch _ ?m ?m' =>
      unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MUc, STc;
      rewrite (proj2 (Z.eqb_neq (S + -92) 0) ltac:(lia)) in MUc; cbn [app] in MUc;
      specialize (HOc ltac:(lia));
      lazymatch goal with
      | ST : stk rsegs m (S - 176) S |- _ =>
          let ST' := fresh "ST" in
          assert (ST' : stk rsegs m' (S - 176) S)
            by (eapply rc_stk_after; [exact ST | exact MUc | exact WMc |];
                intros zq Hzq;
                destruct (Z.ltb_spec zq (S - 96));
                [ right; eapply rc_stk_mrd; [exact STc | lia]
                | destruct (Z.ltb_spec zq (S + -92));
                  [ left; cbn [outside]; lia
                  | destruct (Z.ltb_spec zq (S + -56));
                    [ right; eapply rc_rw_mrd; [exact HOc | lia]
                    | left; cbn [outside]; lia ] ] ]);
          clear ST
      end;
      clear STc;
      transport_after_call rsegs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv rsegs m |- _ => clear H end;
      try clear m
  end;
  replace (ret_pc (Z_to_bv 64 0x14bac)) with (Z_to_bv 64 0x14bac)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).

Ltac parse_call :=
  eapply evt_cut; [eapply PARSE|];
  [ reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | lia | lia
  | unfold REAC_CTRL_PARSE_K; lia
  | unfold REAC_CTRL_PARSE_K;
    match goal with |- stk _ _ ?a ?b =>
      replace a with (S - 176) by lia; replace b with (S - 96) by lia; assumption end
  | assumption
  | exact Hg
  | unfold REAC_CTRL_PARSE_K; intros; lia
  | first [ apply rc_rd_of_bytes; [exact Hg | intros _; assumption]
          | intros i Hi; exfalso; unfold cp_rd in Hi; rewrite (proj2 (Z.leb_gt 50 len) ltac:(lia)) in Hi;
            destruct Hi ]
  | intros _; unfold REAC_CTRL_PARSE_K;
    split; [lia|]; split; [lia|]; split; [eassumption|]; split; [lia|]; intros; lia
  | parse_post ].

Definition Qr : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (reply_ret fr len pa pp pn g))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             Ff (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch (reac_ctrl_identity_reply_fp fr len pa pp pn S g) m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    stk rsegs m' (S - REAC_CTRL_IDENTITY_REPLY_K) S /\
    (reply_ok fr len pa pp pn g = true ->
       rw_cells rsegs m' pa [CB 2 (reply_addr g)] /\
       rw_cells rsegs m' pp [CB 8 (le8 (Z_to_bv 64 (fr + 38)))] /\
       rw_cells rsegs m' pn [CB 8 (le8 (Z_to_bv 64 (ir_s g - 13)))]).

Lemma L_epi : forall (rr t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word) m r,
  munch (reac_ctrl_identity_reply_fp fr len pa pp pn S g) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m (S - 176) S ->
  rw_cells rsegs m (S + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  (reply_ok fr len pa pp pn g = true ->
       rw_cells rsegs m pa [CB 2 (reply_addr g)] /\
       rw_cells rsegs m pp [CB 8 (le8 (Z_to_bv 64 (fr + 38)))] /\
       rw_cells rsegs m pn [CB 8 (le8 (Z_to_bv 64 (ir_s g - 13)))]) ->
  r = reply_ret fr len pa pp pn g ->
  evt rsegs Qr
    (MS (mkR rr (Z_to_bv 64 (S + -96)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Ff (Z_to_bv 64 0x14ca4) fc None m (seg_rom rsegs)).
Proof.
  intros rr t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 m r MU WM MI ST HR HO Er.
  do 9 step.
  try replace (S + -96 + 96) with S by lia.
  apply evt_done. unfold Qr. subst r.
  do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [|exact HO].
  unfold REAC_CTRL_IDENTITY_REPLY_K. exact ST.
Qed.

Lemma fp_no : forall m, reply_ok fr len pa pp pn g = false -> munch [(S - 176, S)] m0 m ->
  munch (reac_ctrl_identity_reply_fp fr len pa pp pn S g) m0 m.
Proof. intros m H MU. unfold reac_ctrl_identity_reply_fp, REAC_CTRL_IDENTITY_REPLY_K. rewrite H. exact MU. Qed.

Lemma fp_yes : forall m, reply_ok fr len pa pp pn g = true ->
  munch [(pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (S - 176, S)] m0 m ->
  munch (reac_ctrl_identity_reply_fp fr len pa pp pn S g) m0 m.
Proof. intros m H MU. unfold reac_ctrl_identity_reply_fp, REAC_CTRL_IDENTITY_REPLY_K. rewrite H. exact MU. Qed.

Lemma L_ret0 : forall (rr t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word) m,
  reply_args fr pa pp pn = true -> ir len g = false ->
  munch [(S - 176, S)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m (S - 176) S ->
  rw_cells rsegs m (S + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  evt rsegs Qr
    (MS (mkR rr (Z_to_bv 64 (S + -96)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Ff (Z_to_bv 64 0x14ca4) fc None m (seg_rom rsegs)).
Proof.
  intros rr t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 m RA EI MU WM MI ST HR.
  assert (OK : reply_ok fr len pa pp pn g = false) by (unfold reply_ok; rewrite RA, EI; reflexivity).
  eapply L_epi; try eassumption.
  - apply fp_no; assumption.
  - intros H. rewrite OK in H. discriminate.
  - unfold reply_ret. rewrite RA, EI. reflexivity.
Qed.

Ltac irf := apply L_ret0; try assumption;
  let E := fresh "EIR" in
  destruct (ir len g) eqn:E; [exfalso; apply ir_true in E; destruct E as (? & ? & ? & ? & ? & ? & ? & ? & ?); lia
                             | reflexivity].

Ltac cv := repeat match goal with
  | |- context [bv_unsigned (cp_b g ?i)] => change (bv_unsigned (cp_b g i)) with (cp_v g i)
  | |- context [bv_unsigned (nth ?i g (Z_to_bv 8 0))] => change (bv_unsigned (nth i g (Z_to_bv 8 0))) with (cp_v g i)
  end;
  try change (cp_v g 26) with (ir_s g).

(* A UBSan pointer test `li a0,-c; bltu a0,s4` with s4 = fr + 18: not taken. *)
Ltac ubn c := step; step; rewrite (u_ltu_negl (fr + 18) c) by lia; cbv iota.

(* An alignment test `andi; bnez` that is not taken. *)
Ltac alz lem x := rewrite (lem x) by lia.
Ltac bnz0 := rewrite (rc_eqb64 0 0) by lia; change (0 =? 0) with true; cbn [negb]; cbv iota.

Definition outp (m : word -> option byte) : Prop :=
  exists ja jp jn,
  rw_cells rsegs m pa [CB 2 ja] /\ rw_cells rsegs m pp [CB 8 jp] /\ rw_cells rsegs m pn [CB 8 jn] /\
  (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
  (pa + 2 <= S - 176 \/ S <= pa) /\ (pp + 8 <= S - 176 \/ S <= pp) /\ (pn + 8 <= S - 176 \/ S <= pn).

Lemma L_long : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (jr js : list byte),
  reply_args fr pa pp pn = true -> 50 <= len ->
  fr + 50 <= 2^64 -> (fr + 50 <= S - 176 \/ S <= fr) ->
  pa mod 2 = 0 -> pp mod 8 = 0 -> pn mod 8 = 0 ->
  stk rsegs m0 (S - 176) S -> mem_inv rsegs m0 -> bytes_at rsegs m0 fr g ->
  rw_cells rsegs m0 (S + -56) [CB 56 jr] -> rw_cells rsegs m0 (S + -92) [CB 36 js] ->
  stk rsegs m0 (S - 176) (S - 96) -> outp m0 ->
  evt rsegs Qr
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fr) (Z_to_bv 64 len) (Z_to_bv 64 pa)
             (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Ff (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 jr js RAb Hl50 Hf50 HfS Ha2 Hp8 Hn8 ST MI HB HR HP STp OUTP.
  unfold REAC_CTRL_IDENTITY_REPLY.
  pose proof (munch_refl [(S - 176, S)] m0) as MU.
  pose proof (wmono_refl rsegs m0) as WM.
  pose proof RAb as RA.
  unfold reply_args in RA. rewrite !andb_true_iff, !negb_true_iff, !Z.eqb_neq in RA.
  destruct RA as [[[Rf Ra] Rp] Rn].
  do 11 step.
  rewrite (rc_beq0_false fr Rf) by lia. cbv iota. step. step.
  rewrite (rc_beq0_false pa Ra) by lia. cbv iota. step. step.
  rewrite (rc_beq0_false pp Rp) by lia. cbv iota. step. step.
  rewrite (rc_beq0_false pn Rn) by lia. cbv iota. step. step. step.
  parse_call.
  pose proof (ctrlparse_kind_range len g) as KR.
  do 4 step.
  rewrite (rc_eqb64 (fst (ctrlparse len g)) 5) by lia.
  zdec (fst (ctrlparse len g)) 5.
  2:{ irf. }
  destruct (ctrlparse_rec len g ltac:(lia)) as (HD & HRC & N28 & N29).
  pose proof (ctrlparse_length len g) as LB.
  pose proof (cp_v_range' g 32). pose proof (cp_v_range' g 33). pose proof (cp_v_range' g 34).
  pose proof (cp_v_range' g 35). pose proof (cp_v_range' g 26) as Rs. pose proof (cp_v_range' g 27).
  apply (rc_rw_rebytes rsegs _ (S + -92) _
           [CB 28 (firstn 28 (snd (ctrlparse len g))); C2 (Z_to_bv 64 (cp_v g 34 * 256 + cp_v g 35));
            CB 6 (skipn 30 (snd (ctrlparse len g)))]) in HOc.
  2:{ cbn [cells_wf cell_wf]. rewrite firstn_length_le, length_skipn, LB by lia. repeat split. }
  2:{ cbn [cells_bytes cbytes]. unfold cp_v. rewrite rc_le2_pair. rewrite !app_nil_r. rewrite <- N28, <- N29.
      symmetry. apply rc_b36_split. exact LB. }
  pose proof (rc_ro_of_bytes rsegs _ fr g HB) as RO. rewrite Hg in RO. cbn [map seq] in RO.
  clear N28 N29 HD LB.
  step. unfold zx16. rewrite (unsigned_lit (cp_v g 34 * 256 + cp_v g 35)) by lia.
  rewrite (Z.mod_small (cp_v g 34 * 256 + cp_v g 35)) by lia.
  step. step.
  rewrite (rc_eqb64 (cp_v g 34 * 256 + cp_v g 35) 1280) by lia.
  zdec (cp_v g 34 * 256 + cp_v g 35) 1280.
  2:{ irf. }
  (* 0x14bc8: fr >= 2^64 - 18 traps *)
  step. step. rewrite (u_ltu_negr fr (-18)) by lia. cbn [negb]. cbv iota.
  step. ubn (-15).
  do 3 step. rewrite (rc_eqb_zxb (cp_b g 32) 18) by lia. cv. zdec (cp_v g 32) 18.
  2:{ step. irf. }
  ubn (-16).
  do 3 step. rewrite (rc_eqb_zxb (cp_b g 33) 18) by lia. cv. zdec (cp_v g 33) 18.
  2:{ step. irf. }
  ubn (-9).
  do 2 step. rewrite rc_uzxb. cv. step. step.
  rewrite (rc_srange (ir_s g)) by exact Rs.
  destruct ((14 <=? ir_s g) && (ir_s g <=? 23)) eqn:SR; cbn [negb]; cbv iota.
  2:{ rewrite andb_false_iff, Z.leb_gt, Z.leb_gt in SR. step. irf. }
  rewrite andb_true_iff, Z.leb_le, Z.leb_le in SR.
  step. rewrite (u_ltu_negl (fr + 18) (-10)) by lia. cbv iota.
  do 3 step. rewrite (rc_eqb_zxb (cp_b g 27) 240) by lia. cv. zdec (cp_v g 27) 240.
  2:{ step. irf. }
  (* 0x14c24: ~(fr + 18) < s + 8 traps *)
  step. step. rewrite ?rc_uzxb. cv.
  try rewrite (unsigned_lit (fr + 18)) by lia. rewrite (zb_lxor_ones (fr + 18)) by lia.
  step. rewrite (rc_ltu64 (18446744073709551615 - (fr + 18)) (ir_s g + 8)) by lia.
  replace (18446744073709551615 - (fr + 18) <? ir_s g + 8) with false by (symmetry; apply Z.ltb_ge; lia).
  cbv iota.
  pose proof (rd_byte rsegs _ fr g (Z.to_nat (26 + ir_s g)) HB ltac:(lia)) as RD8.
  step. step. step. step.
  match goal with |- context [zxb (nth ?i g (Z_to_bv 8 0))] =>
    rewrite (rc_eqb_zxb (nth i g (Z_to_bv 8 0)) 247) by lia end.
  cv. zdec (cp_v g (Z.to_nat (26 + ir_s g))) 247.
  2:{ step. irf. }
  clear RD8.
  (* 0x14c40: the inlined block checksum; its bound min(2^64 - 18 - fr, 31) is 31 *)
  step. step. step. step.
  match goal with |- context [bv_ltu ?X (Z_to_bv 64 31)] =>
    let Hm := fresh "Hm" in
    assert (Hm : bv_ltu X (Z_to_bv 64 31) = false)
      by (unfold bv_ltu; rewrite ?unsigned_lit_wrap; apply Z.ltb_ge;
          change (2^64) with 18446744073709551616 in *; Z.div_mod_to_equations; lia);
    rewrite Hm; clear Hm; cbv iota end.
  do 6 step.
  pose proof (rc_bytes_skip rsegs _ fr g 18 HB ltac:(lia)) as HBk. change (skipn 18 g) with (ir_blk g) in HBk.
  assert (LBk : length (ir_blk g) = 32%nat) by (unfold ir_blk; rewrite length_skipn, Hg; reflexivity).
  change (Z.of_nat 18) with 18 in HBk.
  eapply loopU with (A := fr + 18) (bs := ir_blk g) (c := 32%nat) (n := 32%nat) (i := 0%nat);
    [ exact HBk | exact LBk | lia | lia | f_equal; lia | | reflexivity | lia | lia | reflexivity ].
  intros xb4.
  pose proof (psum_range (ir_blk g) 32) as PB. change (Z.of_nat 32) with 32 in PB.
  remember (psum (ir_blk g) 32) as ps eqn:Eps.
  step. step.
  rewrite (rc_zb0 ps) by lia.
  replace (ps mod 256) with (blocksum (ir_blk g)) by (unfold blocksum; rewrite Eps; reflexivity).
  zdec (blocksum (ir_blk g)) 0.
  2:{ step. irf. }
  clear Eps PB.
  (* 0x14c88: the record checksum, a call in this build *)
  ubn (-17).
  step. step. step. rewrite ?rc_uzxb. cv.
  pose proof (rc_bytes_skip rsegs _ fr g 34 HB ltac:(lia)) as HBr.
  apply (rc_bytes_first rsegs _ _ _ (Z.to_nat (ir_s g - 8))) in HBr. change (Z.of_nat 34) with 34 in HBr.
  change (firstn (Z.to_nat (ir_s g - 8)) (skipn 34 g)) with (ir_rec g) in HBr.
  pose proof (rc_len_rec g Hg ltac:(lia)) as LRr.
  eapply evt_cut.
  { eapply CKV with (bs := ir_rec g).
    - rewrite unsigned_lit by lia. rewrite LRr. first [reflexivity | f_equal; lia].
    - right. rewrite !unsigned_lit by lia. split; [lia|]. split; [lia|]. exact HBr. }
  intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & E). subst ms'.
  replace (ret_pc (Z_to_bv 64 0x14c9c)) with (Z_to_bv 64 0x14c9c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct (Z.eqb_spec (recsum (ir_rec g)) 0) as [B6|B6]; cbv iota.
  2:{ step. rewrite u_eqb_m1. cbv iota. step. irf. }
  step. rewrite (rc_beq0_true 0 eq_refl). cbv iota.
  assert (EIR : ir len g = true).
  { unfold ir. rewrite B, B0, B1, B2, B3, B4, B5, B6.
    rewrite (proj2 (Z.leb_le 14 (ir_s g)) ltac:(lia)), (proj2 (Z.leb_le (ir_s g) 23) ltac:(lia)). reflexivity. }
  assert (OKr : reply_ok fr len pa pp pn g = true) by (unfold reply_ok; rewrite RAb, EIR; reflexivity).
  clear HB HBk HBr HOc HfS.
  destruct OUTP as (ja & jp & jn & HPA0 & HPP0 & HPN0 & D1 & D2 & D3 & D7 & D8 & D9).
  pose proof (rw_cells_transport rsegs _ m0 _ pa _ HPA0 MU WM
                ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as HPA.
  pose proof (rw_cells_transport rsegs _ m0 _ pp _ HPP0 MU WM
                ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as HPP.
  pose proof (rw_cells_transport rsegs _ m0 _ pn _ HPN0 MU WM
                ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as HPN.
  pose proof (rw_cells_bound _ _ _ _ HPA0) as BPA. pose proof (rw_cells_bound _ _ _ _ HPP0) as BPP.
  pose proof (rw_cells_bound _ _ _ _ HPN0) as BPN.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in BPA, BPP, BPN.
  clear HPA0 HPP0 HPN0.
  apply (munch_weaken [(S - 176, S)] [(pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (S - 176, S)]) in MU;
    [|unfold sub_fp; cbn [outside]; intros; tauto].
  (* 0x14cc8: block + 18, + 19 tests; pa alignment; the stores, each after its test *)
  ubn (-19). ubn (-20).
  step. alz u_land1 pa. step. bnz0.
  step. step. clear RO. do 4 step.
  step. rewrite (u_ltu_negl (fr + 18) (-21)) by lia. cbv iota.
  step. alz u_land7 pp. step. bnz0.
  step. step. alz u_land7 pn. step. step. bnz0.
  step. rewrite ?rc_uzxb. cv. step. step. step.
  apply (rc_rw_flat rsegs _ pa _ (reply_addr g)) in HPA;
    [|cbn [cells_bytes cbytes]; rewrite app_nil_r, rc_le2_pack; reflexivity].
  apply (rc_rw_flat rsegs _ pp _ (le8 (Z_to_bv 64 (fr + 38)))) in HPP; [|cbn [cells_bytes cbytes]; apply app_nil_r].
  replace (ir_s g + -13) with (ir_s g - 13) in HPN by lia.
  apply (rc_rw_flat rsegs _ pn _ (le8 (Z_to_bv 64 (ir_s g - 13)))) in HPN; [|cbn [cells_bytes cbytes]; apply app_nil_r].
  rewrite length_le8 in HPP, HPN.
  eapply L_epi; try eassumption.
  - apply fp_yes; assumption.
  - intros _. split; [exact HPA|]. split; assumption.
  - unfold reply_ret. rewrite RAb, EIR. reflexivity.
Qed.

Lemma L_short : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (jr js : list byte),
  reply_args fr pa pp pn = true -> len < 50 ->
  stk rsegs m0 (S - 176) S -> mem_inv rsegs m0 ->
  rw_cells rsegs m0 (S + -56) [CB 56 jr] -> rw_cells rsegs m0 (S + -92) [CB 36 js] ->
  stk rsegs m0 (S - 176) (S - 96) ->
  evt rsegs Qr
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fr) (Z_to_bv 64 len) (Z_to_bv 64 pa)
             (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Ff (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 jr js RAb Hl50 ST MI HR HP STp.
  unfold REAC_CTRL_IDENTITY_REPLY.
  pose proof (munch_refl [(S - 176, S)] m0) as MU.
  pose proof (wmono_refl rsegs m0) as WM.
  pose proof RAb as RA.
  unfold reply_args in RA. rewrite !andb_true_iff, !negb_true_iff, !Z.eqb_neq in RA.
  destruct RA as [[[Rf Ra] Rp] Rn].
  do 11 step.
  rewrite (rc_beq0_false fr Rf) by lia. cbv iota. step. step.
  rewrite (rc_beq0_false pa Ra) by lia. cbv iota. step. step.
  rewrite (rc_beq0_false pp Rp) by lia. cbv iota. step. step.
  rewrite (rc_beq0_false pn Rn) by lia. cbv iota. step. step. step.
  parse_call.
  assert (K0 : fst (ctrlparse len g) = 0) by (apply ctrlparse_none; lia).
  do 4 step.
  rewrite K0. cbv iota.
  irf.
Qed.

Lemma L_null : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (jr : list byte),
  reply_args fr pa pp pn = false ->
  stk rsegs m0 (S - 176) S -> mem_inv rsegs m0 -> rw_cells rsegs m0 (S + -56) [CB 56 jr] ->
  evt rsegs Qr
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fr) (Z_to_bv 64 len) (Z_to_bv 64 pa)
             (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Ff (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 jr RAb ST MI HR.
  unfold REAC_CTRL_IDENTITY_REPLY.
  pose proof (munch_refl [(S - 176, S)] m0) as MU.
  pose proof (wmono_refl rsegs m0) as WM.
  assert (OK : reply_ok fr len pa pp pn g = false) by (unfold reply_ok; rewrite RAb; reflexivity).
  assert (RV : -1 = reply_ret fr len pa pp pn g) by (unfold reply_ret; rewrite RAb; reflexivity).
  do 11 step.
  destruct (Z.eq_dec fr 0) as [Z0|Z0].
  { rewrite (rc_beq0_true fr Z0). cbv iota.
    eapply L_epi; try eassumption; [apply fp_no; assumption | intros H; rewrite OK in H; discriminate]. }
  rewrite (rc_beq0_false fr Z0) by lia. cbv iota. step. step.
  destruct (Z.eq_dec pa 0) as [Z1|Z1].
  { rewrite (rc_beq0_true pa Z1). cbv iota.
    eapply L_epi; try eassumption; [apply fp_no; assumption | intros H; rewrite OK in H; discriminate]. }
  rewrite (rc_beq0_false pa Z1) by lia. cbv iota. step. step.
  destruct (Z.eq_dec pp 0) as [Z2|Z2].
  { rewrite (rc_beq0_true pp Z2). cbv iota.
    eapply L_epi; try eassumption; [apply fp_no; assumption | intros H; rewrite OK in H; discriminate]. }
  rewrite (rc_beq0_false pp Z2) by lia. cbv iota. step. step.
  destruct (Z.eq_dec pn 0) as [Z3|Z3].
  { rewrite (rc_beq0_true pn Z3). cbv iota.
    eapply L_epi; try eassumption; [apply fp_no; assumption | intros H; rewrite OK in H; discriminate]. }
  exfalso. unfold reply_args in RAb.
  rewrite (proj2 (Z.eqb_neq fr 0) Z0), (proj2 (Z.eqb_neq pa 0) Z1), (proj2 (Z.eqb_neq pp 0) Z2),
    (proj2 (Z.eqb_neq pn 0) Z3) in RAb. discriminate.
Qed.

End P.

Theorem reac_ctrl_identity_reply_holds :
  reac_ctrl_parse_contract -> reac_ctrl_record_cksum_verify_contract -> reac_ctrl_identity_reply_contract.
Proof.
  intros PARSE CKV. unfold reac_ctrl_identity_reply_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Ff fc m fr len pa pp pn S g ja jp jn -> -> -> -> -> -> Hfr Hlen Hpa Hpp Hpn HS1 HS16 HSK ST MI Hg HF HO.
  unfold REAC_CTRL_IDENTITY_REPLY_K in HSK, ST, HF, HO.
  destruct (stk_carve rsegs m (S - 176) S 56 ST ltac:(lia)) as [ST1 [jr HR]].
  replace (S - Z.of_nat 56) with (S + -56) in HR by lia.
  destruct (stk_carve rsegs m (S - 176) (S - Z.of_nat 56) 36 ST1 ltac:(lia)) as [ST2 [js HP]].
  replace (S - Z.of_nat 56 - Z.of_nat 36) with (S + -92) in HP by lia.
  destruct (stk_split rsegs m (S - 176) (S - 96) (S - Z.of_nat 56 - Z.of_nat 36) ST2 ltac:(lia)) as [STp _].
  destruct (reply_args fr pa pp pn) eqn:RA.
  - destruct (Z.ltb_spec len 50) as [Hl|Hl].
    + eapply L_short; first [eassumption | lia].
    + destruct (HF eq_refl Hl) as (Hf50 & HB & HfS).
      destruct (HO eq_refl) as (Ha2 & Hp8 & Hn8 & HPA & HPP & HPN & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
      eapply L_long; try eassumption; try lia.
      exists ja, jp, jn. exact (conj HPA (conj HPP (conj HPN (conj D1 (conj D2 (conj D3 (conj D7 (conj D8 D9)))))))).
  - eapply L_null; first [eassumption | lia].
Qed.
