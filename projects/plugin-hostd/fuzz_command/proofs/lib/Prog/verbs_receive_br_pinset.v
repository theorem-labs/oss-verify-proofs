From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun CTypeFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_call verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_br verbs_receive_br2 pin_set_words_c sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require VerbsMem rec_shape_of_c RecKindB reply rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pinset_tail_ne : forall v args, route_tail v args <> RPinset.
Proof.
  intros v args. unfold route_tail, route_conn, route_cd.
  destruct (ledger_of v instance_info_verbs); [discriminate|].
  destruct args as [|x [|y [|z r]]];
    repeat (match goal with |- context [if ?b then _ else _] => destruct b end); cbn; discriminate.
Qed.

Lemma pinset_verb : forall tk, route tk = RPinset -> nth_error tk 0 = Some Verbs.Lit.verb_pin_set.
Proof.
  intros [|v args] H; [discriminate H|]. cbn [nth_error]. unfold route, route_mid in H.
  repeat match type of H with
  | (if ?b then _ else _) = _ => let E := fresh "E" in destruct b eqn:E; [try discriminate H|]
  end.
  all: first [exfalso; exact (pinset_tail_ne v args H)
             | match goal with E : list_eqb _ _ = true |- _ => apply list_eqb_eq in E; rewrite E; reflexivity end].
Qed.

Lemma pinset_code : forall R ln args, (r_refuse R <> 0 -> declared (r_code R) = true) ->
  -2^31 <= snd (VerbsRun.pin_set_run R ln args) < 2^31.
Proof.
  intros R ln args NR. unfold VerbsRun.pin_set_run.
  destruct (Verbs.pin_set_words_m ln args); cbn [snd]; try (unfold Verbs.err_invalid_operation; lia).
  assert (C : snd (pins_set_m R (Some uri) (Some files) (Some layout) verdict) = 0 \/
              -2^31 <= snd (pins_set_m R (Some uri) (Some files) (Some layout) verdict) < 0).
  { unfold pins_set_m, rec_stub_code, rec_answer_code, rec_record, set_calls, set_spill.
    destruct (Nat.ltb _ _); cbn [r_refuse r_code];
      destruct (Z.eqb_spec (r_refuse R) 0) as [Z0|Z0]; cbn [snd];
      first [left; reflexivity | right; apply declared_range, NR, Z0]. }
  destruct (pins_set_m R (Some uri) (Some files) (Some layout) verdict) as [R1 r]. cbn [snd] in *. lia.
Qed.

Lemma pinset_shape : forall ln args, Verbs.pin_set_words_m ln args = Verbs.reject \/
  exists u f l vd, Verbs.pin_set_words_m ln args = Verbs.SPinSet u f l vd.
Proof.
  intros ln args. unfold Verbs.pin_set_words_m.
  destruct args as [|u [|fl [|ly [|vd [|x r]]]]]; try (left; reflexivity);
    repeat (match goal with |- context [if ?b then _ else _] => destruct b end);
    first [left; reflexivity | right; do 4 eexists; reflexivity].
Qed.

Lemma pinset_run : forall rcode R ln tk, route tk = RPinset ->
  VerbsRun.run_step rcode R (plan_at (route tk) atoi_c.atoi_val ln tk) =
  (fst (VerbsRun.pin_set_run R ln (tl tk)), resp (snd (VerbsRun.pin_set_run R ln (tl tk))), false).
Proof.
  intros rcode R ln [|v args] RT; [discriminate RT|]. rewrite RT. cbn [plan_at tl].
  unfold VerbsRun.pin_set_run.
  destruct (pinset_shape ln args) as [E|(u & f & l & vd & E)]; rewrite E; [reflexivity|].
  cbn [VerbsRun.run_step]. destruct (pins_set_m R (Some u) (Some f) (Some l) vd) as [R1 r]. reflexivity.
Qed.

Lemma pinset_nz : forall l, ~ In (Z_to_bv 8 0) l -> Forall (fun b : byte => bv_unsigned b <> 0) l.
Proof.
  intros l H. apply Forall_forall. intros b Hb E. apply H. replace (Z_to_bv 8 0) with b; [exact Hb|].
  apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma pinset_psw_low {rc : YM05.RunCeil} : forall a, psw_writes a -> a < alloc_ceiling.
Proof. intros a Ha. pose proof alloc_ceiling_val. unfold psw_writes, REC_SC, SC_SIZE, G_REC, REC_SIZE in Ha. lia. Qed.

Lemma pinset_psw_gq : forall i, 0 <= i < 4 -> ~ psw_writes (G_QUIT + i).
Proof. intros i Hi Ha. unfold psw_writes, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_QUIT in Ha. lia. Qed.

Lemma pinset_k1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x17930) sp gp tp t0 t1 t2 s0 s1 s0 (Z_to_bv 64 (bv_unsigned sp + 8)) s3 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x17cec) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17920) fc None m (seg_rom rsegs)).
Proof. intros. do 4 zstep. apply evt_done. reflexivity. Qed.

Lemma k_j17930 : forall (R F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS R F (Z_to_bv 64 0x1796c) fc None m (seg_rom rsegs))
    (MS R F (Z_to_bv 64 0x17930) fc None m (seg_rom rsegs)).
Proof. intros R F fc m. zstep. apply evt_done. reflexivity. Qed.

Section V.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.

Local Notation D := (s_D S).

Lemma pinset_tail : forall rg mem1 md1 L1 A1 R1 O1 k1 X K L2 A2 rg2 mem2 md2 R2 O2 k2,
  vtail B API S L1 A1 mem1 md1 R1 O1 k1 X ->
  spZ rg = s_spf S -> 0 <= K <= 14336 ->
  RecKindB.call_post_rec B MR K L1 A1 rg mem1 md1 psw_writes (fun a => In a (map fst O1)) L2 A2 rg2 mem2 md2 ->
  g_rec_rep (ms_segs B) L2 A2 mem2 R2 O2 ->
  (forall pn, In pn (blocks L1 A1) -> ~ In pn O1 -> In pn (blocks L2 A2)) ->
  (forall pn, In pn (blocks L2 A2) -> (In pn (blocks L1 A1) /\ ~ In pn O1) \/ In pn O2) ->
  (forall pn, In pn (blocks L1 A1) -> ~ In pn O1 -> ~ In pn O2) ->
  blocks_kept B L1 A1 mem1 mem2 (fun a => exists j, In (a, j) O1) ->
  ro_agree (ms_segs B) mem2 -> st_init_done A2 = true ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  res_ok_slots A2 (sb_n (s_b S) k2) -> (k2 <= 32)%nat ->
  vtail B API S L2 A2 mem2 md2 R2 O2 k2 X /\
  (forall a k s bs, In (a, k) X -> a <= s -> s + Z.of_nat (length bs) <= a + k ->
     bytes_at rsegs mem1 s bs -> bytes_at rsegs mem2 s bs).
Proof.
  intros rg mem1 md1 L1 A1 R1 O1 k1 X K L2 A2 rg2 mem2 md2 R2 O2 k2 H SPR HK POST HREC SV BLK NO2 KEEP
    RO2 INIT RLEN RES HKB.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  pose proof POST as (HM2 & _).
  pose proof (t_rel B API S _ _ _ _ _ _ _ _ H) as REL. pose proof REL as (HM1 & _).
  pose proof (t_rec B API S _ _ _ _ _ _ _ _ H) as HREC1.
  assert (SURV : forall pn, In pn (blocks L1 A1) -> ~ In pn O1 -> In pn (blocks L2 A2) /\
            (forall i, 0 <= i < snd pn -> mbyte (ms_segs B) mem2 (fst pn + i) = mbyte (ms_segs B) mem1 (fst pn + i))).
  { intros [a k] Hin Hno. split; [exact (SV (a, k) Hin Hno)|]. intros i Hi. cbn [fst snd] in *.
    apply (KEEP a k i Hin); [|exact Hi]. intros (j & Hj).
    apply (addr_notin B API L1 A1 mem1 md1 R1 O1 a k HM1 HREC1 Hin ltac:(lia) Hno).
    apply in_map_iff. exists (a, j). split; [reflexivity | exact Hj]. }
  pose proof (t_x B API S _ _ _ _ _ _ _ _ H) as HX.
  assert (XNO : forall pn, In pn X -> ~ In pn O1).
  { intros pn Hp Ho. apply (proj2 (HX pn Hp)). apply in_map_iff. exists pn. split; [reflexivity | exact Ho]. }
  split.
  2:{ intros a k s bs Hx H1 H2 Hb. destruct (HX (a, k) Hx) as [Hin _].
      apply (bytes_at_transfer rsegs mem1); [exact Hb|]. intros i Hi.
      replace (s + i) with (a + (s - a + i)) by ring. rewrite <- SEGS.
      exact (proj2 (SURV (a, k) Hin (XNO (a, k) Hx)) (s - a + i) ltac:(cbn; lia)). }
  constructor.
  - eapply (rel_call B API (vf_ax B API HF) (vf_ctxo B API HF)); [exact REL | exact POST | exact RLEN | | | | ].
    + intros a [Ha|Ha]; [left; rewrite SPR in Ha; unfold s_spf, VR_K in *; lia | right; exact Ha].
    + intros a Ha. right. unfold psw_writes, vr_writes in *. tauto.
    + intros a Hs Hn. unfold scratch_k in Hs, Hn. rewrite SPR in Hn.
      destruct Hs as [Hs|Hs]; [|exfalso; apply Hn; right; exact Hs].
      split; [unfold VR_K in *; lia|]. unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT, VR_K in *. lia.
    + intros a k i Hin Hx Hi.
      assert (Hno : ~ In (a, k) (s_O S)) by (intros Ho; apply Hx; apply in_map_iff; exists (a, k); split; [reflexivity | exact Ho]).
      destruct (t_old B API S _ _ _ _ _ _ _ _ H (a, k) Hin Hno) as [Hin1 Hno1].
      exact (proj2 (SURV (a, k) Hin1 Hno1) i Hi).
  - exact HREC.
  - exact RO2.
  - exact INIT.
  - split; [exact RES | exact HKB].
  - intros pn Hin Hno. destruct (t_old B API S _ _ _ _ _ _ _ _ H pn Hin Hno) as [H1 H2].
    split; [exact (proj1 (SURV pn H1 H2)) | exact (NO2 pn H1 H2)].
  - intros pn Hin. destruct (BLK pn Hin) as [[H1 H2]|H1].
    + destruct (t_sub B API S _ _ _ _ _ _ _ _ H pn H1) as [H3|[H3|H3]];
        [left; exact H3 | exfalso; exact (H2 H3) | right; right; exact H3].
    + right. left. exact H1.
  - intros pn Hp. destruct (HX pn Hp) as [H1 _]. pose proof (XNO pn Hp) as H3.
    pose proof (proj1 (SURV pn H1 H3)) as H4. split; [exact H4|].
    destruct pn as [a k]. apply (addr_notin B API L2 A2 mem2 md2 R2 O2 a k HM2 HREC H4);
      [exact (t_xsz B API S _ _ _ _ _ _ _ _ H (a, k) Hp) | exact (NO2 _ H1 H3)].
  - exact (t_xap B API S _ _ _ _ _ _ _ _ H).
  - exact (t_xnd B API S _ _ _ _ _ _ _ _ H).
  - exact (t_xsz B API S _ _ _ _ _ _ _ _ H).
Qed.

Lemma pinset_heap : forall rg mem1 md1 L1 A1 R1 O1 k1 K L2 A2 rg2 mem2 md2 R2 O2 k2,
  vheap B API S L1 A1 mem1 md1 R1 O1 k1 None ->
  spZ rg = s_spf S -> 0 <= K <= 14336 ->
  RecKindB.call_post_rec B MR K L1 A1 rg mem1 md1 psw_writes (fun a => In a (map fst O1)) L2 A2 rg2 mem2 md2 ->
  g_rec_rep (ms_segs B) L2 A2 mem2 R2 O2 ->
  (forall pn, In pn (blocks L1 A1) -> ~ In pn O1 -> In pn (blocks L2 A2)) ->
  (forall pn, In pn (blocks L2 A2) -> (In pn (blocks L1 A1) /\ ~ In pn O1) \/ In pn O2) ->
  (forall pn, In pn (blocks L1 A1) -> ~ In pn O1 -> ~ In pn O2) ->
  blocks_kept B L1 A1 mem1 mem2 (fun a => exists j, In (a, j) O1) ->
  ro_agree (ms_segs B) mem2 -> st_init_done A2 = true ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  res_ok_slots A2 (sb_n (s_b S) k2) -> (k2 <= 32)%nat ->
  vheap B API S L2 A2 mem2 md2 R2 O2 k2 None.
Proof.
  intros rg mem1 md1 L1 A1 R1 O1 k1 K L2 A2 rg2 mem2 md2 R2 O2 k2 H SPR HK POST HREC SV BLK NO2 KEEP
    RO2 INIT RLEN RES HKB.
  destruct (pinset_tail rg mem1 md1 L1 A1 R1 O1 k1 (xbl S None) K L2 A2 rg2 mem2 md2 R2 O2 k2
    (h_t B API S _ _ _ _ _ _ _ _ H) SPR HK POST HREC SV BLK NO2 KEEP RO2 INIT RLEN RES HKB) as [T KB].
  constructor.
  - exact T.
  - apply (KB (s_lb S) (s_nlb S)); [left; reflexivity | lia | | exact (h_lb B API S _ _ _ _ _ _ _ _ H)].
    rewrite !length_app, repeat_length. cbn [length]. pose proof (line_le_upto S). unfold s_nlb. lia.
  - eapply Forall2_impl; [|exact (h_tok B API S _ _ _ _ _ _ _ _ H)]. intros p w ((Hb & Hnz) & H1 & H2).
    split; [split; [|exact Hnz]|split; assumption].
    apply (KB (s_cb S) (s_ncb S)); [right; left; reflexivity | exact H1 | | exact Hb].
    rewrite length_app. cbn [length]. lia.
  - exact I.
Qed.

Hypothesis PSW : @pin_set_words_contract fx rc B API.

Lemma pinset_call : forall rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  @vr_state fx _ B API S rg 0x17cec mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  getr rg 1 = Z_to_bv 64 0x17930 -> getr rg 10 = Z_to_bv 64 (s_lb S) ->
  getr rg 11 = Z_to_bv 64 (s_spf S + 8) -> getr rg 12 = Z_to_bv 64 (Z.of_nat (length (toks D))) ->
  nth_error (toks D) 0 = Some Verbs.Lit.verb_pin_set ->
  (r_refuse R1 <> 0 -> declared (r_code R1) = true) -> (k1 + 7 <= 32)%nat ->
  (forall (fx' : YK11.FPState) rg' mem' md' L' A' O' k c',
     @vr_state fx' _ B API S rg' 0x17930 mem' md' L' A' (fst (VerbsRun.pin_set_run R1 (line D) (tl (toks D)))) O'
       (k1 + k) qv None jk c' ->
     getr rg' 10 = Z_to_bv 64 (snd (VerbsRun.pin_set_run R1 (line D) (tl (toks D)))) ->
     regs_preserved rg rg' -> (k <= 7)%nat -> SR rsegs c' P) ->
  SR rsegs c P.
Proof.
  intros rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P HST E1 E10 E11 E12 V0 NR HK7 KONT.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & SP16 & SPF). pose proof alloc_ceiling_val as ACV.
  pose proof HST as (EC & FPK0 & VR & H & FR & GQ & GW).
  assert (RET : YK0s.ret_ok (Z_to_bv 64 0x17930)) by (apply bv_eq; vm_compute; reflexivity).
  assert (KB : 0 <= PSW_K <= 14336) by (unfold PSW_K; lia).
  destruct (vs_pre B API HF S HS rg 0x17cec mem1 md1 L1 A1 R1 O1 k1 qv None jk c PSW_K 0x17930 HST E1 RET KB)
    as (PRE & SPR & FZ & F18 & RO & REC & HM & _).
  destruct (proj2 (st_f18 B API HF _ _ _ _ HM)) as (can & SSP).
  pose proof (h_tok B API S _ _ _ _ _ _ _ _ H) as TOK.
  pose proof (Forall2_length TOK) as LPT.
  pose proof (ok_psl B API S HS) as PSL.
  pose proof (ok_nD B API S HS) as OND. pose proof (ok_n8 B API S HS) as ON8.
  assert (NE : toks D <> []) by (intros E; rewrite E in V0; discriminate V0).
  assert (LT1 : (1 <= length (toks D))%nat) by (destruct (toks D); [contradiction | cbn [length]; lia]).
  pose proof (h_x B API S _ _ _ _ _ _ _ _ H) as HX.
  destruct (HX (s_lb S, s_nlb S) (or_introl eq_refl)) as [INL NOLm].
  destruct (HX (s_cb S, s_ncb S) (or_intror (or_introl eq_refl))) as [INC NOCm].
  assert (NOL : ~ In (s_lb S, s_nlb S) O1)
    by (intros Ho; apply NOLm; apply in_map_iff; exists (s_lb S, s_nlb S); split; [reflexivity | exact Ho]).
  assert (NOC : ~ In (s_cb S, s_ncb S) O1)
    by (intros Ho; apply NOCm; apply in_map_iff; exists (s_cb S, s_ncb S); split; [reflexivity | exact Ho]).
  destruct (blk_low B API HF L1 A1 mem1 md1 (s_cb S) (s_ncb S) 0 HM INC ltac:(unfold s_ncb; lia)) as (CB4 & CBC & _).
  pose proof (st_line_arg B API HF S HS rg 0x17cec mem1 md1 L1 A1 R1 O1 k1 qv None jk c PSW_K HST KB) as SLA.
  unfold RecKindB.str_arg in SLA. destruct SLA as (_ & NZL & _).
  assert (LBB : VerbsB.le_at B mem1 (s_lb S) (line D ++ [Z_to_bv 8 0])).
  { apply reply.bytes_le_at. rewrite SEGS.
    pose proof (h_lb B API S _ _ _ _ _ _ _ _ H) as HL. rewrite repeat_snoc0 in HL.
    replace (line D ++ Z_to_bv 8 0 :: repeat (Z_to_bv 8 0) (length (upto0 D) - length (line D)))
      with ((line D ++ [Z_to_bv 8 0]) ++ repeat (Z_to_bv 8 0) (length (upto0 D) - length (line D))) in HL
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in HL. exact (proj1 HL). }
  assert (LTn : Z.of_nat (length (line D)) + 1 <= s_nlb S) by (pose proof (line_le_upto S); unfold s_nlb; lia).
  assert (TKA : VerbsB.toks_at B mem1 (s_spf S + 8) (map bv_unsigned (s_ps S)) (toks D) (s_cb S) (s_ncb S)).
  { split; [unfold s_spf in *; Z.div_mod_to_equations; lia|].
    split; [rewrite length_map; exact LPT|].
    split.
    { apply reply.bytes_le_at. rewrite SEGS. destruct FR as (_ & _ & FB). rewrite map_map.
      replace (map (fun x : word => le8 (Z_to_bv 64 (bv_unsigned x))) (s_ps S)) with (map le8 (s_ps S)); [exact FB|].
      apply map_ext. intros p. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    intros i p w Ep Ew. rewrite nth_error_map in Ep.
    destruct (nth_error (s_ps S) i) as [pw|] eqn:Epw; cbn in Ep; [|discriminate Ep]. injection Ep as <-.
    destruct (Forall2_nth _ _ _ _ _ _ TOK Epw Ew) as ((Hb & Hnz) & H1 & H2).
    assert (IW : In w (toks D)) by (apply nth_error_In with i; exact Ew).
    pose proof (verbs_receive_route.toks_len D w IW) as LW.
    split; [apply reply.bytes_le_at; rewrite SEGS; exact Hb|].
    split; [exact Hnz|]. split; [lia|]. split; [exact H1|]. split; [exact H2|].
    left. unfold s_spf, VR_K in *. lia. }
  assert (OUTS : VerbsB.outside B L1 A1 PSW_K rg (s_spf S + 8) (8 * Z.of_nat (length (toks D)))).
  { intros i Hi. split.
    - intros Ho. pose proof (owned_low B MR (aa_laws API) L1 A1 mem1 md1 _ HM Ho). unfold s_spf, VR_K in *. lia.
    - unfold scratch_k. rewrite SPR, (vf_errno B API HF). unfold PSW_K, s_spf, VR_K in *. lia. }
  assert (NT : 1 <= Z.of_nat (length (toks D)) <= 64) by lia.
  assert (SPL : bv_unsigned (getr rg 2) <= s_spf S + 8) by (unfold spZ in SPR; lia).
  assert (ROOM : room_slots (sb_n (sb_n (s_b S) k1) PSW_MALLOCS) PSW_REQ).
  { pose proof (ok_room B API S HS) as RM.
    eapply (RecKindB.room_slots_mono _ _ PSW_REQ VR_REQ); [| unfold PSW_REQ, VR_REQ; lia | exact RM].
    unfold RecKindB.sb_le, sb_n, PSW_MALLOCS, SB_REQ. cbn [sb_live sb_bytes sb_cap]. lia. }
  pose proof (h_res B API S _ _ _ _ _ _ _ _ H) as (RES & _).
  eapply SR_bind.
  { rewrite EC. pose proof (PSW L1 A1 rg mem1 md1 (sb_n (s_b S) k1) R1 O1 (s_lb S) (s_nlb S) (s_spf S + 8) (s_cb S) (s_ncb S)
      (Z.of_nat (length (toks D))) (line D) (map bv_unsigned (s_ps S)) (toks D) can
      PRE RO FZ E10 E11 E12 INL NOL LBB (pinset_nz _ NZL) LTn INC NOC TKA eq_refl NT V0 SPL
      ltac:(unfold s_spf, VR_K in *; lia) OUTS REC NR SSP RES ROOM) as C.
    rewrite SEGS in C. unfold PIN_SET_WORDS in C. exact C. }
  intros c' (fx' & L' & A' & rg' & mem' & md' & O' & k & EC' & FPK & POST & RO' & RUN & _ & _ & SV & BLK & NO2
    & RLEN & KEEP & _ & HKk & RES').
  revert RUN KONT. destruct (VerbsRun.pin_set_run R1 (line D) (tl (toks D))) as [R' r]. intros (REC' & A10) KONT.
  cbn [fst snd] in KONT. rewrite <- SEGS in RO', REC'.
  pose proof POST as (HM' & HWF' & _ & _ & _ & HPR & _ & HFR & _ & _).
  pose proof (frame_keep B API HF S HS PSW_K rg mem1 mem' L1 A1 L' A' md1 md' psw_writes HM HM' SPR
    pinset_psw_low HFR) as KP.
  pose proof (gq_keep B API HF S HS PSW_K rg mem1 mem' L1 A1 L' A' md1 md' psw_writes HM HM' SPR KB
    pinset_psw_gq HFR) as KQ.
  destruct (gq_transfer mem1 mem' qv KQ GQ GW) as [GQ' GW'].
  assert (INIT : st_init_done A' = true).
  { pose proof (SV _ INL NOL) as INL'. unfold blocks in INL'. apply in_map_iff in INL' as ([q0 k0] & _ & Hq0).
    destruct (st_init_done A') eqn:EI; [reflexivity|]. exfalso.
    pose proof HWF' as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinit) & _).
    destruct (Hinit EI) as (Hm & _). unfold user_blocks, used_metas in Hq0. rewrite Hm in Hq0. cbn in Hq0. exact Hq0. }
  apply (KONT fx' rg' mem' md' L' A' O' k); [| exact A10 | exact HPR | exact HKk].
  split; [rewrite EC', E1; reflexivity|].
  split; [exact (fp_kept_trans _ _ _ FPK0 FPK)|].
  split; [exact (vregs_pres S rg rg' VR HPR)|].
  split.
  { apply (pinset_heap rg mem1 md1 L1 A1 R1 O1 k1 PSW_K L' A' rg' mem' md' R' O' (k1 + k) H SPR KB POST REC' SV BLK
      NO2 KEEP RO' INIT RLEN).
    - replace (sb_n (s_b S) (k1 + k)) with (sb_n (sb_n (s_b S) k1) k); [exact RES'|].
      unfold sb_n. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
    - unfold PSW_MALLOCS in HKk. lia. }
  split; [exact (vfr_keep B API S HS mem1 mem' jk KP FR)|].
  split; [exact GQ' | exact GW'].
Qed.

End V.

Section R.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis SRESP : forall f : YK11.FPState, @sup_resp_contract f rc B API.
Hypothesis PSW : forall f : YK11.FPState, @pin_set_words_contract f rc B API.

Local Notation D := (s_D S).

Lemma vr_br_pinset : forall (f : YK11.FPState) rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  @vr_state f _ B API S rg (route_pc RPinset) mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  route (toks D) = RPinset -> getr rg 21 = verbs_receive_disp.ntokw (toks D) -> (k1 + 8 <= 32)%nat ->
  getr rg 19 = verbs_receive_disp.ntokw (toks D) ->
  (r_refuse R1 <> 0 -> declared (r_code R1) = true) ->
  join_k B API S 0x17970 10 rg R1 k1 qv P ->
  SR rsegs c P.
Proof.
  intros f rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P HST RT N21 HK N19 NR JOIN.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof HST as (_ & _ & VR & _).
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  assert (SP2 : bv_unsigned (reg_get rg 2) = s_spf S).
  { destruct VR as (V2 & _). change (reg_get rg 2) with (getr rg 2). rewrite V2. apply unsigned_lit.
    unfold s_spf, VR_K in *. lia. }
  eapply (@ka_nw f _ B API HF S HS rg (route_pc RPinset) mem1 md1 L1 A1 R1 O1 k1 qv None jk c _ P HST).
  { unfold Regs6ss.mkR_of. cbn [route_pc]. apply pinset_k1. }
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R' pc' rg' mem2 HQ X MK. cbv beta in HQ. injection HQ as ER EP. subst R' pc'.
  assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
  pose proof (MK 0x17cec eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
  assert (E1 : getr rg' 1 = Z_to_bv 64 0x17930) by (rewrite (getr_of_eqv _ _ 1 X eq_refl); reflexivity).
  assert (E10 : getr rg' 10 = Z_to_bv 64 (s_lb S)).
  { rewrite (getr_of_eqv _ _ 10 X eq_refl). destruct VR as (_ & _ & _ & V8 & _). exact V8. }
  assert (E11 : getr rg' 11 = Z_to_bv 64 (s_spf S + 8)).
  { rewrite (getr_of_eqv _ _ 11 X eq_refl). rewrite <- SP2. reflexivity. }
  assert (E12 : getr rg' 12 = Z_to_bv 64 (Z.of_nat (length (toks D)))).
  { rewrite (getr_of_eqv _ _ 12 X eq_refl). transitivity (getr rg 19); [reflexivity|]. exact N19. }
  apply (pinset_call B API HF S HS (PSW f) rg' mem2 md1 L1 A1 R1 O1 k1 qv jk _ P HST1 E1 E10 E11 E12
           (pinset_verb _ RT) NR ltac:(lia)).
  intros fx' rg2 mem3 md3 L2 A2 O2 k c2 HST2 E10' HP2 HK7.
  pose proof HST2 as (_ & _ & VR2 & _).
  eapply (ka_nw B API HF S HS rg2 0x17930 mem3 md3 L2 A2 _ O2 _ qv None jk c2 _ P HST2 (k_j17930 _ _ _ _)).
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R3 pc3 rg3 mem4 HQ3 X3 MK3. cbv beta in HQ3. injection HQ3 as ER EP. subst R3 pc3.
  pose proof (getr_eqv_of rg2 rg3 X3) as GE.
  pose proof (MK3 0x1796c eq_refl (vregs_pres S rg2 rg3 VR2 (fun r _ => GE _))) as HST3.
  eapply (resp_join B API HF S HS SRESP rg R1 k1 qv false 0x1796c 0x17970 rg3 mem4 md3 L2 A2 _ O2 _ jk _
            (snd (VerbsRun.pin_set_run R1 (line D) (tl (toks D)))) P).
  - left. split; reflexivity.
  - exact HST3.
  - rewrite GE. exact E10'.
  - exact (pinset_code _ _ _ NR).
  - exact (eq_trans (GE _) (eq_trans (HP2 18 ltac:(unfold callee_saved; lia)) (PR 18 ltac:(unfold callee_saved; lia)))).
  - intros _. exact (eq_trans (GE _) (eq_trans (HP2 21 ltac:(unfold callee_saved; lia)) (PR 21 ltac:(unfold callee_saved; lia)))).
  - exact (pinset_run _ _ _ _ RT).
  - lia.
  - lia.
  - exact HK.
  - exact JOIN.
Qed.

End R.
