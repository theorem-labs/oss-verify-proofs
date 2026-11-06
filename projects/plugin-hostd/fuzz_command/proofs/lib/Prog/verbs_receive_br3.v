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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_call verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_br verbs_receive_br2 sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require VerbsMem rec_shape_of_c RecKindB reply rec_shape_of RecTail.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_pre verbs_receive_tok verbs_receive_br_link.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pw_remove : forall {X : Type} (Rl : X -> X -> Prop) l1 x l2,
  pairwise Rl (l1 ++ x :: l2) -> pairwise Rl (l1 ++ l2).
Proof.
  intros X Rl l1. induction l1 as [|y l1 IH]; intros x l2 H; cbn [app pairwise] in *.
  - exact (proj2 H).
  - destruct H as [H1 H2]. split; [|exact (IH x l2 H2)].
    intros z Hz. apply H1. apply in_app_or in Hz. apply in_or_app.
    destruct Hz as [Hz|Hz]; [left; exact Hz | right; right; exact Hz].
Qed.

Section J.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.

Local Notation D := (s_D S).
Local Notation VS f := (@vr_state f _ B API S).

Definition vr_join_ge (f : YK11.FPState) (J ar : Z) (rg0 : bvmap 5 word) (R0 : rstate) (k0 : nat) (qv : Z)
    (rg : bvmap 5 word) (mem : word -> option byte) (md : Model) (L : layout) (A : astate) (R : rstate)
    (O : list (Z * Z)) (k : nat) (q nq : Z) (x jk : list byte) (c : config) : Prop :=
  exists qt : bool,
    VS f rg J mem md L A R O k (if qt then 1 else qv) (Some (q, nq, x)) jk c /\ Z.of_nat (length x) + 1 <= nq /\
    getr rg (Z_to_bv 5 ar) = Z_to_bv 64 q /\ getr rg 18 = getr rg0 18 /\
    (J = 0x17970 \/ J = 0x17974 -> getr rg 21 = getr rg0 21) /\
    VerbsRun.run_step sup_reply_code_c.reply_code R0
      (plan_at (route (toks D)) atoi_c.atoi_val (line D) (toks D)) = (R, x, qt) /\
    (k0 <= k <= k0 + 8)%nat.

Definition join_k_ge (J ar : Z) (rg0 : bvmap 5 word) (R0 : rstate) (k0 : nat) (qv : Z) (P : config -> Prop) : Prop :=
  forall (f : YK11.FPState) rg mem md L A R O k q nq x jk c,
    vr_join_ge f J ar rg0 R0 k0 qv rg mem md L A R O k q nq x jk c -> SR rsegs c P.

Lemma join_k_of_ge : forall J ar rg0 R0 k0 qv P,
  join_k_ge J ar rg0 R0 k0 qv P -> join_k B API S J ar rg0 R0 k0 qv P.
Proof.
  intros J ar rg0 R0 k0 qv P K f rg mem md L A R O k q x jk c (qt & HST & E & E18 & E21 & RUN & HK).
  apply (K f rg mem md L A R O k q (Z.of_nat (length x) + 1) x jk c). exists qt.
  split; [exact HST|]. split; [lia|]. split; [exact E|]. split; [exact E18|]. split; [exact E21|].
  split; [exact RUN | exact HK].
Qed.

Lemma join_jump_ge : forall (f : YK11.FPState) rg0 R0 k0 qv rg pc J mem md L A R O k q nq x jk c P,
  VS f rg pc mem md L A R O k qv (Some (q, nq, x)) jk c -> Z.of_nat (length x) + 1 <= nq ->
  (forall (Rm Fm : bvmap 5 word) (fcm : bv 32) (m : word -> option byte),
     evt rsegs (fun ms' => ms' = MS Rm Fm (Z_to_bv 64 J) fcm None m (seg_rom rsegs))
       (MS Rm Fm (Z_to_bv 64 pc) fcm None m (seg_rom rsegs))) ->
  getr rg 10 = Z_to_bv 64 q -> getr rg 18 = getr rg0 18 -> getr rg 21 = getr rg0 21 ->
  VerbsRun.run_step sup_reply_code_c.reply_code R0
    (plan_at (route (toks D)) atoi_c.atoi_val (line D) (toks D)) = (R, x, false) ->
  (k0 <= k <= k0 + 8)%nat ->
  join_k_ge J 10 rg0 R0 k0 qv P ->
  SR rsegs c P.
Proof using HF HS.
  intros f rg0 R0 k0 qv rg pc J mem md L A R O k q nq x jk c P HST LX JMP E10 E18 E21 RUN HK JOIN.
  apply (@ka_nw f _ B API HF S HS rg pc mem md L A R O k qv _ jk c _ P HST (JMP _ _ _ _)).
  - intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity.
  - intros R' pc' rg' mem2 EQ X MK. cbv beta in EQ. injection EQ as E1 E2. subst R' pc'.
    pose proof (getr_eqv_of rg rg' X) as GE.
    pose proof HST as (_ & _ & VR & _).
    eapply JOIN. exists false.
    split; [apply MK; [reflexivity | apply (vregs_pres S rg rg' VR); intros r _; apply GE]|].
    split; [exact LX|].
    rewrite !GE. split; [exact E10|]. split; [exact E18|]. split; [intros _; exact E21|].
    split; [exact RUN | exact HK].
Qed.

End J.

Section SV.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.

Local Notation O0 := (s_O S).
Local Notation b0 := (s_b S).
Local Notation lb := (s_lb S).
Local Notation cb := (s_cb S).
Local Notation nlb := (s_nlb S).
Local Notation ncb := (s_ncb S).
Local Notation spf := (s_spf S).

Lemma tail_step_sv : forall rg mem1 md1 L1 A1 R1 O1 k1 X K L2 A2 rg2 mem2 md2 R2 O2 NEW k2,
  vtail B API S L1 A1 mem1 md1 R1 O1 k1 X ->
  spZ rg = spf -> 0 <= K <= 14336 ->
  RecKindB.call_post_rec B MR K L1 A1 rg mem1 md1 RecKindB.rec_area (fun a => In a (map fst O1))
    L2 A2 rg2 mem2 md2 ->
  g_rec_rep (ms_segs B) L2 A2 mem2 R2 O2 -> RecKindB.owns_new L1 A1 O1 O2 ->
  (forall pn, In pn (blocks L2 A2) -> (In pn (blocks L1 A1) /\ ~ In pn O1) \/ In pn O2 \/ In pn NEW) ->
  (forall pn, In pn (blocks L1 A1) -> ~ In pn O1 -> In pn (blocks L2 A2) /\
     (forall i, 0 <= i < snd pn -> mbyte (ms_segs B) mem2 (fst pn + i) = mbyte (ms_segs B) mem1 (fst pn + i))) ->
  ro_agree (ms_segs B) mem2 -> st_init_done A2 = true ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  res_ok_slots A2 (sb_n b0 k2) -> (k2 <= 32)%nat ->
  (forall pn, In pn NEW -> In pn (blocks L2 A2) /\ ~ In (fst pn) (map fst O2) /\ 1 <= snd pn /\
     (forall pn', In pn' (blocks L1 A1) -> ~ In pn' O1 -> fst pn + snd pn <= fst pn' \/ fst pn' + snd pn' <= fst pn)) ->
  List.NoDup (map fst NEW) ->
  vtail B API S L2 A2 mem2 md2 R2 O2 k2 (X ++ NEW) /\
  (forall a k s bs, In (a, k) X -> a <= s -> s + Z.of_nat (length bs) <= a + k ->
     bytes_at rsegs mem1 s bs -> bytes_at rsegs mem2 s bs).
Proof using HF HS.
  intros rg mem1 md1 L1 A1 R1 O1 k1 X K L2 A2 rg2 mem2 md2 R2 O2 NEW k2 H SPR HK POST HREC OWN BLK SURV
    RO2 INIT RLEN RES HKB HNEW NDN.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  pose proof POST as (HM2 & _).
  assert (NO2 : forall pn, In pn (blocks L1 A1) -> ~ In pn O1 -> ~ In pn O2).
  { intros pn Hin Hno Ho. destruct (OWN pn Ho) as [H1|H1]; [exact (Hno H1) | exact (H1 Hin)]. }
  pose proof (t_x _ _ _ _ _ _ _ _ _ _ _ H) as HX.
  assert (XNO : forall pn, In pn X -> ~ In pn O1).
  { intros pn Hp Ho. apply (proj2 (HX pn Hp)). apply in_map_iff. exists pn. split; [reflexivity | exact Ho]. }
  split.
  2:{ intros a k s bs Hx H1 H2 Hb. destruct (HX (a, k) Hx) as [Hin _].
      apply (bytes_at_transfer rsegs mem1); [exact Hb|]. intros i Hi.
      replace (s + i) with (a + (s - a + i)) by ring. rewrite <- SEGS.
      exact (proj2 (SURV (a, k) Hin (XNO (a, k) Hx)) (s - a + i) ltac:(cbn; lia)). }
  constructor.
  - eapply (rel_call B API (vf_ax B API HF) (vf_ctxo B API HF)); [exact (t_rel _ _ _ _ _ _ _ _ _ _ _ H) | exact POST
      | exact RLEN | | | | ].
    + intros a [Ha|Ha]; [left; rewrite SPR in Ha; unfold s_spf, VR_K in *; lia | right; exact Ha].
    + intros a Ha. right. unfold RecKindB.rec_area, vr_writes in *. tauto.
    + intros a Hs Hn. unfold scratch_k in Hs, Hn. rewrite SPR in Hn.
      destruct Hs as [Hs|Hs]; [|exfalso; apply Hn; right; exact Hs].
      split; [unfold VR_K in *; lia|]. unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT, VR_K in *. lia.
    + intros a k i Hin Hx Hi.
      assert (Hno : ~ In (a, k) O0) by (intros Ho; apply Hx; apply in_map_iff; exists (a, k); split; [reflexivity | exact Ho]).
      destruct (t_old _ _ _ _ _ _ _ _ _ _ _ H (a, k) Hin Hno) as [Hin1 Hno1].
      exact (proj2 (SURV (a, k) Hin1 Hno1) i Hi).
  - exact HREC.
  - exact RO2.
  - exact INIT.
  - split; [exact RES | exact HKB].
  - intros pn Hin Hno. destruct (t_old _ _ _ _ _ _ _ _ _ _ _ H pn Hin Hno) as [H1 H2].
    split; [exact (proj1 (SURV pn H1 H2)) | exact (NO2 pn H1 H2)].
  - intros pn Hin. destruct (BLK pn Hin) as [[H1 H2]|[H1|H1]].
    + destruct (t_sub _ _ _ _ _ _ _ _ _ _ _ H pn H1) as [H3|[H3|H3]];
        [left; exact H3 | exfalso; exact (H2 H3) | right; right; apply in_or_app; left; exact H3].
    + right. left. exact H1.
    + right. right. apply in_or_app. right. exact H1.
  - intros pn Hp. apply in_app_or in Hp as [Hp|Hp].
    + destruct (HX pn Hp) as [H1 _]. pose proof (XNO pn Hp) as H3.
      pose proof (proj1 (SURV pn H1 H3)) as H4. split; [exact H4|].
      destruct pn as [a k]. apply (addr_notin B API L2 A2 mem2 md2 R2 O2 a k HM2 HREC H4);
        [exact (t_xsz _ _ _ _ _ _ _ _ _ _ _ H (a, k) Hp) | exact (NO2 _ H1 H3)].
    + destruct (HNEW pn Hp) as (H1 & H2 & _). split; assumption.
  - intros pn Hp pn' Hin' Hno'. apply in_app_or in Hp as [Hp|Hp];
      [exact (t_xap _ _ _ _ _ _ _ _ _ _ _ H pn Hp pn' Hin' Hno')|].
    destruct (HNEW pn Hp) as (_ & _ & _ & HA). destruct (t_old _ _ _ _ _ _ _ _ _ _ _ H pn' Hin' Hno') as [H1 H2].
    exact (HA pn' H1 H2).
  - rewrite map_app. apply nodup_app_i; [exact (t_xnd _ _ _ _ _ _ _ _ _ _ _ H) | exact NDN|].
    intros a Ha Hb. apply in_map_iff in Ha as (pn1 & E1 & Hp1). apply in_map_iff in Hb as (pn2 & E2 & Hp2).
    destruct (HNEW pn2 Hp2) as (_ & _ & Hs2 & HA). destruct (HX pn1 Hp1) as [H1 _].
    pose proof (t_xsz _ _ _ _ _ _ _ _ _ _ _ H pn1 Hp1) as Hs1.
    destruct (HA pn1 H1 (XNO pn1 Hp1)); lia.
  - intros pn Hp. apply in_app_or in Hp as [Hp|Hp];
      [exact (t_xsz _ _ _ _ _ _ _ _ _ _ _ H pn Hp) | exact (proj1 (proj2 (proj2 (HNEW pn Hp))))].
Qed.

Lemma heap_step_sv : forall rg mem1 md1 L1 A1 R1 O1 k1 xq K L2 A2 rg2 mem2 md2 R2 O2 NEW xq' k2,
  vheap B API S L1 A1 mem1 md1 R1 O1 k1 xq ->
  spZ rg = spf -> 0 <= K <= 14336 ->
  RecKindB.call_post_rec B MR K L1 A1 rg mem1 md1 RecKindB.rec_area (fun a => In a (map fst O1))
    L2 A2 rg2 mem2 md2 ->
  g_rec_rep (ms_segs B) L2 A2 mem2 R2 O2 -> RecKindB.owns_new L1 A1 O1 O2 ->
  (forall pn, In pn (blocks L2 A2) -> (In pn (blocks L1 A1) /\ ~ In pn O1) \/ In pn O2 \/ In pn NEW) ->
  (forall pn, In pn (blocks L1 A1) -> ~ In pn O1 -> In pn (blocks L2 A2) /\
     (forall i, 0 <= i < snd pn -> mbyte (ms_segs B) mem2 (fst pn + i) = mbyte (ms_segs B) mem1 (fst pn + i))) ->
  ro_agree (ms_segs B) mem2 -> st_init_done A2 = true ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  res_ok_slots A2 (sb_n b0 k2) -> (k2 <= 32)%nat ->
  xbl S xq' = xbl S xq ++ NEW ->
  (forall pn, In pn NEW -> In pn (blocks L2 A2) /\ ~ In (fst pn) (map fst O2) /\ 1 <= snd pn /\
     (forall pn', In pn' (blocks L1 A1) -> ~ In pn' O1 -> fst pn + snd pn <= fst pn' \/ fst pn' + snd pn' <= fst pn)) ->
  List.NoDup (map fst NEW) ->
  (match xq' with
   | Some (q, nq, t) => bytes_at rsegs mem2 q (t ++ [Z_to_bv 8 0]) /\ Z.of_nat (length t) + 1 <= nq
   | None => True
   end) ->
  vheap B API S L2 A2 mem2 md2 R2 O2 k2 xq'.
Proof using HF HS.
  intros rg mem1 md1 L1 A1 R1 O1 k1 xq K L2 A2 rg2 mem2 md2 R2 O2 NEW xq' k2 H SPR HK POST HREC OWN BLK SURV
    RO2 INIT RLEN RES HKB XQ HNEW NDN HQ.
  destruct (tail_step_sv rg mem1 md1 L1 A1 R1 O1 k1 (xbl S xq) K L2 A2 rg2 mem2 md2 R2 O2 NEW k2
    (h_t _ _ _ _ _ _ _ _ _ _ _ H) SPR HK POST HREC OWN BLK SURV RO2 INIT RLEN RES HKB HNEW NDN) as [T KB].
  constructor.
  - rewrite XQ. exact T.
  - apply (KB lb nlb); [left; reflexivity | lia | | exact (h_lb _ _ _ _ _ _ _ _ _ _ _ H)].
    rewrite !length_app, repeat_length. cbn [length]. pose proof (line_le_upto S). unfold s_nlb. lia.
  - eapply Forall2_impl; [|exact (h_tok _ _ _ _ _ _ _ _ _ _ _ H)]. intros p w ((Hb & Hnz) & H1 & H2).
    split; [split; [|exact Hnz]|split; assumption].
    apply (KB cb ncb); [right; left; reflexivity | exact H1 | | exact Hb].
    rewrite length_app. cbn [length]. lia.
  - exact HQ.
Qed.

End SV.

Section T.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.

Lemma vr_start : forall L A regs mem md b (R : rstate) (O : list (Z * Z)) (msg fd data n q0 : Z) (D : list byte)
    (can : word) c,
  call_pre_t B API VR_K L A regs mem md ->
  ro_agree (ms_segs B) mem -> frm_zero (@fp_csr fx) ->
  getr regs 10 = Z_to_bv 64 msg -> msg mod 8 = 0 -> 4096 <= msg -> msg + 24 <= 2 ^ 63 ->
  bv_unsigned (getr regs 2) <= msg -> in_img B (errno_addr B) ->
  le_at B mem msg (Mem.le4 (Z_to_bv 64 fd)) ->
  le_at B mem (msg + 8) (Mem.le8 (Z_to_bv 64 data)) ->
  le_at B mem (msg + 16) (Mem.le8 (Z_to_bv 64 n)) ->
  outside B L A VR_K regs msg 24 -> (forall i, 0 <= i < 24 -> ~ vr_writes (msg + i)) ->
  In (data, Z.max n 1) (blocks L A) -> ~ In (data, Z.max n 1) O ->
  le_at B mem data D -> Z.of_nat (length D) = n -> n <= 8192 ->
  g_rec_rep (ms_segs B) L A mem R O ->
  r_calls R = [] -> r_answer R = None -> r_reply R = None -> r_nreplies R = 0 ->
  (r_refuse R <> 0 -> declared (r_code R) = true) ->
  le_at B mem G_QUIT (Mem.le4 (Z_to_bv 64 q0)) ->
  (forall i, 0 <= i < 4 -> writable_at (ms_segs B) mem (G_QUIT + i)) ->
  outside B L A VR_K regs G_QUIT 4 -> vr_tables B mem can ->
  Mem.bytes_at (ms_segs B) mem rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes ->
  res_ok_slots A b -> room_slots (SB (sb_live b + 32) (sb_bytes b + 262208) (sb_cap b)) VR_REQ ->
  @verbs_receive_pre.vr_mid fx _ B API L A regs mem md b msg D c ->
  exists lb cb ps rg mem1 md1 L1 A1 jk,
    vok B API (verbs_receive_st.VS fx L A regs mem md b R O msg fd data n q0 D can lb cb ps) /\
    @vr_state fx _ B API (verbs_receive_st.VS fx L A regs mem md b R O msg fd data n q0 D can lb cb ps) rg
      (match toks D with [] => verbs_receive_tok.VR_EMPTY | _ => verbs_receive_disp.DISPATCH end)
      mem1 md1 L1 A1 R O 2 q0 None jk c /\
    getr rg 18 = Z_to_bv 64 msg /\
    (toks D <> [] -> getr rg 19 = verbs_receive_disp.ntokw (toks D) /\
                     getr rg 21 = verbs_receive_disp.ntokw (toks D)).
Proof using HF.
  intros L A regs mem md b R O msg fd data n q0 D can c PRE RO FZ A0 M8 M4K M63 SPM EIMG HFD HMD HMN MOUT MNW
    DB DNO HD ND N8 REC CALLS ANS REP NREP DECL HQ HQW QOUT TAB SHP RES ROOM MID.
  destruct MID as (L5 & A5 & R5 & m5 & md5 & lb & cb & ps & can5 & jk & b1 & b2 & c1 & c2 & EC & SI & WK & RO5
    & E2 & E3 & E4 & E8 & E9 & E18 & E1921 & E25 & E26 & E27 & FRS & FRJ & FRP & TOK & BL & CC & BL5 & FLB & FCB
    & UB & INIT & RES5 & HLB & SSP).
  exists lb, cb, ps, R5, m5, md5, L5, A5, jk.
  pose proof (vf_segs B API HF) as SEGS. pose proof (aa_laws API) as LAWS.
  pose proof SI as (HM5 & _).
  pose proof (mr_blocks_disjoint B _ LAWS _ _ _ _ HM5) as PD5.
  assert (INB : forall pn, In pn (blocks L A) -> In pn (c1 ++ c2)).
  { intros pn Hin. rewrite CC. rewrite BL in Hin. apply in_app_or in Hin. apply in_or_app.
    destruct Hin as [H|H]; [left; exact H | right; right; exact H]. }
  assert (IN5 : forall pn, In pn (c1 ++ c2) -> In pn (blocks L5 A5)).
  { intros pn Hin. rewrite BL5. apply in_app_or in Hin. apply in_or_app.
    destruct Hin as [H|H]; [left; exact H | right; right; exact H]. }
  assert (CBAP : forall pn, In pn (c1 ++ c2) ->
            fst pn + snd pn <= cb \/ cb + (Z.of_nat (length (line D)) + 1) <= fst pn).
  { intros [a k] Hin. cbn [fst snd]. exact (RecKindB.blocks_mid_disjoint B _ LAWS _ _ _ _ c1 c2 cb _ a k HM5 BL5 Hin). }
  assert (LBAP : forall pn, In pn (b1 ++ b2) ->
            fst pn + snd pn <= lb \/ lb + (Z.of_nat (length (upto0 D)) + 1) <= fst pn).
  { intros [a k] Hin. cbn [fst snd]. rewrite BL5 in PD5. apply pw_remove in PD5. rewrite CC in PD5.
    destruct (RecKindB.pairwise_app_mid' _ _ _ _ _ PD5 Hin) as [Dj|Dj]; unfold ranges_disjoint in Dj;
      cbn [fst snd] in Dj; lia. }
  assert (LBIN : In (lb, Z.of_nat (length (upto0 D)) + 1) (c1 ++ c2))
    by (rewrite CC; apply in_or_app; right; left; reflexivity).
  assert (LUP : (length (upto0 D) <= length D)%nat) by (unfold upto0; apply verbs_receive_route.upto_len).
  assert (LLU : (length (line D) <= length (upto0 D))%nat).
  { unfold line, trim. rewrite length_rev. pose proof (verbs_receive_route.dropw_len is_trail (rev (upto0 D))) as H.
    rewrite length_rev in H. exact H. }
  assert (HS : vok B API (verbs_receive_st.VS fx L A regs mem md b R O msg fd data n q0 D can lb cb ps)).
  { constructor; unfold s_nlb, s_ncb;
      cbn [s_fx s_L s_A s_regs s_mem s_md s_b s_R s_O s_msg s_fd s_data s_n s_q0 s_D s_can s_lb s_cb s_ps];
      try assumption.
    - exact (proj1 PRE).
    - exact (proj2 PRE).
    - intros pn Hin. rewrite BL in Hin. exact (LBAP pn Hin).
    - intros pn Hin. exact (CBAP pn (INB pn Hin)).
    - exact (CBAP _ LBIN).
    - rewrite (Forall2_length TOK). apply Verbs.toks_length. }
  split; [exact HS|].
  split; [|split; [exact E18 | exact E1921]].
  split; [exact EC|].
  split; [split; [exact FZ | intros r _; reflexivity]|].
  split; [exact (conj E2 (conj E3 (conj E4 (conj E8 (conj E9 (conj E25 (conj E26 E27)))))))|].
  split.
  { constructor.
    - constructor.
      + exact (rel_of_since B API O L A regs mem md L5 A5 m5 md5 SI UB).
      + apply (rec_rep_frame (ms_segs B) G_REC REC_SC L A mem R O L5 A5 m5 REC).
        * intros a Ha. assert (W : vr_writes a) by (unfold vr_writes; tauto).
          destruct (WK a W) as [E W']. rewrite SEGS. split; [exact E | apply W'].
        * intros p k i Hin Hi. destruct (reply.rec_rep_O _ _ _ _ _ _ _ _ REC (p, k) Hin) as [Hb _].
          apply YI04.blocks_In in Hb as (q & Eq & Hq). subst p.
          pose proof SI as (_ & _ & _ & _ & _ & _ & _ & _ & HK & _).
          exact (HK q k i Hq (UB q k Hq) (fun F => F) Hi).
        * intros pn Hin. destruct (reply.rec_rep_O _ _ _ _ _ _ _ _ REC pn Hin) as [Hb _]. exact (IN5 pn (INB pn Hb)).
      + rewrite SEGS. exact RO5.
      + exact INIT.
      + split; [|lia]. cbn [s_b].
        apply (RecKindB.res_ok_slots_le A5
                 (sb_malloc (sb_malloc b (Z.of_nat (length (upto0 D)) + 1)) (Z.of_nat (length (line D)) + 1)));
          [| |exact RES5].
        * unfold RecKindB.sb_le, sb_malloc, sb_n, SB_REQ. cbn [sb_live sb_bytes sb_cap]. lia.
        * unfold sb_n. cbn [sb_live sb_cap]. destruct ROOM as (_ & RC & _). cbn [sb_live sb_cap] in RC. lia.
      + intros pn Hin Hno. split; [exact (IN5 pn (INB pn Hin)) | exact Hno].
      + intros pn Hin. rewrite BL5 in Hin. apply in_app_or in Hin.
        assert (G : In pn (c1 ++ c2) -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O \/
                      In pn (xbl (verbs_receive_st.VS fx L A regs mem md b R O msg fd data n q0 D can lb cb ps) None)).
        { intros H. rewrite CC in H. apply in_app_or in H. destruct H as [H|[H|H]].
          - destruct (in_dec RecTail.pair_dec pn O) as [Ho|Ho]; [right; left; exact Ho|].
            left. split; [rewrite BL; apply in_or_app; left; exact H | exact Ho].
          - right; right. left. exact H.
          - destruct (in_dec RecTail.pair_dec pn O) as [Ho|Ho]; [right; left; exact Ho|].
            left. split; [rewrite BL; apply in_or_app; right; exact H | exact Ho]. }
        destruct Hin as [H|[H|H]].
        * apply G. apply in_or_app. left. exact H.
        * right; right. right. left. exact H.
        * apply G. apply in_or_app. right. exact H.
      + intros pn Hp. destruct Hp as [<-|[<-|[]]]; cbn [fst snd s_lb s_cb].
        * split; [exact (IN5 _ LBIN)|].
          intros Hm. apply in_map_iff in Hm as ([a k] & Ea & Hk). cbn [fst] in Ea. subst a.
          destruct (reply.rec_rep_O _ _ _ _ _ _ _ _ REC _ Hk) as [Hb Hk1]. cbn [snd] in Hk1. rewrite BL in Hb.
          destruct (LBAP _ Hb) as [X|X]; cbn [fst snd] in X; lia.
        * split; [rewrite BL5; apply in_or_app; right; left; reflexivity|].
          intros Hm. apply in_map_iff in Hm as ([a k] & Ea & Hk). cbn [fst] in Ea. subst a.
          destruct (reply.rec_rep_O _ _ _ _ _ _ _ _ REC _ Hk) as [Hb Hk1]. cbn [snd] in Hk1.
          destruct (CBAP _ (INB _ Hb)) as [X|X]; cbn [fst snd] in X; lia.
      + intros pn Hp pn' Hin' Hno'. unfold xbl, s_nlb, s_ncb in Hp.
        cbn [s_L s_A] in Hin'. destruct Hp as [<-|[<-|[]]]; cbn [fst snd s_lb s_cb s_D].
        * rewrite BL in Hin'. destruct (LBAP _ Hin'); lia.
        * destruct (CBAP _ (INB _ Hin')); lia.
      + cbn [xbl map fst s_lb s_cb]. pose proof (CBAP _ LBIN) as X. cbn [fst snd] in X.
        constructor; [|constructor; [intros []|constructor]]. intros [E|[]]. lia.
      + intros pn Hp. unfold xbl, s_nlb, s_ncb in Hp. destruct Hp as [<-|[<-|[]]]; cbn [snd]; lia.
    - exact HLB.
    - eapply Forall2_impl; [|exact TOK]. intros p w (Hc & H1 & H2). unfold s_ncb. cbn [s_cb s_D].
      split; [exact Hc|]. split; [exact H1 | lia].
    - exact I. }
  split; [split; [exact FRS | split; [exact FRJ | exact FRP]]|].
  split.
  { assert (QB : bytes_at (ms_segs B) mem G_QUIT (le4 (Z_to_bv 64 q0)))
      by (apply reply.le_at_bytes; [exact HQ | unfold G_QUIT; lia | rewrite length_le4; unfold G_QUIT; lia]).
    rewrite SEGS in QB. apply (bytes_at_transfer rsegs mem); [exact QB|]. intros i Hi. rewrite length_le4 in Hi.
    assert (W : vr_writes (G_QUIT + i)) by (unfold vr_writes; right; right; lia). exact (proj1 (WK _ W)). }
  intros i Hi. assert (W : vr_writes (G_QUIT + i)) by (unfold vr_writes; right; right; lia).
  apply (proj2 (WK _ W)). rewrite <- SEGS. exact (HQW i Hi).
Qed.

End T.

Lemma empty_k1 : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fdw : word),
  bytes_at rsegs m (bv_unsigned s2) (le4 fdw) ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-902)) a1 a2 a3 a4 a5 a6 a7
                                       (Mem.sx32 fdw) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x176c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x176bc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m fdw HB.
  pose proof (verbs_receive_disp.read_all _ _ _ HB) as RD. rewrite length_le4 in RD.
  rewrite (wa_of_var s2 (bv_unsigned s2) eq_refl) in RD.
  do 2 zstep. apply evt_done. reflexivity.
Qed.

Section E.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis SRESP : forall f : YK11.FPState, @sup_resp_contract f rc B API.

Local Notation D := (s_D S).

Lemma vr_br_empty : forall (f : YK11.FPState) rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  @vr_state f _ B API S rg verbs_receive_tok.VR_EMPTY mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  toks D = [] -> getr rg 18 = Z_to_bv 64 (s_msg S) -> (k1 + 8 <= 32)%nat ->
  (forall rg0, getr rg0 18 = Mem.sx32 (Z_to_bv 64 (s_fd S)) -> join_k B API S 0x176c8 10 rg0 R1 k1 qv P) ->
  SR rsegs c P.
Proof using HF HS SRESP.
  intros f rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P HST TK E18 HK JOIN.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof HST as (_ & _ & VR & H & _).
  pose proof (h_rel B API S _ _ _ _ _ _ _ _ H) as HR.
  pose proof (h_ro B API S _ _ _ _ _ _ _ _ H) as RO1. rewrite SEGS in RO1.
  pose proof (verbs_receive_br_link.msg_keep B API HF S HS L1 A1 mem1 md1 HR RO1) as MK0.
  pose proof (ok_m63 B API S HS) as M63. pose proof (ok_m4k B API S HS) as M4K.
  eapply (@ka_nw f _ B API HF S HS rg verbs_receive_tok.VR_EMPTY mem1 md1 L1 A1 R1 O1 k1 qv None jk c _ P HST).
  { unfold Regs6ss.mkR_of. apply empty_k1 with (fdw := Z_to_bv 64 (s_fd S)).
    change (reg_get rg 18) with (getr rg 18). rewrite E18. rewrite unsigned_lit by lia. exact MK0. }
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R' pc' rg' mem2 EQ X MK. cbv beta in EQ. injection EQ as ER EP. subst R' pc'.
  assert (VR' : vregs S rg').
  { destruct VR as (V2 & V3 & V4 & V8 & V9 & V25 & V26 & V27).
    split; [rewrite (getr_of_eqv _ _ 2 X eq_refl); exact V2|].
    split; [rewrite (getr_of_eqv _ _ 3 X eq_refl); exact V3|].
    split; [rewrite (getr_of_eqv _ _ 4 X eq_refl); exact V4|].
    split; [rewrite (getr_of_eqv _ _ 8 X eq_refl); exact V8|].
    split; [rewrite (getr_of_eqv _ _ 9 X eq_refl); exact V9|].
    split; [rewrite (getr_of_eqv _ _ 25 X eq_refl); exact V25|].
    split; [rewrite (getr_of_eqv _ _ 26 X eq_refl); exact V26|].
    rewrite (getr_of_eqv _ _ 27 X eq_refl); exact V27. }
  pose proof (MK 0x176c4 eq_refl VR') as HST1.
  apply (@resp_join f _ B API HF S HS SRESP rg' R1 k1 qv false 0x176c4 0x176c8 rg' mem2 md1 L1 A1 R1 O1 k1 jk _
           (-902) P).
  - right; right. split; reflexivity.
  - exact HST1.
  - rewrite (getr_of_eqv _ _ 10 X eq_refl). reflexivity.
  - lia.
  - reflexivity.
  - intros Ej. lia.
  - rewrite TK. reflexivity.
  - lia.
  - lia.
  - exact HK.
  - apply JOIN. rewrite (getr_of_eqv _ _ 18 X eq_refl). reflexivity.
Qed.

End E.
