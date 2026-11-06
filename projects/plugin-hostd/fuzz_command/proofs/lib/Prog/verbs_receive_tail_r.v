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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_br.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require VerbsMem rec_shape_of_c RecKindB reply rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_tail0 reply_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma tlr_nd3 : forall a b c : Z, List.NoDup [a; b; c] -> List.NoDup [a; b] /\ a <> c /\ b <> c.
Proof.
  intros a b c H. apply List.NoDup_cons_iff in H as [N1 H]. apply List.NoDup_cons_iff in H as [N2 _].
  split; [|split].
  - constructor; [intros [E|[]]; apply N1; left; exact E | constructor; [intros []|constructor]].
  - intros E. apply N1. right. left. symmetry. exact E.
  - intros E. apply N2. left. symmetry. exact E.
Qed.

Lemma tlr_no0 : forall x : list byte, no0 x -> Forall (fun c => bv_unsigned c <> 0) x.
Proof.
  intros x H. rewrite Forall_forall. intros c Hc E. apply H.
  assert (Ec : c = Z_to_bv 8 0) by (apply bv_eq; rewrite E; reflexivity). rewrite <- Ec. exact Hc.
Qed.

Lemma tlr_sbn : forall b k, sb_n (sb_n b k) 1 = sb_n b (k + 1).
Proof. intros b k. unfold sb_n, SB_REQ. cbn [sb_live sb_bytes sb_cap]. f_equal; lia. Qed.

Lemma tlr_rpw_gq : forall i, 0 <= i < 4 -> ~ rp_writes (G_QUIT + i).
Proof. intros i Hi Ha. unfold rp_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT in Ha. lia. Qed.

Section TR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis RP : forall f : YK11.FPState, @reply_contract f rc B API.
Local Notation D := (s_D S).
Local Notation VS f := (@vr_state f _ B API S).
Local Notation TS f := (@tl_state f _ B API S).

Lemma tlr_rpw_low : forall a, rp_writes a -> a < alloc_ceiling.
Proof. intros a Ha. pose proof alloc_ceiling_val. unfold rp_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha. lia. Qed.

Lemma tlr_le_at : forall m a bs, bytes_at rsegs m a bs -> le_at B m a bs.
Proof using HF.
  intros m a bs (_ & _ & H). unfold VerbsB.le_at, blk_data. intros i Hi.
  rewrite (vf_segs B API HF).
  pose proof (H (Z.to_nat i) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. exact E.
Qed.

Lemma tlr_heap : forall rg mem1 md1 L1 A1 R1 O1 k1 q nq x L' A' rg' mem' md' R' O' k,
  vheap B API S L1 A1 mem1 md1 R1 O1 k1 (Some (q, nq, x)) ->
  spZ rg = s_spf S ->
  RecKindB.call_post_rec B (aa_MR API) RP_K L1 A1 rg mem1 md1 rp_writes (fun a => In a (map fst O1))
    L' A' rg' mem' md' ->
  ro_agree (ms_segs B) mem' -> g_rec_rep (ms_segs B) L' A' mem' R' O' ->
  (forall pn, In pn (blocks L1 A1) -> ~ In pn O1 -> pn <> (q, nq) -> In pn (blocks L' A')) ->
  (forall pn, In pn (blocks L' A') -> (In pn (blocks L1 A1) /\ ~ In pn O1 /\ pn <> (q, nq)) \/ In pn O') ->
  (forall pn, In pn (blocks L1 A1) -> ~ In pn O1 -> ~ In pn O') ->
  (length (st_regions A1) <= length (st_regions A'))%nat ->
  blocks_kept B L1 A1 mem1 mem' (fun a => (exists j, In (a, j) O1) \/ a = q) ->
  (k <= 1)%nat -> res_ok_slots A' (sb_n (sb_n (s_b S) k1) k) -> (k1 + 1 <= 32)%nat ->
  vheap B API S L' A' mem' md' R' O' (k1 + 1) None.
Proof using HF HS.
  intros rg mem1 md1 L1 A1 R1 O1 k1 q nq x L' A' rg' mem' md' R' O' k H SPR POST RO' REC' KEEPB SUB NO' RLEN BK
    HK RES' HK1.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  assert (KR : 0 <= RP_K <= 14336) by (unfold RP_K; lia).
  pose proof POST as (HM' & HW' & _).
  pose proof (h_t _ _ _ _ _ _ _ _ _ _ _ H) as T.
  pose proof (t_rel _ _ _ _ _ _ _ _ _ _ _ T) as REL. pose proof REL as (HM1 & _).
  pose proof (t_rec _ _ _ _ _ _ _ _ _ _ _ T) as REC1.
  pose proof (t_x _ _ _ _ _ _ _ _ _ _ _ T) as HX.
  pose proof (t_xsz _ _ _ _ _ _ _ _ _ _ _ T) as HXS.
  pose proof (t_xap _ _ _ _ _ _ _ _ _ _ _ T) as HXA.
  destruct (tlr_nd3 (s_lb S) (s_cb S) q (t_xnd _ _ _ _ _ _ _ _ _ _ _ T)) as (ND2 & NLQ & NCQ).
  assert (XNO : forall pn, In pn (xbl S (Some (q, nq, x))) -> ~ In pn O1).
  { intros pn Hp Ho. apply (proj2 (HX pn Hp)). apply in_map_iff. exists pn. split; [reflexivity | exact Ho]. }
  assert (QX : In (q, nq) (xbl S (Some (q, nq, x)))) by (right; right; left; reflexivity).
  assert (NQ1 : 1 <= nq) by exact (HXS _ QX).
  assert (SUBX : forall pn, In pn (xbl S None) -> In pn (xbl S (Some (q, nq, x))) /\ fst pn <> q).
  { intros pn [E|[E|[]]]; subst pn.
    - split; [left; reflexivity | exact NLQ].
    - split; [right; left; reflexivity | exact NCQ]. }
  assert (KXB : forall pn, In pn (xbl S (Some (q, nq, x))) -> fst pn <> q -> In pn (blocks L' A') /\ ~ In pn O').
  { intros pn Hp Hq. destruct (HX pn Hp) as [Hin _]. pose proof (XNO pn Hp) as Hno.
    split; [apply KEEPB; [exact Hin | exact Hno | intros E; subst pn; exact (Hq eq_refl)] | exact (NO' pn Hin Hno)]. }
  unfold blocks_kept in BK.
  assert (KX : forall a k0 s bs, In (a, k0) (xbl S (Some (q, nq, x))) -> a <> q -> a <= s ->
              s + Z.of_nat (length bs) <= a + k0 -> bytes_at rsegs mem1 s bs -> bytes_at rsegs mem' s bs).
  { intros a k0 s bs Hx Hq H1 H2 Hb. destruct (HX (a, k0) Hx) as [Hin Hno]. cbn [fst] in Hno.
    apply (bytes_at_transfer rsegs mem1); [exact Hb|]. intros i Hi.
    replace (s + i) with (a + (s - a + i)) by ring. rewrite <- SEGS.
    apply (BK a k0); [exact Hin | | lia].
    intros [(j & Hj)|E]; [apply Hno; apply in_map_iff; exists (a, j); split; [reflexivity | exact Hj] | exact (Hq E)]. }
  constructor.
  - constructor.
    + eapply (rel_call B API (vf_ax B API HF) (vf_ctxo B API HF)); [exact REL | exact POST | exact RLEN | | | | ].
      * intros a [Ha|Ha]; [left; rewrite SPR in Ha; unfold s_spf, VR_K in *; lia | right; exact Ha].
      * intros a Ha. right. unfold rp_writes, vr_writes in *. tauto.
      * intros a Hs Hn. unfold scratch_k in Hs, Hn. rewrite SPR in Hn.
        destruct Hs as [Hs|Hs]; [|exfalso; apply Hn; right; exact Hs].
        split; [unfold VR_K in *; lia|]. unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT, VR_K in *. lia.
      * intros a k0 i Hin Hx Hi.
        assert (Hno : ~ In (a, k0) (s_O S)) by (intros Ho; apply Hx; apply in_map_iff; exists (a, k0); split; [reflexivity | exact Ho]).
        destruct (t_old _ _ _ _ _ _ _ _ _ _ _ T (a, k0) Hin Hno) as [Hin1 Hno1].
        apply (BK a k0); [exact Hin1 | | exact Hi].
        intros [(j & Hj)|E].
        -- apply (addr_notin B API L1 A1 mem1 md1 R1 O1 a k0 HM1 REC1 Hin1 ltac:(lia) Hno1).
           apply in_map_iff. exists (a, j). split; [reflexivity | exact Hj].
        -- subst a. destruct (HXA (q, nq) QX (q, k0) Hin Hno) as [E|E]; cbn [fst snd] in E; lia.
    + exact REC'.
    + exact RO'.
    + destruct (KXB _ (proj1 (SUBX _ (or_introl eq_refl))) (proj2 (SUBX _ (or_introl eq_refl)))) as [HLB _].
      destruct (proj1 (YI04.blocks_In L' A' _ _) HLB) as (p0 & _ & Hp0).
      exact (YI04.init_done_of_block A' (p0, s_nlb S) HW' Hp0).
    + split; [|exact HK1].
      apply (st_le B API S HS A' (sb_n (sb_n (s_b S) k1) k) (k1 + 1)); [|exact HK1|exact RES'].
      unfold RecKindB.sb_le, sb_n, SB_REQ. cbn [sb_live sb_bytes sb_cap]. lia.
    + intros pn Hin Hno. destruct (t_old _ _ _ _ _ _ _ _ _ _ _ T pn Hin Hno) as [H1 H2].
      split; [|exact (NO' pn H1 H2)]. apply KEEPB; [exact H1 | exact H2 |].
      intros E. subst pn. destruct (HXA (q, nq) QX (q, nq) Hin Hno) as [E|E]; cbn [fst snd] in E; lia.
    + intros pn Hin. destruct (SUB pn Hin) as [(H1 & H2 & H3)|H1]; [|right; left; exact H1].
      destruct (t_sub _ _ _ _ _ _ _ _ _ _ _ T pn H1) as [H4|[H4|H4]]; [left; exact H4 | exfalso; exact (H2 H4)|].
      right; right. destruct H4 as [E|[E|[E|[]]]]; [left; exact E | right; left; exact E | exfalso; exact (H3 (eq_sym E))].
    + intros pn Hp. destruct (SUBX pn Hp) as [Hp' Hq].
      destruct (KXB pn Hp' Hq) as [H1 H2]. split; [exact H1|].
      destruct pn as [a k0]. apply (addr_notin B API L' A' mem' md' R' O' a k0 HM' REC' H1); [exact (HXS _ Hp') | exact H2].
    + intros pn Hp. apply HXA. exact (proj1 (SUBX pn Hp)).
    + exact ND2.
    + intros pn Hp. apply HXS. exact (proj1 (SUBX pn Hp)).
  - apply (KX (s_lb S) (s_nlb S) (s_lb S)); [left; reflexivity | exact NLQ | lia | | exact (h_lb _ _ _ _ _ _ _ _ _ _ _ H)].
    rewrite !length_app, repeat_length. cbn [length]. pose proof (line_le_upto S). unfold s_nlb. lia.
  - eapply Forall2_impl; [|exact (h_tok _ _ _ _ _ _ _ _ _ _ _ H)]. intros p w ((Hb & Hnz) & H1 & H2).
    split; [split; [|exact Hnz]|split; assumption].
    apply (KX (s_cb S) (s_ncb S)); [right; left; reflexivity | exact NCQ | exact H1 | | exact Hb].
    rewrite length_app. cbn [length]. lia.
  - exact I.
Qed.

Lemma tl_call_reply : forall rg mem1 md1 L1 A1 R1 O1 k1 qv q nq x jk c ret P,
  VS fx rg REPLY mem1 md1 L1 A1 R1 O1 k1 qv (Some (q, nq, x)) jk c ->
  getr rg 1 = Z_to_bv 64 ret -> YK0s.ret_ok (Z_to_bv 64 ret) ->
  getr rg 11 = Z_to_bv 64 q -> no0 x -> (length x <= 4096)%nat -> (k1 + 1 <= 32)%nat ->
  r_nreplies R1 < 2 ^ 31 - 1 ->
  (forall rg' mem' md' L' A' O' c',
     VS fx rg' ret mem' md' L' A' (fst (socket_send_m R1 (x ++ [Z_to_bv 8 0]))) O' (k1 + 1) qv None jk c' ->
     regs_preserved rg rg' -> SR rsegs c' P) ->
  SR rsegs c P.
Proof using HF HS RP.
  intros rg mem1 md1 L1 A1 R1 O1 k1 qv q nq x jk c ret P HST E1 RET E11 NZ LX HK NREP KONT.
  pose proof (vf_segs B API HF) as SEGS.
  assert (KR : 0 <= RP_K <= 14336) by (unfold RP_K; lia).
  destruct (vs_pre B API HF S HS rg REPLY mem1 md1 L1 A1 R1 O1 k1 qv _ jk c RP_K ret HST E1 RET KR)
    as (PRE & SPR & FZ & F18 & RO & REC & HM & _).
  pose proof HST as (EC & FPK0 & VR & H & FR & GQ & GW).
  pose proof (h_res _ _ _ _ _ _ _ _ _ _ _ H) as (RES & _).
  destruct (h_x _ _ _ _ _ _ _ _ _ _ _ H (q, nq) (or_intror (or_intror (or_introl eq_refl)))) as [INQ NOQ].
  assert (NOQ' : ~ In (q, nq) O1).
  { intros Ho. apply NOQ. apply in_map_iff. exists (q, nq). split; [reflexivity | exact Ho]. }
  destruct (h_q _ _ _ _ _ _ _ _ _ _ _ H) as [BQ BL].
  destruct (st_f18 B API HF _ _ _ _ HM) as [_ (cn & SSP)].
  assert (ROOM : room_slots (sb_n (sb_n (s_b S) k1) RP_MALLOCS) RP_REQ).
  { pose proof (st_room B API S HS (k1 + 1) (@nil Z) RP_REQ ltac:(cbn [length]; lia) ltac:(constructor)
      ltac:(unfold RP_REQ; lia)) as R0.
    cbn [RecKindB.sb_mallocs fold_left] in R0. unfold RP_MALLOCS. rewrite tlr_sbn. exact R0. }
  subst c. rewrite <- SEGS.
  eapply SR_bind.
  { exact (RP fx L1 A1 rg mem1 md1 (sb_n (s_b S) k1) R1 O1 q nq x cn PRE RO E11 INQ NOQ'
      (tlr_le_at _ _ _ BQ) (tlr_no0 x NZ) ltac:(lia) ltac:(lia) REC NREP SSP RES ROOM). }
  intros c' (L' & A' & rg' & mem' & md' & O' & k & -> & POST & RO' & REC' & _ & KEEPB & SUB & _ & NO' & RLEN & BK
    & _ & KK & RES').
  pose proof POST as (HM' & _ & _ & _ & _ & HPR & _ & HFR & _ & _).
  pose proof (h_rel _ _ _ _ _ _ _ _ _ _ _ H) as (HM1 & _).
  pose proof (frame_keep B API HF S HS RP_K rg mem1 mem' L1 A1 L' A' md1 md' rp_writes HM1 HM' SPR tlr_rpw_low HFR)
    as KP.
  pose proof (gq_keep B API HF S HS RP_K rg mem1 mem' L1 A1 L' A' md1 md' rp_writes HM1 HM' SPR KR tlr_rpw_gq HFR)
    as KQ.
  destruct (gq_transfer mem1 mem' qv KQ GQ GW) as [GQ' GW'].
  rewrite SEGS.
  apply (KONT rg' mem' md' L' A' O'); [|exact HPR].
  split; [rewrite E1; reflexivity|].
  split; [exact FPK0|].
  split; [exact (vregs_pres S rg rg' VR HPR)|].
  split.
  { exact (tlr_heap rg mem1 md1 L1 A1 R1 O1 k1 q nq x L' A' rg' mem' md' _ O' k H SPR POST
      RO' REC' KEEPB SUB NO' RLEN BK KK RES' HK). }
  split; [exact (vfr_keep B API S HS mem1 mem' jk KP FR)|].
  split; [exact GQ' | exact GW'].
Qed.

End TR.
