(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module names changed; 179 of its 215 lines of code are new or changed and 1080 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/verbs_receive_br.v, with its module paths and module names changed; 352 of its 395 lines of code are new or changed and 172 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/verbs_receive_fin_t.v, with its module paths and module names changed; 258 of its 300 lines of code are new or changed and 353 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_call verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_br.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c RecKindB reply rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_tail0.
Import ListNotations.
Local Open Scope Z_scope.

Lemma tlf_k1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x17b18) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2 a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x18ad0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17b10) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 zstep. apply evt_done. reflexivity.
Qed.

Lemma tlf_k2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x17b20) sp gp tp t0 t1 t2 s0 s1 s0 a1 a2 a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x18ad0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17b18) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 zstep. apply evt_done. reflexivity.
Qed.

Lemma tlf_m1 : forall (rg F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => exists R', ms' = MS R' F (Z_to_bv 64 0x18ad0) fc None m (seg_rom rsegs) /\
       reg_get R' 1 = Z_to_bv 64 0x17b18 /\ reg_get R' 10 = reg_get rg 9 /\
       (forall r, callee_saved r -> reg_get R' (Z_to_bv 5 r) = reg_get rg (Z_to_bv 5 r)))
    (MS (Regs6ss.mkR_of rg) F (Z_to_bv 64 0x17b10) fc None m (seg_rom rsegs)).
Proof.
  intros rg F fc m. eapply evt_mono; [unfold Regs6ss.mkR_of; apply tlf_k1|].
  intros ms' E. cbv beta in E. subst ms'. eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. intros r Hr. cs_cases r Hr; reflexivity.
Qed.

Lemma tlf_m2 : forall (rg F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => exists R', ms' = MS R' F (Z_to_bv 64 0x18ad0) fc None m (seg_rom rsegs) /\
       reg_get R' 1 = Z_to_bv 64 0x17b20 /\ reg_get R' 10 = reg_get rg 8 /\
       (forall r, callee_saved r -> reg_get R' (Z_to_bv 5 r) = reg_get rg (Z_to_bv 5 r)))
    (MS (Regs6ss.mkR_of rg) F (Z_to_bv 64 0x17b18) fc None m (seg_rom rsegs)).
Proof.
  intros rg F fc m. eapply evt_mono; [unfold Regs6ss.mkR_of; apply tlf_k2|].
  intros ms' E. cbv beta in E. subst ms'. eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. intros r Hr. cs_cases r Hr; reflexivity.
Qed.

Section TF.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis FREE : forall f : YK11.FPState, @free_contract f rc B API.
Local Notation D := (s_D S).
Local Notation VS f := (@vr_state f _ B API S).
Local Notation TS f := (@tl_state f _ B API S).

Lemma tlf_of_vs : forall rg pc mem1 md1 L1 A1 R1 O1 k1 qv jk c,
  VS fx rg pc mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  TS fx rg pc mem1 md1 L1 A1 R1 O1 k1 qv [(s_lb S, s_nlb S); (s_cb S, s_ncb S)] jk c.
Proof.
  intros rg pc mem1 md1 L1 A1 R1 O1 k1 qv jk c (E & FPK & VR & H & FR & GQ & GW).
  split; [exact E|]. split; [exact FPK|]. split; [exact VR|].
  split; [exact (h_t _ _ _ _ _ _ _ _ _ _ _ H)|]. split; [exact FR|]. split; [exact GQ | exact GW].
Qed.

Lemma tlf_seg : forall rg J J' (v : word) mem1 md1 L1 A1 R1 O1 k1 qv X jk c P,
  TS fx rg J mem1 md1 L1 A1 R1 O1 k1 qv X jk c ->
  (forall (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
     evt rsegs (fun ms' => exists R', ms' = MS R' F (Z_to_bv 64 0x18ad0) fc None m (seg_rom rsegs) /\
          reg_get R' 1 = Z_to_bv 64 J' /\ reg_get R' 10 = v /\
          (forall r, callee_saved r -> reg_get R' (Z_to_bv 5 r) = reg_get rg (Z_to_bv 5 r)))
       (MS (Regs6ss.mkR_of rg) F (Z_to_bv 64 J) fc None m (seg_rom rsegs))) ->
  (forall rg' mem2 c', TS fx rg' 0x18ad0 mem2 md1 L1 A1 R1 O1 k1 qv X jk c' ->
     getr rg' 1 = Z_to_bv 64 J' -> getr rg' 10 = v -> SR rsegs c' P) ->
  SR rsegs c P.
Proof using HF HS.
  intros rg J J' v mem1 md1 L1 A1 R1 O1 k1 qv X jk c P HST EV K.
  pose proof HST as (_ & _ & VR & _).
  apply (tl_w B API HF S HS rg J mem1 md1 L1 A1 R1 O1 k1 qv X jk c []
    (fun ms' => exists R', ms' = MS R' fp_regs (Z_to_bv 64 0x18ad0) fp_csr None (normalize rsegs mem1) (seg_rom rsegs) /\
          reg_get R' 1 = Z_to_bv 64 J' /\ reg_get R' 10 = v /\
          (forall r, callee_saved r -> reg_get R' (Z_to_bv 5 r) = reg_get rg (Z_to_bv 5 r))) P HST).
  - intros x _ _. exact I.
  - eapply evt_mono; [exact (EV fp_regs fp_csr (normalize rsegs mem1))|].
    intros ms' (R' & E & H1 & H10 & HC).
    split; [exists R'; split; [exact E|]; split; [exact H1|]; split; [exact H10 | exact HC]|].
    exists R', (Z_to_bv 64 0x18ad0), (normalize rsegs mem1). split; [exact E|].
    split; [apply munch_refl | apply wmono_refl].
  - intros R' pc' m' rg' mem2 (R2 & EQ & H1 & H10 & HC) X' MK.
    injection EQ as ER EP EM. subst R2 pc' m'.
    assert (PR : regs_preserved rg rg') by exact (pres_of rg R' rg' X' HC).
    apply (K rg' mem2 _ (MK 0x18ad0 eq_refl (vregs_pres S rg rg' VR PR))).
    + rewrite (getr_of_eqv _ _ 1 X' eq_refl). exact H1.
    + rewrite (getr_of_eqv _ _ 10 X' eq_refl). exact H10.
Qed.

Lemma tlf_pre : forall rg mem1 md1 L1 A1 R1 O1 k1 X ret K,
  vtail B API S L1 A1 mem1 md1 R1 O1 k1 X -> vregs S rg ->
  getr rg 1 = Z_to_bv 64 ret -> YK0s.ret_ok (Z_to_bv 64 ret) -> 0 <= K <= 14336 ->
  call_pre_k B (aa_MR API) K L1 A1 rg mem1 md1 /\ spZ rg = s_spf S.
Proof using HF HS.
  intros rg mem1 md1 L1 A1 R1 O1 k1 X ret K H VR E1 RET HK.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & SP16 & _). pose proof alloc_ceiling_val as ACV.
  pose proof (ok_ts B API S HS) as TSK.
  pose proof (ok_pre B API S HS) as (_ & _ & _ & _ & _ & _ & _ & _ & TP0 & _).
  pose proof (t_rel _ _ _ _ _ _ _ _ _ _ _ H) as (HM1 & HW1 & HB1 & _ & _ & _ & _ & _ & HS1).
  destruct VR as (V2 & V3 & V4 & _).
  assert (SPR : spZ rg = s_spf S).
  { unfold spZ. rewrite V2. apply unsigned_lit. unfold s_spf, VR_K in *. lia. }
  split; [|exact SPR].
  split; [exact HM1|]. split; [exact HW1|]. split; [exact HB1|].
  split; [rewrite E1; exact RET|].
  split; [rewrite SPR; unfold s_spf; replace (spZ (s_regs S) - 608) with (spZ (s_regs S) + (-38) * 16) by ring;
          rewrite Z.mod_add by lia; exact SP16|].
  split; [rewrite SPR; unfold s_spf, VR_K in *; lia|].
  split; [rewrite SPR; unfold s_spf in *; lia|].
  split; [intros a Ha; apply HS1; left; rewrite SPR in Ha; unfold s_spf, VR_K in *; lia|].
  split; [rewrite V4; exact TP0|].
  split; [intros a Ha; apply HS1; right; exact Ha|].
  intros HI. rewrite (t_init _ _ _ _ _ _ _ _ _ _ _ H) in HI. discriminate.
Qed.

Lemma tlf_tail : forall rg mem1 md1 L1 A1 R1 O1 k1 X1 X2 p n L2 A2 rg2 mem2 md2,
  vtail B API S L1 A1 mem1 md1 R1 O1 k1 (X1 ++ (p, n) :: X2) ->
  spZ rg = s_spf S ->
  call_post_k B (aa_MR API) ALLOC_STACK L1 A1 rg mem1 md1 (fun a => p <= a < p + n) L2 A2 rg2 mem2 md2 ->
  (exists b1 b2, blocks L1 A1 = b1 ++ (p, n) :: b2 /\ blocks L2 A2 = b1 ++ b2) ->
  blocks_kept B L1 A1 mem1 mem2 (fun a => a = p) ->
  ro_agree (ms_segs B) mem2 ->
  (st_init_done A1 = true -> st_init_done A2 = true) ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  res_ok_slots A2 (sb_free (sb_n (s_b S) k1) n) ->
  vtail B API S L2 A2 mem2 md2 R1 O1 k1 (X1 ++ X2).
Proof using HF HS.
  intros rg mem1 md1 L1 A1 R1 O1 k1 X1 X2 p n L2 A2 rg2 mem2 md2 H SPR POST (b1 & b2 & BL1 & BL2) KEPT RO2 INIT
    RLEN RES.
  pose proof (vf_segs B API HF) as SEGS. pose proof (vf_errno B API HF) as ERR.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  pose proof (aa_laws API) as LAWS.
  pose proof (t_rel _ _ _ _ _ _ _ _ _ _ _ H) as REL. pose proof REL as (HM1 & _).
  pose proof POST as (HM2 & _ & _ & _ & _ & _ & _ & HFR & _ & _).
  assert (XIN : In (p, n) (X1 ++ (p, n) :: X2)) by (apply in_or_app; right; left; reflexivity).
  assert (XSUB : forall pn, In pn (X1 ++ X2) -> In pn (X1 ++ (p, n) :: X2)).
  { intros pn Hp. apply in_app_or in Hp. apply in_or_app. destruct Hp as [Hp|Hp]; [left; exact Hp | right; right; exact Hp]. }
  destruct (t_x _ _ _ _ _ _ _ _ _ _ _ H (p, n) XIN) as [PB PNO]. cbn [fst] in PNO.
  pose proof (t_xsz _ _ _ _ _ _ _ _ _ _ _ H (p, n) XIN) as PSZ. cbn [snd] in PSZ.
  pose proof (t_xap _ _ _ _ _ _ _ _ _ _ _ H (p, n) XIN) as OLDAP. cbn [fst snd] in OLDAP.
  pose proof (mr_blocks_disjoint B _ LAWS _ _ _ _ HM1) as DJ1.
  assert (NMID : ~ In (p, n) (b1 ++ b2)) by (apply reply.mid_not_side; [rewrite <- BL1; exact DJ1 | cbn [snd]; lia]).
  assert (KEEPB : forall pn, In pn (blocks L1 A1) -> pn <> (p, n) -> In pn (blocks L2 A2)).
  { intros pn Hin Hne. rewrite BL1 in Hin. rewrite BL2. apply in_app_or in Hin. apply in_or_app.
    destruct Hin as [Hin|[Hin|Hin]]; [left; exact Hin | exfalso; exact (Hne (eq_sym Hin)) | right; exact Hin]. }
  assert (INB2 : forall pn, In pn (blocks L2 A2) -> In pn (blocks L1 A1) /\ pn <> (p, n)).
  { intros pn Hin. rewrite BL2 in Hin. split.
    - rewrite BL1. apply in_app_or in Hin. apply in_or_app.
      destruct Hin as [Hin|Hin]; [left; exact Hin | right; right; exact Hin].
    - intros E. subst pn. exact (NMID Hin). }
  assert (EBLK : forall a, p <= a < p + n -> a < alloc_ceiling /\ ~ in_img B a).
  { intros a Ha. destruct (blk_low B API HF L1 A1 mem1 md1 p n (a - p) HM1 PB ltac:(lia)) as (_ & Hc & Hni & _).
    replace (p + (a - p)) with a in Hni by ring. split; [lia | exact Hni]. }
  assert (NOTP : forall pn, In pn O1 -> ~ fst pn = p).
  { intros pn Hin E. apply PNO. apply in_map_iff. exists pn. split; [exact E | exact Hin]. }
  constructor.
  - assert (PR : RecKindB.call_post_rec B (aa_MR API) ALLOC_STACK L1 A1 rg mem1 md1 (fun a => p <= a < p + n)
                   (fun _ => False) L2 A2 rg2 mem2 md2) by (apply post_k_rec; exact POST).
    eapply (rel_call B API (vf_ax B API HF) (vf_ctxo B API HF)); [exact REL | exact PR | exact RLEN | | | | ].
    + intros a [Ha|Ha]; [left; rewrite SPR in Ha; unfold s_spf, VR_K, ALLOC_STACK in *; lia | right; exact Ha].
    + intros a Ha. cbv beta in Ha. left. intros [Hd|Hd]; destruct (EBLK a Ha) as [H1 H2]; [lia | exact (H2 Hd)].
    + intros a Hs Hn. unfold scratch_k in Hs, Hn. rewrite SPR in Hn.
      destruct Hs as [Hs|Hs]; [|exfalso; apply Hn; right; exact Hs].
      split; [unfold VR_K in *; lia|].
      unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT, VR_K, ALLOC_STACK in *. lia.
    + intros a k i Hin Hx Hi.
      assert (Hno : ~ In (a, k) (s_O S)) by (intros Ho; apply Hx; apply in_map_iff; exists (a, k); split; [reflexivity | exact Ho]).
      destruct (t_old _ _ _ _ _ _ _ _ _ _ _ H (a, k) Hin Hno) as [Hin1 _].
      pose proof (OLDAP (a, k) Hin Hno) as Dk. cbn [fst snd] in Dk.
      apply (KEPT a k i Hin1); [cbv beta; lia | exact Hi].
  - apply (rec_rep_frame (ms_segs B) G_REC REC_SC L1 A1 mem1 R1 O1 L2 A2 mem2 (t_rec _ _ _ _ _ _ _ _ _ _ _ H)).
    + intros a Ha. destruct (vf_globs B API HF a (rec_glob a Ha)) as (Hi & _ & _ & Hne).
      pose proof (in_img_low B SEGS a Hi) as Hlo.
      destruct (HFR a (or_intror Hi) (vf_globo B API HF L1 A1 mem1 md1 a HM1 (rec_glob a Ha))
                  (vf_globo B API HF L2 A2 mem2 md2 a HM2 (rec_glob a Ha))) as [E W].
      * intros [Hs|Hs]; [rewrite SPR in Hs; unfold s_spf, VR_K, ALLOC_STACK in *; lia | exact (Hne Hs)].
      * cbv beta. intros Ha'. destruct (EBLK a Ha') as [_ H2]. exact (H2 Hi).
      * split; [exact E | apply W].
    + intros p' n' i Hin Hi. destruct (reply.rec_rep_O _ _ _ _ _ _ _ _ (t_rec _ _ _ _ _ _ _ _ _ _ _ H) (p', n') Hin) as [Hb _].
      apply (KEPT p' n' i Hb); [|exact Hi]. cbv beta. exact (NOTP (p', n') Hin).
    + intros pn Hin. destruct (reply.rec_rep_O _ _ _ _ _ _ _ _ (t_rec _ _ _ _ _ _ _ _ _ _ _ H) pn Hin) as [Hb _].
      apply KEEPB; [exact Hb|]. intros E. subst pn. exact (NOTP (p, n) Hin eq_refl).
  - exact RO2.
  - exact (INIT (t_init _ _ _ _ _ _ _ _ _ _ _ H)).
  - destruct (t_res _ _ _ _ _ _ _ _ _ _ _ H) as [_ HK]. split; [|exact HK].
    apply (st_le B API S HS A2 (sb_free (sb_n (s_b S) k1) n) k1); [apply RecKindB.sb_free_le; lia | exact HK | exact RES].
  - intros pn Hin Hno. destruct (t_old _ _ _ _ _ _ _ _ _ _ _ H pn Hin Hno) as [H1 H2]. split; [|exact H2].
    apply KEEPB; [exact H1|]. intros E. subst pn. pose proof (OLDAP (p, n) Hin Hno) as Dk. cbn [fst snd] in Dk. lia.
  - intros pn Hin. destruct (INB2 pn Hin) as [H1 H2].
    destruct (t_sub _ _ _ _ _ _ _ _ _ _ _ H pn H1) as [H3|[H3|H3]]; [left; exact H3 | right; left; exact H3|].
    right. right. apply in_app_or in H3. apply in_or_app.
    destruct H3 as [H3|[H3|H3]]; [left; exact H3 | exfalso; exact (H2 (eq_sym H3)) | right; exact H3].
  - intros pn Hp. destruct (t_x _ _ _ _ _ _ _ _ _ _ _ H pn (XSUB pn Hp)) as [H1 H2]. split; [|exact H2].
    apply KEEPB; [exact H1|]. intros E. subst pn.
    pose proof (t_xnd _ _ _ _ _ _ _ _ _ _ _ H) as ND. rewrite map_app in ND. cbn [map] in ND.
    apply List.NoDup_remove_2 in ND. apply ND. rewrite <- map_app. exact (in_map fst _ _ Hp).
  - intros pn Hp. exact (t_xap _ _ _ _ _ _ _ _ _ _ _ H pn (XSUB pn Hp)).
  - pose proof (t_xnd _ _ _ _ _ _ _ _ _ _ _ H) as ND. rewrite map_app in ND. cbn [map] in ND.
    rewrite map_app. exact (List.NoDup_remove_1 _ _ _ ND).
  - intros pn Hp. exact (t_xsz _ _ _ _ _ _ _ _ _ _ _ H pn (XSUB pn Hp)).
Qed.

Lemma tlf_free : forall rg mem1 md1 L1 A1 R1 O1 k1 qv X1 X2 p n jk c ret P,
  TS fx rg 0x18ad0 mem1 md1 L1 A1 R1 O1 k1 qv (X1 ++ (p, n) :: X2) jk c ->
  getr rg 10 = Z_to_bv 64 p -> getr rg 1 = Z_to_bv 64 ret -> YK0s.ret_ok (Z_to_bv 64 ret) ->
  (forall rg' mem' md' L' A' c', TS fx rg' ret mem' md' L' A' R1 O1 k1 qv (X1 ++ X2) jk c' -> SR rsegs c' P) ->
  SR rsegs c P.
Proof using HF HS FREE.
  intros rg mem1 md1 L1 A1 R1 O1 k1 qv X1 X2 p n jk c ret P (-> & FPK & VR & H & FR & GQ & GW) E10 E1 RET K.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof (t_rel _ _ _ _ _ _ _ _ _ _ _ H) as REL. pose proof REL as (HM1 & _).
  destruct (tlf_pre rg mem1 md1 L1 A1 R1 O1 k1 _ ret ALLOC_STACK H VR E1 RET ltac:(unfold ALLOC_STACK; lia))
    as [PRE SPR].
  assert (XIN : In (p, n) (X1 ++ (p, n) :: X2)) by (apply in_or_app; right; left; reflexivity).
  destruct (t_x _ _ _ _ _ _ _ _ _ _ _ H (p, n) XIN) as [PB _].
  pose proof PB as PB'. unfold blocks in PB'. apply in_map_iff in PB' as ([q n'] & Eq & Hq).
  cbv beta in Eq; cbn [fst snd] in Eq. injection Eq as Ep En. subst n'.
  pose proof (FREE fx) as FRE. unfold free_contract in FRE. rewrite SEGS, (vf_free B API HF) in FRE.
  eapply SR_bind.
  { apply (FRE L1 A1 rg mem1 md1 q n (sb_n (s_b S) k1)).
    - apply (proj2 (call_pre_k_alloc B (aa_MR API) L1 A1 rg mem1 md1)). exact PRE.
    - pose proof (t_ro _ _ _ _ _ _ _ _ _ _ _ H) as RO1. rewrite SEGS in RO1. exact RO1.
    - exact Hq.
    - rewrite Ep. exact E10.
    - exact (proj1 (t_res _ _ _ _ _ _ _ _ _ _ _ H)). }
  intros c' (L' & A' & rg' & mem' & md' & -> & POST & BLK & KEPT & RO' & _ & _ & INIT & RLEN & RES).
  rewrite Ep in POST, BLK, KEPT.
  pose proof (proj1 (call_post_k_alloc B (aa_MR API) L1 A1 rg mem1 md1 _ L' A' rg' mem' md') POST) as POSTk.
  pose proof POSTk as (HM' & _ & _ & _ & _ & HPR & _ & HFR & _ & _).
  assert (RO2 : ro_agree (ms_segs B) mem') by (rewrite SEGS; exact RO').
  assert (EL : forall a, p <= a < p + n -> a < alloc_ceiling).
  { intros a Ha. destruct (blk_low B API HF L1 A1 mem1 md1 p n (a - p) HM1 PB ltac:(lia)) as (_ & Hc & _ & _). lia. }
  assert (EQ : forall i, 0 <= i < 4 -> ~ (p <= G_QUIT + i < p + n)).
  { intros i Hi Hr. destruct (blk_low B API HF L1 A1 mem1 md1 p n (G_QUIT + i - p) HM1 PB ltac:(lia)) as (_ & _ & Hni & _).
    apply Hni. replace (p + (G_QUIT + i - p)) with (G_QUIT + i) by ring.
    exact (proj1 (vf_globs B API HF _ (gq_glob i Hi))). }
  pose proof (frame_keep B API HF S HS ALLOC_STACK rg mem1 mem' L1 A1 L' A' md1 md' (fun a => p <= a < p + n)
                HM1 HM' SPR EL HFR) as KP.
  pose proof (gq_keep B API HF S HS ALLOC_STACK rg mem1 mem' L1 A1 L' A' md1 md' (fun a => p <= a < p + n)
                HM1 HM' SPR ltac:(unfold ALLOC_STACK; lia) EQ HFR) as KQ.
  apply (K rg' mem' md' L' A').
  split; [rewrite E1; reflexivity|].
  split; [exact FPK|].
  split; [exact (vregs_pres S rg rg' VR HPR)|].
  split; [exact (tlf_tail rg mem1 md1 L1 A1 R1 O1 k1 X1 X2 p n L' A' rg' mem' md' H SPR POSTk BLK KEPT RO2 INIT RLEN RES)|].
  split; [exact (vfr_keep B API S HS mem1 mem' jk KP FR)|].
  exact (gq_transfer mem1 mem' qv KQ GQ GW).
Qed.

Lemma tl_frees : forall rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  VS fx rg 0x17b10 mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  (forall rg' mem' md' L' A' c',
     TS fx rg' 0x17b20 mem' md' L' A' R1 O1 k1 qv [] jk c' -> SR rsegs c' P) ->
  SR rsegs c P.
Proof using HF HS FREE.
  intros rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P HST K.
  pose proof HST as (_ & _ & (_ & _ & _ & _ & V9 & _) & _).
  apply (tlf_seg rg 0x17b10 0x17b18 (reg_get rg 9) mem1 md1 L1 A1 R1 O1 k1 qv _ jk c P
           (tlf_of_vs rg 0x17b10 mem1 md1 L1 A1 R1 O1 k1 qv jk c HST) (tlf_m1 rg)).
  intros rg1 mem2 c1 HT1 E1 E10.
  apply (tlf_free rg1 mem2 md1 L1 A1 R1 O1 k1 qv [(s_lb S, s_nlb S)] [] (s_cb S) (s_ncb S) jk c1 0x17b18 P HT1).
  - rewrite E10. exact V9.
  - exact E1.
  - apply bv_eq. vm_compute. reflexivity.
  - intros rg2 mem3 md2 L2 A2 c2 HT2.
    pose proof HT2 as (_ & _ & (_ & _ & _ & V8 & _) & _).
    apply (tlf_seg rg2 0x17b18 0x17b20 (reg_get rg2 8) mem3 md2 L2 A2 R1 O1 k1 qv _ jk c2 P HT2 (tlf_m2 rg2)).
    intros rg3 mem4 c3 HT3 E1' E10'.
    apply (tlf_free rg3 mem4 md2 L2 A2 R1 O1 k1 qv [] [] (s_lb S) (s_nlb S) jk c3 0x17b20 P HT3).
    + rewrite E10'. exact V8.
    + exact E1'.
    + apply bv_eq. vm_compute. reflexivity.
    + intros rg4 mem5 md3 L3 A3 c4 HT4. exact (K rg4 mem5 md3 L3 A3 c4 HT4).
Qed.

End TF.
