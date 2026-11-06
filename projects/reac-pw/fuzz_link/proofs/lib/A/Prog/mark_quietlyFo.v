(* reac-pw/fuzz_link, image A: the call of fmemopen's wrapper on the caller's journal, for mark_quietly's opening
   arm (+0x3c `jal 0x430a8`, fmemopen(g_said, 4096, "w")).

   `aj_gx_fmemopen_at` lifts lib/A/Rt/LinkFoSpec.v `afmemopen_w_spec` (at CTX = link_afmemopen_ctx = [[]]) onto the
   caller's journal `ajournal_gx G XO OUT` (lib/A/W_journalG.v). The spec's pre-state: link_ajkit.v aj_gx_ecall_pre
   at the window AFMW_STK, the stack fields from the caller's journal, the frame chain empty (s0 below the allocator's
   ceiling: YCbq.v achain's first arm). The spec's post is a callee journal from the call state with the footprint
   [sink_token]; it extends the caller's journal by YC85G.v ajournal_sub_tok (the token is in the caller's footprint:
   `sink_open_fp FP`), repacked by ajournal_gx_pack (the XO band lies above the call's sp, so the callee kept it).
   The post also gives, from the callee journal: the world grows, the layout's fixed fields are the call's, the
   call's kept clause with the window AFMW_STK and the write set {the open-file list head}, and the grant of the fresh
   FILE block: every byte of it is a byte the caller's journal lets a later callee write (`ajw`), at any later state
   whose blocks hold it (a block not of the journal's start is a temporary block; one of the start was freed since,
   so its bytes are in the footprint).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP09 YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC85G.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkFoSpec LinkFoInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem link_ajkit LinkWalk LinkWalkSide.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variable MT : ameter_ops.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* presence from an equal view off the image *)
Lemma apresent_of_aview_eq : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs H' m' a = aview segs H m a -> apresent H m a -> apresent H' m' a.
Proof.
  intros H H' m m' a Ha Hni Hv (Hh & b & Hb).
  unfold aview, mbyte, mrestrict in Hv. rewrite Hh, Hb in Hv. cbn in Hv.
  destruct (H' (Z_to_bv 64 a)) eqn:Eh'.
  - exfalso. rewrite (seg_rom_none segs a Ha Hni) in Hv. discriminate Hv.
  - destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em'.
    + split; [exact Eh' | exists b'; exact Em'].
    + exfalso. rewrite (seg_rom_none segs a Ha Hni) in Hv. discriminate Hv.
Qed.

Lemma aj_gx_fmemopen_at : forall pc,
  afmemopen_w_spec SK segs B link_amf MT link_afmemopen_ctx pc LA_FM_MALLOC_RA 0x10360 0x10380 ->
  forall G XO OUT (W : world segs) regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  YI16.sink_open_fp FP ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - AFMW_STK -> spZ regsT <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  s0Z regsT < alloc_ceiling ->
  @amf_head_law SK link_amf ->
  afm_w_args segs link_amf 0x10360 0x10380 regsT (rdW W memT) ->
  st_nev S + k + 1 <= EV_MAX ->
  blocks_bytes Sc + AMF_BLOCK <= LIVE_MAX ->
  mo_ok MT Sc (mo_malloc MT AMF_BLOCK) ->
  In [pc_malloc_ra0 (as_code B)] (as_universe B) ->
  (forall c, In c link_afmemopen_ctx -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (LA_FM_MALLOC_RA :: c)))
     (as_universe B)) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
       mo_le MT Sc S2 (mo_malloc MT AMF_BLOCK) /\ m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc /\
       4096 <= res /\ res mod 16 = 0 /\
       ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, AMF_BLOCK)] /\ ~ In (res, AMF_BLOCK) (ablocks B lyc Sc) /\
       LinkMfDefs.amf_k segs link_amf (rdW W2 mem2) res 0 /\
       amf_dyn segs link_amf (rdW W2 mem2) res AF_NORD 0 0 0 0 0 0 /\
       val_mem segs (rdW W2 mem2) (amf_ofl_head link_amf) 8 res /\
       amf_env segs link_amf (rdW W2 mem2) /\
       (length (wild_part (as_universe B) (st_depot S2)) <= length (wild_part (as_universe B) (st_depot Sc)))%nat /\
       wle W W2 /\ layout_le 0 lyc ly2 /\
       akept segs B lyc Sc W memT W2 mem2 (spZ regsT - AFMW_STK) (spZ regsT)
         (fun a => amf_ofl_head link_amf <= a < amf_ofl_head link_amf + 8) /\
       (forall a, res <= a < res + req_size AMF_BLOCK -> forall ly3 S3,
          In (res, AMF_BLOCK) (ablocks B ly3 S3) -> ajw B G XO OUT STK sp0 FP ly S ly3 S3 own a)).
Proof.
intros pc FM G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw HG HJX HSO H16 Hlo Hhi Hgp Htp
  Hra Hraw Hra4 Hs0 HHL Hargs Hev Hlive Hmo HU0 HU1.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (Hes : ESTACK <= AFMW_STK) by (unfold AFMW_STK, ESTACK, ASTACK; lia).
destruct (aj_gx_ecall_pre SK segs B AFMW_STK G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT HJX
  Hes H16 Hlo Hhi ltac:(rewrite Hra; exact Hraw) Hgp Htp) as (Hpre & Hroom & Hwin).
destruct (aj_gx_unpack SK segs B LAWS segs_low G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT AFMW_STK
  HJX ltac:(unfold AFMW_STK, ASTACK; lia) H16 Hlo Hhi)
  as (memS & HJ & Hag & Hout & HSTK & HXO & Esp & Ho16 & Ho & Hb & Hceil & H47).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnev & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & Hqt).
pose proof Hastk as (_ & _ & Hceil' & Hslo & Hshi & Hhi47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hpre as (_ & _ & _ & _ & Hshi2 & _ & _ & _).
(* the spec's pre *)
assert (HPRE : afm_w_pre (SK := SK) segs B link_amf MT link_afmemopen_ctx LA_FM_MALLOC_RA 0x10360 0x10380
                 lyc Sc W regsT memT mdc []).
{ split; [exact HHL|].
  split.
  { split; [exact HAR|].
    split; [rewrite Hra; exact Hraw|].
    split; [unfold raZ; rewrite Hra; exact Hra4|].
    split; [exact Hgp|]. split; [exact Htp|].
    split.
    { unfold astk_ok. unfold ly_bot in *. rewrite Etop in *.
      split; [exact H16|]. split; [unfold AFMW_STK, ASTACK; lia|].
      split; [rewrite Eslo; exact Hceil'|].
      split; [lia|]. split; [exact Hshi2|]. split; [rewrite Eshi; exact Hhi47|].
      split; [unfold AFMW_STK, ASTACK in *; lia|]. split; [lia|]. rewrite Eshi; exact Htop2. }
    split; [exact Hwin|].
    split; [left; split; [left; exact Hs0 | reflexivity]|].
    exact Hqt. }
  split; [left; reflexivity|].
  split; [exact Hargs|].
  split; [lia|]. split; [exact Hlive|]. split; [exact Hmo|].
  split; [exact HU0 | exact HU1]. }
eapply SRr_mono; [exact (FM W lyc Sc regsT memT mdc [] HPRE)|].
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & Ec & HJ1 & HP & Hres & Hfr & Hmle & Hfd & Hfs & H4096 & H16r
  & Hbl & Hk & Hdyn & Hofl & Henv & Hwild).
pose proof HJ1 as (HAR2 & Hly2 & _ & Hwle & _ & Hfr1 & _ & _ & Hstk1 & Hblk1 & Himg1 & Hfrm1 & _ & Hpres1 & _ & _ & _).
exists ly2, S2, regs2, mem2, md2, res.
split; [rewrite Ec, Hra; reflexivity|].
(* the composed journal *)
assert (HJc : ajournal segs B (STK + XO) (sp0 + XO) FP ly S W0 memS md own ly2 S2 W2 mem2 md2 (k + 1)).
{ replace own with ([] ++ own) by reflexivity.
  apply (ajournal_sub_tok segs B LAWS segs_low (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc W memT mdc k
    AFMW_STK (spZ regsT) afmemopen_w_fp [] ly2 S2 W2 mem2 md2 1 HJ HJ1); [lia | lia |].
  intros a (r & Hr & Ha). left. unfold afmemopen_w_fp, YI16.sink_token in Hr. destruct Hr as [<- | []].
  cbn [fst snd] in Ha. replace a with 0 by lia. exact HSO. }
split.
{ apply (ajournal_gx_pack segs B G XO OUT STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) memS HSTK HXO HJc Hag).
  intros a Ha Hno. rewrite (Hstk1 a ltac:(lia) ltac:(lia)). exact (Hout a Ha Hno). }
split; [exact HP|]. split; [exact Hres|]. (* the fresh block is no block of the call state *)
assert (Hfresh : ~ In (res, AMF_BLOCK) (ablocks B lyc Sc)).
{ intros Hin. destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res AMF_BLOCK HAR2 ltac:(rewrite Hbl; apply in_or_app;
    right; left; reflexivity)) as (_ & _ & _ & _ & _ & Hpw & _).
  rewrite Hbl, map_app in Hpw.
  destruct (pairwise_app_inv _ _ _ Hpw) as (_ & _ & Hx).
  assert (Hreq : 0 < req_size AMF_BLOCK) by (apply Z.ltb_lt; vm_compute; reflexivity).
  pose proof (Hx (res, req_size AMF_BLOCK) (res, req_size AMF_BLOCK)
    ltac:(apply (in_map (fun b => (fst b, req_size (snd b))) _ _ Hin)) ltac:(left; reflexivity)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
split; [exact Hfr|]. split; [exact Hmle|].
split; [exact Hfd|]. split; [exact Hfs|]. split; [exact H4096|]. split; [exact H16r|].
split; [exact Hbl|]. split; [exact Hfresh|]. split; [exact Hk|]. split; [exact Hdyn|]. split; [exact Hofl|]. split; [exact Henv|].
split; [exact Hwild|]. split; [exact Hwle|].
split; [exact (layout_le_mono 0 _ _ _ ltac:(lia) Hly2)|].
split.
{ (* the call's kept clause *)
  assert (Hspare : forall a, fp_spares afmemopen_w_fp a <-> ~ (amf_ofl_head link_amf <= a < amf_ofl_head link_amf + 8)).
  { intros a. unfold fp_spares, AOFL_HEAD. rewrite <- HHL. split.
    - intros H. apply H. exists YI16.sink_token. split; [left; reflexivity | unfold YI16.sink_token; cbn; lia].
    - intros H _. exact H. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn _. exact (Hstk1 a Ha Hn).
  - intros b m i Hin Hi _.
    destruct (al_blocks _ _ LAWS lyc Sc W memT mdc b m HAR Hin) as (_ & Hb4096 & _).
    apply (Hblk1 b m i); [exact Hin | rewrite Hbl; apply in_or_app; left; exact Hin | exact Hi |].
    intros (r & Hr & Hra'). unfold afmemopen_w_fp, YI16.sink_token in Hr. destruct Hr as [<- | []].
    cbn [fst snd] in Hra'. lia.
  - intros a Hi Hno Herr HE. apply Himg1; [exact Hi | exact Hno | exact Herr | apply Hspare; exact HE].
  - intros cid pos a Hin Hr _.
    destruct (al_sep _ _ LAWS lyc Sc W memT mdc HAR) as (_ & Hfa).
    rewrite Forall_forall in Hfa. destruct (Hfa (cid, pos) Hin) as (Hf4096 & _).
    cbn [fst snd] in Hf4096.
    apply (Hfrm1 cid pos a); [exact Hin | exact Hr |].
    intros (r & Hr' & Hra'). unfold afmemopen_w_fp, YI16.sink_token in Hr'. destruct Hr' as [<- | []].
    cbn [fst snd] in Hra'. unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hr. cbn [fst snd] in Hr.
    assert (Hd8 : 0 <= frame_addr lyc cid pos / 8) by (apply Z.div_pos; lia).
    destruct Hr as [Hr | Hr]; lia.
  - intros a Ha Hn Hp.
    apply (apresent_of_aview_eq (w_H W) (w_H W2) memT mem2 a ltac:(lia)).
    + intros Hi. pose proof (segs_low a Hi). lia.
    + exact (Hstk1 a Ha Hn).
    + exact Hp.
  - exact Hpres1. }
(* the grant of the fresh block *)
intros a Ha ly3 S3 Hin3.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res AMF_BLOCK HAR2 ltac:(rewrite Hbl; apply in_or_app;
  right; left; reflexivity)) as (_ & _ & Hrc & _).
left. split; [|lia].
assert (Dz : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
destruct (in_dec Dz (res, AMF_BLOCK) (ablocks B ly S)) as [HinS | HninS].
- right. left. split.
  + pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfreed & _).
    replace a with (res + (a - res)) by lia. apply (Hfreed res AMF_BLOCK (a - res) HinS Hfresh). lia.
  + exists res, AMF_BLOCK. split; [exact Hin3 | lia].
- right. right. left. exists res, AMF_BLOCK. split; [exact Hin3|]. split; [exact HninS | lia].
Qed.

End f.

Arguments aj_gx_fmemopen_at {fx rc} SK segs B LAWS segs_low MT.
Print Assumptions aj_gx_fmemopen_at.
