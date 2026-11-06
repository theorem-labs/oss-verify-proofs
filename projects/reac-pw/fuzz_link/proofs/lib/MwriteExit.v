From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05 YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN35 YN34.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN03 YL07 YL01 YL00 YL0d YL0g YL05 YL0s YL0k GIWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YI06 YI16 YI14 YI5b YI5c YL0i YL06.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import MemFileSink MemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import SlotAgree AllocSlots MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import StdioExitMF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Img0 KindBGlue AgreeLift RoAdapt.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require link_spec link_mem memfile_c memfile_place.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import mwrite_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require PropExec MState Mem Frame Exec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Ltac nums :=
  unfold memfile_c.mf_place_ok, memfile_c.IMG_LO, memfile_c.IMG_TOP, link_mem.A_G_SAID, link_spec.SAID_SIZE,
    link_mem.A_G_SAY, memfile_c.GOT_GUARD, MF_BLOCK, MF_ZEROED, MF_BUF, MF_BUFSIZ, MW_STACK, memfile_c.MWRITE_K,
    SX_MW_RA in *;
  try change (errno_addr src0_msyms) with 0x75564 in *.

Lemma errno_val : errno_addr src0_msyms = 0x75564.
Proof. reflexivity. Qed.

Lemma tp_val : ms_tp src0_msyms = 0x75608.
Proof. reflexivity. Qed.

Lemma seg_ck : forallb (fun s => (memfile_c.IMG_LO <=? Z.of_N (seg_base s)) &&
    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? memfile_c.IMG_TOP)) Img0.rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma seg_in_img : forall x s, find_segment Img0.rsegs x 1 = Some s -> in_img src0_msyms x.
Proof.
  intros x s H. destruct (KindBGlue.kb_find_segment _ x 1 s H) as (Hin & H1 & H2).
  pose proof seg_ck as C. rewrite forallb_forall in C. specialize (C s Hin).
  apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
  apply memfile_place.img_range_in_img. lia.
Qed.

Lemma noimg_noseg : forall x, ~ in_img src0_msyms x -> find_segment Img0.rsegs x 1 = None.
Proof.
  intros x Hn. destruct (find_segment Img0.rsegs x 1) as [s|] eqn:E; [|reflexivity].
  exfalso. exact (Hn (seg_in_img x s E)).
Qed.

Lemma noimg_nro : forall x, 0 <= x < 2 ^ 64 -> ~ in_img src0_msyms x -> Mem.ro_addr Img0.rsegs (Mem.wa x) = false.
Proof.
  intros x Hx Hn. unfold Mem.ro_addr. rewrite Mem.wa_unsigned by exact Hx.
  rewrite (noimg_noseg x Hn). reflexivity.
Qed.

Lemma noimg_wview : forall m x, 0 <= x < 2 ^ 64 -> ~ in_img src0_msyms x ->
  wview Img0.rsegs m (Z_to_bv 64 x) <> None -> exists b, m (Z_to_bv 64 x) = Some b.
Proof.
  intros m x Hx Hn. unfold wview.
  destruct (m (Z_to_bv 64 x)) as [b|]; intros Hw; [exists b; reflexivity|].
  rewrite MState.unsigned_lit in Hw by exact Hx.
  try change (Z.of_N 1) with 1 in Hw.
  destruct (find_segment Img0.rsegs x 1) as [seg|] eqn:F; [|contradiction].
  exfalso. exact (Hn (seg_in_img x seg F)).
Qed.

Lemma norm_present : forall mem x, 0 <= x < 2 ^ 64 -> ~ in_img src0_msyms x -> present mem x ->
  present (MemNorm.normalize Img0.rsegs mem) x.
Proof.
  intros mem x Hx Hn [b Hb]. exists b. unfold MemNorm.normalize. cbv beta.
  change (Z_to_bv 64 x) with (Mem.wa x). rewrite (noimg_nro x Hx Hn). exact Hb.
Qed.

Definition nro_ck (lo n : Z) : bool :=
  forallb (fun i => negb (Mem.ro_addr Img0.rsegs (Mem.wa (lo + Z.of_nat i)))) (seq 0 (Z.to_nat n)).

Lemma nro_ck_sound : forall lo n x, nro_ck lo n = true -> lo <= x < lo + n ->
  Mem.ro_addr Img0.rsegs (Mem.wa x) = false.
Proof.
  intros lo n x H Hx. unfold nro_ck in H. rewrite forallb_forall in H.
  assert (Hin : In (Z.to_nat (x - lo)) (seq 0 (Z.to_nat n))) by (apply in_seq; lia).
  specialize (H _ Hin). rewrite Z2Nat.id in H by lia. replace (lo + (x - lo)) with x in H by lia.
  apply negb_true_iff in H. exact H.
Qed.

Lemma nro_said : nro_ck link_mem.A_G_SAID link_spec.SAID_SIZE = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nro_errno : nro_ck (errno_addr src0_msyms) 4 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nro_static :
  nro_ck (ms_lock src0_msyms) 4 && nro_ck (ms_libc src0_msyms + 3) 1 && nro_ck (ms_libc src0_msyms + 8) 8 &&
  nro_ck (ms_libc src0_msyms + 48) 8 && nro_ck (ms_got_guard src0_msyms) 8 && nro_ck (ms_guard src0_msyms) 8 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma wx0 : MemNorm.wx_apart Img0.rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma said_img : forall a, link_mem.A_G_SAID <= a < link_mem.A_G_SAID + link_spec.SAID_SIZE -> in_img src0_msyms a.
Proof. intros a Ha. apply memfile_place.img_range_in_img. nums. lia. Qed.

Lemma errno_img : forall a, errno_addr src0_msyms <= a < errno_addr src0_msyms + 4 -> in_img src0_msyms a.
Proof. intros a Ha. apply memfile_place.img_range_in_img. nums. lia. Qed.

Lemma pairwise_In2 : forall {T : Type} (R : T -> T -> Prop) (l : list T) x y,
  YO0f.pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
  intros T R l. induction l as [|z l IH]; intros x y H Hx Hy Hne; [destruct Hx|].
  destruct H as [Hz Hl]. destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - contradiction.
  - left. exact (Hz y Hy).
  - right. exact (Hz x Hx).
  - exact (IH x y Hl Hx Hy Hne).
Qed.

Lemma nth_map_seq : forall {T : Type} (g : nat -> T) n s i, (i < n)%nat ->
  nth_error (map g (seq s n)) i = Some (g (s + i)%nat).
Proof.
  intros T g n. induction n as [|n IH]; intros s i Hi; [lia|].
  cbn [seq map]. destruct i as [|i]; cbn [nth_error].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite (IH (S s) i) by lia. f_equal. f_equal. lia.
Qed.

Lemma bytes_of : forall (m : word -> option byte) a n, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> exists b, m (Mem.wa (a + Z.of_nat i)) = Some b) ->
  exists bs, length bs = n /\ Mem.bytes_at Img0.rsegs m a bs.
Proof.
  intros m a n H0 H1 H.
  exists (map (fun i => match m (Mem.wa (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)).
  rewrite length_map, length_seq. split; [reflexivity|].
  split; [exact H0|]. rewrite length_map, length_seq. split; [exact H1|].
  intros i Hi. rewrite (nth_map_seq _ n 0 i Hi). cbn [Nat.add].
  destruct (H i Hi) as [b Hb]. unfold Mem.mrd. rewrite Hb. reflexivity.
Qed.

Section bridge.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Hypothesis MWC : mwrite_contract.

Lemma img_low0 : KindBGlue.img_low src0_msyms.
Proof.
  apply (KindBGlue.img_low_of_check src0_msyms CEIL_MIN); [vm_compute; reflexivity|].
  pose proof alloc_ceiling_value. lia.
Qed.

Lemma static_ro_rom : forall L A mem md, aa_MR API L A mem md ->
  forall a, static_owned src0_msyms a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr (ms_segs src0_msyms) (Z_to_bv 64 a) = true ->
  mbyte (ms_segs src0_msyms) mem a = seg_rom (ms_segs src0_msyms) (Z_to_bv 64 a).
Proof.
  intros L A mem md HM a Hs Ha Hro.
  pose proof nro_static as N.
  apply andb_prop in N as [N N6]. apply andb_prop in N as [N N5]. apply andb_prop in N as [N N4].
  apply andb_prop in N as [N N3]. apply andb_prop in N as [N1 N2].
  assert (NR : forall lo n, nro_ck lo n = true -> lo <= a < lo + n -> False).
  { intros lo n Hc Hr. pose proof (nro_ck_sound lo n a Hc Hr) as E.
    change (Mem.wa a) with (Z_to_bv 64 a) in E. change (ms_segs src0_msyms) with Img0.rsegs in Hro.
    rewrite E in Hro. discriminate. }
  unfold static_owned in Hs.
  destruct Hs as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]].
  - exfalso. apply (NR _ 4 N1). lia.
  - exfalso. apply (NR _ 1 N2). lia.
  - exfalso. apply (NR _ 8 N3). lia.
  - exfalso. apply (NR _ 8 N4). lia.
  - exfalso. apply (NR _ 8 N5). lia.
  - exfalso. apply (NR _ 8 N6). lia.
  - apply (ax_tables AX L A mem md a HM). left. exact H.
  - apply (ax_tables AX L A mem md a HM). right. left. exact H.
  - apply (ax_tables AX L A mem md a HM). right. right. left. exact H.
  - apply (ax_tables AX L A mem md a HM). right. right. right. exact H.
  - exfalso. unfold vml_lo, vml_len in H. cbn in H. lia.
Qed.

Lemma owned_apart : forall L A mem md a, aa_MR API L A mem md -> owned src0_msyms L A a ->
  ~ (link_mem.A_G_SAID <= a < link_mem.A_G_SAID + link_spec.SAID_SIZE) /\
  ~ (errno_addr src0_msyms <= a < errno_addr src0_msyms + 4).
Proof.
  intros L A mem md a HM [Ho|Ho].
  - split; intros Hr.
    + pose proof (ax_img AX L A mem md a HM (said_img a Hr) Ho) as Hc.
      change (ms_ctx src0_msyms) with 0x95910 in Hc. unfold CTX_SIZE in Hc. nums. lia.
    + pose proof (ax_img AX L A mem md a HM (errno_img a Hr) Ho) as Hc.
      change (ms_ctx src0_msyms) with 0x95910 in Hc. unfold CTX_SIZE in Hc. nums. lia.
  - unfold static_owned, vml_lo, vml_len in Ho.
    change (ms_lock src0_msyms) with 0x95908 in Ho. change (ms_libc src0_msyms) with 0x95898 in Ho.
    change (ms_got_guard src0_msyms) with 0x208d8 in Ho. change (ms_guard src0_msyms) with 0x95878 in Ho.
    change (ms_debruijn src0_msyms) with 0x10778 in Ho. change (ms_debruijn_len src0_msyms) with 32 in Ho.
    change (ms_size_classes src0_msyms) with 0x10798 in Ho. change (ms_small_cnt src0_msyms) with 0x107f8 in Ho.
    change (ms_med_cnt src0_msyms) with 0x10813 in Ho. change (ms_vmlock src0_msyms) with (@None Z) in Ho.
    cbv beta iota in Ho. nums. lia.
Qed.

Lemma mw_post_getr : forall L A regs mem md f R R' mem',
  (forall r, getr R' r = getr R r) ->
  mw_post src0_msyms API L A regs mem md f R mem' -> mw_post src0_msyms API L A regs mem md f R' mem'.
Proof.
  intros L A regs mem md f R R' mem' HR (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [rewrite HR; exact H2|].
  split; [intros r Hr; rewrite HR; exact (H3 r Hr) | exact H4].
Qed.

Lemma mw_evt : forall L A regs mem md f,
  mw_pre src0_msyms API SX_MW_RA L A regs mem md f ->
  Exec.evt (ms_segs src0_msyms)
    (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom (ms_segs src0_msyms)) /\
       pc' = Z_to_bv 64 SX_MW_RA /\ mw_post src0_msyms API L A regs mem md f R mem')
    (MState.MS (KindBGlue.rmk regs) fp_regs (Z_to_bv 64 (mf_write link_mf)) fp_csr None mem
       (seg_rom (ms_segs src0_msyms))).
Proof.
  intros L A regs mem md f HP.
  change (ms_segs src0_msyms) with Img0.rsegs.
  destruct HP as (HMR & HWF & HB & Hra & H16 & Hlo & Hhi & Hstw & Htp & Herrw & Ha0 & Ha1 & Ha2 & Hblk & Hmf
    & Hsaidw & Hrod).
  clear H16.
  destruct alloc_ceiling_value as [AC _].
  pose proof img_low0 as IMGL.
  pose proof Hblk as HblkF.
  unfold blocks in Hblk. apply in_map_iff in Hblk as ([q nq] & Eq & Hq). cbn [fst snd] in Eq.
  injection Eq as Eqf Eqn. subst nq.
  assert (HFB : forall i, 0 <= i < MF_BLOCK ->
    present mem (f + i) /\ ~ owned src0_msyms L A (f + i) /\ ~ in_img src0_msyms (f + i)).
  { intros i Hi. destruct (mr_blocks _ _ (aa_laws API) L A mem md q MF_BLOCK i HMR Hq Hi) as (Hp & _ & _ & Ho).
    pose proof (ax_blocks_img AX L A mem md q MF_BLOCK i HMR Hq Hi) as Hn.
    rewrite Eqf in Hp, Ho, Hn. split; [exact Hp|]. split; [exact Ho | exact Hn]. }
  destruct (mr_blocks_range _ _ (aa_laws API) L A mem md q MF_BLOCK HMR Hq) as [Hf1 Hf2].
  rewrite Eqf in Hf1, Hf2.
  assert (Hplace : memfile_c.mf_place_ok f).
  { apply memfile_place.mf_place_of_fresh; [lia|]. intros i Hi. exact (proj2 (proj2 (HFB i Hi))). }
  assert (HRO : MemNorm.ro_agree Img0.rsegs mem).
  { exact (MemNorm.ro_agree_of_rodata_ok src0_msyms mem Hrod (static_ro_rom L A mem md HMR)). }
  pose (m0 := MemNorm.normalize Img0.rsegs mem).
  pose proof (MemNorm.mem_rel_normalize Img0.rsegs mem HRO) as REL.
  pose proof (MemNorm.mem_inv_normalize Img0.rsegs mem) as MIN.
  assert (G : forall r, PropExec.getr (KindBGlue.rmk regs) r = getr regs r).
  { intros r. exact (KindBGlue.kb_rmk_getr regs r). }
  assert (HspR : spZ (KindBGlue.rmk regs) = spZ regs).
  { unfold spZ. rewrite KindBGlue.kb_rmk_getr. reflexivity. }
  assert (Hf64 : 0 <= f < 2 ^ 64) by (nums; lia).
  assert (HA0 : link_mem.arg (KindBGlue.rmk regs) 0 = f).
  { unfold link_mem.arg. replace (Z_to_bv 5 (10 + 0)) with (10%bv : reg) by (apply bv_eq; reflexivity).
    rewrite ?G, ?KindBGlue.kb_rmk_getr. rewrite Ha0. apply MState.unsigned_lit. exact Hf64. }
  assert (HA1 : link_mem.arg (KindBGlue.rmk regs) 1 = 0).
  { unfold link_mem.arg. replace (Z_to_bv 5 (10 + 1)) with (11%bv : reg) by (apply bv_eq; reflexivity).
    rewrite ?G, ?KindBGlue.kb_rmk_getr. rewrite Ha1. reflexivity. }
  assert (HA2 : link_mem.arg (KindBGlue.rmk regs) 2 = 0).
  { unfold link_mem.arg. replace (Z_to_bv 5 (10 + 2)) with (12%bv : reg) by (apply bv_eq; reflexivity).
    rewrite ?G, ?KindBGlue.kb_rmk_getr. rewrite Ha2. reflexivity. }
  assert (HerrR : link_mem.errno_at (KindBGlue.rmk regs) = errno_addr src0_msyms).
  { unfold link_mem.errno_at, link_mem.ERRNO_TP_OFF. rewrite ?G, ?KindBGlue.kb_rmk_getr. rewrite Htp.
    rewrite MState.unsigned_lit by (rewrite tp_val; lia). reflexivity. }
  assert (Hmf0 : memfile_at src0_msyms link_mf m0 f).
  { eapply MemFile.memfile_at_frame; [|exact Hmf]. intros x _. symmetry.
    exact (MemNorm.mbyte_rel Img0.rsegs mem m0 x REL). }
  pose proof Hmf0 as (_ & _ & _ & _ & Hfl & Hom & Hwin & Hck).
  assert (EFL : exists fl, 0 <= fl < 2 ^ 32 /\ memfile_c.mf_fld m0 f 0 4 fl).
  { destruct Hfl as [H|H]; [exists F_NORD | exists (F_NORD + F_ERR)];
      (split; [unfold F_NORD, F_ERR; lia | exact H]). }
  assert (EOM : exists om, 0 <= om < 2 ^ 32 /\ memfile_c.mf_fld m0 f 136 4 om).
  { destruct Hom as [H|H]; [exists 0 | exists U32M1]; (split; [unfold U32M1; lia | exact H]). }
  assert (EWI : exists k wend wpos wbase, 0 <= k <= MF_BUFSIZ /\ memfile_c.mf_win m0 f k /\
     0 <= wend < 2 ^ 64 /\ 0 <= wpos < 2 ^ 64 /\ 0 <= wbase < 2 ^ 64 /\
     memfile_c.mf_fld m0 f 32 8 wend /\ memfile_c.mf_fld m0 f 40 8 wpos /\ memfile_c.mf_fld m0 f 56 8 wbase).
  { destruct Hwin as (_ & _ & [(W1 & W2 & W3) | (k & Hk & W1 & W2 & W3)]).
    - exists 0, 0, 0, 0. split; [unfold MF_BUFSIZ; lia|].
      split; [left; split; [reflexivity|]; split; [exact W1|]; split; [exact W2 | exact W3]|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact W1|]. split; [exact W2 | exact W3].
    - exists k, (f + MF_BUF + MF_BUFSIZ), (f + MF_BUF + k), (f + MF_BUF). split; [exact Hk|].
      split; [right; split; [exact Hk|]; split; [exact W1|]; split; [exact W2 | exact W3]|].
      split; [nums; lia|]. split; [nums; lia|]. split; [nums; lia|].
      split; [exact W1|]. split; [exact W2 | exact W3]. }
  destruct Hck as (pos & len & Hpl & Hls & Hc1 & Hc2). change (mf_size link_mf) with 4096 in Hls.
  destruct EFL as (fl & Hfl1 & Hfl2). destruct EOM as (om & Hom1 & Hom2).
  destruct EWI as (k & wend & wpos & wbase & Hk & WIN & Hwe & Hwp & Hwb & W1 & W2 & W3).
  assert (DYN : memfile_c.mf_dyn m0 f fl om wend wpos wbase pos len).
  { unfold memfile_c.mf_dyn. split; [exact Hfl1|]. split; [exact Hom1|]. split; [exact Hwe|].
    split; [exact Hwp|]. split; [exact Hwb|]. split; [exact Hpl|]. split; [unfold link_spec.SAID_SIZE; exact Hls|].
    split; [exact Hfl2|]. split; [exact Hom2|]. split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
    split; [exact Hc1 | exact Hc2]. }
  assert (PBX : exists pb, length pb = Z.to_nat k /\ Mem.bytes_at Img0.rsegs m0 (f + MF_BUF) pb).
  { apply bytes_of.
    - nums. lia.
    - rewrite Z2Nat.id by lia. nums. lia.
    - intros i Hi. destruct (HFB (MF_BUF + Z.of_nat i) ltac:(nums; lia)) as (Hp & _ & Hni).
      replace (f + MF_BUF + Z.of_nat i) with (f + (MF_BUF + Z.of_nat i)) by lia.
      exact (norm_present mem (f + (MF_BUF + Z.of_nat i)) ltac:(nums; lia) Hni Hp). }
  destruct PBX as (pb & PBL0 & PB).
  assert (PBL : Z.of_nat (length pb) = k) by (rewrite PBL0; apply Z2Nat.id; lia).
  assert (WRF : Mem.wr_at Img0.rsegs m0 f MF_BLOCK).
  { split; [lia|]. split; [nums; lia|]. intros i Hi.
    destruct (HFB i Hi) as (Hp & _ & Hni).
    exact (YL01.present_writable Img0.rsegs m0 (f + i) (norm_present mem (f + i) ltac:(nums; lia) Hni Hp)). }
  assert (WRS : Mem.wr_at Img0.rsegs m0 link_mem.A_G_SAID link_spec.SAID_SIZE).
  { apply (MemNorm.wr_at_norm Img0.rsegs mem m0 _ _ REL).
    - split; [nums; lia|]. split; [nums; lia|]. intros i Hi.
      refine (Hsaidw (link_mem.A_G_SAID + i) _).
      exists (mf_buf link_mf), (mf_size link_mf). split; [left; reflexivity|].
      cbn [mf_buf mf_size link_mf]. nums. lia.
    - intros i Hi. exact (nro_ck_sound _ _ (link_mem.A_G_SAID + i) nro_said ltac:(lia)). }
  assert (WRE : Mem.wr_at Img0.rsegs m0 (errno_addr src0_msyms) 4).
  { apply (MemNorm.wr_at_norm Img0.rsegs mem m0 _ _ REL).
    - split; [nums; lia|]. split; [nums; lia|]. intros i Hi. exact (Herrw (errno_addr src0_msyms + i) ltac:(lia)).
    - intros i Hi. exact (nro_ck_sound _ _ (errno_addr src0_msyms + i) nro_errno ltac:(lia)). }
  assert (STK : Frame.stk Img0.rsegs m0 (spZ regs - MW_STACK) (spZ regs)).
  { split; [nums; lia|]. split; [lia|]. intros a Ha.
    assert (Hna : ~ in_img src0_msyms a).
    { intros Hi. destruct IMGL as [IL _]. pose proof (IL a Hi). nums. lia. }
    destruct (noimg_wview mem a ltac:(nums; lia) Hna (Hstw a Ha)) as [b Hb].
    pose proof (norm_present mem a ltac:(nums; lia) Hna (ex_intro _ b Hb)) as Hp.
    split; [exact (YL01.present_writable Img0.rsegs m0 a Hp)|].
    destruct Hp as [b' Hb']. exists b'. unfold Mem.mrd. change (Mem.wa a) with (Z_to_bv 64 a).
    unfold m0. rewrite Hb'. reflexivity. }
  pose proof (MWC f k fl om wend wpos wbase pos len pb [] (KindBGlue.rmk regs) fp_regs fp_csr m0
    (spZ regs - MW_STACK)) as LF.
  cbv beta zeta in LF.
  rewrite HspR, HerrR, HA0, HA1, HA2 in LF.
  match type of LF with ?P -> _ => assert (PRE : P) end.
  { split; [reflexivity|]. split; [reflexivity|].
    split; [exact (conj Hmf0 (conj WIN (conj WRF (conj WRS Hplace))))|].
    split; [exact DYN|]. split; [exact PB|]. split; [exact PBL|].
    split.
    { unfold Mem.bytes_at. cbn [length Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
    unfold memfile_c.errno_ok, memfile_c.rapart, link_mem.apart_frame. rewrite ?HspR, ?HerrR.
    cbn [length Z.of_nat].
    split; [nums; lia|]. split; [nums; lia|]. split; [nums; lia|]. split; [nums; lia|].
    split; [nums; lia|]. split; [nums; lia|]. split; [nums; lia|].
    split; [exact WRE|]. nums.
    repeat match goal with |- _ /\ _ => split end; lia. }
  specialize (LF PRE MIN STK ltac:(nums; lia) ltac:(lia)).
  clear PRE.
  eapply Exec.evt_mono.
  { change (mf_write link_mf) with memfile_c.MWRITE.
    exact (MemNorm.evt_normalize Img0.rsegs _ _ _ _ _ _ mem _ wx0 HRO LF). }
  intros s (s0 & HQ & HMS & HRS).
  destruct HQ as (regs' & m0' & Es0 & RP & MU & WM & MI' & ST' & PO). subst s0.
  destruct s as [r1 fr1 pc1 svc1 rv1 fc1 m' ro1].
  destruct HMS as (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS] in Hr, Hf, Hpc, Hsvc,
    Hres, Hfc, Hrom, Hmem, HRS.
  subst r1 fr1 pc1 svc1 rv1 fc1 ro1.
  pose proof (MemNorm.munch_rel Img0.rsegs _ mem m0 m' m0' REL Hmem HRS MU) as MU'.
  pose proof (MemNorm.wmono_rel Img0.rsegs mem m0 m' m0' REL Hmem HRS WM) as WM'.
  pose proof (RoAdapt.stk_back Img0.rsegs m' m0' _ _ Hmem ST') as ST''.
  destruct PO as (MFK' & _ & PL & PE).
  pose proof (MemNorm.wr_at_rel Img0.rsegs m' m0' f MF_BLOCK Hmem (proj1 (proj2 (proj2 MFK')))) as WRF'.
  match type of MU' with Frame.munch ?W _ _ =>
    assert (OUTW : forall x, ~ (spZ regs - memfile_c.MWRITE_K <= x < spZ regs) -> ~ (f <= x < f + MF_ZEROED) ->
       ~ (link_mem.A_G_SAID <= x < link_mem.A_G_SAID + link_spec.SAID_SIZE) ->
       ~ (errno_addr src0_msyms <= x < errno_addr src0_msyms + 4) -> Frame.outside W x)
  end.
  { intros x H1 H2 H3 H4. unfold memfile_c.mf_hdr, memfile_c.mf_said. cbn [Frame.outside]. tauto. }
  assert (OWN : forall a, owned src0_msyms L A a -> 0 <= a < 2 ^ 64 /\
    ~ (spZ regs - memfile_c.MWRITE_K <= a < spZ regs) /\ ~ (f <= a < f + MF_ZEROED) /\
    ~ (link_mem.A_G_SAID <= a < link_mem.A_G_SAID + link_spec.SAID_SIZE) /\
    ~ (errno_addr src0_msyms <= a < errno_addr src0_msyms + 4)).
  { intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HMR Ho) as Hal.
    destruct (owned_apart L A mem md a HMR Ho) as [Hs He].
    split; [lia|]. split; [nums; lia|]. split; [|exact (conj Hs He)].
    intros Hr. destruct (HFB (a - f) ltac:(nums; lia)) as (_ & Hno & _).
    replace (f + (a - f)) with a in Hno by lia. exact (Hno Ho). }
  exists regs'. eexists. exists m'.
  split; [reflexivity|].
  split.
  { transitivity (MState.ret_pc (Z_to_bv 64 SX_MW_RA)).
    - f_equal. exact (eq_trans (G _) Hra).
    - apply MState.ret_pc_even; unfold SX_MW_RA; [lia | reflexivity]. }
  unfold mw_post.
  split.
  { destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hl & Hmat).
    apply (mr_frame _ _ (aa_laws API) L A mem m' md md HMR).
    - intros a Ho. destruct (OWN a Ho) as (Hr & O1 & O2 & O3 & O4).
      exact (KindBGlue.mbyte_munch Img0.rsegs _ mem m' a MU' Hr (OUTW a O1 O2 O3 O4)).
    - intros a Ho [b Hb]. exists b. destruct (OWN a Ho) as (Hr & O1 & O2 & O3 & O4).
      rewrite (MU' (Z_to_bv 64 a)); [exact Hb|]. rewrite MState.unsigned_lit by exact Hr.
      exact (OUTW a O1 O2 O3 O4).
    - intros p n i Hin Hi.
      destruct (mr_blocks _ _ (aa_laws API) L A mem md p n i HMR Hin Hi) as ([b Hb] & Hp1 & Hp2 & _).
      pose proof (ax_blocks_img AX L A mem md p n i HMR Hin Hi) as Hni.
      assert (D : (f <= ptr_addr L p + i < f + MF_ZEROED) \/ ~ (f <= ptr_addr L p + i < f + MF_ZEROED)) by lia.
      destruct D as [D|D].
      + destruct WRF' as (_ & _ & Hw).
        pose proof (Hw (ptr_addr L p + i - f) ltac:(nums; lia)) as Hw1.
        replace (f + (ptr_addr L p + i - f)) with (ptr_addr L p + i) in Hw1 by lia.
        exact (noimg_wview m' (ptr_addr L p + i) ltac:(lia) Hni Hw1).
      + exists b. rewrite (MU' (Z_to_bv 64 (ptr_addr L p + i))); [exact Hb|].
        rewrite MState.unsigned_lit by lia.
        apply OUTW; [nums; lia | exact D | intros Hr; exact (Hni (said_img _ Hr)) |
          intros Hr; exact (Hni (errno_img _ Hr))].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split.
  { assert (RES : link_mem.res regs' = 0).
    { destruct (Z_lt_le_dec (memfile_c.mf_n1 k pos) k) as [Hlt|Hge].
      - exact (proj1 (PL Hlt)).
      - assert (Heq : memfile_c.mf_n1 k pos = k) by (unfold memfile_c.mf_n1 in *; lia).
        rewrite (proj1 (PE Heq)). unfold mw_n2, mw_pos1, memfile_c.mf_n1. cbn [length Z.of_nat].
        unfold link_spec.SAID_SIZE. lia. }
    apply bv_eq. rewrite MState.unsigned_lit by lia. exact RES. }
  split.
  { intros r Hr. rewrite (RP r Hr). apply KindBGlue.kb_rmk_getr. }
  split.
  { intros a Ha Hns. unfold lib_scratch in Hns.
    pose proof (OUTW a ltac:(nums; lia) ltac:(nums; lia) ltac:(nums; lia) ltac:(nums; lia)) as Ho.
    split; [exact (KindBGlue.mbyte_munch Img0.rsegs _ mem m' a MU' ltac:(lia) Ho)
           | exact (KindBGlue.writable_munch Img0.rsegs _ mem m' a MU' ltac:(lia) Ho)]. }
  split.
  { intros a Hi Hst Hctx Herr Hg.
    destruct IMGL as [IL _]. pose proof (IL a Hi) as Hal.
    assert (O2 : ~ (f <= a < f + MF_ZEROED)).
    { intros Hr. destruct (HFB (a - f) ltac:(nums; lia)) as (_ & _ & Hni).
      replace (f + (a - f)) with a in Hni by lia. exact (Hni Hi). }
    assert (O3 : ~ (link_mem.A_G_SAID <= a < link_mem.A_G_SAID + link_spec.SAID_SIZE)).
    { intros Hr. apply Hg. exists (mf_buf link_mf), (mf_size link_mf). split; [left; reflexivity|].
      cbn [mf_buf mf_size link_mf]. nums. lia. }
    pose proof (OUTW a ltac:(nums; lia) O2 O3 Herr) as Ho.
    split; [exact (KindBGlue.mbyte_munch Img0.rsegs _ mem m' a MU' ltac:(lia) Ho)
           | exact (KindBGlue.writable_munch Img0.rsegs _ mem m' a MU' ltac:(lia) Ho)]. }
  split.
  { intros q' k' i Hin Hne Hi.
    destruct (mr_blocks _ _ (aa_laws API) L A mem md q' k' i HMR Hin Hi) as (_ & Hq1 & Hq2 & _).
    pose proof (ax_blocks_img AX L A mem md q' k' i HMR Hin Hi) as Hni.
    assert (Hdis : YO0f.ranges_disjoint (ptr_addr L q', k') (f, MF_BLOCK) \/
                   YO0f.ranges_disjoint (f, MF_BLOCK) (ptr_addr L q', k')).
    { apply (pairwise_In2 YO0f.ranges_disjoint (blocks L A)).
      - exact (mr_blocks_disjoint _ _ (aa_laws API) L A mem md HMR).
      - unfold blocks. apply in_map_iff. exists (q', k'). split; [reflexivity | exact Hin].
      - exact HblkF.
      - intros E. injection E as E1 E2. exact (Hne E1). }
    unfold YO0f.ranges_disjoint in Hdis. cbn [fst snd] in Hdis.
    apply (KindBGlue.mbyte_munch Img0.rsegs _ mem m' _ MU'); [lia|].
    apply OUTW; [nums; lia | nums; lia | intros Hr; exact (Hni (said_img _ Hr)) |
      intros Hr; exact (Hni (errno_img _ Hr))]. }
  split.
  { intros a [Hs|He].
    - destruct ST'' as (_ & _ & HS). exact (proj1 (HS a Hs)).
    - exact (WM' (Z_to_bv 64 a) (Herrw a He)). }
  { destruct MFK' as (MA' & _). eapply MemFile.memfile_at_frame; [|exact MA'].
    intros x _. exact (MemNorm.mbyte_rel Img0.rsegs m' m0' x Hmem). }
Qed.

End bridge.

Section cfrun.
Context {fx : YK11.FPState}.

Lemma kb_run_SRcf : forall regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop)
    (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt (ms_segs src0_msyms)
    (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom (ms_segs src0_msyms)) /\
       K R pc' mem')
    (MState.MS (KindBGlue.rmk regs) fp_regs pc fp_csr None mem (seg_rom (ms_segs src0_msyms))) ->
  (forall R pc' mem' regs', K R pc' mem' -> (forall r, getr regs' r = getr R r) ->
     SRcf src0_msyms (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs src0_msyms))) md) P) ->
  SRcf src0_msyms (mkCfg (mkst regs pc mem (seg_rom (ms_segs src0_msyms))) md) P.
Proof.
  intros regs pc mem md K P Hh Hl HE HK.
  eapply (AgreeLift.evt_SRcf_canon src0_msyms (mkst regs pc mem (seg_rom (ms_segs src0_msyms))) _ md P);
    [exact HE | exact Hh | exact Hl |].
  intros ms' (can & (R & pc' & mem' & -> & HKR) & Heq).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' HKR). apply KindBGlue.kb_getr_eqv. exact HR.
Qed.
End cfrun.

Theorem mwrite_exit_of_contract : forall {rc : YM05.RunCeil} (API : AllocAPI src0_msyms),
  AllocExtra src0_msyms (aa_MR API) -> mwrite_contract -> mwrite_exit_contract_all src0_msyms API.
Proof.
  intros rc API AX MWC fx. unfold mwrite_exit_contract. intros L A regs mem md f HP.
  destruct (KindBGlue.kb_md src0_msyms API L A mem md (proj1 HP)) as [Hh Hl].
  apply (KindBGlue.kb_run src0_msyms regs (Z_to_bv 64 (mf_write link_mf)) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 SX_MW_RA /\ mw_post src0_msyms API L A regs mem md f R mem') _ Hh Hl).
  - exact (mw_evt API AX MWC L A regs mem md f HP).
  - intros R pc' mem' regs' (-> & HPo) HR. apply SR_ret. exists regs', mem'. split; [reflexivity|].
    exact (mw_post_getr API L A regs mem md f R regs' mem' HR HPo).
Qed.

Theorem mwrite_exit_cf_of_contract : forall {rc : YM05.RunCeil} (API : AllocAPI src0_msyms),
  AllocExtra src0_msyms (aa_MR API) -> mwrite_contract -> mwrite_exit_contract_cf_all API.
Proof.
  intros rc API AX MWC fx. unfold mwrite_exit_contract_cf. intros L A regs mem md f HP.
  destruct (KindBGlue.kb_md src0_msyms API L A mem md (proj1 HP)) as [Hh Hl].
  apply (kb_run_SRcf regs (Z_to_bv 64 (mf_write link_mf)) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 SX_MW_RA /\ mw_post src0_msyms API L A regs mem md f R mem') _ Hh Hl).
  - exact (mw_evt API AX MWC L A regs mem md f HP).
  - intros R pc' mem' regs' (-> & HPo) HR. apply AgreeLift.SRcf_ret. exists regs', mem'. split; [reflexivity|].
    exact (mw_post_getr API L A regs mem md f R regs' mem' HR HPo).
Qed.
