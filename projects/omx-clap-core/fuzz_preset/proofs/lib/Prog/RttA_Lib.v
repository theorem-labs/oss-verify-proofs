From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
Ledger PjStruct ReaderRes tx_put_c TxRet WriterSpec WriterValue PjWriteHyp round_trip_text_c RttDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import RttGlue RttModel RttBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require strtod_c.
Import ListNotations.
Local Open Scope Z_scope.
Module LM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.

Lemma ra_uns : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity. Qed.

Lemma ra_node_top : forall segs m lb p u Du, pj_node segs m lb p u Du -> p + 56 <= 2 ^ 64.
Proof.
  intros segs m lb p u Du H. destruct u; cbn [pj_node] in H;
    destruct H as (_ & _ & num & str & kids & keys & n & cap & ((_ & _ & Htop & _) & _) & _); exact Htop.
Qed.

Lemma ra_pw_mid : forall {T : Type} (R : T -> T -> Prop) l1 x l2 y,
  pairwise R (l1 ++ x :: l2) -> In y (l1 ++ l2) -> R x y \/ R y x.
Proof.
  intros T R l1. induction l1 as [|h l1 IH]; intros x l2 y Hp Hy; cbn [app pairwise] in Hp, Hy.
  - destruct Hp as [Hh _]. left. exact (Hh y Hy).
  - destruct Hp as [Hh Hp]. destruct Hy as [<-|Hy].
    + right. apply Hh. apply in_or_app. right. left. reflexivity.
    + exact (IH x l2 y Hp Hy).
Qed.

(* #102 frame of round_trip_text (0x14d88 in the plain twin c8f4d6b8e567): addi sp, sp, -0x70; ra s0 s1 s2 s3 s4 s5
   saved at [S-56, S) (sd at sp+0x68 .. sp+0x38); the locals in [S-112, S-56). Was -0x60 / [S-40, S) / [S-96, S-40). *)
Lemma ra_mod8 : forall x, x mod 16 = 0 -> (x - 112) mod 8 = 0.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

Lemma ra_mod16 : forall x, x mod 16 = 0 -> (x - 112) mod 16 = 0.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

Ltac ra_inj E R pc m :=
  let ER := fresh "ER" in let EP := fresh "EP" in let EM := fresh "EM" in
  pose proof (f_equal ms_regs E) as ER; pose proof (f_equal ms_pc_val E) as EP;
  pose proof (f_equal ms_mem E) as EM; cbn [ms_regs ms_pc_val ms_mem MState.MS] in ER, EP, EM;
  subst R pc m; clear E.

Ltac ra_ret := unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity.

Section A.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
#[local] Set Default Proof Using "All".

Let AX : AllocExtra B (aa_MR API) := rtt_AX B API HSEG FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a :=
  rtt_FG B API HSEG FA.

Lemma ra_blow : forall L A mem md p n, aa_MR API L A mem md -> In (p, n) (blocks L A) -> 4096 <= p.
Proof. destruct (FA fx) as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma ra_run : forall (fx1 : YK11.FPState) regs1 pc mem1 md1 (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md1 = None -> m_vm_lazy md1 = [] ->
  Exec.evt rsegs Q (MState.MS (rmk regs1) (@fp_regs fx1) pc (@fp_csr fx1) None mem1 (seg_rom rsegs)) ->
  (forall ms', Q ms' -> exists R pc' m', ms' = MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m' (seg_rom rsegs)) ->
  (forall R pc' mem' regs', Q (MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None mem' (seg_rom rsegs)) ->
     (forall r, getr regs' r = getr R r) ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs' pc' mem' (seg_rom (ms_segs B))) md1) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 pc mem1 (seg_rom (ms_segs B))) md1) P.
Proof.
  intros fx1 regs1 pc mem1 md1 Q P Hh Hz HE HS HK.
  apply (@kb_run fx1 B regs1 pc mem1 md1
    (fun R pc' mem' => Q (MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None mem' (seg_rom rsegs))) P Hh Hz).
  - rewrite HSEG. eapply Exec.evt_mono; [exact HE|]. intros ms' HQ. destruct (HS ms' HQ) as (R & pc' & m' & E).
    exists R, pc', m'. split; [exact E | rewrite <- E; exact HQ].
  - exact HK.
Qed.

Lemma ra_stk : forall mem lo hi, alloc_ceiling <= lo -> lo <= hi -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at (ms_segs B) mem a) -> Frame.stk (ms_segs B) mem lo hi.
Proof.
  intros mem lo hi H1 H2 H3 HW.
  destruct (rtt_img_low B API HSEG FA) as [_ HI].
  pose proof alloc_ceiling_val as Hc.
  split; [lia|]. split; [lia|]. intros a Ha.
  assert (Hw : writable_at (ms_segs B) mem a) by (apply HW; lia).
  split; [exact Hw|].
  revert Hw. unfold LM.mrd, LM.wa, writable_at, wview.
  destruct (mem (Z_to_bv 64 a)) as [b|]; intros Hw; [exists b; reflexivity|].
  rewrite MState.unsigned_lit in Hw by lia.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:Fs; [|contradiction].
  exfalso. destruct (HI a seg Fs). lia.
Qed.

Lemma ra_ro_munch : forall m m' lo hi, MemNorm.ro_agree (ms_segs B) m -> Frame.munch [(lo, hi)] m m' ->
  alloc_ceiling <= lo -> MemNorm.ro_agree (ms_segs B) m'.
Proof.
  intros m m' lo hi Hro HM Hlo a Ha.
  assert (Hlt : bv_unsigned a < alloc_ceiling).
  { unfold MemNorm.ro_agree, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.ro_addr in Ha.
    destruct (find_segment (ms_segs B) (bv_unsigned a) 1) as [seg|] eqn:Ef; [|discriminate].
    destruct (rtt_img_low B API HSEG FA) as [_ HI]. exact (proj2 (HI _ _ Ef)). }
  assert (E : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.mrd (ms_segs B) m' a =
              OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.mrd (ms_segs B) m a).
  { unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.mrd. rewrite (HM a); [reflexivity|].
    apply outside_one. lia. }
  rewrite E. exact (Hro a Ha).
Qed.

(* #102: struct text gains `int failed` at offset 24 (24 -> 32 bytes); tx_put_c's text_rec (cold/h-rw-pre-4-rw102-txp
   f441f17d4895) = the three words + t + 28 <= 2 ^ 64 + failed = 0 (4 bytes at t + 24). *)
Lemma ra_rec : forall m t b len cap,
  LM.bytes_at (ms_segs B) m t (LM.le8 (Z_to_bv 64 b)) ->
  LM.bytes_at (ms_segs B) m (t + 8) (LM.le8 (Z_to_bv 64 len)) ->
  LM.bytes_at (ms_segs B) m (t + 16) (LM.le8 (Z_to_bv 64 cap)) ->
  t + 28 <= 2 ^ 64 ->
  LM.bytes_at (ms_segs B) m (t + 24) (LM.le4 (Z_to_bv 64 0)) ->
  text_rec B m t b len cap.
Proof.
  intros m t b len cap (_ & _ & H1) (_ & _ & H2) (_ & _ & H3) HT (_ & _ & H4).
  split; [|split; [exact HT|]].
  - intros i Hi.
    assert (L8 : forall w, length (LM.le8 w) = 8%nat) by (intros w; apply LM.length_le8).
    rewrite !length_app, !L8 in Hi.
    destruct (Z_lt_le_dec i 8) as [Hi1|Hi1]; [|destruct (Z_lt_le_dec i 16) as [Hi2|Hi2]].
    + rewrite nth_error_app1 by (rewrite !L8; lia).
      specialize (H1 (Z.to_nat i) ltac:(rewrite !L8; lia)). rewrite Z2Nat.id in H1 by lia. exact H1.
    + rewrite nth_error_app2 by (rewrite !L8; lia). rewrite nth_error_app1 by (rewrite !L8; lia).
      rewrite !L8. specialize (H2 (Z.to_nat i - 8)%nat ltac:(rewrite !L8; lia)).
      replace (t + 8 + Z.of_nat (Z.to_nat i - 8)) with (t + i) in H2 by lia. exact H2.
    + rewrite nth_error_app2 by (rewrite !L8; lia). rewrite nth_error_app2 by (rewrite !L8; lia).
      rewrite !L8. specialize (H3 (Z.to_nat i - 8 - 8)%nat ltac:(rewrite !L8; lia)).
      replace (t + 16 + Z.of_nat (Z.to_nat i - 8 - 8)) with (t + i) in H3 by lia. exact H3.
  - intros i Hi.
    assert (L4 : length (LM.le4 (Z_to_bv 64 0)) = 4%nat) by apply LM.length_le4.
    rewrite L4 in Hi.
    specialize (H4 (Z.to_nat i) ltac:(rewrite L4; lia)). rewrite Z2Nat.id in H4 by lia. exact H4.
Qed.

Lemma ra_keep : forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D
    fx1 L A mem md X Lam peak cnt bnd q Kc (Ec gc : Z -> Prop) L' A' mem' md',
  @rtt_ent fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L A mem md X Lam peak cnt bnd ->
  rt_text B L0 A0 mem Lam t (negb (pretty =? 0)) q ->
  rstep B API Kc (spZ regs0 - 112) Ec gc L A mem md L' A' mem' md' -> 0 <= Kc -> 112 + Kc <= RTT_K ->
  (forall a, Ec a -> (spZ regs0 - 112 <= a < spZ regs0 - 56) \/
     (0 <= a < alloc_ceiling /\ ~ in_img B a /\ forall b k, In (b, k) (blocks L A) -> ~ gc b -> ~ (b <= a < b + k))) ->
  (forall a k, In (a, k) Lam -> ~ gc (a - 16)) ->
  ledger B L' A' mem' Lam peak cnt (2 ^ 64 - 1) /\ pj_node (ms_segs B) mem' (lin Lam) doc t D /\
  rt_text B L0 A0 mem' Lam t (negb (pretty =? 0)) q.
Proof.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem md X Lam peak cnt bnd q
    Kc Ec gc L' A' mem' md' ENT INV RT STEP HK0 HK1 HEC HG.
  pose proof ENT as (REN & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSUB & _ & DOCS & _ & _ & WL & _).
  pose proof REN as (_ & _ & ERRB & _ & _ & PRE0 & _).
  pose proof PRE0 as (_ & _ & _ & _ & _ & SPC & SP63 & _).
  pose proof INV as (RS & _ & _ & _ & _ & _ & LED & _ & PERM & NODE & _).
  pose proof RS as (MRc & _).
  pose proof STEP as (_ & _ & _ & _ & _ & _ & _ & _ & U' & _).
  destruct (rtt_img_low B API HSEG FA) as (HIL & _).
  pose proof alloc_ceiling_val as HCV.
  assert (HERR : errno_addr B = 0x347f4) by (rewrite ERRB; reflexivity).
  pose proof LED as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB.
  assert (HLS : forall a k, In (a, k) Lam -> forall i, -16 <= i < k -> ~ Ec (a + i)).
  { intros a k Hin i Hi He. destruct (FB (a, k) Hin) as (Hk & Hblk & _ & _). cbn [fst snd] in Hk, Hblk.
    destruct (rg_blk B API HSEG AX FG L A mem md (a - 16) (k + 16) (i + 16) MRc Hblk ltac:(lia)) as (_ & H1 & H2 & _).
    destruct (HEC _ He) as [Hm | (_ & _ & Hb)]; [lia|].
    apply (Hb (a - 16) (k + 16) Hblk (HG a k Hin)). lia. }
  assert (HDL : forall bk, In bk D -> In bk Lam).
  { intros bk Hb. apply (Permutation_in _ (Permutation_sym PERM)). apply in_or_app. right. exact (DSUB bk Hb). }
  split.
  { apply (ledger_rstep B API HSEG AX FG Kc (spZ regs0 - 112) Ec gc L A mem md L' A' mem' md' Lam peak cnt (2 ^ 64 - 1)
      MRc LED STEP).
    - intros a Ha. destruct (statics_img B API HSEG AX FG a Ha) as [Hi _]. pose proof (HIL a Hi) as Ha'.
      split.
      + unfold rwin. rewrite HERR. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. lia.
      + intros He. destruct (HEC a He) as [Hm | (_ & Hn & _)]; [lia | exact (Hn Hi)].
    - intros a k Hin. split; [exact (HG a k Hin) | exact (HLS a k Hin)]. }
  split.
  { apply (pj_node_rstep B API HSEG AX FG Kc (spZ regs0 - 112) Ec gc L A mem md L' A' mem' md' Lam Lam peak cnt
      (2 ^ 64 - 1) doc t D MRc LED NODE HDL STEP).
    - lia.
    - exact (ra_node_top _ _ _ _ _ _ NODE).
    - intros i Hi. split.
      + unfold rwin. rewrite HERR. lia.
      + intros He. destruct (HEC _ He) as [Hm | (Hlo & _)]; lia.
    - intros a k Hin. split; [exact (HG a k (HDL _ Hin)) | intros i Hi; apply (HLS a k (HDL _ Hin)); lia].
    - intros bk Hb; exact Hb. }
  destruct RT as (Hq & HqL & HqB & HqF & HqY).
  split; [exact Hq|]. split; [exact HqL|]. split; [exact HqB|]. split; [exact HqF|].
  destruct (FB _ HqL) as (Hk & Hblk & _ & _). cbn [fst snd] in Hk, Hblk.
  assert (HW : wlen t (negb (pretty =? 0)) + 1 <= wcap t (negb (pretty =? 0))) by (apply wcap_ge; lia).
  apply (ia_bytes B mem); [exact HqY|]. intros i Hi.
  rewrite length_map, length_app in Hi. cbn [length] in Hi. unfold wlen in HW.
  pose proof (U' (q - 16) (wcap t (negb (pretty =? 0)) + 16) (i + 16) Hblk (HG q _ HqL) ltac:(lia)) as Ub.
  replace (q - 16 + (i + 16)) with (q + i) in Ub by lia. apply Ub.
  intros He. apply (HLS q _ HqL i ltac:(lia)). exact He.
Qed.

Lemma ra_write : forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D
    fx1 L A mem md X Lam peak cnt bnd q mem' lo hi,
  @rtt_ent fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L A mem md X Lam peak cnt bnd ->
  rt_text B L0 A0 mem Lam t (negb (pretty =? 0)) q ->
  Frame.munch [(lo, hi)] mem mem' -> Frame.wmono (ms_segs B) mem mem' ->
  spZ regs0 - 112 <= lo -> lo <= hi -> hi <= spZ regs0 - 56 ->
  (forall a, lo <= a < hi -> writable_at (ms_segs B) mem' a) ->
  @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L A mem' md X Lam peak cnt bnd /\
  rt_text B L0 A0 mem' Lam t (negb (pretty =? 0)) q.
Proof.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem md X Lam peak cnt bnd q
    mem' lo hi ENT INV RT HM HWM H1 H2 H3 HWR.
  pose proof ENT as (REN & _).
  pose proof REN as (_ & _ & ERRB & _ & _ & PRE0 & _).
  pose proof PRE0 as (_ & _ & _ & _ & _ & SPC & SP63 & _).
  pose proof INV as (RS & _ & _ & RD & FRM & _ & _ & _ & PERM & _ & RES & _).
  pose proof RS as (MRc & WFc & BDc & _ & _ & _ & _ & _ & _ & WRc).
  pose proof alloc_ceiling_val as HCV.
  assert (HK0 : 112 <= RTT_K) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (STEP : rstep B API 0 (spZ regs0 - 112) (fun a => lo <= a < hi) (fun _ => False) L A mem md L A mem' md).
  { apply (rstep_of_munch B API HSEG AX FG 0 (spZ regs0 - 112) _ _ L A mem mem' md [(lo, hi)] MRc WFc BDc).
    - intros a Ha. apply WRc. unfold rwin in Ha |- *. lia.
    - exact HM.
    - exact HWM.
    - intros x Hx Ho. right. destruct (Z_lt_le_dec x lo) as [Hl|Hl]; [exfalso; apply Ho; apply outside_one; lia|].
      destruct (Z_lt_le_dec x hi) as [Hh|Hh]; [lia | exfalso; apply Ho; apply outside_one; lia].
    - intros x Hx _. apply outside_one. lia. }
  destruct (ra_keep L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem md X Lam peak cnt bnd q
    0 _ _ L A mem' md ENT INV RT STEP ltac:(lia) ltac:(lia)) as (LED' & NODE' & RT').
  { intros a Ha. left. lia. }
  { intros a k _ []. }
  split; [|exact RT'].
  apply (inv_after B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem md X Lam peak
    cnt bnd 0 (fun a => lo <= a < hi) (fun _ => False) fx1 L A mem' md X Lam peak cnt bnd ENT INV STEP).
  - lia.
  - lia.
  - intros a Ha. right. left. lia.
  - intros a _ Ha. exact (HWR a Ha).
  - intros a k _ _ [].
  - intros a k Hin _. exact Hin.
  - apply (ra_ro_munch mem mem' lo hi); [exact (proj1 RD) | exact HM | lia].
  - exact FRM.
  - intros r _. reflexivity.
  - exact LED'.
  - lia.
  - exact PERM.
  - exact NODE'.
  - exact RES.
Qed.

Definition txr (K : Z) (regs : bvmap 5 word) (tr b0 cap0 : Z) (L : layout) (A : astate) (mem : word -> option byte)
    (md : Model) (L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model) (b1 len1 cap1 : Z)
    (txt1 : list byte) : Prop :=
  tx_frame B API K regs (tx_writes tr b0 cap0 b1 cap1) L A mem md L' A' mem' md' /\
  blocks_kept B L A mem mem' (fun a => a = b0) /\
  (forall a k, In (a, k) (blocks L A) -> (a, k) <> (b0, cap0) -> In (a, k) (blocks L' A') /\ (a, k) <> (b1, cap1)) /\
  (forall a k, In (a, k) (blocks L A) -> 0 < k -> a <> b0 -> a <> b1) /\
  text_rec B mem' tr b1 len1 cap1 /\ (forall i, 0 <= i < 24 -> writable_at (ms_segs B) mem' (tr + i)) /\
  tx_inv B L' A' mem' b1 len1 cap1 txt1 /\ MemNorm.ro_agree (ms_segs B) mem' /\ st_init_done A' = true.

Lemma ra_ec : forall K regs tr b0 len0 cap0 txt0 L A mem md L' A' mem' md' b1 len1 cap1 txt1,
  aa_MR API L A mem md -> tx_inv B L A mem b0 len0 cap0 txt0 ->
  txr K regs tr b0 cap0 L A mem md L' A' mem' md' b1 len1 cap1 txt1 ->
  forall a, (b0 <= a < b0 + cap0 \/ b1 <= a < b1 + cap1) ->
  0 <= a < alloc_ceiling /\ ~ in_img B a /\ forall b k, In (b, k) (blocks L A) -> b <> b0 -> ~ (b <= a < b + k).
Proof.
  intros K regs tr b0 len0 cap0 txt0 L A mem md L' A' mem' md' b1 len1 cap1 txt1 HM TI0
    (FR & _ & OLD & NB & _ & _ & TI1 & _) a Ha.
  pose proof FR as (MR' & _).
  destruct Ha as [Ha|Ha].
  - destruct TI0 as (_ & [(C0 & _ & _) | (Cp & Hin & _ & _ & NI)]); [lia|].
    destruct (rg_blk B API HSEG AX FG L A mem md b0 cap0 (a - b0) HM Hin ltac:(lia)) as (_ & H1 & H2 & _).
    split; [lia|]. split; [replace a with (b0 + (a - b0)) by lia; apply NI; lia|].
    intros b k Hb Hne Hx.
    exact (blocks_apart B API HSEG AX FG L A mem md b0 cap0 b k a HM Hin Hb (fun E => Hne (eq_sym E)) Ha Hx).
  - destruct TI1 as (_ & [(C0 & _ & _) | (Cp & Hin & _ & _ & NI)]); [lia|].
    destruct (rg_blk B API HSEG AX FG L' A' mem' md' b1 cap1 (a - b1) MR' Hin ltac:(lia)) as (_ & H1 & H2 & _).
    split; [lia|]. split; [replace a with (b1 + (a - b1)) by lia; apply NI; lia|].
    intros b k Hb Hne Hx.
    assert (Hk : 0 < k) by lia.
    destruct (OLD b k Hb ltac:(intros E; injection E as E1 E2; exact (Hne E1))) as [Hb' _].
    pose proof (NB b k Hb Hk Hne) as Hb1.
    exact (blocks_apart B API HSEG AX FG L' A' mem' md' b1 cap1 b k a MR' Hin Hb' (fun E => Hb1 (eq_sym E)) Ha Hx).
Qed.

Lemma ra_after : forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D
    fx1 L A mem md X Lam peak cnt bnd q want len cap txt K regs1 L' A' mem' md' b1 len1 cap1 txt1 bnd',
  @rtt_ent fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L A mem md X Lam peak cnt bnd ->
  rt_text B L0 A0 mem Lam t (negb (pretty =? 0)) q ->
  rt_harn B L0 A0 L A mem Lam (spZ regs0 - 112) want len cap txt ->
  spZ regs1 = spZ regs0 - 112 -> 0 <= K -> 112 + K <= RTT_K ->
  txr K regs1 (spZ regs0 - 112) want cap L A mem md L' A' mem' md' b1 len1 cap1 txt1 ->
  rf_ok F A' bnd' ->
  @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L' A' mem' md' X Lam peak cnt bnd' /\
  rt_text B L0 A0 mem' Lam t (negb (pretty =? 0)) q /\
  rt_harn B L0 A0 L' A' mem' Lam (spZ regs0 - 112) b1 len1 cap1 txt1.
Proof.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem md X Lam peak cnt bnd q want len
    cap txt K regs1 L' A' mem' md' b1 len1 cap1 txt1 bnd' ENT INV RT HARN SP1 HK0 HK1 TXR RES'.
  pose proof ENT as (REN & _).
  pose proof REN as (_ & _ & ERRB & _ & _ & PRE0 & _).
  pose proof PRE0 as (_ & _ & _ & _ & _ & SPC & SP63 & _).
  pose proof INV as (RS & _ & _ & _ & FRM & _ & LED & _ & PERM & _ & _ & _).
  pose proof RS as (MRc & _ & _ & _ & PSc & _).
  pose proof HARN as (_ & _ & _ & _ & _ & TI0 & HB0 & HL0).
  pose proof TXR as (FR & BK & OLD & NB & REC' & TW' & TI1 & RA' & IN').
  pose proof FR as (MR' & _).
  pose proof alloc_ceiling_val as HCV.
  pose proof LED as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB.
  set (E := tx_writes (spZ regs0 - 112) want cap b1 cap1).
  assert (STEP : rstep B API K (spZ regs0 - 112) E (fun a => a = want) L A mem md L' A' mem' md').
  { rewrite <- SP1. apply (rstep_of_tx_frame B API HSEG AX FG K regs1 E _ L A mem md L' A' mem' md' MRc FR).
    - intros _. exact IN'.
    - intros a k Hin Hk Hne. apply (OLD a k Hin). intros Xe. injection Xe as X1 X2. exact (Hne X1).
    - intros a k i Hin Hne Hi _. exact (BK a k i Hin Hne Hi). }
  assert (HEC : forall a, E a -> (spZ regs0 - 112 <= a < spZ regs0 - 56) \/
     (0 <= a < alloc_ceiling /\ ~ in_img B a /\
      forall b k, In (b, k) (blocks L A) -> ~ (b = want) -> ~ (b <= a < b + k))).
  { intros a Ha. unfold E, tx_writes in Ha. destruct Ha as [Ha|Ha]; [left; lia|right].
    exact (ra_ec K regs1 _ want len cap txt L A mem md L' A' mem' md' b1 len1 cap1 txt1 MRc TI0 TXR a Ha). }
  destruct (ra_keep L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem md X Lam peak cnt bnd q
    K E (fun a => a = want) L' A' mem' md' ENT INV RT STEP HK0 HK1 HEC) as (LED' & NODE' & RT').
  { intros a k Hin. exact (HL0 a k Hin). }
  split; [|split; [exact RT'|]].
  - apply (inv_after B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D
      fx1 L A mem md X Lam peak cnt bnd K E (fun a => a = want) fx1 L' A' mem' md' X Lam peak cnt bnd'
      ENT INV STEP HK0 HK1).
    + intros a Ha. destruct (HEC a Ha) as [H|H]; [right; left; exact H | right; right; exact H].
    + intros a Ha He. unfold E, tx_writes in He. destruct He as [He|[He|He]].
      * replace a with (spZ regs0 - 112 + (a - (spZ regs0 - 112))) by lia. apply TW'. lia.
      * destruct (ra_ec K regs1 _ want len cap txt L A mem md L' A' mem' md' b1 len1 cap1 txt1 MRc TI0 TXR a
          (or_introl He)) as (Hl & _). lia.
      * destruct (ra_ec K regs1 _ want len cap txt L A mem md L' A' mem' md' b1 len1 cap1 txt1 MRc TI0 TXR a
          (or_intror He)) as (Hl & _). lia.
    + intros a k Hin Hk Heq. exact (HB0 a k Hin Hk Heq).
    + intros a k Hin Hk. apply (OLD a k Hin). intros Xe. injection Xe as X1 X2. subst a k.
      destruct TI0 as (_ & [(C0 & W0 & _) | (Cp & _)]); [| lia].
      subst want. pose proof (ra_blow L A mem md 0 cap MRc Hin). lia.
    + exact RA'.
    + exact FRM.
    + intros r _. reflexivity.
    + exact LED'.
    + lia.
    + exact PERM.
    + exact NODE'.
    + exact RES'.
  - pose proof TI1 as (TL1 & TC1).
    assert (RNG : 0 <= b1 < 2 ^ 64 /\ 0 <= len1 < 2 ^ 64 /\ 0 <= cap1 < 2 ^ 64).
    { destruct TC1 as [(C0 & B0 & L0') | (Cp & Hin & Hlc & _)]; [lia|].
      destruct (rg_blk B API HSEG AX FG L' A' mem' md' b1 cap1 0 MR' Hin ltac:(lia)) as (_ & H1 & H2 & _). lia. }
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact REC'|]. split; [exact TW'|]. split; [exact TI1|].
    split.
    + intros a k Hin Hk. apply (NB a k (PSc a k Hin Hk (fun h => h)) Hk). exact (HB0 a k Hin Hk).
    + intros a n Hin. destruct (FB _ Hin) as (Hn & Hblk & _). cbn [fst snd] in Hn, Hblk.
      apply (NB (a - 16) (n + 16) Hblk ltac:(lia)). exact (HL0 a n Hin).
Qed.

(* #102: the `sd zero, 0x18(sp)` at 0x14dc8 zeroes struct text's `failed` word (offset 24); its low 4 bytes are the
   le4 0 that tx_put_c's text_rec asks for, and its end bound gives r + 28 <= 2 ^ 64. *)
Lemma ra_z8_z4 : forall m a,
  LM.bytes_at (ms_segs B) m a (LM.le8 (Z_to_bv 64 0)) -> LM.bytes_at (ms_segs B) m a (LM.le4 (Z_to_bv 64 0)).
Proof.
  intros m a (H0 & H1 & H2). rewrite LM.length_le8 in H1.
  split; [exact H0|]. split; [rewrite LM.length_le4; lia|].
  intros i Hi. rewrite LM.length_le4 in Hi.
  rewrite (H2 i ltac:(rewrite LM.length_le8; lia)).
  destruct i as [|[|[|[|i]]]]; [vm_compute; reflexivity .. | lia].
Qed.

Lemma ra_harn0 : forall L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L A mem md X Lam peak cnt bnd,
  @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L A mem md X Lam peak cnt bnd ->
  LM.bytes_at (ms_segs B) mem (spZ regs0 - 112) (LM.le8 (Z_to_bv 64 0)) ->
  LM.bytes_at (ms_segs B) mem (spZ regs0 - 112 + 8) (LM.le8 (Z_to_bv 64 0)) ->
  LM.bytes_at (ms_segs B) mem (spZ regs0 - 112 + 16) (LM.le8 (Z_to_bv 64 0)) ->
  LM.bytes_at (ms_segs B) mem (spZ regs0 - 112 + 24) (LM.le8 (Z_to_bv 64 0)) ->
  (forall i, 0 <= i < 24 -> writable_at (ms_segs B) mem (spZ regs0 - 112 + i)) ->
  rt_harn B L0 A0 L A mem Lam (spZ regs0 - 112) 0 0 0 [].
Proof.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L A mem md X Lam peak cnt bnd INV Z0 Z8 Z16 Z24 HW.
  pose proof INV as (RS & _ & _ & _ & _ & _ & LED & _).
  pose proof RS as (MRc & _ & _ & _ & PSc & _).
  pose proof LED as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB.
  assert (HT : spZ regs0 - 112 + 28 <= 2 ^ 64).
  { destruct Z24 as (_ & HB & _). rewrite LM.length_le8 in HB. lia. }
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact (ra_rec mem _ 0 0 0 Z0 Z8 Z16 HT (ra_z8_z4 mem _ Z24))|].
  split; [exact HW|].
  split; [split; [reflexivity | left; lia]|].
  split.
  - intros a k Hin Hk Ea. subst a. pose proof (ra_blow L A mem md 0 k MRc (PSc 0 k Hin Hk (fun h => h))). lia.
  - intros a n Hin Ea. destruct (FB _ Hin) as (Hn & Hblk & _). cbn [fst snd] in Hn, Hblk.
    pose proof (ra_blow L A mem md (a - 16) (n + 16) MRc Hblk). lia.
Qed.

(* #102 rtt_regs (RttBase at cold/h-rw-pre-4-rw102-rtt 133613731c31): sp = S-112, s0 = copy, s1 = regs0 a0,
   s2..s5 = s2v..s5v, gp / tp kept, s6..s11 kept. *)
Lemma ra_regs_pres : forall regs0 regs1 regs2 copy s2v s3v s4v s5v,
  rtt_regs regs0 regs1 copy s2v s3v s4v s5v -> regs_preserved regs1 regs2 ->
  rtt_regs regs0 regs2 copy s2v s3v s4v s5v.
Proof.
  intros regs0 regs1 regs2 copy s2v s3v s4v s5v (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G3 & G4 & G22) RR.
  split; [rewrite <- G2; apply (RR 2); unfold callee_saved; lia|].
  split; [rewrite <- G8; apply (RR 8); unfold callee_saved; lia|].
  split; [rewrite <- G9; apply (RR 9); unfold callee_saved; lia|].
  split; [rewrite <- G18; apply (RR 18); unfold callee_saved; lia|].
  split; [rewrite <- G19; apply (RR 19); unfold callee_saved; lia|].
  split; [rewrite <- G20; apply (RR 20); unfold callee_saved; lia|].
  split; [rewrite <- G21; apply (RR 21); unfold callee_saved; lia|].
  split; [rewrite <- G3; apply (RR 3); unfold callee_saved; lia|].
  split; [rewrite <- G4; apply (RR 4); unfold callee_saved; lia|].
  intros r Hr. rewrite <- (G22 r Hr). apply RR. unfold callee_saved. lia.
Qed.

End A.
