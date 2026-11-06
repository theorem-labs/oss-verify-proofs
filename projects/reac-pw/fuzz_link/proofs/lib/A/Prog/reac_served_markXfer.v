(* reac_served_mark on image A: the objects a cut carries, moved across one callee.

   After an own callee (or a wrapper) the walk holds the callee's `akept` (link_amem.v) from the call state
   (ly3, S3, W3, m3) to the return state (W4, m4), with the callee's write set Ec excepted, and the AR of the return
   state (its journal). The lemmas below move the objects the cuts of reac_served_markDefs.v name:
   - the marks block and the memory FILE: heap blocks of both states, so akept's block clause keeps their bytes and
     AR's block law at the return state gives their writability (xfer_amarks, xfer_amemfile_k; g_said, the FILE's
     buffer, is a writable image object and stays writable by the segment, under HSEGS);
   - the fake kernel: g_nl is an image byte outside the runtime statics and errno (xfer_gnl_img), so akept's image
     clause keeps it; the interface-table strings move by a view equality the caller gives (at a cut they have the
     entry's view) (xfer_kern, xfer_kern_view);
   - F's two buffers and their shadow: F is a side frame of both states, so akept's frame clause keeps them and AR's
     frame law gives their writability (xfer_bufs); srm_R_lens bounds the two strings the read leaves.

   Proves no function (kind: segment lemma of reac_served_mark's walk: object transports across a callee). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_link.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalkSide PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_markDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- byte algebra, over any segments ---- *)
Section bytes.
Variable segs : list Segment.

Lemma xf_mbyte : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  aview segs H' m' a = aview segs H m a -> mbyte segs (mrestrict H' m') a = mbyte segs (mrestrict H m) a.
Proof.
  intros H H' m m' a E. unfold aview in E.
  destruct (mbyte segs (mrestrict H' m') a) as [b'|], (mbyte segs (mrestrict H m) a) as [b|];
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma xf_wr : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> writable_at segs (mrestrict H m) a.
Proof. intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate. Qed.

Lemma xf_abytes : forall (m m' : word -> option byte) p bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (p + i) = mbyte segs m (p + i)) ->
  abytes segs m p bs -> abytes segs m' p bs.
Proof.
  intros m m' p bs Hfr (H0 & H1 & Hn). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (Hfr (Z.of_nat i) ltac:(lia)). exact (Hn i Hi).
Qed.

Lemma xf_val_mem : forall (m m' : word -> option byte) a n v,
  (forall i, 0 <= i < Z.of_nat n -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
  val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros m m' a n v Hfr Hv k Hk. rewrite (Hfr (Z.of_nat k) ltac:(lia)). exact (Hv k Hk). Qed.

Lemma xf_acstr : forall (m m' : word -> option byte) p s,
  (forall i, 0 <= i <= Z.of_nat (length s) -> mbyte segs m' (p + i) = mbyte segs m (p + i)) ->
  acstr_at segs m p s -> acstr_at segs m' p s.
Proof.
  intros m m' p s Hfr (HB & HN). split; [|exact HN].
  apply (xf_abytes m m' p (s ++ [zb 0])); [|exact HB].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hfr. lia.
Qed.

Lemma xf_acstr_range : forall (m : word -> option byte) p s,
  acstr_at segs m p s -> 0 <= p /\ p + Z.of_nat (length s) + 1 <= 2 ^ 64.
Proof.
  intros m p s ((H0 & H1 & _) & _). rewrite length_app in H1. cbn [length] in H1. lia.
Qed.
End bytes.

(* the bytes the read leaves fit their buffers *)
Lemma srm_R_lens : forall s kbs tab,
  Z.of_nat (length (r_kind (srm_R s kbs tab))) < KIND_CAP /\
  Z.of_nat (length (r_alias (srm_R s kbs tab))) < ALIAS_MAX.
Proof.
  intros s kbs tab. unfold srm_R, read_lib, read_core.
  destruct (Nat.eqb (length s) 0); [cbn; unfold KIND_CAP, ALIAS_MAX; lia|].
  destruct (index_of tab s =? 0); [cbn; unfold KIND_CAP, ALIAS_MAX; lia|].
  cbn [r_kind r_alias].
  assert (T : forall o cap, 1 <= cap -> Z.of_nat (length (text_of_attr o cap)) <= cap - 1).
  { intros o cap Hc. destruct o as [pay|]; cbn [text_of_attr]; [apply cut_text_len; exact Hc | cbn; lia]. }
  assert (E1 : (32 <? 1) = false) by reflexivity. assert (E2 : (256 <? 1) = false) by reflexivity.
  unfold KIND_CAP, ALIAS_MAX. rewrite E1, E2. cbv beta iota zeta.
  split; (eapply Z.le_lt_trans; [apply T; lia | lia]).
Qed.

(* ---- image facts at link's segments ---- *)
Lemma xf_tfib_hull : forall a, 0x10000 <= a < 0x654000 -> in_img tfibsegs a.
Proof.
  intros a Ha. unfold in_img.
  assert (E : tfibsegs = [Asan_segment_000; Asan_segment_001; Asan_segment_002; Asan_segment_003]) by reflexivity.
  rewrite E.
  destruct (Z.lt_ge_cases a 0x31000); [exists Asan_segment_000; split; [cbn; tauto | cbn; lia]|].
  destruct (Z.lt_ge_cases a 0xa1000); [exists Asan_segment_001; split; [cbn; tauto | cbn; lia]|].
  destruct (Z.lt_ge_cases a 0xa3000); [exists Asan_segment_002; split; [cbn; tauto | cbn; lia]|].
  exists Asan_segment_003. split; [cbn; tauto | cbn; lia].
Qed.

Lemma xf_gnl_not_owned : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ Exists (in_zr a) Tfib_owned_static.
Proof.
  intros a Ha X. unfold LA_G_NL, NK_SIZE in Ha. unfold Tfib_owned_static in X.
  repeat (apply Exists_cons in X; destruct X as [X|X]; [unfold in_zr in X; cbn [fst snd] in X; lia|]).
  inversion X.
Qed.

Lemma xf_wseg_said : wseg_ok tfibsegs (Z_to_bv 64 LA_G_SAID) (Z.to_nat 4096) = true.
Proof. vm_compute. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HSEGS : SEGS = tfibsegs.
Hypothesis TB : PcapSyms B.

(* g_nl: an image byte outside the runtime statics and errno *)
Lemma xfer_gnl_img : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. rewrite HSEGS, (ts_owned B TB), (ts_errno B TB).
  split; [apply xf_tfib_hull; unfold LA_G_NL, NK_SIZE in Ha; lia|].
  split; [exact (xf_gnl_not_owned a Ha)|].
  unfold TFIB_ERRNO, LA_G_NL, NK_SIZE in *. lia.
Qed.

Lemma xfer_gnl_awrange : forall m, awrange SEGS m LA_G_NL NK_SIZE.
Proof.
  intros m i Hi. rewrite HSEGS. apply link_ajkit.LA_G_NL_writable. unfold NK_SIZE in Hi. lia.
Qed.

Lemma xfer_gsaid_awrange : forall m, awrange SEGS m LA_G_SAID SAID_SIZE.
Proof.
  intros m i Hi. rewrite HSEGS.
  apply (link_ajkit.writable_at_of_wseg tfibsegs m LA_G_SAID 4096);
    [unfold LA_G_SAID; lia | unfold LA_G_SAID; lia | exact xf_wseg_said | unfold SAID_SIZE in Hi; lia].
Qed.

(* a byte of a heap block of both states, outside Ec *)
Lemma xf_blk_byte : forall ly3 S3 (W3 : world SEGS) m3 (W4 : world SEGS) m4 slo shi (Ec : Z -> Prop) p n a,
  akept SEGS B ly3 S3 W3 m3 W4 m4 slo shi Ec -> In (p, n) (ablocks B ly3 S3) ->
  p <= a < p + req_size n -> ~ Ec a ->
  mbyte SEGS (rdW W4 m4) a = mbyte SEGS (rdW W3 m3) a.
Proof.
  intros ly3 S3 W3 m3 W4 m4 slo shi Ec p n a (_ & K2 & _) Hin Ha HE.
  apply xf_mbyte. replace a with (p + (a - p)) by lia.
  apply (K2 p n (a - p) Hin ltac:(lia)). replace (p + (a - p)) with a by lia. exact HE.
Qed.

Lemma xf_blk_wr : forall ly4 S4 (W4 : world SEGS) m4 md4 p n a,
  AR SEGS B ly4 S4 W4 m4 md4 -> In (p, n) (ablocks B ly4 S4) -> p <= a < p + req_size n ->
  writable_at SEGS (rdW W4 m4) a.
Proof.
  intros ly4 S4 W4 m4 md4 p n a HAR Hin Ha.
  destruct (al_blocks _ _ LAWS ly4 S4 W4 m4 md4 p n HAR Hin) as (_ & _ & _ & _ & Hpres & _).
  apply xf_wr. exact (proj1 (Hpres a Ha)).
Qed.

(* (a) the marks block *)
Lemma xfer_amarks : forall ly3 S3 (W3 : world SEGS) m3 (W4 : world SEGS) m4 ly4 S4 md4 slo shi (Ec : Z -> Prop) p gbs,
  akept SEGS B ly3 S3 W3 m3 W4 m4 slo shi Ec -> AR SEGS B ly4 S4 W4 m4 md4 ->
  In (p, MK_SIZE) (ablocks B ly3 S3) -> In (p, MK_SIZE) (ablocks B ly4 S4) ->
  (forall a, p <= a < p + MK_SIZE -> ~ Ec a) ->
  amarks_at SEGS (rdW W3 m3) p gbs -> amarks_at SEGS (rdW W4 m4) p gbs.
Proof.
  intros ly3 S3 W3 m3 W4 m4 ly4 S4 md4 slo shi Ec p gbs HK HAR Hin3 Hin4 HE ((HB & _) & HL).
  assert (RS : req_size MK_SIZE = MK_SIZE) by reflexivity.
  split; [|exact HL]. split.
  - apply (xf_abytes SEGS (rdW W3 m3) (rdW W4 m4) p gbs); [|exact HB].
    intros i Hi. rewrite HL in Hi.
    apply (xf_blk_byte ly3 S3 W3 m3 W4 m4 slo shi Ec p MK_SIZE); [exact HK | exact Hin3 | rewrite RS; lia | apply HE; lia].
  - intros i Hi. rewrite HL in Hi.
    apply (xf_blk_wr ly4 S4 W4 m4 md4 p MK_SIZE); [exact HAR | exact Hin4 | rewrite RS; lia].
Qed.

(* (b) the memory FILE *)
Lemma xfer_amemfile_k : forall ly3 S3 (W3 : world SEGS) m3 (W4 : world SEGS) m4 ly4 S4 md4 slo shi (Ec : Z -> Prop) f k,
  akept SEGS B ly3 S3 W3 m3 W4 m4 slo shi Ec -> AR SEGS B ly4 S4 W4 m4 md4 ->
  In (f, AMF_BLOCK) (ablocks B ly3 S3) -> In (f, AMF_BLOCK) (ablocks B ly4 S4) ->
  (forall a, f <= a < f + AMF_BLOCK -> ~ Ec a) ->
  amemfile_k SEGS (rdW W3 m3) f k -> amemfile_k SEGS (rdW W4 m4) f k.
Proof.
  intros ly3 S3 W3 m3 W4 m4 ly4 S4 md4 slo shi Ec f k HK HAR Hin3 Hin4 HE (Hat & Hwin & _ & _).
  assert (RS : req_size AMF_BLOCK = AMF_BLOCK) by reflexivity.
  assert (FR : forall x, f <= x < f + AMF_BLOCK -> mbyte SEGS (rdW W4 m4) x = mbyte SEGS (rdW W3 m3) x).
  { intros x Hx. apply (xf_blk_byte ly3 S3 W3 m3 W4 m4 slo shi Ec f AMF_BLOCK);
      [exact HK | exact Hin3 | rewrite RS; exact Hx | exact (HE x Hx)]. }
  assert (FV : forall off n v, 0 <= off -> off + Z.of_nat n <= AMF_BLOCK ->
            amf_fld SEGS (rdW W3 m3) f off n v -> amf_fld SEGS (rdW W4 m4) f off n v).
  { intros off n v H0 H1 Hv. unfold amf_fld in *. apply (xf_val_mem SEGS (rdW W3 m3) (rdW W4 m4)); [|exact Hv].
    intros i Hi. apply FR. lia. }
  split; [|split; [|split]].
  - apply (amemfile_at_frame SEGS link_amf (rdW W3 m3) (rdW W4 m4) f); [|exact Hat].
    intros x Hx. apply FR. unfold AMF_ZEROED, AMF_BLOCK in *. lia.
  - unfold amf_win in *. unfold AMF_BLOCK in FV.
    destruct Hwin as [(Hk & H1 & H2 & H3) | (Hk & H1 & H2 & H3)]; [left | right];
      (split; [exact Hk|]); (split; [apply FV; [lia | cbn; lia | exact H1]|]);
      (split; [apply FV; [lia | cbn; lia | exact H2] | apply FV; [lia | cbn; lia | exact H3]]).
  - intros i Hi. apply (xf_blk_wr ly4 S4 W4 m4 md4 f AMF_BLOCK); [exact HAR | exact Hin4 | rewrite RS; lia].
  - apply xfer_gsaid_awrange.
Qed.

(* (c) the fake kernel *)
Lemma xfer_kern_view : forall (W3 : world SEGS) m3 (W4 : world SEGS) m4 kbs kbs' tab St reqs n,
  (forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     au64_at SEGS (rdW W3 m3) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
     forall a, p <= a <= p + Z.of_nat (length n2) -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) ->
  srm_kern (rdW W3 m3) kbs kbs' tab St reqs n -> srm_kern (rdW W4 m4) kbs kbs' tab St reqs n.
Proof.
  intros W3 m3 W4 m4 kbs kbs' tab St reqs n HG HT
    (((HB & _) & HL) & WF & E1 & E2 & E3 & (Hn & Hl & HI) & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12).
  assert (FG : forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> mbyte SEGS (rdW W4 m4) x = mbyte SEGS (rdW W3 m3) x)
    by (intros x Hx; apply xf_mbyte; exact (HG x Hx)).
  split.
  { split; [|exact HL]. split; [|rewrite HL; apply xfer_gnl_awrange].
    apply (xf_abytes SEGS (rdW W3 m3) (rdW W4 m4) LA_G_NL kbs'); [|exact HB].
    intros i Hi. apply FG. lia. }
  split; [exact WF|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
  split.
  { split; [exact Hn|]. split; [exact Hl|].
    intros i nm ix Hi. destruct (HI i nm ix Hi) as (Hix & p & Hp & Hp0 & Hs & Hx).
    assert (Hilt : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    split; [exact Hix|]. exists p.
    pose proof (xf_acstr_range SEGS _ p nm Hs) as Hpr.
    split; [|split; [exact Hp0 | split]].
    - apply (xf_val_mem SEGS (rdW W3 m3) (rdW W4 m4)); [|exact Hp].
      intros j Hj. apply FG. unfold NK_IF_NAME, NK_SIZE in *. cbn in Hj. lia.
    - apply (xf_acstr SEGS (rdW W3 m3) (rdW W4 m4) p nm); [|exact Hs].
      intros j Hj. apply xf_mbyte. apply (HT i nm ix p Hi Hp ltac:(lia)). lia.
    - apply (xf_val_mem SEGS (rdW W3 m3) (rdW W4 m4)); [|exact Hx].
      intros j Hj. apply FG. unfold NK_IF_INDEX, NK_SIZE in *. cbn in Hj. lia. }
  split; [exact E4|]. split; [exact E5|]. split; [exact E6|]. split; [exact E7|]. split; [exact E8|].
  split; [exact E9|]. split; [exact E10|]. split; [exact E11|]. exact E12.
Qed.

Lemma xfer_kern : forall ly3 S3 (W3 : world SEGS) m3 (W4 : world SEGS) m4 slo shi (Ec : Z -> Prop)
    kbs kbs' tab St reqs n,
  akept SEGS B ly3 S3 W3 m3 W4 m4 slo shi Ec ->
  (forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ Ec a) ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     au64_at SEGS (rdW W3 m3) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
     forall a, p <= a <= p + Z.of_nat (length n2) -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) ->
  srm_kern (rdW W3 m3) kbs kbs' tab St reqs n -> srm_kern (rdW W4 m4) kbs kbs' tab St reqs n.
Proof.
  intros ly3 S3 W3 m3 W4 m4 slo shi Ec kbs kbs' tab St reqs n HK HE HT.
  apply xfer_kern_view; [|exact HT].
  intros a Ha. destruct HK as (_ & _ & K3 & _). destruct (xfer_gnl_img a Ha) as (I1 & I2 & I3).
  exact (K3 a I1 I2 I3 (HE a Ha)).
Qed.

(* (d) F's two buffers and their shadow *)
Lemma xfer_bufs : forall (cx : srmcx) fpos ly3 S3 (W3 : world SEGS) m3 (W4 : world SEGS) m4 ly4 S4 md4 slo shi
    (Ec : Z -> Prop) R,
  akept SEGS B ly3 S3 W3 m3 W4 m4 slo shi Ec -> AR SEGS B ly4 S4 W4 m4 md4 ->
  In (SRM_CID, fpos) (frames S3) -> In (SRM_CID, fpos) (frames S4) ->
  (forall c q, frame_addr ly3 c q = frame_addr (sm_lyc cx) c q) ->
  (forall c q, frame_addr ly4 c q = frame_addr (sm_lyc cx) c q) ->
  (forall a, srm_kind cx fpos <= a < srm_kind cx fpos + KIND_CAP \/
             srm_alias cx fpos <= a < srm_alias cx fpos + ALIAS_MAX -> ~ Ec a) ->
  (forall i, srm_bufsh_off i -> ~ Ec (srm_SH cx fpos + i)) ->
  Z.of_nat (length (r_kind R)) < KIND_CAP -> Z.of_nat (length (r_alias R)) < ALIAS_MAX ->
  srm_bufs cx fpos W3 m3 R -> srm_bufs cx fpos W4 m4 R.
Proof.
  intros cx fpos ly3 S3 W3 m3 W4 m4 ly4 S4 md4 slo shi Ec R HK HAR Hin3 Hin4 EF3 EF4 HEb HEs Lk La
    (Ck & Ca & (jk & Ljk & HBk & _) & (ja & Lja & HBa & _) & Hsh).
  destruct HK as (_ & _ & _ & K4 & _).
  assert (FB : fs_frame_bytes SRM_CID = 512) by reflexivity.
  assert (KF : srm_kind cx fpos = srm_F cx fpos + 32) by reflexivity.
  assert (AF : srm_alias cx fpos = srm_F cx fpos + 96) by reflexivity.
  (* a byte of F outside Ec keeps its view *)
  assert (VF : forall a, srm_F cx fpos <= a < srm_F cx fpos + 512 -> ~ Ec a ->
             mbyte SEGS (rdW W4 m4) a = mbyte SEGS (rdW W3 m3) a).
  { intros a Ha HE. apply xf_mbyte. apply (K4 SRM_CID fpos a Hin3); [|exact HE].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF3, FB. unfold srm_F in Ha. exact Ha. }
  (* a byte of F is writable at the return state *)
  assert (WF : forall a, srm_F cx fpos <= a < srm_F cx fpos + 512 -> writable_at SEGS (rdW W4 m4) a).
  { intros a Ha.
    destruct (al_frames _ _ LAWS ly4 S4 W4 m4 md4 SRM_CID fpos HAR Hin4) as (_ & _ & Hp & _).
    apply xf_wr. apply (Hp a). rewrite EF4, FB. unfold srm_F in Ha. exact Ha. }
  unfold KIND_CAP, ALIAS_MAX in *.
  split; [|split; [|split; [|split]]].
  - apply (xf_acstr SEGS (rdW W3 m3) (rdW W4 m4) _ (r_kind R)); [|exact Ck].
    intros i Hi. apply VF; [rewrite KF in *; lia | apply HEb; left; lia].
  - apply (xf_acstr SEGS (rdW W3 m3) (rdW W4 m4) _ (r_alias R)); [|exact Ca].
    intros i Hi. apply VF; [rewrite AF in *; lia | apply HEb; right; lia].
  - exists jk. split; [exact Ljk|]. split.
    + apply (xf_abytes SEGS (rdW W3 m3) (rdW W4 m4) _ jk); [|exact HBk].
      intros i Hi. apply VF; [rewrite KF in *; lia | apply HEb; left; lia].
    + intros i Hi. apply WF. rewrite KF in *. lia.
  - exists ja. split; [exact Lja|]. split.
    + apply (xf_abytes SEGS (rdW W3 m3) (rdW W4 m4) _ ja); [|exact HBa].
      intros i Hi. apply VF; [rewrite AF in *; lia | apply HEb; right; lia].
    + intros i Hi. apply WF. rewrite AF in *. lia.
  - intros i Hi. rewrite <- (Hsh i Hi). apply (K4 SRM_CID fpos _ Hin3); [|exact (HEs i Hi)].
    right. unfold in_zr. cbn [fst snd]. rewrite EF3, FB. unfold srm_SH, srm_F, srm_bufsh_off in *. lia.
Qed.

End b.
End a.
