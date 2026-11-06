(* reac-pw/fuzz_link, image A: the FILE and g_said premises of the rewind call in mark_quietly's later arm (0x883d4,
   listing (internal path) (internal record, sha256 83bb83545bf3), +0x50
   `jal wrapper_rewind`). At the entry (regs, lyc, Sc, W, memc) the arm holds mark_quietly_c.v's
   `mark_quietly_apre_again` and apre's write-set clause; the prologue stores ra / s0 / s1 / s2 into [sp - 32, sp)
   (memory mem1) and calls the rewind wrapper with sp = sp - 32. `mqa_rw_args` gives, at mem1, every premise of
   lib/A/Rt/LinkMfDefs.v `arewind_mf_realizes` that is about the FILE and g_said: the FILE with its k pending bytes
   (`amf_k`), its seven changing words (`amf_dyn`), the pending bytes as numbers (`amf_pend`), g_said as the copy's
   destination (`amf_buf_ok` at ARW_STK), and the caller journal's grant (`ajw`) of the FILE's first AMF_ZEROED bytes
   and of g_said. The FILE block is a heap block of the call's ledger and g_said an image byte range, so both lie below
   alloc_ceiling and the prologue's stores do not reach them or their shadow.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink AMemFile AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem model_decide_c remember_c reac_code_emit_c reac_served_mark_c mark_quietly_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs.
From OSSVerify.reac_pw.fuzz_link.images Require Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- bytes that agree in a range carry the FILE's predicates --------------------------------------------- *)

Lemma mqa_mb_eq : forall segs H (m m' : word -> option byte) a,
  aview segs H m' a = aview segs H m a -> mbyte segs (mrestrict H m') a = mbyte segs (mrestrict H m) a.
Proof.
  intros segs H m m' a E. unfold aview in E.
  destruct (mbyte segs (mrestrict H m') a) as [b'|], (mbyte segs (mrestrict H m) a) as [b|];
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma mqa_mb_present : forall segs H (m : word -> option byte) a,
  apresent H m a -> mbyte segs (mrestrict H m) a <> None.
Proof. intros segs H m a [Hh [b Hb]]. unfold mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.

Lemma mqa_vm_tr : forall segs (m m' : word -> option byte) lo hi,
  (forall a, lo <= a < hi -> mbyte segs m' a = mbyte segs m a) ->
  forall a (n : nat) v, lo <= a -> a + Z.of_nat n <= hi -> val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros segs m m' lo hi HE a n v H1 H2 Hv k Hk. rewrite HE by lia. exact (Hv k Hk). Qed.

Ltac mqa_vt T :=
  lazymatch goal with
  | |- val_mem _ _ ?a ?n ?v =>
      apply (T a n v);
      [ unfold AMF_BLOCK, AMF_COOKIE, AMF_BUF, AMF_BUFSIZ in *; lia
      | unfold AMF_BLOCK, AMF_COOKIE, AMF_BUF, AMF_BUFSIZ in *; lia
      | assumption ]
  end.

Lemma mqa_amemfile_at_tr : forall segs MS (m m' : word -> option byte) f,
  (forall a, f <= a < f + AMF_BLOCK -> mbyte segs m' a = mbyte segs m a) ->
  amemfile_at segs MS m f -> amemfile_at segs MS m' f.
Proof.
  intros segs MS m m' f HE H. pose proof (mqa_vm_tr segs m m' f (f + AMF_BLOCK) HE) as T. clear HE.
  destruct H as (H1 & H2 & H3 & HS & HF & HO & HW & HC).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [|split; [|split; [|split]]].
  - clear - HS T. unfold amemfile_static in *.
    repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
    repeat split; mqa_vt T.
  - unfold amemfile_flags in *. destruct HF as [HF|HF]; [left|right]; mqa_vt T.
  - unfold amemfile_omode in *. destruct HO as [HO|HO]; [left|right]; mqa_vt T.
  - unfold amemfile_window in *.
    destruct HW as (W1 & W2 & [(W3 & W4 & W5) | (kk & Hk & W3 & W4 & W5)]);
      (split; [mqa_vt T|]); (split; [mqa_vt T|]).
    + left. split; [mqa_vt T|]. split; mqa_vt T.
    + right. exists kk. split; [exact Hk|]. split; [mqa_vt T|]. split; mqa_vt T.
  - unfold amemfile_cookie in *. destruct HC as (pos & len & P1 & P2 & C1 & C2). exists pos, len.
    split; [exact P1|]. split; [exact P2|]. split; mqa_vt T.
Qed.

Lemma mqa_amf_win_tr : forall segs (m m' : word -> option byte) f k,
  (forall a, f <= a < f + AMF_BLOCK -> mbyte segs m' a = mbyte segs m a) ->
  LinkMfDefs.amf_win segs m f k -> LinkMfDefs.amf_win segs m' f k.
Proof.
  intros segs m m' f k HE H. pose proof (mqa_vm_tr segs m m' f (f + AMF_BLOCK) HE) as T. clear HE.
  unfold LinkMfDefs.amf_win in *.
  destruct H as [(Hk & W1 & W2 & W3) | (Hk & W1 & W2 & W3)]; [left | right];
    (split; [exact Hk|]); (split; [mqa_vt T|]); (split; mqa_vt T).
Qed.

Lemma mqa_amf_win_k : forall segs (m : word -> option byte) f k,
  LinkMfDefs.amf_win segs m f k -> 0 <= k <= AMF_BUFSIZ.
Proof. intros segs m f k [(-> & _) | (Hk & _)]; unfold AMF_BUFSIZ in *; lia. Qed.

(* the seven words the rewind path changes, read off the FILE and its window *)
Lemma mqa_amf_dyn_of : forall segs MS (m : word -> option byte) f k,
  amemfile_at segs MS m f -> LinkMfDefs.amf_win segs m f k -> f + AMF_BLOCK < 2 ^ 64 ->
  exists fl om wend wpos wbase pos len, amf_dyn segs MS m f fl om wend wpos wbase pos len.
Proof.
  intros segs MS m f k HA HW Hhi.
  destruct HA as (Hf0 & _ & _ & _ & HF & HO & _ & (pos & len & P1 & P2 & C1 & C2)).
  unfold amemfile_flags, amemfile_omode in *.
  destruct HF as [HF|HF]; [exists AF_NORD | exists (AF_NORD + AF_ERR)];
    (destruct HO as [HO|HO]; [exists 0 | exists AU32M1]);
    (destruct HW as [(Hk & W1 & W2 & W3) | (Hk & W1 & W2 & W3)];
      [exists 0, 0, 0 | exists (f + AMF_BUF + AMF_BUFSIZ), (f + AMF_BUF + k), (f + AMF_BUF)]);
    exists pos, len; unfold amf_dyn;
    repeat split; first [assumption | unfold AF_NORD, AF_ERR, AU32M1, AMF_BUF, AMF_BUFSIZ, AMF_BLOCK in *; lia].
Qed.

Lemma mqa_nth_map_seq : forall (g : nat -> Z) n i, (i < n)%nat -> nth i (map g (seq 0 n)) 0 = g i.
Proof.
  intros g n i Hi. transitivity (nth i (map g (seq 0 n)) (g 0%nat)).
  - apply nth_indep. rewrite length_map, length_seq. exact Hi.
  - rewrite map_nth, seq_nth by exact Hi. reflexivity.
Qed.

(* the k pending bytes, read off a memory where each of them is a byte *)
Lemma mqa_amf_pend_ex : forall segs (m : word -> option byte) f k,
  0 <= k -> (forall i, 0 <= i < k -> mbyte segs m (f + AMF_BUF + i) <> None) ->
  exists pb, amf_pend segs m f pb /\ Z.of_nat (length pb) = k.
Proof.
  intros segs m f k Hk Hs.
  exists (map (fun i => match mbyte segs m (f + AMF_BUF + Z.of_nat i) with Some b => bv_unsigned b | None => 0 end)
            (seq 0 (Z.to_nat k))).
  split.
  - unfold amf_pend, azbytes, amf_rd. intros i Hi. rewrite length_map, length_seq in Hi.
    rewrite mqa_nth_map_seq by exact Hi. cbv beta.
    pose proof (Hs (Z.of_nat i) ltac:(lia)) as Hn.
    destruct (mbyte segs m (f + AMF_BUF + Z.of_nat i)) as [b|]; [reflexivity | exfalso; exact (Hn eq_refl)].
  - rewrite length_map, length_seq. lia.
Qed.

(* ---- g_said on the image ------------------------------------------------------------------------------- *)

Lemma mqa_said_in_img : forall a, LA_G_SAID <= a < LA_G_SAID + SAID_SIZE -> YG0d.in_img tfibsegs a.
Proof.
  intros a Ha. unfold YG0d.in_img. unfold LA_G_SAID, SAID_SIZE in Ha.
  assert (E : tfibsegs = [Asan.Asan_segment_000; Asan.Asan_segment_001;
                          Asan.Asan_segment_002; Asan.Asan_segment_003]) by reflexivity.
  exists Asan.Asan_segment_003. split; [rewrite E; cbn; tauto | cbn; lia].
Qed.

(* none of the runtime's owned static ranges meets g_said (rows (0x62fec8, 0x18) and (0x630ee0, 0x400) end and start
   at its two ends) *)
Lemma mqa_said_not_static : forall a, LA_G_SAID <= a < LA_G_SAID + SAID_SIZE -> ~ Exists (in_zr a) Tfib_owned_static.
Proof.
  intros a Ha O. unfold Tfib_owned_static in O. apply Exists_exists in O as (r & Hr & X).
  unfold in_zr in X. unfold LA_G_SAID, SAID_SIZE in Ha. cbn [In] in Hr.
  repeat match type of Hr with
  | _ \/ _ => destruct Hr as [<-|Hr]; [cbn [fst snd] in X; lia|]
  | False => destruct Hr
  end.
Qed.

(* ---- the lemma --------------------------------------------------------------------------------------- *)

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.

Lemma mqa_rw_args : forall sink lyc Sc (W : world SEGS) memc mem1 mdc (regs regsT : bvmap 5 word)
    G XO OUT STK sp0 FP ly S own,
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= spZ regs - MARK_QUIETLY_AK ->
  mark_quietly_apre_again SEGS B sink (ablocks B lyc Sc) regs (rdW W memc) ->
  (forall a, inFP (mark_quietly_awr_again sink regs (rdW W memc)) a -> ajw B G XO OUT STK sp0 FP ly S lyc Sc own a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
     aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) memc a) ->
  mem_grows (rdW W memc) (rdW W mem1) ->
  spZ regsT = spZ regs - 32 ->
  exists kk fl om wend wpos wbase pos len (pb : list Z),
    LinkMfDefs.amf_k SEGS link_amf (rdW W mem1) sink kk /\
    amf_dyn SEGS link_amf (rdW W mem1) sink fl om wend wpos wbase pos len /\
    amf_pend SEGS (rdW W mem1) sink pb /\ Z.of_nat (length pb) = kk /\
    amf_buf_ok SEGS B link_amf ARW_STK lyc Sc W regsT mem1 /\
    (forall a, sink <= a < sink + AMF_ZEROED -> ajw B G XO OUT STK sp0 FP ly S lyc Sc own a) /\
    (forall a, amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf ->
       ajw B G XO OUT STK sp0 FP ly S lyc Sc own a).
Proof.
  intros sink lyc Sc W memc mem1 mdc regs regsT G XO OUT STK sp0 FP ly S own
    HAR Hceil HP Hwr Hview Hgrow HspT.
  rewrite MARK_QUIETLY_AK_val in Hceil.
  pose proof (@alloc_ceiling_value rc) as [[CL CH] _].
  destruct HP as (HIn & _ & Hs0 & _ & (k & HK) & _ & _ & _ & HwS & HmrS & HraS & HshS).
  destruct HK as (HAT & HWIN & _ & _).
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc sink AMF_BLOCK HAR HIn)
    as (_ & Hb4096 & Hbceil & _ & Hbpres & _ & _).
  replace (req_size AMF_BLOCK) with AMF_BLOCK in Hbceil, Hbpres by reflexivity.
  (* below alloc_ceiling the prologue changed nothing *)
  assert (HEG : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) memc a).
  { intros a Ha. apply Hview; lia. }
  assert (HEB : forall a, sink <= a < sink + AMF_BLOCK ->
            mbyte SEGS (rdW W mem1) a = mbyte SEGS (rdW W memc) a).
  { intros a Ha. apply mqa_mb_eq. apply HEG. unfold AMF_BLOCK in *. lia. }
  assert (HWINc : LinkMfDefs.amf_win SEGS (rdW W memc) sink k) by exact HWIN.
  pose proof (mqa_amemfile_at_tr _ _ _ _ _ HEB HAT) as HAT1.
  pose proof (mqa_amf_win_tr _ _ _ _ _ HEB HWINc) as HWIN1.
  pose proof (mqa_amf_win_k _ _ _ _ HWIN1) as Hk.
  destruct (mqa_amf_dyn_of _ _ _ _ _ HAT1 HWIN1 ltac:(unfold AMF_BLOCK in *; lia))
    as (fl & om & wend & wpos & wbase & pos & len & HD).
  assert (Hsome : forall i, 0 <= i < k -> mbyte SEGS (rdW W mem1) (sink + AMF_BUF + i) <> None).
  { intros i Hi. rewrite HEB by (unfold AMF_BUF, AMF_BUFSIZ, AMF_BLOCK in *; lia).
    apply mqa_mb_present. apply (Hbpres (sink + AMF_BUF + i)). unfold AMF_BUF, AMF_BUFSIZ, AMF_BLOCK in *; lia. }
  destruct (mqa_amf_pend_ex SEGS (rdW W mem1) sink k ltac:(lia) Hsome) as (pb & HPB & HL).
  exists k, fl, om, wend, wpos, wbase, pos, len, pb.
  split; [split; [exact HAT1 | exact HWIN1]|].
  split; [exact HD|]. split; [exact HPB|]. split; [exact HL|].
  split; [|split].
  - (* g_said as the checked copy's destination *)
    unfold amf_buf_ok. change (amf_buf link_amf) with LA_G_SAID. change (amf_size link_amf) with SAID_SIZE.
    split; [unfold LA_G_SAID; lia|]. split; [unfold LA_G_SAID, SAID_SIZE; lia|].
    split; [unfold SAID_SIZE; lia|].
    split; [|split; [exact HmrS|split]].
    + intros a Ha. split; [|split].
      * assert (Hw : writable_at SEGS (rdW W memc) a).
        { replace a with (LA_G_SAID + (a - LA_G_SAID)) by lia. apply HwS. lia. }
        unfold writable_at in *. exact (wview_grows _ _ _ _ Hgrow Hw).
      * intros Ho.
        assert (Hi : YG0d.in_img SEGS a) by (rewrite HSEGS; exact (mqa_said_in_img a Ha)).
        apply (proj1 (al_owned_image _ _ LAWS lyc Sc W memc mdc a HAR Hi)) in Ho.
        rewrite (ts_owned B TB) in Ho. exact (mqa_said_not_static a Ha Ho).
      * rewrite HspT. unfold ARW_STK, ESTACK, LA_G_SAID, SAID_SIZE in *. lia.
    + apply (ra_shadow_eq (aview SEGS (w_H W) memc)); [exact HraS|].
      intros x Hx. apply HEG. unfold shadow_addr, SHADOW_OFF, LA_G_SAID, SAID_SIZE in *. lia.
    + unfold shadow_hull_vis in *. intros s Hs. rewrite HEG; [exact (HshS s Hs)|].
      unfold shadow_addr, SHADOW_OFF, LA_G_SAID, SAID_SIZE in Hs. lia.
  - (* the FILE's first AMF_ZEROED bytes: the write set's FILE block *)
    intros a Ha. apply Hwr. exists (aivl sink AMF_BLOCK). split.
    + unfold mark_quietly_awr_again. cbn [In]. right; right; right; left; reflexivity.
    + unfold aivl. cbn [fst snd]. rewrite (proj2 (Z.eqb_neq sink 0) Hs0). unfold AMF_ZEROED, AMF_BLOCK in *. lia.
  - (* g_said: the write set's g_said *)
    change (amf_buf link_amf) with LA_G_SAID. change (amf_size link_amf) with SAID_SIZE.
    intros a Ha. apply Hwr. exists (LA_G_SAID, LA_G_SAID + SAID_SIZE). split.
    + unfold mark_quietly_awr_again. cbn [In]. right; right; left; reflexivity.
    + cbn [fst snd]. lia.
Qed.

End s.

Check mqa_rw_args.
Print Assumptions mqa_rw_args.
