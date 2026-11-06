(* A store into fuzz/alloc.c's statics keeps ARU (fs.asan, image tfibsegs): the AR-after-store lemma every
   static-writing walk of fs's ALLOC group needs (fuzz_malloc, fuzz_free p <> 0, fuzz_realloc, fuzz_alloc_peak_reset,
   fuzz_alloc_fail), stated ONCE, generic in which of the four statics are written and in the bytes written.
   The statics FS_PSTAT_FP (lib/A/FSPstat.v) lie in fs.asan's last RW segment [0xa1000, 0x5fd000) (images/Asan.v
   Asan_segment_003), so they are in_img, never hidden by a world's H (H_off_segments), and far below SHADOW_OFF, so no
   user-poisoned shadow byte of U is one of them. AR's frame law (Reusable/YG0d.v:438-445) keeps AR across a memory
   change that leaves every OWNED byte alone and keeps every visible byte visible; AR_owned_image_law (YG0d.v:473-474)
   says an in-image byte is owned exactly when it is in as_owned_static B, and fs_img_facts' first conjunct
   (FSH_Gen.v fs_img_facts_at, projection fs_pstat_not_owned) says no static byte is.
   This file proves only the AR side of a store. The journal side (awr_byte / ajournal_after_write accepting a write
   whose bytes are inFP FP a /\ in_img segs a) is the core's (a Theorem Labs lane) and FSW_K's fsw_ajournal_writeU.
   port-from: the AR_frame_law use of cgif_file lib/A/AE2x.v:253-264 (al_frame over a write that leaves owned bytes
   alone); the unpoison bookkeeping of FSW_K.v:62-83 (fsw_unpoison_high). No rename. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YP09 YP03 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI04 YI16 YM05 YG0q.
From OSSVerify.omx_clap_core.fuzz_state.images Require Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v FSupoison FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- where the statics are ---- *)
Lemma fs_rw3_seg : In Asan.Asan_segment_003 tfibsegs /\ Z.of_N (seg_base Asan.Asan_segment_003) = 0xa1000 /\
  Z.of_N (seg_size Asan.Asan_segment_003) = 0x55c000.
Proof.
split; [|split; reflexivity].
unfold tfibsegs, Asan.M.loaded_segments, Asan.Asan_loaded_segments. right; right; right; left; reflexivity.
Qed.
Lemma fs_rw3_img : forall a, 0xa1000 <= a < 0x5fd000 -> in_img tfibsegs a.
Proof.
intros a Ha. destruct fs_rw3_seg as (Hin & Hb & Hs). exists Asan.Asan_segment_003.
split; [exact Hin|]. rewrite Hb, Hs. lia.
Qed.
(* no world hides a byte of the image (H_off_segments) *)
Lemma fs_rw3_vis : forall (W : world tfibsegs) a, 0xa1000 <= a < 0x5fd000 -> w_H W (Z_to_bv 64 a) = false.
Proof.
intros W a Ha. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
pose proof (w_Hoff W _ E) as F. rewrite unsigned_lit_small in F by lia.
destruct fs_rw3_seg as (Hin & Hb & Hs).
apply (find_segment_none_spec tfibsegs a 1 F _ Hin). rewrite Hb, Hs. lia.
Qed.
Lemma pstat_bounds : forall a, inFP FS_PSTAT_FP a -> 0xa1000 <= a < 0x5fd000.
Proof.
intros a (r & Hr & Ha). unfold FS_PSTAT_FP in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; lia.
Qed.
Definition pstatb (a : Z) : bool := existsb (fun r => (fst r <=? a) && (a <? snd r)) FS_PSTAT_FP.
Lemma pstatb_spec : forall a, pstatb a = true <-> inFP FS_PSTAT_FP a.
Proof.
intros a. unfold pstatb, inFP. rewrite existsb_exists. split; intros (r & Hr & H); exists r; split; try exact Hr.
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
- apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma pstat_dec : forall a, inFP FS_PSTAT_FP a \/ ~ inFP FS_PSTAT_FP a.
Proof.
intros a. destruct (pstatb a) eqn:E; [left; apply pstatb_spec; exact E|].
right. intros H. apply pstatb_spec in H. congruence.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* no user-poisoned shadow byte of U is a static byte: unpoison U is the identity on the statics *)
Lemma pstat_unpoison_id : forall B ly S U (W : world tfibsegs) mem md (m : word -> option byte) (x : word),
  ARU tfibsegs B ly S U W mem md -> inFP FS_PSTAT_FP (bv_unsigned x) -> unpoison U m x = m x.
Proof.
intros B ly S U W mem md m x HARU Hx. pose proof (AR_laws_ok tfibsegs B) as LAWS.
apply unpoison_out. destruct (in_ush U (bv_unsigned x)) eqn:E; [|reflexivity]. exfalso.
assert (UF : aowned B ly S (bv_unsigned x) /\ SHADOW_OFF <= bv_unsigned x < kHighMemBeg) by (eapply ush_facts; eassumption).
pose proof (pstat_bounds _ Hx). unfold SHADOW_OFF in UF. lia.
Qed.

(* a memory change confined to the statics, which keeps every present static byte present, keeps ARU (U unchanged) *)
Lemma pstat_write_ARU : forall B ly S U (W : world tfibsegs) mem mem' md,
  (forall a, inFP FS_PSTAT_FP a -> ~ Exists (in_zr a) (as_owned_static B)) ->
  ARU tfibsegs B ly S U W mem md ->
  (forall x : word, ~ inFP FS_PSTAT_FP (bv_unsigned x) -> mem' x = mem x) ->
  (forall x : word, inFP FS_PSTAT_FP (bv_unsigned x) -> mem x <> None -> mem' x <> None) ->
  ARU tfibsegs B ly S U W mem' md.
Proof.
intros B ly S U W mem mem' md PSF HARU Hout Hin.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HARU as (HAR & OK & PO).
assert (NUSH : forall s, in_ush U s = true -> ~ inFP FS_PSTAT_FP s).
{ intros s Hs Hp. assert (UF : aowned B ly S s /\ SHADOW_OFF <= s < kHighMemBeg) by (eapply ush_facts; eassumption).
  pose proof (pstat_bounds s Hp). unfold SHADOW_OFF in UF. lia. }
assert (EQ : forall x : word, ~ inFP FS_PSTAT_FP (bv_unsigned x) -> unpoison U mem' x = unpoison U mem x).
{ intros x Hx. unfold unpoison. destruct (in_ush U (bv_unsigned x)); [reflexivity | exact (Hout x Hx)]. }
assert (UIN : forall m x, inFP FS_PSTAT_FP (bv_unsigned x) -> unpoison U m x = m x).
{ intros m x Hx. apply unpoison_out. destruct (in_ush U (bv_unsigned x)) eqn:E; [|reflexivity].
  exfalso. exact (NUSH _ E Hx). }
assert (HV : forall x : word, inFP FS_PSTAT_FP (bv_unsigned x) -> w_H W x = false).
{ intros x Hx. pose proof (fs_rw3_vis W (bv_unsigned x) (pstat_bounds _ Hx)) as E.
  rewrite Z_to_bv_bv_unsigned in E. exact E. }
split; [|split; [exact OK|]].
- apply (al_frame _ _ LAWS ly S W (unpoison U mem) md (unpoison U mem') md HAR).
  + intros a Ha Hown. apply aview_at.
    destruct (pstat_dec (bv_unsigned (Z_to_bv 64 a))) as [Hp|Hp]; [exfalso | exact (EQ _ Hp)].
    rewrite unsigned_lit_small in Hp by lia.
    apply (PSF a Hp). apply (proj1 (al_owned_image _ _ LAWS ly S W (unpoison U mem) md a HAR (fs_rw3_img a (pstat_bounds a Hp)))).
    exact Hown.
  + intros a Hv. destruct (pstat_dec (bv_unsigned (Z_to_bv 64 a))) as [Hp|Hp].
    * unfold aview, mbyte, mrestrict in Hv |- *. rewrite (HV _ Hp), (UIN mem' _ Hp). rewrite (HV _ Hp), (UIN mem _ Hp) in Hv.
      destruct (mem' (Z_to_bv 64 a)) as [b|] eqn:E'; [discriminate|].
      destruct (mem (Z_to_bv 64 a)) as [b|] eqn:E; [exfalso; exact (Hin _ Hp ltac:(congruence) E') | exact Hv].
    * rewrite (aview_at tfibsegs (w_H W) (unpoison U mem') (unpoison U mem) a (EQ _ Hp)). exact Hv.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + intros a _ Hh. assert (Hh' : w_H W (Z_to_bv 64 a) = true) by exact Hh.
    destruct (pstat_dec (bv_unsigned (Z_to_bv 64 a))) as [Hp|Hp].
    * rewrite (HV _ Hp) in Hh'. discriminate.
    * exact (EQ _ Hp).
- intros s Hs. rewrite <- (PO s Hs). apply aview_at.
  assert (UF : aowned B ly S s /\ SHADOW_OFF <= s < kHighMemBeg) by (eapply ush_facts; eassumption).
  apply Hout. rewrite unsigned_lit_small by (unfold SHADOW_OFF, kHighMemBeg in UF; lia). exact (NUSH s Hs).
Qed.

(* the same with the non-ownership fact taken from the build's image facts (FSH_Rt.v fs_img_facts) *)
Lemma pstat_write_ARU_img : forall B ly S U (W : world tfibsegs) mem mem' md,
  fs_img_facts tfibsegs B ->
  ARU tfibsegs B ly S U W mem md ->
  (forall x : word, ~ inFP FS_PSTAT_FP (bv_unsigned x) -> mem' x = mem x) ->
  (forall x : word, inFP FS_PSTAT_FP (bv_unsigned x) -> mem x <> None -> mem' x <> None) ->
  ARU tfibsegs B ly S U W mem' md.
Proof.
intros B ly S U W mem mem' md IMG. apply pstat_write_ARU. exact (fs_pstat_not_owned tfibsegs B _ _ _ _ _ _ _ IMG).
Qed.

(* one 8-byte store at a static g: the form a walk's `sd` produces (bytes changed only in [g, g + 8), all present) *)
Lemma pstat_store_ARU : forall B ly S U (W : world tfibsegs) mem mem' md g,
  (forall a, inFP FS_PSTAT_FP a -> ~ Exists (in_zr a) (as_owned_static B)) ->
  ARU tfibsegs B ly S U W mem md ->
  In (g, g + 8) FS_PSTAT_FP ->
  (forall x : word, ~ (g <= bv_unsigned x < g + 8) -> mem' x = mem x) ->
  (forall x : word, g <= bv_unsigned x < g + 8 -> mem' x <> None) ->
  ARU tfibsegs B ly S U W mem' md.
Proof.
intros B ly S U W mem mem' md g PSF HARU Hg Hout Hin.
apply (pstat_write_ARU B ly S U W mem mem' md PSF HARU).
- intros x Hx. apply Hout. intros Hr. apply Hx. exists (g, g + 8). split; [exact Hg | cbn [fst snd]; exact Hr].
- intros x _ Hm. destruct (Z_lt_le_dec (bv_unsigned x) g) as [L|L].
  + rewrite (Hout x ltac:(lia)). exact Hm.
  + destruct (Z_lt_le_dec (bv_unsigned x) (g + 8)) as [L'|L'].
    * exact (Hin x ltac:(lia)).
    * rewrite (Hout x ltac:(lia)). exact Hm.
Qed.

End c.

Print Assumptions pstat_write_ARU.
Print Assumptions pstat_write_ARU_img.
Print Assumptions pstat_store_ARU.
