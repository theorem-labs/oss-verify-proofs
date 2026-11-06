(* rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from 82a1d1bf3a6 lib/A/FSH_crt_segD1_keep.v)
   Port source: a working branch 82a1d1bf3a6 proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segD1_keep.v (helper
   lemmas of check_round_trip's D1 segment lemma), itself PORTED from a working branch d25a984c903
   check_round_trip_sd16.v / sd17.v / sd18.v. Same Lemma names and statements as the A file, over image B (lib/B/YB1v.v
   tfibsegs, fs.asan-ubsan sha256 5ac5ce0954f8...), on the B interface (lib/B/FSH_crt_base.v's crt_pstat_img: B's
   statics FS_PSTAT_FP, lib/B/FSPstat.v, are image bytes of the RW segment [0xa1000, 0x5fd000)). A new file: no
   licence lines.
   A name -> A pc -> B pc: no name of this file carries a pc, register or image constant; the B content is the B
   FS_PSTAT_FP and the B image under every lemma.
   This file holds the separation facts the D1 segment lemma (segments 30-33) needs at its frees and its decode call:
   two different live blocks are apart, a block of the walk's own list is not one of the entry's blocks, and the
   footprints of one fuzz_free call and of one preset_base64_decode call meet no other live block, no live frame byte
   and no shadow byte. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP03 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
SetShadowDefU FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSW_K FSW_rres FSW_ret FSW_frame FSW_frame3 FSW_crt_tbl
FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSH_crt_base FSW_rd FSH_crt_site.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YE2k.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- list facts: a pairwise-apart list of ranges of positive size has no duplicate; a duplicate-free list has no
   element in both halves. List.NoDup, not stdpp's NoDup (which the imports put in scope), so Permutation_NoDup
   applies ---- *)
Lemma crtD1_nodup_of_pw : forall L : list (Z * Z),
  Forall (fun b => 1 <= req_size (snd b)) L ->
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) L) -> List.NoDup L.
Proof.
induction L as [|x t IH]; intros HF Hp; [constructor|].
pose proof (Forall_inv HF) as Hx. pose proof (Forall_inv_tail HF) as HF'. cbv beta in Hx.
cbn [map pairwise] in Hp. destruct Hp as [Hx' Hp'].
constructor; [|exact (IH HF' Hp')].
intros Hin. rewrite Forall_forall in Hx'.
pose proof (Hx' _ (in_map (fun b => (fst b, req_size (snd b))) t x Hin)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma crtD1_app_dup : forall (A0 l : list (Z * Z)) x, List.NoDup (A0 ++ l) -> In x A0 -> In x l -> False.
Proof.
induction A0 as [|y A0 IH]; intros l x HN H0 Hl; [destruct H0|].
cbn [app] in HN. apply List.NoDup_cons_iff in HN as [Hy HN'].
destruct H0 as [<-|H0].
- apply Hy. apply in_or_app. right. exact Hl.
- exact (IH l x HN' H0 Hl).
Qed.
(* the statics of FS_PSTAT_FP lie below the shadow band *)
Lemma crtD1_pstat_low : forall a, inFP FS_PSTAT_FP a -> 0 <= a < SHADOW_OFF.
Proof.
intros a (r & Hr & Hra). unfold FS_PSTAT_FP in Hr. unfold SHADOW_OFF.
cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Hra; lia|]). destruct Hr.
Qed.

Section d1keep. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* the shadow of a live frame lies in the shadow band [SHADOW_OFF, kHighMemBeg) *)
Lemma crtD1_frame_shadow_band : forall ly S (W : world tfibsegs) mem md cid pos a,
  AR tfibsegs B ly S W mem md -> In (cid, pos) (frames S) ->
  shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
  SHADOW_OFF <= a < kHighMemBeg.
Proof.
intros ly S W mem md cid pos a HAR Hin Ha.
destruct (frames_bounds tfibsegs B LAWS ly S W mem md cid pos HAR Hin) as (HF4096 & HFc & _).
pose proof (fs_frame_bytes_nonneg cid) as Hnn. pose proof asan_consts as (C1 & _).
unfold shadow_addr in Ha. unfold SHADOW_OFF, kHighMemBeg in *.
Z.div_mod_to_equations. lia.
Qed.

(* 1. two DIFFERENT live blocks are apart (al_sep's pairwise zdisjoint over the mapped ablocks) *)
Lemma crtD1_blk_apart : forall ly S (W : world tfibsegs) mem md p n q m,
  AR tfibsegs B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) -> (p, n) <> (q, m) ->
  p + req_size n <= q \/ q + req_size m <= p.
Proof.
intros ly S W mem md p n q m HAR Hp Hq Hne.
pose proof (sep_blocks tfibsegs B LAWS ly S W mem md p n q m HAR Hp Hq Hne) as D.
unfold zdisjoint in D. cbn [fst snd] in D. exact D.
Qed.

(* 2. a block of the walk's own list is not one of the entry's blocks: if it were, the permuted list would hold it
   twice, which al_sep forbids *)
Lemma crtD1_not_entry : forall ly S (W : world tfibsegs) mem md (A0 l : list (Z * Z)) b n,
  AR tfibsegs B ly S W mem md -> Permutation (ablocks B ly S) (A0 ++ l) -> In (b, n) l -> In (b, n) A0 -> False.
Proof.
intros ly S W mem md A0 l b n HAR HP Hl H0.
assert (Hpos : Forall (fun bk => 1 <= req_size (snd bk)) (ablocks B ly S)).
{ apply Forall_forall. intros [q m] Hin.
  destruct (al_blocks tfibsegs B LAWS ly S W mem md q m HAR Hin) as (_ & _ & _ & _ & _ & _ & Hm).
  exact (proj1 (req_size_pos m ltac:(lia))). }
destruct (al_sep tfibsegs B LAWS ly S W mem md HAR) as [Hpw _].
apply pairwise_app_l in Hpw as [Hpw _].
pose proof (crtD1_nodup_of_pw _ Hpos Hpw) as HN.
exact (crtD1_app_dup A0 l (b, n) (Permutation_NoDup HP HN) H0 Hl).
Qed.

(* 3. the footprint of one fuzz_free call (its statics and the freed block) meets no byte of ANOTHER live block, no
   byte of a live frame, and no byte of the shadow band *)
Lemma crtD1_free_fp_clear : forall ly S (W : world tfibsegs) mem md p n,
  AR tfibsegs B ly S W mem md -> In (p - HEAD, n + HEAD) (ablocks B ly S) ->
  (forall q m a, In (q, m) (ablocks B ly S) -> (q, m) <> (p - HEAD, n + HEAD) -> q <= a < q + req_size m ->
     ~ inFP (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, n + HEAD)]) a) /\
  (forall cid pos a, In (cid, pos) (frames S) ->
     (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid \/
      shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8) ->
     ~ inFP (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, n + HEAD)]) a) /\
  (forall a, inFP (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, n + HEAD)]) a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)).
Proof.
intros ly S W mem md p n HAR Hx.
pose proof asan_consts as (C1 & _).
destruct (al_blocks tfibsegs B LAWS ly S W mem md _ _ HAR Hx) as (_ & _ & _ & Happx & _).
assert (Hfx : forall a, inFP (ablocks_fp [(p - HEAD, n + HEAD)]) a -> p - HEAD <= a < p - HEAD + req_size (n + HEAD)).
{ intros a Ha. apply inFP_ablocks_fp_inv in Ha as (p' & n' & Hin & Hr).
  destruct Hin as [E|[]]. injection E as <- <-. exact Hr. }
split; [|split].
- intros q m a Hq Hne Ha HF. apply inFP_app in HF as [HF|HF].
  + exact (blk_img tfibsegs B LAWS ly S W mem md q m a HAR Hq Ha (crt_pstat_img a HF)).
  + pose proof (Hfx a HF) as Hr.
    pose proof (sep_blocks tfibsegs B LAWS ly S W mem md q m _ _ HAR Hq Hx Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. lia.
- intros cid pos a Hin Ha HF. apply inFP_app in HF as [HF|HF].
  + destruct Ha as [Ha|Ha].
    * exact (frm_img tfibsegs B LAWS ly S W mem md cid pos a HAR Hin Ha (crt_pstat_img a HF)).
    * pose proof (crtD1_pstat_low a HF) as Hl.
      pose proof (crtD1_frame_shadow_band ly S W mem md cid pos a HAR Hin Ha) as Hs. lia.
  + pose proof (Hfx a HF) as Hr. destruct Ha as [Ha|Ha].
    * pose proof (sep_block_frame tfibsegs B LAWS ly S W mem md _ _ cid pos HAR Hx Hin) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. lia.
    * pose proof (in_app_addr _ _ a Happx Hr) as Hap.
      pose proof (crtD1_frame_shadow_band ly S W mem md cid pos a HAR Hin Ha) as Hs.
      unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia.
- intros a HF. apply inFP_app in HF as [HF|HF].
  + pose proof (crtD1_pstat_low a HF) as Hl. lia.
  + pose proof (in_app_addr _ _ a Happx (Hfx a HF)) as Hap.
    unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia.
Qed.

(* 4. the same for one preset_base64_decode call, whose footprint is the statics plus the 8-byte length cell at `lenp`
   inside the caller's class-3 fake frame: it meets no live block, no OTHER frame byte, no shadow byte *)
Lemma crtD1_dec_fp_clear : forall ly S (W : world tfibsegs) mem md pos lenp,
  AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) ->
  frame_addr ly 3 pos <= lenp -> lenp + 8 <= frame_addr ly 3 pos + fs_frame_bytes 3 ->
  (forall q m a, In (q, m) (ablocks B ly S) -> q <= a < q + req_size m ->
     ~ inFP (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) a) /\
  (forall a, frame_addr ly 3 pos <= a < frame_addr ly 3 pos + fs_frame_bytes 3 -> ~ (lenp <= a < lenp + 8) ->
     ~ inFP (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) a) /\
  (forall a, shadow_addr (frame_addr ly 3 pos) <= a < shadow_addr (frame_addr ly 3 pos) + fs_frame_bytes 3 / 8 ->
     ~ inFP (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) a) /\
  (forall a, inFP (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)).
Proof.
intros ly S W mem md pos lenp HAR Hin Hl1 Hl2.
pose proof asan_consts as (C1 & _).
destruct (frames_bounds tfibsegs B LAWS ly S W mem md 3 pos HAR Hin) as (HF4096 & HFc & HFapp).
assert (Hc : forall a, inFP [(lenp, lenp + 8)] a -> lenp <= a < lenp + 8).
{ intros a Ha. apply inFP_cons in Ha as [Ha|Ha]; [exact Ha | destruct (inFP_nil a Ha)]. }
split; [|split; [|split]].
- intros q m a Hq Ha HF. apply inFP_app in HF as [HF|HF].
  + exact (blk_img tfibsegs B LAWS ly S W mem md q m a HAR Hq Ha (crt_pstat_img a HF)).
  + pose proof (Hc a HF) as Hr.
    pose proof (sep_block_frame tfibsegs B LAWS ly S W mem md q m 3 pos HAR Hq Hin) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. lia.
- intros a Ha Hna HF. apply inFP_app in HF as [HF|HF].
  + exact (frm_img tfibsegs B LAWS ly S W mem md 3 pos a HAR Hin Ha (crt_pstat_img a HF)).
  + exact (Hna (Hc a HF)).
- intros a Ha HF. pose proof (crtD1_frame_shadow_band ly S W mem md 3 pos a HAR Hin Ha) as Hs.
  apply inFP_app in HF as [HF|HF].
  + pose proof (crtD1_pstat_low a HF) as Hl. lia.
  + pose proof (Hc a HF) as Hr.
    pose proof (in_app_addr _ _ a HFapp ltac:(lia)) as Hap.
    unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia.
- intros a HF. apply inFP_app in HF as [HF|HF].
  + pose proof (crtD1_pstat_low a HF) as Hl. lia.
  + pose proof (Hc a HF) as Hr.
    pose proof (in_app_addr _ _ a HFapp ltac:(lia)) as Hap.
    unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia.
Qed.
End d1keep.

Print Assumptions crtD1_blk_apart.
Print Assumptions crtD1_not_entry.
Print Assumptions crtD1_free_fp_clear.
Print Assumptions crtD1_dec_fp_clear.
