(* reac-pw/fuzz_link, image A: what a walk needs at the call of one of link's own `aleaf_rd` contracts made from
   inside its own side frame, i.e. on the caller's journal with own' = (c, pos) :: own and a callee window
   [slo', shi') inside the caller's window (link_amem.v apre / aleaf_rd).

   - akb_sub: a byte the caller's read set may hold (`akb` at the caller's call state and window) is one the
     callee's read set may hold (`akb` at the callee's call state, whose blocks and frames include the caller's,
     with the same frame addresses, and whose window lies inside the caller's).
   - ajw_akb: a byte the caller may write (`ajw`, apre) that lies outside the callee window, below the journal's
     sp0, in application memory (not shadow memory) and not in errno is a byte the callee may read (`akb`): the
     names reac_served_unmark_all passes to its alias callees lie in its marks block, which is in its write set.
   - ajw_mono: `ajw` survives a step that keeps the blocks, the frame addresses and the owned frames (own grows).
   - ajw_frame: a byte of a frame of own is `ajw` (the callee's buffer in the caller's fresh side frame).
   - aj_frame_addr: the frame addresses of the journal's current layout are those of its start layout.
   The side-stack room of a callee after the caller took a frame is LinkWalkSide.v's aside_room_push.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

(* The frame addresses of a journal's current layout are those of its start layout. *)
Lemma aj_frame_addr : forall G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  forall c q, frame_addr lyc c q = frame_addr ly c q.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k (_ & _ & (memS & HJ & _) & _) c q.
  pose proof HJ as (_ & Hly & _). unfold frame_addr.
  destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.

(* The frames the journal's owner took are frames of the current state. *)
Lemma aj_own_frames : forall G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  forall c q, In (c, q) own -> In (c, q) (frames Sc).
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k (_ & _ & (memS & HJ & _) & _) c q Hin.
  pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. apply in_or_app. left. exact Hin.
Qed.

(* The journal's window lies above the allocator's ceiling and below 2 ^ 47. *)
Lemma aj_window_bounds : forall G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  alloc_ceiling <= sp0 - STK /\ sp0 + XO <= 2 ^ 47 /\ 0 <= STK /\ 0 <= XO.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k (H0 & H1 & (memS & HJ & _) & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _). lia.
Qed.

(* Two layouts of journals with the same start layout have the same stack row. *)
Lemma aj_stk_row_eq : forall G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  ly_stk_lo lyc = ly_stk_lo ly /\ ly_stk_hi lyc = ly_stk_hi ly.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k (_ & _ & (memS & HJ & _) & _).
  destruct HJ as (_ & Hly & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  split; [exact Elo | exact Ehi].
Qed.

Lemma akb_sub : forall lyc Sc lyc' Sc' slo shi slo' shi' a,
  akb segs B lyc Sc slo shi a ->
  slo <= slo' -> shi' <= shi ->
  ly_stk_lo lyc' = ly_stk_lo lyc -> ly_stk_hi lyc' = ly_stk_hi lyc ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B lyc' Sc')) ->
  (forall c q, In (c, q) (frames Sc) -> In (c, q) (frames Sc')) ->
  (forall c q, frame_addr lyc' c q = frame_addr lyc c q) ->
  akb segs B lyc' Sc' slo' shi' a.
Proof.
  intros lyc Sc lyc' Sc' slo shi slo' shi' a Hb Hlo Hhi Erl Erh Hbl Hfr Hfa.
  destruct Hb as [(H1 & H2) | [(b & m & Hin & Hr) | [H3 | (c & q & Hin & Hr)]]].
  - left. rewrite Erl, Erh. split; [exact H1 | lia].
  - right; left. exists b, m. split; [exact (Hbl b m Hin) | exact Hr].
  - right; right; left. exact H3.
  - right; right; right. exists c, q. split; [exact (Hfr c q Hin)|].
    unfold frame_rng in *. cbn [fst snd] in *. rewrite Hfa. exact Hr.
Qed.

Lemma ajw_akb : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc' Sc' slo' shi' a,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajw B G XO OUT STK sp0 FP ly S lyc Sc own a ->
  ~ (slo' <= a < shi') ->
  (a < kLowMemEnd \/ kHighMemBeg <= a) ->
  ~ (as_errno B <= a < as_errno B + 4) ->
  ly_stk_lo lyc' = ly_stk_lo lyc -> ly_stk_hi lyc' = ly_stk_hi lyc ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B lyc' Sc')) ->
  (forall c q, In (c, q) (frames Sc) -> In (c, q) (frames Sc')) ->
  (forall c q, frame_addr lyc' c q = frame_addr lyc c q) ->
  akb segs B lyc' Sc' slo' shi' a.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc' Sc' slo' shi' a
    HG HJ Hw Hwin Happ Herr Erl Erh Hbl Hfr Hfa.
  pose proof (aj_window_bounds G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ)
    as (Hceil & H47 & HSTK & HXO).
  assert (HR := HJ). apply ajournal_gx_row in HR. destruct HR as (R1 & R2 & R3 & R4).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct Hw as [(Haw & Hno) | [HGa | (_ & Hout)]].
  - destruct Haw as [Hs | [(_ & b & n & Hin & Hr) | [(b & n & Hin & _ & Hr) | (c & q & Hin & Hr)]]].
    + left. rewrite Erl, Erh. split; [lia | exact Hwin].
    + right; left. exists b, n. split; [exact (Hbl b n Hin) | exact Hr].
    + right; left. exists b, n. split; [exact (Hbl b n Hin) | exact Hr].
    + pose proof (aj_own_frames G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ c q Hin) as Hcq.
      destruct Hr as [Hr | Hr].
      * right; right; right. exists c, q. split; [exact (Hfr c q Hcq)|].
        unfold frame_rng. cbn [fst snd]. rewrite Hfa. exact Hr.
      * exfalso. destruct HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
        destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c q HAR Hcq) as (Hf4096 & Hfceil & _).
        pose proof (fs_frame_bytes_nonneg c) as Hnn.
        unfold in_zr, shadow_addr in Hr. cbn [fst snd] in Hr.
        unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg in *. lia.
  - right; right; left. destruct (HG a HGa) as (Hi & Hno). split; [exact Hi|]. split; [exact Hno | exact Herr].
  - left. rewrite Erl, Erh. split; [lia | exact Hwin].
Qed.

Lemma ajw_mono : forall G XO OUT STK sp0 FP ly S lyc Sc own lyc' Sc' own' a,
  ajw B G XO OUT STK sp0 FP ly S lyc Sc own a ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B lyc' Sc')) ->
  (forall x, In x own -> In x own') ->
  (forall c q, frame_addr lyc' c q = frame_addr lyc c q) ->
  ajw B G XO OUT STK sp0 FP ly S lyc' Sc' own' a.
Proof.
  intros G XO OUT STK sp0 FP ly S lyc Sc own lyc' Sc' own' a Hw Hbl Hown Hfa.
  destruct Hw as [(Haw & Hno) | [HGa | Hout]]; [left | right; left; exact HGa | right; right; exact Hout].
  split; [|exact Hno].
  destruct Haw as [Hs | [(Hf & b & n & Hin & Hr) | [(b & n & Hin & Hn0 & Hr) | (c & q & Hin & Hr)]]].
  - left. exact Hs.
  - right; left. split; [exact Hf|]. exists b, n. split; [exact (Hbl b n Hin) | exact Hr].
  - right; right; left. exists b, n. split; [exact (Hbl b n Hin)|]. split; [exact Hn0 | exact Hr].
  - right; right; right. exists c, q. split; [exact (Hown _ Hin)|]. rewrite !Hfa. exact Hr.
Qed.

Lemma ajw_frame : forall G XO OUT STK sp0 FP ly S lyc Sc own cid pos a,
  In (cid, pos) own ->
  frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid ->
  ~ (sp0 <= a < sp0 + XO) ->
  ajw B G XO OUT STK sp0 FP ly S lyc Sc own a.
Proof.
  intros G XO OUT STK sp0 FP ly S lyc Sc own cid pos a Hin Ha Hno.
  left. split; [|exact Hno]. right; right; right. exists cid, pos. split; [exact Hin|].
  left. unfold in_zr. cbn [fst snd]. exact Ha.
Qed.

End a.
