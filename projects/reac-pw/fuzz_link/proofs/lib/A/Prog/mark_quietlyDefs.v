(* reac-pw/fuzz_link, image A: the definitions the walk of mark_quietly (0x883d4, listing
   (internal path) (internal record, sha256 83bb83545bf3)) shares between its pieces.

   `mqa_X`: the bytes the later arm may change between its entry and its tail jump: its own window, the FILE
   block's first AMF_ZEROED bytes and g_said (the rewind), and errno (mwrite's ENOSPC arm).
   `mem_grows_of_apresent`: presence growth (the runtime contracts' form) as the run lemmas state it.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem model_decide_c remember_c reac_code_emit_c reac_served_mark_c mark_quietly_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the bytes the later arm may change between its entry (sp) and its tail jump, FILE block f *)
Definition mqa_X (B : asyms) (sp f : Z) (a : Z) : Prop :=
  (sp - MARK_QUIETLY_AK <= a < sp) \/ (f <= a < f + AMF_ZEROED) \/
  (LA_G_SAID <= a < LA_G_SAID + SAID_SIZE) \/ (as_errno B <= a < as_errno B + 4).

(* presence growth as the run lemmas state it *)
Lemma mem_grows_of_apresent : forall (H : word -> bool) (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
  intros H m m' Hp x Hx. unfold mrestrict in Hx |- *. destruct (H x) eqn:Eh; [exact Hx|].
  destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
  assert (Ha : apresent H m (bv_unsigned x)) by (unfold apresent; rewrite Z_to_bv_bv_unsigned; split; [exact Eh | exists b; exact Em]).
  destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

(* THE OPENING ARM. `mqo_E`: the globals it writes before its tail jump (g_sink at +0x40, g_said in the rewind,
   g_say in reac_served_say_to, the open-file list head in fmemopen) and errno (rewind's mwrite). *)
Definition mqo_E (B : asyms) (a : Z) : Prop :=
  (LA_G_SINK <= a < LA_G_SINK + 8) \/ (LA_G_SAID <= a < LA_G_SAID + SAID_SIZE) \/
  (LA_G_SAY <= a < LA_G_SAY + 8) \/ (LA_OFL_HEAD <= a < LA_OFL_HEAD + 8) \/ (as_errno B <= a < as_errno B + 4).

Section o. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* `mqo_rel`: what the opening arm's walk knows of a later state x (layout lyx, allocator state Sx, world Wx, memory
   memx) relative to its entry (sp, lyc, Sc, W, memc): AR at x, the world grows, the layout's fixed fields are the
   entry's, the frames are the entry's, every block of the entry is a block of x, and the entry's kept clause with
   the window [sp - K, sp) and the write set mqo_E. *)
Definition mqo_rel (segs : list Segment) (B : asyms) (sp : Z) (lyc : alayout) (Sc : astate) (W : world segs)
    (memc : word -> option byte) (lyx : alayout) (Sx : astate) (Wx : world segs) (memx : word -> option byte)
    (mdx : Model) : Prop :=
  AR segs B lyx Sx Wx memx mdx /\ wle W Wx /\ layout_le 0 lyc lyx /\ frames Sx = frames Sc /\
  (forall b n, In (b, n) (ablocks B lyc Sc) -> In (b, n) (ablocks B lyx Sx)) /\
  akept segs B lyc Sc W memc Wx memx (sp - MARK_QUIETLY_AK) sp (mqo_E B).
End o.
