(* fs WRITER walks, image B (fs.asan-ubsan), the bookkeeping half: the facts about U (the live user-poisoned heads)
   that every writer walk needs, proved once over S0's names and lib/B/FSH_Fn_writer's `uswap`. The lib/B twin of
   lib/A/FSW_writer_kit.v (a working branch 1a264574ee7), same lemma names; no address numeral. Used by
   lib/B/FSW_indent.v (fs_heads_put, through fs_heads_uswap and uswap_new_head). `uswap` is lib/B/FSH_Fn_writer.v's
   (a working branch adfa7850046, over a working branch bddf781b317).
   rule 24: proves no function (kind: segment lemma). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI04 YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_Base FSH_Fn_writer.
Import ListNotations.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.

Definition zz_eq_dec (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* U' keeps fs's shape (every range is the 16-byte head of a live block) across a writer call, whatever the
   buffer did. The two premises are exactly what a walk reads off its own post: a head that is still in U' is
   still a live block, and a head that is NEW is the new buffer's. No disjointness argument is needed, because
   `uswap` adds at most the one new head. *)
Lemma fs_heads_uswap :
  forall ly S ly' S' U U' buf buf' cap,
  fs_heads B ly S U ->
  uswap U U' buf buf' cap ->
  (forall r, In r U' -> In r U -> exists m, In (fst r, m) (ablocks B ly' S') /\ 16 <= req_size m) ->
  (forall r, In r U' -> ~ In r U ->
     r = (buf' - HEAD, HEAD) /\ exists m, In (buf' - HEAD, m) (ablocks B ly' S') /\ 16 <= req_size m) ->
  fs_heads B ly' S' U'.
Proof.
  intros ly S ly' S' U U' buf buf' cap HU _ Hkept Hnew r Hr.
  destruct (in_dec zz_eq_dec r U) as [Hin | Hout].
  - split; [exact (proj1 (HU r Hin)) | exact (Hkept r Hr Hin)].
  - destruct (Hnew r Hr Hout) as (-> & m & Hm & H16). split; [reflexivity | exists m; split; assumption].
Qed.

(* the only new head `uswap` can introduce is the new buffer's, which is what the second premise above asks a
   walk to show *)
Lemma uswap_new_head :
  forall U U' buf buf' cap r, uswap U U' buf buf' cap -> In r U' -> ~ In r U -> r = (buf' - HEAD, HEAD).
Proof.
  intros U U' buf buf' cap r HS Hr Hout.
  destruct HS as [[-> _] | [(U1 & U2 & -> & ->) | (_ & ->)]].
  - destruct (Hout Hr).
  - apply in_app_or in Hr. destruct Hr as [H1 | H2].
    + destruct (Hout (in_or_app _ _ _ (or_introl H1))).
    + apply in_app_or in H2. destruct H2 as [H2 | [<- | []]].
      * destruct (Hout (in_or_app _ _ _ (or_intror (in_cons _ _ _ H2)))).
      * reflexivity.
  - apply in_app_or in Hr. destruct Hr as [H1 | [<- | []]].
    + destruct (Hout H1).
    + reflexivity.
Qed.

(* a head that survives the call was already one before it *)
Lemma uswap_kept_head :
  forall U U' buf buf' cap r, uswap U U' buf buf' cap -> In r U' -> In r U \/ r = (buf' - HEAD, HEAD).
Proof.
  intros U U' buf buf' cap r HS Hr.
  destruct (in_dec zz_eq_dec r U) as [Hin | Hout];
    [left; exact Hin | right; exact (uswap_new_head U U' buf buf' cap r HS Hr Hout)].
Qed.

End c.
