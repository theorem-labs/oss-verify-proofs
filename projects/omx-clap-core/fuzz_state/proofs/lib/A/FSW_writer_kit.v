(* fs WRITER walks, the bookkeeping half: the facts about U (the live user-poisoned heads) and about the
   level-indexed stack bound that every writer walk needs, proved once over S0's names and lib/A/FSH_Fn_writer's
   `uswap`. No run step and no image stepping here: those wait on FSW_K (a Theorem Labs lane's U-form run step and
   ajournal_init at a raised window top).
   Rule 24 (proof-index v5 built 2026-10-28T21:58:24Z, exit 0, read from a file, not a pipe): put, indent,
   put_string, write_value, pj_write, preset_base64_encode and preset_base64_decode have RELEASED proofs for fs's
   PLAIN and UBSAN builds only (lib/Prog, lib/U/Prog, ossv/recipes@566eb6ffa5, release/pau-projects-recipes@b6a0088adc),
   none for an ASan build. Those plain contracts / proofs are the templates used here, not drop-ins.
   Lemma names (git grep -w, the four released refs, under proofs/): fs_heads_uswap, uswap_new_head, uswap_kept_head: none. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI04 YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Fn_writer.
Import ListNotations.
Local Open Scope Z_scope.

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

(* the level-indexed stack bound's monotonicity (STK_write_value m <= STK_write_value (S m)) is not stated
   here yet: write_value's walk takes the bound of its own level from FSH_Base directly, and the step that
   needs the comparison is the level k -> k+1 lemma, which lands with that walk. *)

End c.
