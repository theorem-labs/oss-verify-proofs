From Stdlib Require Import Arith Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YO0d YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
  fuzz_malloc_c fuzz_free_c fuzz_realloc_c fuzz_strdup_c memset_c memcpy_c strcmp_c put_utf8_c
  pj_parse_c pj_free_c pj_string_c pj_set_c pj_get_c pj_get_str_c grow_c parse_string_c
  parse_value_c parse_items_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require
  literal_c strtod_c hex4_c pj_parse pj_free pj_string pj_set pj_get pj_get_str grow parse_string ParseUnit
  parse_items.

Section Link.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.

Theorem reader_link :
  AllocExtra B (aa_MR API) -> ctx_owned B API -> errno_unowned B API ->
  (forall fx, @fuzz_malloc_contract fx rc B API RF) ->
  (forall fx, @fuzz_free_contract fx rc B API RF) ->
  (forall fx, @fuzz_realloc_contract fx rc B API RF) ->
  (forall fx, @fuzz_strdup_contract fx rc B API RF) ->
  memset_contract -> memcpy_contract -> strtod_c.strtod_contract -> strcmp_contract ->
  literal_c.literal_contract -> put_utf8_contract -> hex4_c.hex4_contract ->
  forall fx,
    @pj_parse_contract fx rc B API RF /\ @pj_free_contract fx rc B API RF /\
    @pj_string_contract fx rc B API RF /\ @pj_set_contract fx rc B API RF /\
    pj_get_contract /\ pj_get_str_contract /\
    @grow_contract fx rc B API RF /\ @parse_string_contract fx rc B API RF /\
    (forall d, (d <= MAXD)%nat ->
       @parse_value_contract fx rc B API RF d /\ @parse_items_contract fx rc B API RF d).
Proof.
  intros AX CO ERR FM FF FR FS MS MC SC SCMP LIT PU HX.
  pose proof (@parse_items.parse_items_step rc B API RF AX CO) as PI.
  assert (GROW : forall fx, @grow_contract fx rc B API RF).
  { intros fx. apply grow.grow_holds; [exact AX | exact (FR fx)]. }
  assert (PSTR : forall fx, @parse_string_contract fx rc B API RF).
  { intros fx. apply parse_string.parse_string_holds; [exact AX | exact CO | exact (FM fx) | exact (FF fx) | exact PU | exact HX]. }
  assert (PFREE : forall fx, @pj_free_contract fx rc B API RF).
  { intros fx. apply pj_free.pj_free_holds; [exact (FF fx) | exact MS | exact AX]. }
  assert (GET : pj_get_contract) by exact (pj_get.pj_get_holds SCMP).
  assert (UNIT : forall d, (d <= MAXD)%nat -> forall fx,
    @parse_value_contract fx rc B API RF d /\ @parse_items_contract fx rc B API RF d).
  { exact (ParseUnit.parse_unit B API RF PI AX CO ERR GROW PSTR MS FF LIT FM MC SC). }
  intros fx.
  split.
  { apply pj_parse.pj_parse_holds; [exact MS | exact (proj1 (UNIT 0%nat ltac:(unfold MAXD; lia) fx)) | exact PFREE]. }
  split; [exact (PFREE fx)|].
  split.
  { apply pj_string.pj_string_holds; [exact AX | exact MS | exact (FS fx)]. }
  split.
  { apply pj_set.pj_set_holds; [exact AX | exact GET | exact MC | exact MS | exact (PFREE fx) | exact (GROW fx) | exact (FS fx)]. }
  split; [exact GET|].
  split; [exact (pj_get_str.pj_get_str_holds GET)|].
  split; [exact (GROW fx)|].
  split; [exact (PSTR fx)|].
  intros d Hd. exact (UNIT d Hd fx).
Qed.

End Link.
