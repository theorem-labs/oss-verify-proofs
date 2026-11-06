From Stdlib Require Import Arith Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YM05 YO0d YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require literal_c memset_c memcpy_c strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require parse_value parse_value_c parse_items_c parse_string_c grow_c fuzz_free_c fuzz_malloc_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF.

Section Unit.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : Contract.ResForm.

Definition pv_c (fx : FPState) (d : nat) : Prop := @parse_value_c.parse_value_contract fx rc B API F d.
Definition pi_c (fx : FPState) (d : nat) : Prop := @parse_items_c.parse_items_contract fx rc B API F d.

Theorem parse_unit :
  (forall d, ((d < MAXD)%nat -> forall fx, pv_c fx (S d)) ->
     (forall fx, @grow_c.grow_contract fx rc B API F) ->
     (forall fx, @parse_string_c.parse_string_contract fx rc B API F) ->
     memset_c.memset_contract ->
     (forall fx, @fuzz_free_c.fuzz_free_contract fx rc B API F) ->
     forall fx, pi_c fx d) ->
  AllocExtra B (aa_MR API) -> Contract.ctx_owned B API -> Contract.errno_unowned B API ->
  (forall fx, @grow_c.grow_contract fx rc B API F) ->
  (forall fx, @parse_string_c.parse_string_contract fx rc B API F) ->
  memset_c.memset_contract ->
  (forall fx, @fuzz_free_c.fuzz_free_contract fx rc B API F) ->
  literal_c.literal_contract ->
  (forall fx, @fuzz_malloc_c.fuzz_malloc_contract fx rc B API F) ->
  memcpy_c.memcpy_contract ->
  strtod_c.strtod_contract ->
  forall d, (d <= MAXD)%nat -> forall fx, pv_c fx d /\ pi_c fx d.
Proof.
  intros ITEMS AX CO ERR GROW PSTR MEMSET FREE LIT MALLOC MEMCPY STRTOD.
  assert (VALUE : forall fx d, pi_c fx d -> pv_c fx d).
  { intros fx d PI. exact (parse_value.parse_value_step B API F d AX CO ERR PI (PSTR fx) LIT (MALLOC fx) MEMCPY STRTOD). }
  assert (H : forall k, (k <= MAXD)%nat -> forall fx, pv_c fx (MAXD - k) /\ pi_c fx (MAXD - k)).
  { induction k as [|k IH]; intros Hk fx.
    - assert (PI : forall fx', pi_c fx' (MAXD - 0)).
      { apply ITEMS; [intros Hlt; exfalso; lia | exact GROW | exact PSTR | exact MEMSET | exact FREE]. }
      split; [exact (VALUE fx _ (PI fx)) | exact (PI fx)].
    - assert (PV : forall fx', pv_c fx' (S (MAXD - S k))).
      { intros fx'. replace (S (MAXD - S k)) with (MAXD - k)%nat by (unfold MAXD in *; lia).
        exact (proj1 (IH ltac:(lia) fx')). }
      assert (PI : forall fx', pi_c fx' (MAXD - S k)).
      { apply ITEMS; [intros _; exact PV | exact GROW | exact PSTR | exact MEMSET | exact FREE]. }
      split; [exact (VALUE fx _ (PI fx)) | exact (PI fx)]. }
  intros d Hd fx. replace d with (MAXD - (MAXD - d))%nat by lia. apply H. lia.
Qed.

End Unit.
