From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YO0i YO0f YO0g YO0s YO03.
Import ListNotations.
Local Open Scope Z_scope.

Definition GSX (X : list sptr) (s : astate) : Prop :=
  forall g am, usedX X s g am -> 0 < am_maplen am ->
  (am_sc am < 48 -> am_maplen am * PGSZ <= MMAX) /\
  (am_sc am = 63 -> forall fr, ss_fr (nth_slot am 0) = Some fr -> am_maplen am * PGSZ <= fr_n fr + 3 * PGSZ).

Definition GS (s : astate) : Prop := GSX [] s.

Definition ubytes (s : astate) : Z := fold_right (fun b acc => snd b + acc) 0 (user_blocks s).

Definition noraw (s : astate) : Prop := forall q, MT s q <> Some MRaw.

Lemma GS_init : GS init_state.
Proof. intros g am H. unfold usedX, MTX, MT in H. cbn in H. discriminate. Qed.

Lemma noraw_init : noraw init_state.
Proof. intros q H. unfold MT in H. cbn in H. discriminate. Qed.

Definition NLX (X : list sptr) (s : astate) : Prop :=
  forall g am, usedX X s g am -> am_maplen am = 0 -> 1 <= am_last am.

Definition NL (s : astate) : Prop := NLX [] s.

Lemma NL_init : NL init_state.
Proof. intros g am H. unfold usedX, MTX, MT in H. cbn in H. discriminate. Qed.
