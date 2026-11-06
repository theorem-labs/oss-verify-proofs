(* fs WRITER walks, the model half: what fs's writer model does on the harness document, proved over fs's
   released pure models only (lib/Prog/WriterSpec.v, WriterValue.v). No image, no ASan kit, no Section
   variable: these lemmas hold for both builds and are what the put_string / write_value / pj_write walks use
   to discharge the escape machinery, and what READER (a Theorem Labs lane) reads the character set off.

   The premise is the byte-level side of FS_DOC_STRS (owner a Theorem Labs lane): a document string has no byte below
   0x20, no 0x22 and no 0x5c (a Theorem Labs lane 20:36Z, a Theorem Labs lane confirmed). Under it `esc` never runs, so
   put_string writes the string between two quotes and its snprintf arm is unreachable.
   Rule 24 (proof-index v5 built 2026-10-28T21:58:24Z, exit 0, read from a file, not a pipe): put, indent,
   put_string, write_value, pj_write, preset_base64_encode and preset_base64_decode have RELEASED proofs for fs's
   PLAIN and UBSAN builds only (lib/Prog, lib/U/Prog, ossv/recipes@566eb6ffa5, release/pau-projects-recipes@b6a0088adc),
   none for an ASan build. Those plain contracts / proofs are the templates used here, not drop-ins.
   Lemma names, git grep -w over origin/main, ossv/recipes, ossv/candidates, release/pau-projects-recipes (under proofs/):
   dbl_pow / newcap_pow / newcap_pos exist released (reused below); the others have no hit. *)

From Stdlib Require Import ZArith List Lia Bool.
(* lib/Prog modules are Required, never Imported (a Theorem Labs lane 21:43Z: they load lib.Lib's getr / mkst / seg_rom) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec put_blocks WriterRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSH_Gen.
Import ListNotations.
Local Open Scope Z_scope.

(* plain_byte / plain_bytes / jv_plain are S0's (lib/A/FSH_Gen.v:144-), one text for every lane *)

Lemma plain_not_special : forall c, plain_byte c -> WriterSpec.special c = false.
Proof.
  intros c (H32 & H34 & H92). unfold WriterSpec.special.
  apply orb_false_intro; [apply orb_false_intro|].
  - apply Z.eqb_neq. exact H34.
  - apply Z.eqb_neq. exact H92.
  - apply Z.ltb_ge. exact H32.
Qed.

Lemma spieces_run_plain : forall bs run, plain_bytes bs -> WriterSpec.spieces_run run bs = [run ++ bs].
Proof.
  induction bs as [|c r IH]; intros run H; simpl.
  - rewrite app_nil_r. reflexivity.
  - inversion H as [|? ? Hc Hr]; subst.
    rewrite (plain_not_special c Hc). rewrite (IH (run ++ [c]) Hr).
    rewrite <- app_assoc. reflexivity.
Qed.

(* the one shape the put_string walk needs: an opening quote, the bytes themselves, a closing quote *)
Lemma spieces_plain : forall bs, plain_bytes bs -> WriterSpec.spieces bs = [[34]; bs; [34]].
Proof.
  intros bs H. unfold WriterSpec.spieces. rewrite (spieces_run_plain bs [] H). reflexivity.
Qed.

Lemma wstr_plain : forall bs, plain_bytes bs -> WriterSpec.wstr bs = 34 :: bs ++ [34].
Proof.
  intros bs H. unfold WriterSpec.wstr. rewrite (spieces_plain bs H). simpl. reflexivity.
Qed.

Lemma wstr_plain_length :
  forall bs, plain_bytes bs -> length (WriterSpec.wstr bs) = S (S (length bs)).
Proof.
  intros bs H. rewrite (wstr_plain bs H). simpl. rewrite length_app. simpl. lia.
Qed.

(* every byte the writer puts for a plain string is either a quote or a byte of the string: the fact READER's
   character-set lemma rests on (no 0x5c anywhere, so no escape can be read back) *)
Lemma wstr_plain_mem : forall bs c, plain_bytes bs -> In c (WriterSpec.wstr bs) -> c = 34 \/ In c bs.
Proof.
  intros bs c H Hin. rewrite (wstr_plain bs H) in Hin. destruct Hin as [<-|Hin]; [left; reflexivity|].
  apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]]; [right; exact Hin|left; reflexivity].
Qed.

(* ---- the buffer's size class after a grow: RELEASED lemmas, reused, not copied: fs's plain proof of put
   (lib/Prog/put_blocks.v:249-281, dbl_pow / newcap_pow, ossv/recipes@566eb6ffa5) states them over WriterSpec's
   newcap, and fs's WriterRet.v:163 states newcap_pos. ---- *)

(* ---- every allocation size the writer passes is at least 1 (owner-ruled, a Theorem Labs lane 21:53Z: ALLOC's
   fuzz_malloc_spec / fuzz_realloc_spec take `1 <= n`, and each caller discharges it from its own size
   arithmetic). The sizes are fs's own: put's newcap (>= 4096; positivity alone is the released WriterRet.newcap_pos), encode's (len + 2) / 3 * 4 + 1, decode's
   length / 4 * 3 + 3 (lib/Prog/preset_base64_{en,de}code_c.v:16-17). ---- *)
Lemma newcap_ge_4096 : forall c need, (c = 0 \/ exists j, 0 <= j <= 51 /\ c = 4096 * 2^j) -> need <= 2^63 ->
  4096 <= WriterSpec.newcap c need.
Proof.
  intros c need Hc Hn. destruct (put_blocks.newcap_pow c need Hc Hn) as (j & Hj & E & _). rewrite E.
  assert (0 < 2^j) by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

Lemma enc_size_pos : forall len, 0 <= len -> 1 <= (len + 2) / 3 * 4 + 1.
Proof. intros len H. assert (0 <= (len + 2) / 3) by (apply Z.div_pos; lia). lia. Qed.

Lemma dec_size_pos : forall (tb : list Z), 1 <= Z.of_nat (length tb) / 4 * 3 + 3.
Proof. intros tb. assert (0 <= Z.of_nat (length tb) / 4) by (apply Z.div_pos; lia). lia. Qed.

