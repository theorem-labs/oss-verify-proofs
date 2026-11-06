(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfVa.v (cold/port-fm-rtprintf-param 3e35620c52e); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/FMsnprintfVa.table). *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/FMsnprintfVa.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/FMsnprintfVa.v at 71994ff034c7, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/FMsnprintfVa.v was made and quote that file's image-A values; the code below carries image B's values; a numeral in a comment that quotes the donor's text (lib/A/FMsnprintfVa.v keeps its donor's comment text) is kept as lib/A/FMsnprintfVa.v writes it. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import SnUpoison PfFacts SnShared.
Import ListNotations.
Local Open Scope Z_scope.

Record va_spill_geom : Type := { vs_off : Z; vs_regs : list nat }.

Lemma words_at_app (rd : reader) (p : Z) (us vs : list Z) :
  words_at rd p us -> words_at rd (p + 8 * Z.of_nat (length us)) vs -> words_at rd p (us ++ vs).
Proof.
  unfold words_at. intros Hu Hv i Hi. rewrite length_app in Hi.
  destruct (Nat.lt_ge_cases i (length us)) as [H | H].
  - rewrite app_nth1 by exact H. apply Hu. exact H.
  - rewrite app_nth2 by exact H.
    replace (p + 8 * Z.of_nat i) with (p + 8 * Z.of_nat (length us) + 8 * Z.of_nat (i - length us)) by lia.
    apply Hv. lia.
Qed.

Lemma va_spill_words (g : va_spill_geom) (regs : bvmap 5 word) (rd' : reader) (xs : list Z) :
  vs_off g = 8 * Z.of_nat (length (vs_regs g)) ->
  words_at rd' (spZ regs - vs_off g) (map (argZ regs) (map Z.of_nat (vs_regs g))) ->
  words_at rd' (spZ regs) xs ->
  words_at rd' (spZ regs - vs_off g) (map (argZ regs) (map Z.of_nat (vs_regs g)) ++ xs).
Proof.
  intros Ho Hr Hx. apply words_at_app; [exact Hr |].
  rewrite !length_map, Ho.
  replace (spZ regs - 8 * Z.of_nat (length (vs_regs g)) + 8 * Z.of_nat (length (vs_regs g))) with (spZ regs) by lia.
  exact Hx.
Qed.

Lemma va_spill_of_va_words (g : va_spill_geom) (regs : bvmap 5 word) (rd rd' : reader) (xs ws : list Z) :
  vs_regs g = [3; 4; 5; 6; 7]%nat ->
  vs_off g = 8 * Z.of_nat (length (vs_regs g)) ->
  va_words regs rd (spZ regs) xs ws ->
  (forall i, (i < length xs)%nat -> rdword rd' (spZ regs + 8 * Z.of_nat i) = rdword rd (spZ regs + 8 * Z.of_nat i)) ->
  words_at rd' (spZ regs - vs_off g) (map (argZ regs) (map Z.of_nat (vs_regs g))) ->
  words_at rd' (spZ regs - vs_off g) ws.
Proof.
  intros Hg Ho Hv Hu Hr. unfold va_words in Hv. destruct Hv as [Hws Hx]. subst ws.
  replace [3; 4; 5; 6; 7] with (map Z.of_nat (vs_regs g)) by (rewrite Hg; reflexivity).
  apply va_spill_words; [exact Ho | exact Hr |].
  unfold words_at in *. intros i Hi. rewrite Hu by exact Hi. apply Hx. exact Hi.
Qed.

Lemma va_spill_ap_ok (g : va_spill_geom) (regs : bvmap 5 word) (S' fr K K' d n : Z) (xs : list Z) :
  vs_off g = 8 * Z.of_nat (length (vs_regs g)) ->
  vs_off g <= spZ regs ->
  spZ regs + 8 * Z.of_nat (length xs) < 2 ^ 63 ->
  S' = spZ regs - fr -> vs_off g <= fr -> vs_off g <= K -> 0 < n ->
  Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length xs))) (snp_out K (spZ regs) d n) ->
  pairwise zdisjoint (snp_out K (spZ regs) d n) ->
  0 <= spZ regs - vs_off g /\
  spZ regs - vs_off g + 8 * Z.of_nat (length (vs_regs g) + length xs) < 2 ^ 63 /\
  Forall (zdisjoint (spZ regs - vs_off g, 8 * Z.of_nat (length (vs_regs g) + length xs))) (snp_out K' S' d n).
Proof.
  intros Ho HS Hhi HS' Hfr HK Hn Hx Hp. unfold snp_out in Hx, Hp |- *.
  rewrite !Forall_cons_iff in Hx. destruct Hx as [_ [Hx _]].
  cbn [pairwise] in Hp. destruct Hp as [Hp _]. rewrite Forall_cons_iff in Hp. destruct Hp as [Hp _].
  unfold zdisjoint in Hx, Hp. cbn [fst snd] in Hx, Hp. rewrite Nat2Z.inj_add.
  split; [lia |]. split; [lia |].
  constructor; [| constructor; [| constructor]]; unfold zdisjoint; cbn [fst snd]; lia.
Qed.

Definition asan_snprintf_frame : Z := 0x60.
Definition asan_snprintf_spill_post : Z := 0x38.
Definition asan_snprintf_spill : va_spill_geom := {| vs_off := 40; vs_regs := [3; 4; 5; 6; 7]%nat |}.

Lemma asan_snprintf_spill_prologue : vs_off asan_snprintf_spill = asan_snprintf_frame - asan_snprintf_spill_post.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_snprintf_spill_off : vs_off asan_snprintf_spill = 8 * Z.of_nat (length (vs_regs asan_snprintf_spill)).
Proof. vm_compute. reflexivity. Qed.
