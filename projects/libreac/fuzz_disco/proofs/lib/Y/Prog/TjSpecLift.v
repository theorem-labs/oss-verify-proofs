(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC8a.v, with its module paths and module names changed; 553 of its 629 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/JtokIs.v, with its module paths and module names changed; 58 of its 94 lines of code are new or changed and 593 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableJson.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Definition tj_postPF (STK EV : Z) (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (T : list byte) (now buf cap : Z) : world SEGS -> config -> Prop :=
  apost_base (fx := fq) SEGS B STK (tj_fp buf cap) regs ly S W mem md EV
    (fun ly' S' W' regs' mem' md' =>
       Permutation (ablocks B ly' S') (ablocks B ly S) /\
       (cap < 3 -> getr regs' 10 = w64 (-1)) /\
       (3 <= cap -> tj_len T now < cap ->
          getr regs' 10 = w64 (tj_len T now) /\
          garr8 SEGS (mrestrict (w_H W') mem') buf (reac_disco_table_json_c.tj_text T now ++ [0])) /\
       (3 <= cap -> cap <= tj_len T now -> getr regs' 10 = w64 (-1))).
Definition tj_specPF (STK EV : Z) (IMG : world SEGS -> (word -> option byte) -> Prop) : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (t now buf cap Nb : Z) (T : list byte),
  afn_pre SEGS B STK ly S W regs mem md ch ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fq)) 5) 7 = 0 ->
  Z.of_nat (length (frames S)) <= 7 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  IMG W mem ->
  getr regs 10 = w64 t -> getr regs 11 = w64 now -> getr regs 12 = w64 buf -> getr regs 13 = w64 cap ->
  0 <= now < 2 ^ 64 -> 0 <= cap < 2 ^ 31 ->
  afobj SEGS B ly S W mem t 400 ->
  garr8 SEGS (mrestrict (w_H W) mem) t (map bv_unsigned T) -> length T = 400%nat -> disco_table_c.table_ok T ->
  (3 <= cap -> In (buf, Nb) (ablocks B ly S) /\ cap <= req_size Nb) ->
  st_nev S + EV <= EV_MAX ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_disco_table_json) regs mem md)
    (tj_postPF STK EV fq regs ly S W mem md T now buf cap).
Lemma tj_specPF_of_spec : forall IMG, treac_disco_table_json_spec B IMG ->
  forall STK, REAC_DISCO_TABLE_JSON_STK <= STK -> tj_specPF STK 0 IMG.
Proof.
intros IMG HS STK HSTK fq ly S W regs mem md ch t now buf cap Nb T
  HPRE Hfrm Hfr Hro Himg R10 R11 R12 R13 Hnow Hcap Hobj Hgt HT Hok Hbuf _.
pose proof (@pa_segs_low _ _ PI) as Hsegs.
assert (WS : REAC_DISCO_TABLE_JSON_STK = 12416) by reflexivity.
pose proof (ajournal_init SEGS B STK (tj_fp buf cap) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (_ & Hra & Hra4 & Hgp & Htp & _ & _ & Hch & _).
pose proof (afn_pre_at SEGS B STK (spZ regs) (tj_fp buf cap) ly S W mem md [] ly S W mem md 0 regs
  REAC_DISCO_TABLE_JSON_STK 0 ch HJ ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
  Hra Hra4 Hgp Htp Hch) as HPRE0.
eapply SRr_mono;
  [exact (HS fq ly S W regs mem md ch t now buf cap Nb T HPRE0 Hfrm Hfr Hro Himg R10 R11 R12 R13 Hnow Hcap Hobj Hgt HT Hok Hbuf)|].
intros W' c' _ Hpost.
unfold treac_disco_table_json_post, apost_base in Hpost.
destruct Hpost as (fx' & ly' & S' & regs' & mem' & md' & Hc & Hfp & Hcsr & HJ1 & Hkeep & HQ).
unfold tj_postPF, apost_base.
exists fx', ly', S', regs', mem', md'.
split; [exact Hc|]. split; [exact Hfp|]. split; [exact Hcsr|].
split; [|split; [exact Hkeep | exact HQ]].
assert (HF : forall a, inFP (tj_fp buf cap) a ->
  (inFP (tj_fp buf cap) a /\ exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly S) a).
{ intros a Ha. left. split; [exact Ha|].
  unfold tj_fp in Ha. revert Ha. destruct (Z.ltb_spec cap 3) as [Hc3|Hc3]; intros Ha; [exfalso; exact (inFP_nil a Ha)|].
  destruct Ha as (r & Hr & Hra'). destruct Hr as [<-|[]]. cbn [fst snd] in Hra'.
  destruct (Hbuf Hc3) as (Hin & Hle). exists buf, Nb. split; [exact Hin | lia]. }
pose proof (ajournal_sub SEGS B LAWS Hsegs STK (spZ regs) (tj_fp buf cap) ly S W mem md [] ly S W mem md 0
  REAC_DISCO_TABLE_JSON_STK (spZ regs) (tj_fp buf cap) [] ly' S' W' mem' md' 0 HJ HJ1
  ltac:(lia) ltac:(lia) HF) as HJ2.
cbn [app] in HJ2. change (0 + 0) with 0 in HJ2. exact HJ2.
Qed.
End h.
End f.
End d.
