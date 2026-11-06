(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__ArtRuns () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns.Runs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1list"; "1option"; "2and"; "2eq"; "2not"; "3Z"; "4machine_state"; "0M"; "0Q"; "0Q'"; "0Q1"; "0Q2"; "6aruns"; "5aev"]; ["5art_reveal"; "5art_unmap"; "5art_zfill"; "7msteps"; "8add"; "8le"; "8lt"; "0a"; "0b"; "0hi"; "0len"; "0lo"; "0log"; "0log'"; "0r"; "0s"]; ["0s'"; "0segs"; "9Z_to_bv"; "9bv"; "9bv_unsigned"; "0x"]]).
Inductive aev : Type :=
| AMmapFixed (addr len : Z)
| AMmapNull (len r : Z)
| AMmapFixedNR (addr len : Z)
| AMunmap (addr len : Z)
| AMadvise (addr len : Z).
Definition art_zfill (M : word -> option byte) (r len : Z) : word -> option byte :=
fun a => if (r <=? bv_unsigned a) && (bv_unsigned a <? r + len) then Some (Z_to_bv 8 0) else M a.
Definition art_unmap (M : word -> option byte) (r len : Z) : word -> option byte :=
fun a => if (r <=? bv_unsigned a) && (bv_unsigned a <? r + len) then None else M a.
Definition art_shlo (r : Z) : Z := (r / 8 + 0x7fff8000) / 4096 * 4096.
Definition art_shhi (r len : Z) : Z := ((r + len) / 8 + 0x7fff8000 + 4095) / 4096 * 4096.
Definition art_reveal (M : word -> option byte) (lo hi : Z) : word -> option byte :=
fun a => if (lo <=? bv_unsigned a) && (bv_unsigned a <? hi) then (match M a with Some b => Some b | None => Some (Z_to_bv 8 0) end) else M a.
Lemma art_reveal_in : forall M lo hi a, lo <= bv_unsigned a < hi -> art_reveal M lo hi a = match M a with Some b => Some b | None => Some (Z_to_bv 8 0) end.
Proof. intros M lo hi a H. unfold art_reveal. replace ((lo <=? bv_unsigned a) && (bv_unsigned a <? hi)) with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. Qed.
Lemma art_reveal_out : ltac2:(TCodec.tc2 tcn__ArtRuns "Q2'Q3yR0%211'3y8%511%311p051'7&6'4&Er3&Q4r1%22>1%5241&Fr2%2241%:241%<11'5&@r5r4%3421>8%319%63F21p081pQ@L1pQDG1pQHH1pDJ1").
Proof.
intros M lo hi a H. unfold art_reveal. destruct (lo <=? bv_unsigned a) eqn:E1; [|reflexivity]. destruct (bv_unsigned a <? hi) eqn:E2; [|reflexivity].
apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. apply H. lia.
Qed.
Lemma art_reveal_some : ltac2:(TCodec.tc2 tcn__ArtRuns "N'Q3yR0%211'3y8%511%311pR<51'7'5r5r2%211(1r1%22:1%73:41&@r6r4r3%443;21%92A;%>3A21p081pQBD1pQ@H1pQDC1pQHD1pDF1").
Proof. intros M lo hi a b H. unfold art_reveal. rewrite H. destruct ((lo <=? bv_unsigned a) && (bv_unsigned a <? hi)); reflexivity. Qed.
Lemma art_reveal_defined : ltac2:(TCodec.tc2 tcn__ArtRuns "Q3'Q3yR0%211'3y8%511%311p051'7'4&Er3&Q4r1%22=1%5241&Fr2%2241%:241&6'5&@r5r4%3421>8(0%11F%73F31%911p0;1pQ@M1pQDH1pQHI1pDK1").
Proof. intros M lo hi a H. rewrite art_reveal_in by exact H. destruct (M a); discriminate. Qed.
Lemma art_zfill_in : ltac2:(TCodec.tc2 tcn__ArtRuns "Q6'Q3yR0%211'3y8%511%311p051'7'4&Er3&Q4r1%22=1%5241&F&Dr2%2281%4261%<261'5&Br5r4%3421?8(1&Q2z%22J1%42J1%:3J61p0<1pQ@Q01pQFK1pQNL1pDN1").
Proof. intros M r len a H. unfold art_zfill. replace ((r <=? bv_unsigned a) && (bv_unsigned a <? r + len)) with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. Qed.
Lemma art_zfill_out : ltac2:(TCodec.tc2 tcn__ArtRuns "Q4'Q3yR0%211'3y8%511%311p051'7&6'4&Er3&Q4r1%22>1%5241&F&Dr2%2281%4261%<261%>11'5&Br5r4%3421@9%31:%63H21p081pQ@N1pQFI1pQNJ1pDL1").
Proof.
intros M r len a H. unfold art_zfill. destruct (r <=? bv_unsigned a) eqn:E1; [|reflexivity]. destruct (bv_unsigned a <? r + len) eqn:E2; [|reflexivity].
apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. apply H. lia.
Qed.
Lemma art_unmap_in : ltac2:(TCodec.tc2 tcn__ArtRuns "Q3'Q3yR0%211'3y8%511%311p051'7'4&Er3&Q4r1%22=1%5241&F&Dr2%2281%4261%<261'5&Ar5r4%3421?8(0%11G%73G31p091pQ@M1pQFH1pQNI1pDK1").
Proof. intros M r len a H. unfold art_unmap. replace ((r <=? bv_unsigned a) && (bv_unsigned a <? r + len)) with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. Qed.
Lemma art_unmap_out : ltac2:(TCodec.tc2 tcn__ArtRuns "Q4'Q3yR0%211'3y8%511%311p051'7&6'4&Er3&Q4r1%22>1%5241&F&Dr2%2281%4261%<261%>11'5&Ar5r4%3421@9%31:%63H21p081pQ@N1pQFI1pQNJ1pDL1").
Proof.
intros M r len a H. unfold art_unmap. destruct (r <=? bv_unsigned a) eqn:E1; [|reflexivity]. destruct (bv_unsigned a <? r + len) eqn:E2; [|reflexivity].
apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. apply H. lia.
Qed.
Section Runs.
Variable segs : list Segment.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.
Definition art_at_ecall (pc : word) : Prop := exists w, fetch_word segs pc = Some w /\ is_ecall w = true.
Definition art_mmap_args (regs : bvmap 5 word) (addr len flags : Z) : Prop :=
getr regs 17 = Z_to_bv 64 222 /\ getr regs 10 = Z_to_bv 64 addr /\ getr regs 11 = Z_to_bv 64 len /\ getr regs 12 = Z_to_bv 64 3
/\ getr regs 13 = Z_to_bv 64 flags /\ getr regs 14 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr regs 15 = Z_to_bv 64 0.
Definition art_munmap_args (regs : bvmap 5 word) (addr len : Z) : Prop :=
getr regs 17 = Z_to_bv 64 215 /\ getr regs 10 = Z_to_bv 64 addr /\ getr regs 11 = Z_to_bv 64 len.
Definition art_madvise_args (regs : bvmap 5 word) (addr len : Z) : Prop :=
getr regs 17 = Z_to_bv 64 233 /\ getr regs 10 = Z_to_bv 64 addr /\ getr regs 11 = Z_to_bv 64 len /\ getr regs 12 = Z_to_bv 64 4.
Inductive aruns (Q : list aev -> machine_state -> Prop) : list aev -> machine_state -> Prop :=
| ar_done : forall log s, Q log s -> aruns Q log s
| ar_steps : forall log s s', msteps segs s s' -> aruns Q log s' -> aruns Q log s
| ar_mmap_fixed : forall log regs (pc pc' : word) M rom addr len,
art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_mmap_args regs addr len 50 -> EVOK log (AMmapFixed addr len) ->
aruns Q (log ++ [AMmapFixed addr len]) (mkst (regupd regs 10 (Z_to_bv 64 addr)) pc' (art_zfill M addr len) rom) ->
aruns Q log (mkst regs pc M rom)
| ar_mmap_null : forall log regs (pc pc' : word) M rom len,
art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_mmap_args regs 0 len 34 -> EVOK log (AMmapNull len 0) ->
(forall r, GR log M len r ->
aruns Q (log ++ [AMmapNull len r]) (mkst (regupd regs 10 (Z_to_bv 64 r)) pc' (art_reveal (art_zfill M r len) (art_shlo r) (art_shhi r len)) rom)) ->
aruns Q log (mkst regs pc M rom)
| ar_mmap_fixed_nr : forall log regs (pc pc' : word) M rom addr len,
art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_mmap_args regs addr len 16434 -> EVOK log (AMmapFixedNR addr len) ->
aruns Q (log ++ [AMmapFixedNR addr len]) (mkst (regupd regs 10 (Z_to_bv 64 addr)) pc' (art_zfill M addr len) rom) ->
aruns Q log (mkst regs pc M rom)
| ar_munmap : forall log regs (pc pc' : word) M rom addr len,
art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_munmap_args regs addr len -> EVOK log (AMunmap addr len) ->
aruns Q (log ++ [AMunmap addr len]) (mkst (regupd regs 10 (Z_to_bv 64 0)) pc' (art_unmap M addr len) rom) ->
aruns Q log (mkst regs pc M rom)
| ar_madvise : forall log regs (pc pc' : word) M rom addr len,
art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_madvise_args regs addr len -> EVOK log (AMadvise addr len) ->
aruns Q (log ++ [AMadvise addr len]) (mkst (regupd regs 10 (Z_to_bv 64 0)) pc' (art_zfill M addr len) rom) ->
aruns Q log (mkst regs pc M rom).
Lemma aruns_mono : ltac2:(TCodec.tc2 tcn__ArtRuns "K'2'?%211'8!p021p041'>r4r2r1%43321r7%1243r3%3216p031pR2>1pQL@1r5%=31<6p031p0;1pR0D1pQJF1pHC1pFD1").
Proof.
intros Q Q' log s H HQ. induction H.
- apply ar_done. apply HQ. assumption.
- eapply ar_steps; eassumption.
- eapply ar_mmap_fixed; eassumption.
- eapply ar_mmap_null; eassumption.
- eapply ar_mmap_fixed_nr; eassumption.
- eapply ar_munmap; eassumption.
- eapply ar_madvise; eassumption.
Qed.
Lemma aruns_bind : ltac2:(TCodec.tc2 tcn__ArtRuns "K'2'?%211'8!p021p041'>r4r2r1%43321r7%1243r3%83316p031pR2>1pQL@1r5%=31<6p031p0;1pR0D1pQJF1pLC1pJD1").
Proof.
intros Q1 Q2 log s H HQ. induction H.
- apply HQ. assumption.
- eapply ar_steps; eassumption.
- eapply ar_mmap_fixed; eassumption.
- eapply ar_mmap_null; eassumption.
- eapply ar_mmap_fixed_nr; eassumption.
- eapply ar_munmap; eassumption.
- eapply ar_madvise; eassumption.
Qed.
Lemma aruns_msteps_done : ltac2:(TCodec.tc2 tcn__ArtRuns "H'2'?%211'8!p021p041'CvQ1r2r1%43321r5r4%2215'>r6%23154p041p081pR2A1pR0B1pQJD1pFA1").
Proof. intros Q log s s' H HQ. eapply ar_steps; [exact H|]. apply ar_done. exact HQ. Qed.
Lemma aruns_of_msteps : ltac2:(TCodec.tc2 tcn__ArtRuns "H'2'?%211'8!p021p041'CvQ1r2r1%43321'>r5r4%33216r6%53143p031p081pR2A1pR0B1pQJD1pFA1").
Proof. intros. eapply ar_steps; eassumption. Qed.
End Runs.
Arguments aruns segs EVOK GR {fx} Q log s.
