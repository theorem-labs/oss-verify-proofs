(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module BoAllocFRc3U.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p.BoAllocFRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S.BoAllocFRc3b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFRc3c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p.BoAllocFRc3R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p.BoAllocFRc3T.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Section ITEMMEM.
  Variables (memD : word -> option byte) (S ra0 s0v s1v s2v s3v s4v x21 : word) (m ab n8 T c cnt e : Z) (h1 h2 h3 : byte) (j0 j1 stw : word).
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gm : 0x10007fff8000 <= ab /\ (ab = m \/ ab + 16 <= m) /\ m + 16 + n8 <= U S - 3584 /\ m mod 16 = 0.
  Hypothesis Gn8 : 8 <= n8 /\ n8 mod 8 = 0 /\ n8 <= 2 ^ 40.
  Hypothesis GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584).
  Hypothesis GabT : m + 16 + n8 <= T \/ T + 4096 <= ab.
  Hypothesis Gc : 1 <= c <= 30.
  Hypothesis Gcnt : 0 <= cnt < 16.
  #[local] Abbreviation M9 := (fr_item memD S ra0 s0v s1v s2v s3v s4v x21 m ab n8 T c cnt e h1 h2 h3 j0 j1 stw).
  #[local] Abbreviation pc_ := (T + 208 + 80 * c).
  #[local] Abbreviation shlo := (0x7fff8000 + (m + 16) / 8).

  Lemma TSB_IM : (T + 4096 <= 0x7fff7000) \/ (0x10007fff8000 <= T).
  Proof using GT n8 m S. pose proof GT as X. unfold hideW in X. lia. Qed.
  Lemma shlen8I : shlen (Z_to_bv 64 n8) = n8 / 8.
  Proof using Gn8 m. (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm. reflexivity. Qed.
  Lemma shad_m : shad (Z_to_bv 64 (m + 16)) = shlo.
  Proof using Gn8 Gm GS n8 ab S. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold shad in G in change_no_check G' end). unorm. lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma md8 : 8 * ((m + 16) / 8) = m + 16 /\ 8 * (n8 / 8) = n8 /\ 0x10007fff8000 / 8 <= (m + 16) / 8 /\ (m + 16) / 8 + n8 / 8 <= 2 ^ 44.
  Proof using Gcnt GT Gn8 Gm GS stw cnt T ab S memD. pose proof (u64_range S). Z.div_mod_to_equations. lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Ltac lsideI := wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; rewrite ?Z2Nat.id by lia;
                 (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.

  Ltac wo tac := rewrite wbytes_outside by (tac; lsideI).
  Ltac ro tac := rewrite rdn_wbytes_out by (tac; lsideI).

  Lemma fr_item_outside : forall a : word,
    (U a < U S - 2512 \/ U S - 2400 <= U a) -> (U a < m \/ m + 4 <= U a) -> (ab = m \/ U a < ab \/ ab + 8 <= U a) ->
    (U a < shlo \/ shlo + n8 / 8 <= U a) ->
    (U a < pc_ \/ pc_ + 4 <= U a) -> (U a < pc_ + 16 + 4 * cnt \/ pc_ + 16 + 4 * cnt + 4 <= U a) ->
    (U a < T + 2784 \/ T + 2792 <= U a) -> (U a < T + 2840 \/ T + 2856 <= U a) -> M9 a = memD a.
  Proof using Gcnt Gc GT Gn8 Gm GS.
    intros a A1 A2 A3 A4 A5 A6 A7 A8. pose proof (u64_range S) as HSr. pose proof md8 as MD.
    destruct GS as (GS1 & GS2). destruct GT as (GT1 & (_ & GT2)). destruct Gm as (Gm1 & Gm2 & Gm3 & Gm4).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_item, fr_k35, fr_k5, fr_k4, fr_k3, fr_k12, fr_k1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite ?shad_m, ?shlen8I.
    wo ltac:(clear - A7 GT1 GT2 HSr GS1 GS2).                       (* [comment removed for export] *)
    wo ltac:(clear - A6 GT1 GT2 HSr GS1 GS2 Gc Gcnt).               (* [comment removed for export] *)
    wo ltac:(clear - A5 GT1 GT2 HSr GS1 GS2 Gc Gcnt).               (* [comment removed for export] *)
    do 6 wo ltac:(clear - A1 HSr GS1 GS2).                          (* [comment removed for export] *)
    do 2 wo ltac:(clear - A8 GT1 GT2 HSr GS1 GS2).                  (* [comment removed for export] *)
    do 2 wo ltac:(clear - A1 HSr GS1 GS2).                          (* [comment removed for export] *)
    wo ltac:(clear - A4 MD HSr GS1 GS2 Gm3 Gm1 Gm2 Gn8).            (* [comment removed for export] *)
    do 7 wo ltac:(clear - A1 HSr GS1 GS2).                          (* [comment removed for export] *)
    wo ltac:(clear - A2 HSr GS1 GS2 Gm3 Gm1 Gm2 Gn8).                   (* [comment removed for export] *)
    destruct (Z.eqb_spec ab m) as [E | N].
    - do 6 wo ltac:(clear - A1 HSr GS1 GS2). reflexivity.
    - assert (A3' : U a < ab \/ ab + 8 <= U a) by (destruct A3 as [A3 | A3]; [contradiction | exact A3]).
      wo ltac:(clear - A3' HSr GS1 GS2 Gm3 Gm1 Gm2 Gn8).
      do 6 wo ltac:(clear - A1 HSr GS1 GS2). reflexivity.
  Qed.
  Lemma fr_item_foot : forall a : word, M9 a <> memD a ->
    (U S - 2512 <= U a < U S - 2400) \/ (m <= U a < m + 4) \/ (ab <> m /\ ab <= U a < ab + 8) \/ (shlo <= U a < shlo + n8 / 8)
    \/ (pc_ <= U a < pc_ + 4) \/ (pc_ + 16 + 4 * cnt <= U a < pc_ + 16 + 4 * cnt + 4) \/ (T + 2784 <= U a < T + 2792) \/ (T + 2840 <= U a < T + 2856).
  Proof using GS GT GabT Gc Gcnt Gm Gn8.
    intros a NE.
    destruct (decide (U S - 2512 <= U a < U S - 2400)) as [wcY|N1]; [clear - wcY; tauto|].
    destruct (decide (m <= U a < m + 4)) as [wcY|N2]; [clear - wcY; tauto|].
    destruct (decide (ab <> m /\ ab <= U a < ab + 8)) as [wcY|N3]; [clear - wcY; tauto|].
    destruct (decide (shlo <= U a < shlo + n8 / 8)) as [wcY|N4]; [clear - wcY; tauto|].
    destruct (decide (pc_ <= U a < pc_ + 4)) as [wcY|N5]; [clear - wcY; tauto|].
    destruct (decide (pc_ + 16 + 4 * cnt <= U a < pc_ + 16 + 4 * cnt + 4)) as [wcY|N6]; [clear - wcY; tauto|].
    destruct (decide (T + 2784 <= U a < T + 2792)) as [wcY|N7]; [clear - wcY; tauto|].
    destruct (decide (T + 2840 <= U a < T + 2856)) as [wcY|N8]; [clear - wcY; tauto|].
    exfalso. apply NE. apply fr_item_outside; [clear - N1; lia | clear - N2; lia | | clear - N4; lia | clear - N5; lia | clear - N6; lia | clear - N7; lia | clear - N8; lia].
    destruct (Z.eq_dec ab m) as [E | N]; [left; exact E | right; clear - N3 N; lia].
  Qed.
  Lemma fr_item_grows : mem_grows memD M9.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_item, fr_k35, fr_k5, fr_k4, fr_k3, fr_k12, fr_k1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    destruct (Z.eqb_spec ab m); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma fr_item_cnt : rdn BSEGS M9 (Z_to_bv 64 pc_) 4 = Some (LE4 (cnt + 1)).
  Proof using Gcnt Gc GT Gn8 Gm GS.
    pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct GT as (GT1 & (_ & GT2)).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_item, fr_k35, fr_k5 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    do 2 ro ltac:(clear - GT1 GT2 HSr GS1 GS2 Gc Gcnt).
    pose proof (rdn_wbytes_hit BSEGS (LE4 (cnt + 1))) as X. rewrite length_N_to_le_bytes in X. apply X. unorm. lia.
  Qed.
  Lemma fr_item_slot : rdn BSEGS M9 (Z_to_bv 64 (pc_ + 16 + 4 * cnt)) 4 = Some (LE4 (e / 16)).
  Proof using Gcnt Gc GT Gn8 Gm GS.
    pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct GT as (GT1 & (_ & GT2)).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_item, fr_k35, fr_k5 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    ro ltac:(clear - GT1 GT2 HSr GS1 GS2 Gc Gcnt).
    pose proof (rdn_wbytes_hit BSEGS (LE4 (e / 16))) as X. rewrite length_N_to_le_bytes in X. apply X. unorm. lia.
  Qed.
  Lemma fr_item_shadow : forall i, 0 <= i < n8 / 8 -> M9 (Z_to_bv 64 (shlo + i)) = Some (Z_to_bv 8 0xfa).
  Proof using Gcnt Gc GabT GT Gn8 Gm GS.
    intros i Hi. pose proof TSB_IM as TSB1. pose proof (u64_range S) as HSr. pose proof md8 as MD.
    destruct GS as (GS1 & GS2). destruct GT as (GT1 & (_ & GT2)). destruct Gm as (Gm1 & Gm2 & Gm3 & Gm4).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_item, fr_k35, fr_k5, fr_k4, fr_k3 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite ?shad_m, ?shlen8I.
    do 3 wo ltac:(clear - Hi TSB1 MD GT1 GT2 HSr GS1 GS2 Gc Gcnt Gm3 Gm1).
    do 6 wo ltac:(clear - Hi MD HSr GS1 GS2 Gm3 Gm1).
    do 2 wo ltac:(clear - Hi TSB1 MD GT1 GT2 HSr GS1 GS2 Gm3 Gm1).
    do 2 wo ltac:(clear - Hi MD HSr GS1 GS2 Gm3 Gm1).
    rewrite wbytes_inside by (clear - Hi MD HSr GS1 GS2 Gm3 Gm1 Gn8; lsideI).
    f_equal. rewrite nth_repeat_lt; [(lazymatch goal with |- ?G => let G' := eval unfold cbyte in G in change_no_check G' end); unorm; reflexivity|].
    unorm. apply Z2Nat.inj_lt; lia.
  Qed.

End ITEMMEM.

(* [comment removed for export] *)
Section K5MEM.
  Variables (mem : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word) (T c cnt e : Z) (stw : word).
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584).
  Hypothesis Gc : 1 <= c <= 30.
  Hypothesis Gcnt : 0 <= cnt < 16.
  #[local] Abbreviation M5 := (fr_k5 mem S ra0 s0v s1v s2v s3v s4v T c cnt e stw).
  #[local] Abbreviation pc_ := (T + 208 + 80 * c).
  Ltac lsideV := wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
  Ltac woV tac := rewrite wbytes_outside by (tac; lsideV).
  Ltac roV tac := rewrite rdn_wbytes_out by (tac; lsideV).

  Lemma fr_k5_outside : forall a : word,
    (U a < U S - 2448 \/ U S - 2400 <= U a) -> (U a < pc_ \/ pc_ + 4 <= U a) -> (U a < pc_ + 16 + 4 * cnt \/ pc_ + 16 + 4 * cnt + 4 <= U a) ->
    (U a < T + 2784 \/ T + 2792 <= U a) -> M5 a = mem a.
  Proof using Gcnt Gc GT GS.
    intros a A1 A5 A6 A7. pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct GT as (GT1 & (_ & GT2)).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_k5 in G in change_no_check G' end).
    woV ltac:(clear - A7 GT1 GT2 HSr GS1 GS2).
    woV ltac:(clear - A6 GT1 GT2 HSr GS1 GS2 Gc Gcnt).
    woV ltac:(clear - A5 GT1 GT2 HSr GS1 GS2 Gc Gcnt).
    do 6 woV ltac:(clear - A1 HSr GS1 GS2). reflexivity.
  Qed.
  Lemma fr_k5_foot : forall a : word, M5 a <> mem a ->
    (U S - 2448 <= U a < U S - 2400) \/ (pc_ <= U a < pc_ + 4) \/ (pc_ + 16 + 4 * cnt <= U a < pc_ + 16 + 4 * cnt + 4) \/ (T + 2784 <= U a < T + 2792).
  Proof using GS GT Gc Gcnt.
    intros a NE.
    destruct (decide (U S - 2448 <= U a < U S - 2400)) as [wcY|N1]; [clear - wcY; tauto|].
    destruct (decide (pc_ <= U a < pc_ + 4)) as [wcY|N5]; [clear - wcY; tauto|].
    destruct (decide (pc_ + 16 + 4 * cnt <= U a < pc_ + 16 + 4 * cnt + 4)) as [wcY|N6]; [clear - wcY; tauto|].
    destruct (decide (T + 2784 <= U a < T + 2792)) as [wcY|N7]; [clear - wcY; tauto|].
    exfalso. apply NE. apply fr_k5_outside; [clear - N1; lia | clear - N5; lia | clear - N6; lia | clear - N7; lia].
  Qed.
  Lemma fr_k5_grows : mem_grows mem M5.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_k5 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma fr_k5_cnt : rdn BSEGS M5 (Z_to_bv 64 pc_) 4 = Some (LE4 (cnt + 1)).
  Proof using Gcnt Gc GT GS.
    pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct GT as (GT1 & (_ & GT2)).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_k5 in G in change_no_check G' end). do 2 roV ltac:(clear - GT1 GT2 HSr GS1 GS2 Gc Gcnt).
    pose proof (rdn_wbytes_hit BSEGS (LE4 (cnt + 1))) as X. rewrite length_N_to_le_bytes in X. apply X. unorm. lia.
  Qed.
  Lemma fr_k5_slot : rdn BSEGS M5 (Z_to_bv 64 (pc_ + 16 + 4 * cnt)) 4 = Some (LE4 (e / 16)).
  Proof using Gcnt Gc GT GS.
    pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct GT as (GT1 & (_ & GT2)).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_k5 in G in change_no_check G' end). roV ltac:(clear - GT1 GT2 HSr GS1 GS2 Gc Gcnt).
    pose proof (rdn_wbytes_hit BSEGS (LE4 (e / 16))) as X. rewrite length_N_to_le_bytes in X. apply X. unorm. lia.
  Qed.
End K5MEM.
End FPGen.
End BoAllocFRc3U.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcK2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p.BoAllocFRc3T BoAllocFRc3U.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation up8 := AsAinvOpsPf3d.AsAinvFreeS.up8.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma down8_up8K : forall n, AsRtRegion.down8 (n + 7) = up8 n.
Proof. intros n. (lazymatch goal with |- ?G => let G' := eval unfold AsRtRegion.down8, AsAinvOpsPf3d.AsAinvFreeS.up8 in G in change_no_check G' end). lia. Qed.
Lemma rz_16_32 : forall r, r mod 16 = 0 -> 16 <= r -> r = 16 \/ 32 <= r.
Proof. intros. lia. Qed.
Lemma mod16_8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros. lia. Qed.
Lemma sh_range_in : forall lo len a n8, lo mod 8 = 0 -> len mod 8 = 0 -> a mod 8 = 0 -> n8 mod 8 = 0 -> lo <= a -> a + n8 <= lo + len -> 0 <= n8 ->
  lo / 8 <= a / 8 /\ a / 8 + n8 / 8 <= lo / 8 + len / 8 /\ 8 * (a / 8) = a /\ 8 * (n8 / 8) = n8.
Proof. intros. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section K2.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis HTP : TP = ia_tp both_addrs.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation CTX := (bt_tctx bt).

  Theorem rc_item_prim_pf : rc_item_stmt bt FXOK arm_prim_room.
  Proof using HTP RCC CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    (lazymatch goal with |- ?G => let G' := eval unfold rc_item_stmt in G in change_no_check G' end).
    intros fx X Xd qt qg st Lc FF M mdl R S ret ba m n its rest HFX HH MW W RX EGQ (HP & ROOM) XSUB XQ XOBJ QDEF
           R1 RET R2 R10 R11 R4 CCB S16 Slo Shi SOK _.
    pose proof ceil_rng as CR. pose proof (u64_range S) as HSr.
    destruct RX as (M0 & RP & DX).
    assert (EQ0 : forall a : word, ~ X (U a) -> M a = M0 a).
    { intros a Ha. destruct (decide (M a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX a N))). }
    assert (GR0 : mem_grows M0 M) by (intros a Ha; destruct (decide (M a = M0 a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (DX a N))]).
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CELL_hook
                      & CELL_mcsz & CELL_msz & CELL_gfl & CELL_mff & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he
                      & CELL_grm & CELL_rm & CELL_cpm & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9 & Gc10).
    destruct RCC as (CELL_rib & CELL_magic & G_tsdp).
    unfold free_cells_nb in CELLNB.
    (* [comment removed for export] *)
    assert (Hq : In (m, n) (quar st)).
    { (lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end). apply in_flat_map. exists (BATCH ba ((m, n) :: its)). split; [apply in_app_iff; right; rewrite EGQ; left; reflexivity | left; reflexivity]. }
    assert (Hb : In (BATCH ba ((m, n) :: its)) (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite EGQ; left; reflexivity).
    pose proof (cinit_of_batch bt st Lc FF qt qg _ W Hb) as CINIT.
    pose proof (quar_chunk bt st Lc FF W m n Hq HP) as G. cbn zeta in G.
    unfold arm_prim_room in *. remember (blk_class n) as c eqn:Ec. remember (prim_alloc_beg (m + 16) n) as ab eqn:Eab0.
    destruct G as (Hc & CV & INQ & G4 & G5 & G6).
    destruct (carved_range bt st Lc FF W c ab Hc CV) as (C1 & C2 & C3 & C4 & C5).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
    pose proof (csize_pos c Hc) as ((CS1 & CS2) & CS16).
    destruct (quar_item_range bt st Lc FF W m n Hq) as (QR1 & QR2 & QR3).
    pose proof (rz_mod16 n) as RM. pose proof (rz_range n) as RZ.
    assert (N64 : n <= 64512) by (apply (is_primary_iff n ltac:(lia)); exact HP).
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & CPG' & GCT' & SB0 & SB1 & SBH & SB16).
    pose proof (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _ & _ & INC).
    pose proof (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as SPT.
    pose proof (space_vs_fixed bt st Lc FF W _ _ INC ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as SPC.
    destruct CV as (j & Hj0 & Hj1 & Eab). pose proof Eab as Eab'. unfold chunk_addr, region_beg, KREGION in Eab'.
    assert (CVc : carved bt st c ab) by (exists j; repeat split; assumption).
    destruct (up8_facts n ltac:(lia)) as (U8a & U8b & U8c & U8d).
    assert (T16 : T mod 16 = 0) by (clear - TPG; unfold PG in TPG; Z.div_mod_to_equations; lia).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    rewrite BT_ia in GTI, GCI. cbn [ia_img_lo ia_img_hi both_addrs] in GTI, GCI.
    unfold IB in *. rewrite BT_ia in *. cbn [ia_instance both_addrs] in *.
    unfold fa_beg, reginfo, region_beg, KREGION, KFAOFF, KSPACE, PG, AS_HEAPLO, AS_LO, NMAX, PTRHI in *.
    remember (csize c) as cs eqn:Ecs. set (d := m - SBEG - c * 2 ^ 32).
    assert (Em : m = ab + rz n - 16) by (clear - G4; lia).
    assert (M16 : m mod 16 = 0) by (clear - Em C5 RM; Z.div_mod_to_equations; lia).
    assert (Ed : d = j * cs + (rz n - 16)) by ((lazymatch goal with |- ?G => let G' := eval unfold d in G in change_no_check G' end); clear - Em Eab'; lia).
    assert (Hrz : 0 <= rz n - 16 < cs) by (clear - G5 G4 QR3 RZ; lia).
    assert (Eidx : d / cs = j) by (symmetry; apply (Z.div_unique d cs j (rz n - 16)); [left; exact Hrz | clear - Ed; lia]).
    assert (JJ : (j + 1) * cs = j * cs + cs) by ring.
    assert (JJ0 : 0 <= j * cs) by (clear - Hj0 CS1; nia).
    assert (Hd32 : 0 <= d < 2 ^ 32) by (clear - Ed Hrz JJ JJ0 Hj1 Q3 Q2; lia).
    assert (Eabm : SBEG + c * 2 ^ 32 + d / cs * cs = ab) by (rewrite Eidx; clear - Eab'; lia).
    assert (P8 : (m + 16) mod 8 = 0) by (clear - M16; Z.div_mod_to_equations; lia).
    assert (N8le : m + 16 + up8 n <= ab + cs).
    { apply (up8_le (m + 16) n (ab + cs) P8); [clear - C5 CS16; Z.div_mod_to_equations; lia | exact G5]. }
    destruct (sh_up8 (m + 16) n P8 ltac:(lia)) as [SHhi SHlo]. unfold SB in SHhi, SHlo.
    destruct (sh_range_in (SBEG + c * 2 ^ 32) (r_mapped_user (a_reg st c)) (m + 16) (up8 n))
      as (SR1 & SR2 & SR3 & SR4);
      [clear - Q11; Z.div_mod_to_equations; lia | clear - Q13; Z.div_mod_to_equations; lia | exact P8 | exact U8d
      | clear - Em C1 RZ; lia | clear - N8le C2 Q3; lia | clear - U8b; lia |].
    (* [comment removed for export] *)
    pose proof RP as (Rc & Ri & Rt & Rr & _ & _ & _ & Rh & _ & _ & _ & Rs & R13 & R14 & _ & _ & Csb & _ & SHM0).
    first [pose proof (proj1 SHM0) as SHM | pose proof SHM0 as SHM]. clear SHM0.          (* [comment removed for export] *)
    rewrite BT_ia in Csb. cbn [ia_rtc_sb both_addrs] in Csb.
    destruct Rt as (_ & _ & _ & _ & _ & _ & _ & TPC & TW & Tback & _).
    destruct (TPC c Hc) as (PCcnt & PCmax & PCcs & _). rewrite CINIT in PCmax.
    destruct (Rr c Hc) as [(_ & _ & _ & _ & _ & _ & RImu & _) (_ & _ & RWR)].
    destruct Rh as [_ RHQ]. destruct (RHQ m n Hq) as [(Hst & (b1 & Hb1 & H11) & Hnhi & Hnlo & _ & _ & HMAG) _].
    destruct R14 as (B1 & B2 & _ & _ & BSH & _).
    destruct (BSH c Hc) as [BSHu _].
    rewrite BT_segs in *.
    unfold T_PC, PC_SZ in *. unfold fa_beg, reginfo, region_beg, KREGION, KFAOFF, KSPACE, sh_lo, SB in *.
    replace (m + 16 - 16) with m in * by lia. replace (m + 16 - 15) with (m + 1) in * by lia.
    replace (m + 16 - 14) with (m + 2) in * by lia. replace (m + 16 - 12) with (m + 4) in * by lia.
    assert (Hb1r : 0 <= b1 < 256) by (destruct Hb1; subst; lia).
    (* [comment removed for export] *)
    assert (XZ : forall z, X z -> (0x10ab58 + 888 <= z < 0x10ab58 + 920) \/ SBEG <= z < SBEG + 2 ^ 37).
    { intros z Hz. destruct (XB_zone bt st Lc FF W z (XSUB z Hz)) as [Q | Q]; [left; unfold qhdr, IB in Q; rewrite BT_ia in Q; exact Q | right; exact Q]. }
    assert (XCH : forall z, ab <= z < ab + cs -> ~ X z).
    { intros z Hz Hx. rewrite Ecs in Hz. exact (XB_not_owned bt st Lc FF W z c ab (XSUB z Hx) Hc CVc (or_introl INQ) Hz). }
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHT : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GT0 GTC CR; lia|]. apply (rep_nolazy_thread bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    assert (NHC : forall z, CTX <= z < CTX + 65536 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GC0 GCC CR; lia|]. apply (rep_nolazy_tctx bt st Lc FF M0 mdl W RP). exact Hz. }
    assert (NHR : forall z, SBEG + 2 ^ 37 <= z < SBEG + 2 ^ 37 + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz SB0 SB1 CR; lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). exact Hz. }
    assert (NHch : forall z, ab <= z < ab + cs -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz C3 C4 SB0 SB1 CR; lia|]. rewrite Ecs in Hz. exact (rep_nolazy_chunk bt st Lc FF M0 mdl W RP c ab z Hc CVc Hz). }
    assert (NHsh : forall z, 0x7fff8000 + (m + 16) / 8 <= z < 0x7fff8000 + (m + 16) / 8 + up8 n / 8 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_allowed. apply BSHu. clear - Hz SR1 SR2. lia. }
    (* [comment removed for export] *)
    pose (memD := mrestrict Hd M).
    Ltac cimg XZ SBH NHs := intros z Hz; split; [ intros Hx; destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q; lia | clear - Hz Q SBH; lia]
                                                 | apply NHs; [clear - Hz; lia | right; clear - Hz; lia] ].
    Ltac czl := first [ reflexivity | (vm_compute; discriminate) | (vm_compute; reflexivity) ].
    Ltac konstK Hd M M0 X Rc EQ0 XZ SBH NHs C := apply (cellX Hd M M0 X _ _ _ (const_cell bt _ _ _ _ Rc C) EQ0); [czl | czl | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); cimg XZ SBH NHs].
    assert (K_spb : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SBEG))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELLNB.
    assert (K_rib : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 48)) 8 = Some (LE8 (Z_to_bv 64 (SBEG + 2 ^ 37)))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_rib.
    assert (K_magc : rdn BSEGS memD (Z_to_bv 64 0x103b0) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_magic.
    assert (K_gsh : rdn BSEGS memD (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_gsh.
    assert (K_sh : rdn BSEGS memD (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000))).
    { apply (cellX Hd M M0 X _ _ _ Csb EQ0); [czl | czl | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); cimg XZ SBH NHs]. }
    assert (K_gmb : rdn BSEGS memD (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_gmb.
    assert (K_mb : rdn BSEGS memD (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_mb.
    assert (K_gme : rdn BSEGS memD (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_gme.
    assert (K_me : rdn BSEGS memD (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 (Z_to_bv 64 MIDEND))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_me.
    assert (K_ghe : rdn BSEGS memD (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_ghe.
    assert (K_he : rdn BSEGS memD (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_he.
    assert (K_grm : rdn BSEGS memD (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_grm.
    assert (K_rm : rdn BSEGS memD (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_rm.
    assert (K_cpm : rdn BSEGS memD (Z_to_bv 64 0x10da1c) 1 = Some [Z_to_bv 8 CPM]).
    { rewrite <- w2b1 by (clear - Gc8; lia). konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_cpm. }
    assert (K_kif : rdn BSEGS memD (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1]).
    { rewrite <- w2b1 by (clear; lia). konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_kif. }
    assert (K_key : rdn BSEGS memD (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0)).
    { replace (at_ (Z_to_bv 64 0x10da20) 4) with (Z_to_bv 64 0x10da24 : word) by (clear - HSr; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity). konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_key. }
    subst TP. cbn [ia_tp both_addrs] in CELL_tsdp, Gc9, Gc10.
    assert (Utp : U (getr R 4) = 0x641380) by (rewrite R4; vm_compute; reflexivity).
    assert (K_tsdp : rdn BSEGS memD (at_ (getr R 4) (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP))).
    { replace (at_ (getr R 4) (-88)) with (Z_to_bv 64 (0x641380 - 88) : word) by (clear - Utp; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite Utp; unorm; reflexivity).
      konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_tsdp. }
    assert (K_tctx : rdn BSEGS memD (Z_to_bv 64 TSDP) 8 = Some (LE8 (Z_to_bv 64 CTX))).
    { apply (cellX Hd M M0 X _ _ _ (const_cell bt _ _ _ _ Rc CELL_tctx) EQ0); [clear - Gc1; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Gc2; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q G_tsdp; lia | clear - Hz Q SBH Gc2; lia].
      - apply NHs; [clear - Hz Gc1 Gc2; lia | right; clear - Hz Gc1 Gc2; lia]. }
    assert (K_thr : rdn BSEGS memD (at_ (Z_to_bv 64 CTX) 152) 8 = Some (LE8 (Z_to_bv 64 T))).
    { replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152) : word) by (clear - GC0 GCC CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply (cellX Hd M M0 X _ _ _ Tback EQ0); [clear - GC0; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GCC CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q GCI; lia | clear - Hz Q SPC; lia].
      - apply NHC. clear - Hz. lia. }
    assert (K_au : rdn BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c + 48)) 8 = Some (LE8 (Z_to_bv 64 (r_mapped_user (a_reg st c))))).
    { apply (cellX Hd M M0 X _ _ _ RImu EQ0); [clear - SB0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - SB1 Hc CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q SBH Hc; lia | clear - Hz Q Hc; lia].
      - apply NHR. clear - Hz Hc. lia. }
    assert (K_mx : rdn BSEGS memD (Z_to_bv 64 (T + 208 + 80 * c + 4)) 4 = Some (LE4 (cache_max c))).
    { apply (cellX Hd M M0 X _ _ _ PCmax EQ0); [clear - GT0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC Hc CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q GTI Hc; lia | clear - Hz Q SPT Hc; lia].
      - apply NHT. clear - Hz Hc. lia. }
    assert (K_cnt : rdn BSEGS memD (Z_to_bv 64 (T + 208 + 80 * c)) 4 = Some (LE4 (Z.of_nat (length (a_cache st c))))).
    { apply (cellX Hd M M0 X _ _ _ PCcnt EQ0); [clear - GT0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC Hc CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q GTI Hc; lia | clear - Hz Q SPT Hc; lia].
      - apply NHT. clear - Hz Hc. lia. }
    assert (K_magic : ab <> m -> rdn BSEGS memD (Z_to_bv 64 ab) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9))).
    { intros NE. pose proof (rz_16_32 (rz n) RM ltac:(clear - RZ; lia)) as RZC. destruct (HMAG ltac:(clear - NE Em RZC; lia)) as [MG _]. replace (m + 16 - rz n) with ab in MG by (clear - Em; lia).
      apply (cellX Hd M M0 X _ _ _ MG EQ0); [clear - C3 SB0; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - C4 SB1 CR CS1; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split; [apply XCH | apply NHch]; clear - Hz CS1; lia. }
    assert (OFFm : forall z, m <= z < m + 8 -> ~ X z /\ Hd (Z_to_bv 64 z) = false).
    { intros z Hz. split; [apply XCH | apply NHch]; clear - Hz Em RZ G5 QR3; lia. }
    assert (Kh0 : rdn BSEGS memD (Z_to_bv 64 m) 1 = Some [Z_to_bv 8 3]).
    { rewrite <- w2b1 by (clear; lia). apply (cellX Hd M M0 X _ _ _ Hst EQ0); [clear - C3 SB0 Em RZ; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - C4 SB1 CR Em Hrz; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFm. clear - Hz. lia. }
    assert (Kh1 : rdn BSEGS memD (Z_to_bv 64 (m + 1)) 1 = Some [Z_to_bv 8 b1]).
    { rewrite <- w2b1 by (clear - Hb1r; lia). apply (cellX Hd M M0 X _ _ _ H11 EQ0); [clear - C3 SB0 Em RZ; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - C4 SB1 CR Em Hrz; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFm. clear - Hz. lia. }
    assert (Kh2 : rdn BSEGS memD (Z_to_bv 64 (m + 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32)))).
    { apply (cellX Hd M M0 X _ _ _ Hnhi EQ0); [clear - C3 SB0 Em RZ; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - C4 SB1 CR Em Hrz; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFm. clear - Hz. lia. }
    assert (K_nlo : rdn BSEGS memD (Z_to_bv 64 (m + 4)) 4 = Some (LE4 (n mod 2 ^ 32))).
    { apply (cellX Hd M M0 X _ _ _ Hnlo EQ0); [clear - C3 SB0 Em RZ; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - C4 SB1 CR Em Hrz; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFm. clear - Hz. lia. }
    set (h2 := Z_to_bv 8 (U (Z_to_bv 64 (n / 2 ^ 32)))). set (h3 := Z_to_bv 8 (Z.shiftr (U (Z_to_bv 64 (n / 2 ^ 32))) 8)).
    assert (Mrng : 0 <= m /\ m + 16 < 2 ^ 64) by (clear - C3 SB0 Em RZ C4 SB1 CR Hrz; lia).
    assert (K_hdr : rdn BSEGS memD (Z_to_bv 64 m) 4 = Some [Z_to_bv 8 3; Z_to_bv 8 b1; h2; h3]).
    { change 4%nat with (1 + (1 + 2))%nat.
      apply (rdn_cat BSEGS memD _ 1 3 [Z_to_bv 8 3]); [exact Kh0 | | clear - Mrng; wd_ulia].
      replace (at_ (Z_to_bv 64 m) (Z.of_nat 1)) with (Z_to_bv 64 (m + 1)) by (clear - Mrng; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply (rdn_cat BSEGS memD _ 1 2 [Z_to_bv 8 b1]); [exact Kh1 | | clear - Mrng; wd_ulia].
      replace (at_ (Z_to_bv 64 (m + 1)) (Z.of_nat 1)) with (Z_to_bv 64 (m + 2)) by (clear - Mrng; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      exact Kh2. }
    (* [comment removed for export] *)
    assert (TDEF : forall i, T <= i < T + 4096 -> memD (Z_to_bv 64 i) <> None).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite mrestrict_off by (apply NHT; exact Hi). apply GR0. apply (writableZ_def M0 _ _ _ TW). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hi. }
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 2840)) 8) as (bf0 & Cf0 & Lf0);
      [intros i Hi; apply TDEF; clear - Hi GT0 GTC CR; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 2848)) 8) as (bf1 & Cf1 & Lf1);
      [intros i Hi; apply TDEF; clear - Hi GT0 GTC CR; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 2784)) 8) as (bst & Cst & Lst);
      [intros i Hi; apply TDEF; clear - Hi GT0 GTC CR; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 208 + 80 * c + 8)) 8) as (bcs & Ccs & Lcs);
      [intros i Hi; apply TDEF; clear - Hi GT0 GTC CR Hc; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR Hc; wd_ulia |].
    (* [comment removed for export] *)
    assert (K_cache : rdn BSEGS memD (at_ S (-2392)) 8 = Some (LE8 (Z_to_bv 64 (T + 208)))).
    { (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite rdn_mrestrict; [exact CCB | clear - HSr Slo Shi CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      rewrite at_u by (clear - HSr Slo Shi CR; lia). apply hid_off_of. intros z Hz. split; [clear - Hz HSr Slo Shi CR; lia | apply NHs; [clear - Hz HSr Slo Shi CR; lia | left; clear - Hz Slo; lia]]. }
    (* [comment removed for export] *)
    assert (SOKstk : store_ok BSEGS memD (at_ S (-2512)) 112 = true).
    { replace (at_ S (-2512)) with (Z_to_bv 64 (U S - 2512) : word) by (clear - HSr Slo Shi CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - Slo CR; lia | clear - HSr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - apply (SOK (Z_to_bv 64 z)). clear - Hz HSr Slo CR. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hz. unorm. lia.
      - apply NHs; [clear - Hz HSr Slo CR; lia | left; clear - Hz Slo; lia]. }
    assert (RWlo : SBEG + c * 2 ^ 32 <= ab /\ ab + cs <= SBEG + c * 2 ^ 32 + r_mapped_user (a_reg st c) /\ SBEG + c * 2 ^ 32 + r_mapped_user (a_reg st c) < 2 ^ 64).
    { clear - C1 C2 Q3 Q2 SB1 CR Hc. lia. }
    assert (SOKhdr : store_ok BSEGS memD (Z_to_bv 64 m) 4 = true).
    { apply (sokX Hd M M0 _ _ m 4 RWR GR0); [clear - RWlo Em RZ; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - RWlo Em G5 QR3; lia | clear - RWlo; lia | clear - Mrng; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFm. clear - Hz. lia. }
    assert (SOKab : ab <> m -> store_ok BSEGS memD (Z_to_bv 64 ab) 8 = true).
    { intros NE. apply (sokX Hd M M0 _ _ ab 8 RWR GR0); [clear - RWlo; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - RWlo CS1; lia | clear - RWlo; lia | clear - C3 SB0; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply NHch. clear - Hz CS1. lia. }
    assert (SHB : 0x2008fff7000 <= 0x7fff8000 + (m + 16) / 8 /\ 0x7fff8000 + (m + 16) / 8 + up8 n / 8 <= 0x10007fff8000).
    { clear - SR3 SR4 Em RZ C3 SBH N8le C4 SB1 CR. lia. }
    assert (SOKsh : store_ok BSEGS memD (Z_to_bv 64 (AsRtPoison.shad (Z_to_bv 64 (m + 16)))) (Z.to_nat (up8 n / 8)) = true).
    { replace (AsRtPoison.shad (Z_to_bv 64 (m + 16))) with (0x7fff8000 + (m + 16) / 8) by (clear - Mrng; (lazymatch goal with |- ?G => let G' := eval unfold AsRtPoison.shad in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - SHB; lia | rewrite Z2Nat.id by (clear - SR4 U8b; lia); clear - SHB; lia |].
      rewrite Z2Nat.id by (clear - SR4 U8b; lia). intros z Hz. split; [| apply NHsh; exact Hz].
      apply GR0. apply SHM. (lazymatch goal with |- ?G => let G' := eval unfold shmaps, AS_GAPHI, AS_GAPLO, AS_LO, AS_HEAPLO in G in change_no_check G' end). right. clear - Hz SHB. lia. }
    unfold PG in TW.
    assert (SOKT : store_ok BSEGS memD (Z_to_bv 64 T) (Z.to_nat 4096) = true).
    { apply (sokX Hd M M0 _ _ T _ TW GR0); [clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | clear - GTC CR; lia | clear - GT0; lia |].
      intros z Hz. apply NHT. clear - Hz. cbn in Hz. lia. }
    (* [comment removed for export] *)
    subst cs.
    set (hdr := [Z_to_bv 8 3; Z_to_bv 8 b1; h2; h3]).
    pose proof (bytes_le_to_Z_bound hdr) as Bhv. cbn [length hdr] in Bhv. pose proof (bytes_le_to_Z_nonneg hdr) as Bhv0.
    assert (P_hv : bytes_le_to_Z [Z_to_bv 8 3; Z_to_bv 8 b1; h2; h3] = U (Z_to_bv 64 (bytes_le_to_Z hdr))) by (clear - Bhv Bhv0; unorm; reflexivity).
    assert (P_GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (clear - Slo Shi CR; lia).
    assert (P_Gspb : 0x10007fff8000 <= SBEG /\ SBEG + 2 ^ 37 < 2 ^ 47) by (clear - SBH SB1 CR; lia).
    assert (P_Gm : m = SBEG + c * 2 ^ 32 + d /\ 0 <= d < 2 ^ 32 /\ 1 <= c <= 30) by (unfold d in *; clear - Hd32 Hc; lia).
    assert (P_Gm2 : m + 16 + up8 n <= U S - 3584 /\ m mod 16 = 0) by (split; [clear - N8le C4 SB1 Slo; lia | exact M16]).
    assert (P_Gab : SBEG + c * 2 ^ 32 + d / csize c * csize c = m \/ SBEG + c * 2 ^ 32 + d / csize c * csize c + 16 <= m).
    { rewrite Eabm. pose proof (rz_16_32 (rz n) RM ltac:(clear - RZ; lia)) as RZC. clear - RZC Em. lia. }
    assert (P_Gab8 : (SBEG + c * 2 ^ 32 + d / csize c * csize c) mod 8 = 0) by (rewrite Eabm; apply mod16_8; exact C5).
    assert (P_Grib : AIMGHI <= SBEG + 2 ^ 37 /\ SBEG + 2 ^ 37 + 4096 <= U S - 3584) by (clear - SBH SB1 Slo; lia).
    assert (P_Gau : (d / csize c + 1) * csize c <= r_mapped_user (a_reg st c) /\ r_mapped_user (a_reg st c) < 2 ^ 64) by (rewrite Eidx; clear - Hj1 Q3 RWlo SB0 Hc; lia).
    assert (P_Gn : 1 <= n <= 2 ^ 28) by (clear - QR3 N64; lia).
    assert (P_Gn8 : AsRtRegion.down8 (n + 7) = up8 n /\ n <= up8 n <= n + 7 /\ up8 n mod 8 = 0 /\ 8 <= up8 n) by (split; [apply down8_up8K | clear - U8a U8b U8c U8d; lia]).
    assert (P_GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0).
    { split; [exact GT4|]. split; [split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - GTI GTB; lia | clear - GTC Slo; lia] | exact T16]. }
    assert (P_GabT : m + 16 + up8 n <= T \/ T + 4096 <= SBEG + c * 2 ^ 32 + d / csize c * csize c) by (rewrite Eabm; clear - SPT N8le C3 C4; lia).
    assert (P_Gctx : 1 <= CTX /\ CTX + 4096 <= U S - 3584) by (clear - GC0 GCC Slo; lia).
    assert (P_Gctxm : CTX + 4096 <= SBEG + c * 2 ^ 32 + d / csize c * csize c \/ m + 16 + up8 n <= CTX) by (rewrite Eabm; clear - SPC N8le C3 C4; lia).
    assert (P_Gctxs : CTX + 4096 <= 0x7fff8000 \/ 0x10007fff8000 <= CTX) by (clear - GCB; lia).
    assert (P_Gtp : AIMGLO + 88 <= U (getr R 4) /\ U (getr R 4) + 8 <= AIMGHI) by (rewrite Utp; clear; lia).
    assert (P_Gtsdp : AIMGLO <= U (Z_to_bv 64 TSDP) /\ U (Z_to_bv 64 TSDP) + 8 <= AIMGHI) by (clear - Gc1 Gc2; wd_ulia).
    assert (P_Gcnt : 0 <= Z.of_nat (length (a_cache st c)) < cache_max c /\ cache_max c <= 16) by (clear - ROOM; unfold cache_max, cache_hint in *; lia).
    assert (P_cpm1 : U (Z_to_bv 8 CPM) <> 0) by (clear - Gc8; rewrite (Z_to_bv_small 8 CPM ltac:(change (bv_modulus 8) with 256; lia)); lia).
    assert (P_magic : SBEG + c * 2 ^ 32 + d / csize c * csize c <> m -> rdn BSEGS memD (Z_to_bv 64 (SBEG + c * 2 ^ 32 + d / csize c * csize c)) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9))) by (rewrite Eabm; exact K_magic).
    assert (P_okab : SBEG + c * 2 ^ 32 + d / csize c * csize c <> m -> store_ok BSEGS memD (Z_to_bv 64 (SBEG + c * 2 ^ 32 + d / csize c * csize c)) 8 = true) by (rewrite Eabm; exact SOKab).
    (* [comment removed for export] *)
    destruct (rc_item_prim_run memD (seg_rom BSEGS) R S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 4) (Z_to_bv 64 TSDP)
                m SBEG c d (SBEG + 2 ^ 37) (r_mapped_user (a_reg st c)) n (up8 n) T CTX (Z.of_nat (length (a_cache st c))) (cache_max c)
                (Z_to_bv 8 b1) h2 h3 (Z_to_bv 64 (bytes_le_to_Z hdr)) (Z_to_bv 8 CPM) (Z_to_bv 64 MIDEND) bf0 bf1 bst bcs
                R1 R2 R10 R11 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                P_GS P_Gspb P_Gm P_Gm2 P_Gab P_Gab8 P_Grib P_Gau P_Gn P_Gn8 P_GT P_GabT P_Gctx P_Gctxm P_Gctxs P_Gtp P_Gtsdp P_Gcnt RET
                SOKstk SOKhdr P_okab SOKsh SOKT K_spb K_rib K_au K_magc P_magic K_hdr P_hv eq_refl K_nlo
                K_gsh K_sh K_gmb K_mb K_gme K_me K_ghe K_he K_grm K_rm K_cpm P_cpm1 K_kif K_key K_tsdp K_tctx K_thr
                Cf0 Lf0 Cf1 Lf1 K_cache K_mx K_cnt Ccs Lcs Cst Lst)
      as (rf & RUN & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z3 & Z4 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
    (* [comment removed for export] *)
    rewrite Eabm, Eidx in RUN.
    match type of RUN with msteps _ _ (mkst _ _ ?mf _) => remember mf as MF eqn:EMF end.
    assert (I_GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by exact P_GS.
    assert (I_Gm : 0x10007fff8000 <= ab /\ (ab = m \/ ab + 16 <= m) /\ m + 16 + up8 n <= U S - 3584 /\ m mod 16 = 0).
    { rewrite Eabm in P_Gab. split; [clear - C3 SBH; lia|]. split; [exact P_Gab|]. exact P_Gm2. }
    assert (I_Gn8 : 8 <= up8 n /\ up8 n mod 8 = 0 /\ up8 n <= 2 ^ 40) by (clear - U8b U8c U8d N64; lia).
    assert (I_GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)) by (destruct P_GT as (X1 & X2 & _); exact (conj X1 X2)).
    assert (I_GabT : m + 16 + up8 n <= T \/ T + 4096 <= ab) by (rewrite Eabm in P_GabT; exact P_GabT).
    assert (I_Gcnt : 0 <= Z.of_nat (length (a_cache st c)) < 16) by (clear - P_Gcnt; lia).
    match type of EMF with
    | MF = fr_item ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 ?a18 ?a19 ?a20 ?a21 ?a22 =>
        pose proof (fr_item_foot a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 I_GS I_Gm I_Gn8 I_GT I_GabT Hc I_Gcnt) as FT;
        pose proof (fr_item_grows a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22) as GRF;
        pose proof (fr_item_cnt a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 I_GS I_Gm I_Gn8 I_GT Hc I_Gcnt) as FCNT;
        pose proof (fr_item_slot a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 I_GS I_Gm I_Gn8 I_GT Hc I_Gcnt) as FSLOT;
        pose proof (fr_item_shadow a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 I_GS I_Gm I_Gn8 I_GT I_GabT Hc I_Gcnt) as FSH
    end.
    rewrite <- EMF in FT, GRF, FCNT, FSLOT, FSH.
    (* [comment removed for export] *)
    replace (0x4e8a4%bv : word) with (Z_to_bv 64 0x4e8a4 : word) in RUN by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x4e8a4) M (seg_rom BSEGS)) (@mkst fx rf ret MF (seg_rom BSEGS)) mdl).
    { apply lazy_cover_HID. } { exact B1. } { exact B2. } { exact HH. } { rewrite restrict_mkstK. exact RUN. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x4e8a4) M (seg_rom BSEGS))) with M by reflexivity.
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
    destruct SF1 as (_ & Evm1 & Elz1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh1 & _).
    set (M1 := munrestrict Hd M MF).
    assert (VIS : forall a : word, Hd a = false -> M1 a = MF a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (HIDv : forall a : word, Hd a = true -> M1 a = M a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_on; exact Ha).
    assert (MrM : forall a : word, Hd a = false -> memD a = M a) by (intros a Ha; apply mrestrict_off; exact Ha).
    assert (GR1 : mem_grows M M1).
    { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply GRF. rewrite (MrM a Eh). exact Ha. }
    assert (FOOT1 : forall a : word, M1 a <> M a ->
              (U S - 2512 <= U a < U S - 2400) \/ (m <= U a < m + 4) \/ (ab <> m /\ ab <= U a < ab + 8)
              \/ (0x7fff8000 + (m + 16) / 8 <= U a < 0x7fff8000 + (m + 16) / 8 + up8 n / 8)
              \/ (T + 208 + 80 * c <= U a < T + 208 + 80 * c + 4)
              \/ (T + 208 + 80 * c + 16 + 4 * Z.of_nat (length (a_cache st c)) <= U a < T + 208 + 80 * c + 16 + 4 * Z.of_nat (length (a_cache st c)) + 4)
              \/ (T + 2784 <= U a < T + 2792) \/ (T + 2840 <= U a < T + 2856)).
    { intros a NE. destruct (Hd a) eqn:Eh; [exfalso; apply NE; apply HIDv; exact Eh|].
      rewrite (VIS a Eh) in NE. rewrite <- (MrM a Eh) in NE. exact (FT a NE). }
    assert (DEF1 : forall a : word, M1 a <> M a -> M1 a <> None).
    { intros a NE E1. apply NE. rewrite E1. destruct (M a) eqn:E0; [|reflexivity]. exfalso.
      assert (D : M a <> None) by (rewrite E0; discriminate). apply GR1 in D. exact (D E1). }
    set (k := compact_of SBEG c ab).
    assert (Ek : k = j * csize c / 16).
    { (lazymatch goal with |- ?G => let G' := eval unfold k, compact_of, region_beg, KREGION in G in change_no_check G' end). f_equal. clear - Eab'. lia. }
    assert (Ek0 : k = compact_of SBEG c (prim_alloc_beg (m + 16) n)) by (rewrite <- Eab0; reflexivity).
    assert (HFA : forall a : word, M1 a <> M a -> foot_recycle_prim bt st m n c (U a)).
    { intros a NE. (lazymatch goal with |- ?G => let G' := eval unfold foot_recycle_prim in G in change_no_check G' end). rewrite <- Eab0. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). rewrite <- SHhi. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end).
      destruct (FOOT1 a NE) as [F|[F|[F|[F|[F|[F|[F|F]]]]]]].
      - do 5 right. clear - F Slo. lia.
      - left. clear - F Em RZ G5 QR3. lia.
      - left. clear - F CS1. lia.
      - right; left. clear - F. lia.
      - right; right; left. clear - F. lia.
      - right; right; right; left. clear - F. lia.
      - do 4 right. left. clear - F. lia.
      - do 4 right. left. clear - F. lia. }
    assert (NOX : forall a : word, M1 a <> M a -> ~ X (U a) /\ U a < U S - 2400).
    { intros a NE. destruct (FOOT1 a NE) as [F|[F|[F|[F|[F|[F|[F|F]]]]]]].
      - split; [| clear - F; lia]. intros Hx. destruct (XZ _ Hx) as [Q|Q]; [clear - F Q Slo CR; lia | clear - F Q SB1 Slo; lia].
      - split; [apply XCH; clear - F Em RZ G5 QR3; lia | clear - F P_Gm2 U8b; lia].
      - split; [apply XCH; clear - F CS1; lia | clear - F I_Gm U8b; lia].
      - split; [| clear - F SHB Slo CR; lia]. intros Hx. destruct (XZ _ Hx) as [Q|Q]; [clear - F Q SHB; lia | clear - F Q SHB SBH; lia].
      - split; [| clear - F GTC Slo Hc; lia]. intros Hx. destruct (XZ _ Hx) as [Q|Q]; [clear - F Q GTI Hc; lia | clear - F Q SPT Hc; lia].
      - split; [| clear - F GTC Slo Hc I_Gcnt; lia]. intros Hx. destruct (XZ _ Hx) as [Q|Q]; [clear - F Q GTI Hc I_Gcnt; lia | clear - F Q SPT Hc I_Gcnt; lia].
      - split; [| clear - F GTC Slo; lia]. intros Hx. destruct (XZ _ Hx) as [Q|Q]; [clear - F Q GTI; lia | clear - F Q SPT; lia].
      - split; [| clear - F GTC Slo; lia]. intros Hx. destruct (XZ _ Hx) as [Q|Q]; [clear - F Q GTI; lia | clear - F Q SPT; lia]. }
    assert (RX1 : AsAinvOpsRc73.AsAinvRepX3.RepX bt X (op_recycle_prim st c k) Lc FF M1 mdl1).
    { apply (OPS_REPX_recycle_prim_pf bt X Xd st Lc FF M M1 mdl mdl1 ba m n its rest c k qt qg W (ex_intro _ M0 (conj RP DX)) EGQ HP Ec Ek0 ROOM XSUB XQ XOBJ).
      - intros a Ha. apply GR1. exact (QDEF a Ha).
      - intros a NE. split; [left; exact (HFA a NE) | exact (DEF1 a NE)].
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end).
        eapply rd_same; [| clear - GT0 GTC CR Hc; wd_ulia_c | exact FCNT].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHT. clear - Hx GT0 GTC CR Hc. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). rewrite Ek.
        eapply rd_same; [| clear - GT0 GTC CR Hc I_Gcnt; wd_ulia_c | exact FSLOT].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHT. clear - Hx GT0 GTC CR Hc I_Gcnt. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
      - intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold FA in G in change_no_check G' end). rewrite w2b1 by (clear; lia).
        rewrite <- SHhi in Hi. unfold sh_lo, SB in Hi.
        apply heap_rdn1; [clear - Hi SHB; wd_ulia|].
        rewrite VIS by (apply NHsh; exact Hi).
        replace i with (0x7fff8000 + (m + 16) / 8 + (i - (0x7fff8000 + (m + 16) / 8))) by (clear; lia). apply FSH. clear - Hi. lia.
      - exact SBM1.
      - exact MI1. }
    apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold rc_step_post in G in change_no_check G' end). exists fx, (op_recycle_prim st c k), M1, mdl1, rf.
    split; [reflexivity|]. split; [exact HFX|]. split; [rewrite Eh1; exact HH|]. split; [exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW)|].
    split; [exact (OPS_WFq_recycle_prim_pf bt st Lc FF ba m n its rest c k qt qg W EGQ HP Ec Ek0 ROOM)|].
    split; [exact RX1|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_recycle_prim, op_qitem in G in change_no_check G' end); rewrite EGQ; reflexivity|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_recycle_prim, op_qitem in G in change_no_check G' end); rewrite EGQ; reflexivity|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_recycle_prim, op_qitem in G in change_no_check G' end); rewrite EGQ; reflexivity|].
    split; [split; [intros h HL; unfold holes_le in *; (lazymatch goal with |- ?G => let G' := eval unfold op_recycle_prim, op_qitem in G in change_no_check G' end); rewrite EGQ; exact HL
                  | exact (fk_recycle_prim_at bt st c k (touchable_carved bt st c ab Hc CVc))]|].          (* [comment removed for export] *)
    split; [intros z Hz; exact (XB_recycle_prim bt st ba (m, n) its rest c k z EGQ (XSUB z Hz))|].
    split.
    { intros a Ha. destruct (decide (M1 a = M a)) as [E|NE]; [exact E|]. exfalso. destruct (NOX a NE) as [N1 N2].
      destruct Ha as [Ha|Ha]; [exact (N1 Ha) | clear - Ha N2; lia]. }
    split.
    { intros a NE. split; [| left; exact (DEF1 a NE)]. (lazymatch goal with |- ?G => let G' := eval unfold rc_changed in G in change_no_check G' end).
      destruct (FOOT1 a NE) as [F|[F|[F|[F|[F|[F|[F|F]]]]]]].
      - left. clear - F. lia.
      - right; left. apply (quar_prim_private bt st Lc FF W m n (U a) Hq HP). rewrite <- Eab0, <- Ec. clear - F Em RZ G5 QR3. lia.
      - right; left. apply (quar_prim_private bt st Lc FF W m n (U a) Hq HP). rewrite <- Eab0, <- Ec. clear - F CS1. lia.
      - right; left. apply (quar_prim_shadow_private bt st Lc FF W m n (U a) Hq HP). rewrite <- SHhi. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end). clear - F. lia.
      - right; left. apply (OBL_rt_private_pf bt st Lc FF W (U a)). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - F Hc. lia.
      - right; left. apply (OBL_rt_private_pf bt st Lc FF W (U a)). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - F Hc I_Gcnt. lia.
      - right; left. apply (OBL_rt_private_pf bt st Lc FF W (U a)). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - F. lia.
      - right; left. apply (OBL_rt_private_pf bt st Lc FF W (U a)). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - F. lia. }
    split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz1; reflexivity|].
    split; [apply same_but_materialized_except_vm; exact SBM1|].
    apply regs_kept_intro; rewrite ?Z2, ?Z3, ?Z4, ?Z8, ?Z9, ?Z18, ?Z19, ?Z20, ?Z21, ?Z22, ?Z23, ?Z24, ?Z25, ?Z26, ?Z27; try reflexivity. symmetry; exact R2.
  Qed.
End K2.
End BoAllocFRcK2.
Module BoAllocFRcK3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFRc3c BoAllocFRc3U.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation up8 := AsAinvOpsPf3d.AsAinvFreeS.up8.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).




Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section K3.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLNB : free_cells_nb bt.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  Theorem rc_bfree_room_pf : rc_bfree_stmt bt FXOK arm_room24.
  Proof using CELLNB BT_ia BT_segs.
    (lazymatch goal with |- ?G => let G' := eval unfold rc_bfree_stmt in G in change_no_check G' end).
    intros fx X Xd qt qg st Lc FF M mdl R S ret ba rest HFX HH MW W RX EGQ ROOM XSUB XQ XOBJ QDEF
           R1 RET R2 R10 R11 R12 R13r R4 S16 Slo Shi SOK _.
    pose proof ceil_rng as CR. pose proof (u64_range S) as HSr.
    destruct RX as (M0 & RP & DX).
    assert (EQ0 : forall a : word, ~ X (U a) -> M a = M0 a).
    { intros a Ha. destruct (decide (M a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX a N))). }
    assert (GR0 : mem_grows M0 M) by (intros a Ha; destruct (decide (M a = M0 a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (DX a N))]).
    unfold free_cells_nb in CELLNB. unfold arm_room24 in ROOM.
    assert (Hnth : nth_error (a_gq st) 0 = Some (BATCH ba [])) by (rewrite EGQ; reflexivity).
    assert (Hb : In (BATCH ba []) (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite EGQ; left; reflexivity).
    pose proof (cinit_of_batch bt st Lc FF qt qg _ W Hb) as CINIT.
    destruct (batch_facts bt st Lc FF W _ Hb) as (CV & _ & B1' & B2'). cbn [ba_addr] in CV, B1', B2'.
    assert (Hc : 1 <= BATCHCLASS <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia).
    pose proof (region_facts bt st Lc FF W BATCHCLASS Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & _).
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & _ & _ & _ & _ & _ & _ & SB0 & SB1 & SBH & SB16).
    pose proof (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _).
    pose proof (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as SPT.
    destruct CV as (j & Hj0 & Hj1 & Eab). change (csize BATCHCLASS) with 8192 in Hj1, Eab.
    assert (T16 : T mod 16 = 0) by (clear - TPG; unfold PG in TPG; Z.div_mod_to_equations; lia).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    rewrite BT_ia in GTI. cbn [ia_img_lo ia_img_hi both_addrs] in GTI.
    unfold IB in *. rewrite BT_ia in *. cbn [ia_instance both_addrs] in *.
    unfold chunk_addr, fa_beg, region_beg, KREGION, KFAOFF, KSPACE, PG, AS_HEAPLO, AS_LO, PTRHI, BATCHSZ, BATCHCLASS in *.
    change (csize 24) with 8192 in *.
    set (e := j * 8192).
    assert (He : 0 <= e < 2 ^ 32 /\ ba = SBEG + 24 * 2 ^ 32 + e) by ((lazymatch goal with |- ?G => let G' := eval unfold e in G in change_no_check G' end); clear - Hj0 Hj1 Q3 Q2 Eab; lia).
    (* [comment removed for export] *)
    pose proof RP as (Rc & _ & Rt & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13 & R14 & _).
    destruct Rt as (_ & _ & _ & _ & _ & _ & _ & TPC & TW & _).
    destruct (TPC 24 ltac:(clear; lia)) as (PCcnt & PCmax & _ & _). rewrite CINIT in PCmax.
    destruct R14 as (B1 & B2 & _).
    rewrite BT_segs in *. unfold T_PC, PC_SZ, PG in *.
    assert (XZ : forall z, X z -> (0x10ab58 + 888 <= z < 0x10ab58 + 920) \/ SBEG <= z < SBEG + 2 ^ 37).
    { intros z Hz. destruct (XB_zone bt st Lc FF W z (XSUB z Hz)) as [Q | Q]; [left; unfold qhdr, IB in Q; rewrite BT_ia in Q; exact Q | right; exact Q]. }
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHT : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GT0 GTC CR; lia|]. apply (rep_nolazy_thread bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    (* [comment removed for export] *)
    pose (memD := mrestrict Hd M).
    Ltac cimg3 XZ SBH NHs := intros z Hz; split; [ intros Hx; destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q; lia | clear - Hz Q SBH; lia]
                                                  | apply NHs; [clear - Hz; lia | right; clear - Hz; lia] ].
    Ltac czl3 := first [ reflexivity | (vm_compute; discriminate) | (vm_compute; reflexivity) ].
    assert (K_spb : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SBEG))).
    { apply (cellX Hd M M0 X _ _ _ (const_cell bt _ _ _ _ Rc CELLNB) EQ0); [czl3 | czl3 | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); cimg3 XZ SBH NHs]. }
    assert (OFFT : forall z, T <= z < T + 4096 -> ~ X z /\ Hd (Z_to_bv 64 z) = false).
    { intros z Hz. split; [| apply NHT; exact Hz]. intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q GTI; lia | clear - Hz Q SPT; lia]. }
    assert (K_mx : rdn BSEGS memD (Z_to_bv 64 (T + 208 + 80 * 24 + 4)) 4 = Some (LE4 (cache_max 24))).
    { apply (cellX Hd M M0 X _ _ _ PCmax EQ0); [clear - GT0; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFT. clear - Hz. lia. }
    assert (K_cnt : rdn BSEGS memD (Z_to_bv 64 (T + 208 + 80 * 24)) 4 = Some (LE4 (Z.of_nat (length (a_cache st 24))))).
    { apply (cellX Hd M M0 X _ _ _ PCcnt EQ0); [clear - GT0; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFT. clear - Hz. lia. }
    assert (TDEF : forall i, T <= i < T + 4096 -> memD (Z_to_bv 64 i) <> None).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite mrestrict_off by (apply NHT; exact Hi). apply GR0. apply (writableZ_def M0 _ _ _ TW). exact Hi. }
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 2784)) 8) as (bst & Cst & Lst);
      [intros i Hi; apply TDEF; clear - Hi GT0 GTC CR; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 208 + 80 * 24 + 8)) 8) as (bcs & Ccs & Lcs);
      [intros i Hi; apply TDEF; clear - Hi GT0 GTC CR; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR; wd_ulia |].
    assert (SOKstk : store_ok BSEGS memD (at_ S (-2448)) 48 = true).
    { replace (at_ S (-2448)) with (Z_to_bv 64 (U S - 2448) : word) by (clear - HSr Slo Shi CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - Slo CR; lia | clear - HSr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - apply (SOK (Z_to_bv 64 z)). clear - Hz HSr Slo CR. unorm. lia.
      - apply NHs; [clear - Hz HSr Slo CR; lia | left; clear - Hz Slo; lia]. }
    assert (SOKT : store_ok BSEGS memD (Z_to_bv 64 T) (Z.to_nat 4096) = true).
    { apply (sokX Hd M M0 _ _ T _ TW GR0); [clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | clear - GTC CR; lia | clear - GT0; lia |].
      intros z Hz. apply NHT. clear - Hz. cbn in Hz. lia. }
    (* [comment removed for export] *)
    assert (P_GS : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47) by (clear - Slo Shi CR; lia).
    assert (P_GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0).
    { split; [exact GT4|]. split; [split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - GTI GTB; lia | clear - GTC Slo; lia] | exact T16]. }
    assert (P_Gspb : 0 <= SBEG /\ SBEG + 2 ^ 37 < 2 ^ 47) by (clear - SB0 SB1 CR; lia).
    assert (P_Gcnt : 0 <= Z.of_nat (length (a_cache st 24)) < cache_max 24 /\ cache_max 24 <= 16) by (clear - ROOM; unfold cache_max, cache_hint in *; lia).
    assert (P_13 : getr R 13 = Z_to_bv 64 (SBEG + 24 * 2 ^ 32 + e)) by (rewrite R13r; f_equal; clear - He; lia).
    destruct (k5_run memD (seg_rom BSEGS) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) T SBEG 24 e
                (Z.of_nat (length (a_cache st 24))) (cache_max 24) bst bcs R
                R1 R2 R10 R11 R12 P_13 eq_refl eq_refl eq_refl eq_refl eq_refl P_GS P_GT P_Gspb ltac:(clear; lia) (proj1 He) P_Gcnt RET Lst Lcs
                SOKstk SOKT K_mx K_cnt Ccs Cst K_spb)
      as (rf & RUN & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z3 & Z4 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
    match type of RUN with msteps _ _ (mkst _ _ ?mf _) => remember mf as MF eqn:EMF end.
    assert (I_GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (clear - Slo Shi CR; lia).
    assert (I_GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)) by (destruct P_GT as (X1 & X2 & _); exact (conj X1 X2)).
    assert (I_Gcnt : 0 <= Z.of_nat (length (a_cache st 24)) < 16) by (clear - P_Gcnt; lia).
    match type of EMF with
    | MF = fr_k5 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13 =>
        pose proof (fr_k5_foot a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 I_GS I_GT ltac:(clear; lia) I_Gcnt) as FT;
        pose proof (fr_k5_grows a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13) as GRF;
        pose proof (fr_k5_cnt a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 I_GS I_GT ltac:(clear; lia) I_Gcnt) as FCNT;
        pose proof (fr_k5_slot a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 I_GS I_GT ltac:(clear; lia) I_Gcnt) as FSLOT
    end.
    rewrite <- EMF in FT, GRF, FCNT, FSLOT.
    (* [comment removed for export] *)
    replace (0x4eca8%bv : word) with (Z_to_bv 64 0x4eca8 : word) in RUN by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x4eca8) M (seg_rom BSEGS)) (@mkst fx rf ret MF (seg_rom BSEGS)) mdl).
    { apply lazy_cover_HID. } { exact B1. } { exact B2. } { exact HH. } { rewrite restrict_mkstK. exact RUN. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x4eca8) M (seg_rom BSEGS))) with M by reflexivity.
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
    destruct SF1 as (_ & Evm1 & Elz1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh1 & _).
    set (M1 := munrestrict Hd M MF).
    assert (VIS : forall a : word, Hd a = false -> M1 a = MF a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (HIDv : forall a : word, Hd a = true -> M1 a = M a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_on; exact Ha).
    assert (MrM : forall a : word, Hd a = false -> memD a = M a) by (intros a Ha; apply mrestrict_off; exact Ha).
    assert (GR1 : mem_grows M M1).
    { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply GRF. rewrite (MrM a Eh). exact Ha. }
    assert (FOOT1 : forall a : word, M1 a <> M a ->
              (U S - 2448 <= U a < U S - 2400) \/ (T + 208 + 80 * 24 <= U a < T + 208 + 80 * 24 + 4)
              \/ (T + 208 + 80 * 24 + 16 + 4 * Z.of_nat (length (a_cache st 24)) <= U a < T + 208 + 80 * 24 + 16 + 4 * Z.of_nat (length (a_cache st 24)) + 4)
              \/ (T + 2784 <= U a < T + 2792)).
    { intros a NE. destruct (Hd a) eqn:Eh; [exfalso; apply NE; apply HIDv; exact Eh|].
      rewrite (VIS a Eh) in NE. rewrite <- (MrM a Eh) in NE. exact (FT a NE). }
    assert (DEF1 : forall a : word, M1 a <> M a -> M1 a <> None).
    { intros a NE E1. apply NE. rewrite E1. destruct (M a) eqn:E0; [|reflexivity]. exfalso.
      assert (D : M a <> None) by (rewrite E0; discriminate). apply GR1 in D. exact (D E1). }
    assert (Ek : compact_of SBEG 24 ba = e / 16).
    { (lazymatch goal with |- ?G => let G' := eval unfold compact_of, region_beg, KREGION in G in change_no_check G' end). f_equal. clear - He. lia. }
    assert (NOX : forall a : word, M1 a <> M a -> ~ X (U a) /\ U a < U S - 2400).
    { intros a NE. destruct (FOOT1 a NE) as [F|[F|[F|F]]].
      - split; [| clear - F; lia]. intros Hx. destruct (XZ _ Hx) as [Q|Q]; [clear - F Q Slo CR; lia | clear - F Q SB1 Slo; lia].
      - split; [apply (OFFT (U a)); clear - F; lia | clear - F GTC Slo; lia].
      - split; [apply (OFFT (U a)); clear - F I_Gcnt; lia | clear - F GTC Slo I_Gcnt; lia].
      - split; [apply (OFFT (U a)); clear - F; lia | clear - F GTC Slo; lia]. }
    assert (RX1 : AsAinvOpsRc73.AsAinvRepX3.RepX bt X (op_qbatch_free SBEG st 0) Lc FF M1 mdl1).
    { apply (OPS_REPX_qbatch_free_pf bt X Xd st Lc FF M M1 mdl mdl1 0%nat ba qt qg W (ex_intro _ M0 (conj RP DX)) Hnth ROOM XSUB XQ).
      - intros i' bp E. discriminate E.
      - intros a Ha. apply GR1. exact (QDEF a Ha).
      - intros a NE. split; [left | exact (DEF1 a NE)]. (lazymatch goal with |- ?G => let G' := eval unfold foot_qbatch_free, T_PC, PC_SZ, BATCHCLASS in G in change_no_check G' end).
        destruct (FOOT1 a NE) as [F|[F|[F|F]]]; [do 3 right; clear - F Slo; lia | left; clear - F; lia | right; left; clear - F; lia | right; right; left; clear - F; lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ, BATCHCLASS in G in change_no_check G' end).
        eapply rd_same; [| clear - GT0 GTC CR; wd_ulia_c | exact FCNT].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHT. clear - Hx GT0 GTC CR. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). change BATCHCLASS with 24. rewrite Ek.
        eapply rd_same; [| clear - GT0 GTC CR I_Gcnt; wd_ulia_c | exact FSLOT].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHT. clear - Hx GT0 GTC CR I_Gcnt. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
      - exact SBM1.
      - exact MI1. }
    apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold rc_step_post in G in change_no_check G' end). exists fx, (op_qbatch_free SBEG st 0), M1, mdl1, rf.
    split; [reflexivity|]. split; [exact HFX|]. split; [rewrite Eh1; exact HH|]. split; [exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW)|].
    split; [exact (OPS_WFq_qbatch_free_pf bt st Lc FF 0%nat ba qt qg W Hnth ROOM)|].
    split; [exact RX1|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_qbatch_free in G in change_no_check G' end); rewrite Hnth; (lazymatch goal with |- ?G => let G' := eval cbn [a_gq set_cache set_gq] in G in change_no_check G' end); rewrite EGQ; reflexivity|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_qbatch_free in G in change_no_check G' end); rewrite Hnth; reflexivity|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_qbatch_free in G in change_no_check G' end); rewrite Hnth; reflexivity|].
    split; [split; [intros h HL; unfold holes_le in *; (lazymatch goal with |- ?G => let G' := eval unfold op_qbatch_free in G in change_no_check G' end); rewrite Hnth; exact HL | apply fk_qbatch_free]|].          (* [comment removed for export] *)
    split; [intros z Hz; exact (XB_qbatch_free bt st Lc FF qt qg 0%nat ba z W Hnth (XSUB z Hz))|].
    split.
    { intros a Ha. destruct (decide (M1 a = M a)) as [E|NE]; [exact E|]. exfalso. destruct (NOX a NE) as [N1 N2].
      destruct Ha as [Ha|Ha]; [exact (N1 Ha) | clear - Ha N2; lia]. }
    split.
    { intros a NE. split; [| left; exact (DEF1 a NE)]. (lazymatch goal with |- ?G => let G' := eval unfold rc_changed in G in change_no_check G' end).
      destruct (FOOT1 a NE) as [F|[F|[F|F]]].
      - left. clear - F. lia.
      - right; left. apply (OBL_rt_private_pf bt st Lc FF W (U a)). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - F. lia.
      - right; left. apply (OBL_rt_private_pf bt st Lc FF W (U a)). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - F I_Gcnt. lia.
      - right; left. apply (OBL_rt_private_pf bt st Lc FF W (U a)). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - F. lia. }
    split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz1; reflexivity|].
    split; [apply same_but_materialized_except_vm; exact SBM1|].
    apply regs_kept_intro; rewrite ?Z2, ?Z3, ?Z4, ?Z8, ?Z9, ?Z18, ?Z19, ?Z20, ?Z21, ?Z22, ?Z23, ?Z24, ?Z25, ?Z26, ?Z27; try reflexivity. symmetry; exact R2.
  Qed.
End K3.
End BoAllocFRcK3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcM1U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcK5.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcM1U.BoAllocFRc1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRc2.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK4a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK1a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Lemma nodup_app_disj : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x ND H1 H2; [contradiction|]. cbn [app] in ND. inversion ND as [|y' l' NI ND']; subst.
  destruct H1 as [-> | H1]; [apply NI; apply in_app_iff; right; exact H2 | exact (IH l2 x ND' H1 H2)].
Qed.

Section K5.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variable MINSZ : Z.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis CELL_min : In (0x10ab58 + 800, 8%nat, MINSZ) (bt_consts bt).
  Hypothesis G_min : 0 <= MINSZ <= 2 ^ 28.
  Hypothesis HITEM : rc_item_stmt bt FXOK arm_any.
  Hypothesis HBFREE : rc_bfree_stmt bt FXOK arm_any24.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  (* [comment removed for export] *)
  Definition HYP_RECYCLE_arm (ARM : ast -> Prop) : Prop :=
    forall fx st2 Lc FF (M M0 : mem) mdl (R : bvmap 5 word) (sp ret stk : word),
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WFX bt st2 Lc FF -> a_tq st2 = [] -> 2 ^ 28 < q_bytes (a_gq st2) < 2 ^ 41 ->
      Rep bt st2 Lc FF M0 mdl -> (forall a : word, M a <> M0 a -> U a = IB bt + 881) -> M (Z_to_bv 64 (IB bt + 881)) = Some (Z_to_bv 8 1) ->
      (forall a : word, IB bt + 904 <= U a < IB bt + 912 -> M a <> None) ->
      M0 (Z_to_bv 64 (IB bt + 880)) = Some (Z_to_bv 8 0) -> M0 (Z_to_bv 64 (IB bt + 881)) = Some (Z_to_bv 8 0) ->
      getr R 1 = ret -> getr R 2 = sp ->
      getr R 10 = Z_to_bv 64 (IB bt + 728) -> getr R 12 = Z_to_bv 64 (bt_thread bt + T_PC) -> getr R 13 = stk ->
      (exists mn, getr R 11 = Z_to_bv 64 mn /\ In (IB bt + 800, 8%nat, mn) (bt_consts bt)) ->
      getr R 4 = Z_to_bv 64 (ia_tp (bt_ia bt)) ->
      U sp mod 16 = 0 -> CEIL + 1376 <= U sp -> U sp + 2224 <= PTRHI -> ret_ok ret ->
      (forall a : word, U sp - 1376 <= U a < U sp -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
      ARM st2 ->
      katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x4e404) M (seg_rom BSEGS)) mdl)
           (drain_post bt FXOK 1376 st2 Lc FF M mdl R sp ret).

  Theorem hyp_recycle_nomerge : HYP_RECYCLE_arm arm_nomerge.
  Proof using HBFREE HITEM G_min CELL_min CELLNB BT_ia BT_segs MINSZ.
    (lazymatch goal with |- ?G => let G' := eval unfold HYP_RECYCLE_arm in G in change_no_check G' end).
    intros fx st2 Lc FF M M0 mdl R sp ret stk HFX HH MW WX ETQ GQB RP DM L881 D904 D880 D881 X1 X2 X10 X12 X13 (mn & X11 & CMN) X4 SP16 SPlo SPhi RET SOK NOM.
    pose proof ceil_rng as CR. pose proof (u64_range sp) as Hsp.
    (* [comment removed for export] *)
    assert (X11' : getr R 11 = Z_to_bv 64 MINSZ).
    { rewrite X11. pose proof RP as (Rc & _). rewrite BT_segs in Rc.
      pose proof (const_cell bt _ _ _ _ Rc CMN) as C1. unfold IB in C1. rewrite BT_ia in C1. cbn [ia_instance both_addrs] in C1.
      pose proof (const_cell bt _ _ _ _ Rc CELL_min) as C2. unfold cellZ, cellN in C1, C2. rewrite C1 in C2.
      pose proof (f_equal (fun o : option (list byte) => match o with Some bs => bytes_le_to_Z bs | None => 0 end) C2) as E2. cbv beta iota in E2.
      apply bv_eq. rewrite !bytes_le_to_Z_8 in E2. exact E2. }
    apply (katD_bind BSEGS _ _ _ (rc_prefix_kat bt FXOK MINSZ BT_segs BT_ia G_min fx st2 Lc FF M M0 mdl R sp ret stk HFX HH MW WX ETQ GQB NOM RP DM L881 D904 D880 D881
                                     X1 X2 X10 X12 X13 X11' X4 SP16 SPlo SPhi RET SOK)).
    intros c1 (fx1 & M1 & mdl1 & R1 & pb0 & rest & -> & EGQ & NEpb & RESTB & INV1 & A10 & RL1 & (Fra & Fs0 & Fs1 & Fs2 & Fs3 & Fs4) & DK1 & CH1 & LZ1 & SEV1).
    set (S := at_ sp 2208) in *.
    unfold PTRHI in SPhi.
    assert (US : U S = U sp + 2208) by ((lazymatch goal with |- ?G => let G' := eval unfold S in G in change_no_check G' end); rewrite at_u by lia; reflexivity).
    assert (ES : at_ S (-2208) = sp) by (apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (S16 : U S mod 16 = 0) by (rewrite US; clear - SP16; Z.div_mod_to_equations; lia).
    assert (Slo : CEIL + 3584 <= U S) by (rewrite US; clear - SPlo; lia).
    assert (Shi : U S + 16 <= PTRHI) by ((lazymatch goal with |- ?G => let G' := eval unfold PTRHI in G in change_no_check G' end); rewrite US; clear - SPhi; lia).
    pose proof (WFX_WFq bt st2 Lc FF WX) as W2.
    apply (katD_bind BSEGS _ _ _
             (rc_batch_loop bt FXOK BT_segs BT_ia CELLNB HITEM HBFREE S (XP bt pb0) (XP_dec bt pb0) (q_bytes (a_tq st2)) (q_bytes (a_gq st2)) Lc FF st2 M1 mdl1 rest
                (Z_to_bv 64 0x4e574) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                ltac:(intros z Q; left; exact Q) S16 Slo Shi (proj2 GQB) ltac:(apply ret_ok_lit; [clear; lia | reflexivity])
                (conj (WFX_qroom bt st2 Lc FF WX) (WFX_kact bt st2 Lc FF WX))
                pb0 fx1 st2 M1 mdl1 R1 NEpb INV1 A10 ltac:(intros b z Hb Hz; right; exists b; split; [exact Hb | exact Hz]))).
    intros c2 (fx2 & st3 & M3 & mdl3 & R3 & -> & HFX3 & HH3 & MW3 & W3 & RX3 & EGQ3 & XSUB3 & QDEF3 & ACC3 & REGS3 & DK3 & KEPT3).
    destruct REGS3 as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25).
    destruct ACC3 as (ETQ3 & EKA3 & HO3 & XK3 & CHA3 & LZ3 & SEV3).
    pose proof RX3 as (M03 & RP3 & DX3).
    pose proof RP3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13 & (_ & MI3 & _) & _).
    (* [comment removed for export] *)
    assert (NHs3 : forall z, 0 <= z < 2 ^ 64 -> CEIL <= z -> HID st3 mdl3 (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st3 mdl3 z R13 Hz). left. exact Hr. }
    assert (FRC : forall kk v, -2256 <= kk -> kk + 8 <= -2208 -> rdn BSEGS M1 (at_ S kk) 8 = Some v -> rdn BSEGS (mrestrict (HID st3 mdl3) M3) (at_ S kk) 8 = Some v).
    { intros kk v Hk1 Hk2 Hr. rewrite rdn_mrestrict; [| clear - Hk1 Hk2 US Hsp SPhi Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      - eapply rd_same; [| clear - Hk1 Hk2 US Hsp SPhi Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
        intros x Hx. apply KEPT3. clear - Hx Hk1 Hk2 US Hsp SPhi Slo CR. rewrite at_u in Hx by lia. cbn in Hx. lia.
      - rewrite at_u by (clear - Hk1 Hk2 US Hsp SPhi Slo CR; lia). apply hid_off_of. intros z Hz. split; [clear - Hz Hk1 Hk2 US Hsp SPhi Slo CR; lia | apply NHs3; clear - Hz Hk1 Hk2 US Hsp SPhi Slo CR; lia]. }
    destruct (rc_epilogue (mrestrict (HID st3 mdl3) M3) (seg_rom BSEGS) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) R3 Y2 RET
                (FRC (-2216) _ ltac:(clear; lia) ltac:(clear; lia) Fra) (FRC (-2224) _ ltac:(clear; lia) ltac:(clear; lia) Fs0) (FRC (-2232) _ ltac:(clear; lia) ltac:(clear; lia) Fs1)
                (FRC (-2240) _ ltac:(clear; lia) ltac:(clear; lia) Fs2) (FRC (-2248) _ ltac:(clear; lia) ltac:(clear; lia) Fs3) (FRC (-2256) _ ltac:(clear; lia) ltac:(clear; lia) Fs4))
      as (r9 & RUN9 & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z3 & Z4 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
    replace (0x4e574%bv : word) with (Z_to_bv 64 0x4e574 : word) in RUN9 by (apply bv_eq; reflexivity).
    apply (katD_loadsX bt BT_ia fx2 st3 Lc FF M3 M03 mdl3 R3 r9 _ _ _ RP3 HH3 RUN9). intros mdl9 RP9 HH9 SBM9.
    pose proof RP9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & MI9 & _) & _).
    pose proof (same_but_materialized_frame mdl3 mdl9 SBM9) as (_ & _ & Elz9 & _).
    (* [comment removed for export] *)
    assert (XQ : forall z, qhdr bt z -> XP bt pb0 z) by (intros z Q; left; exact Q).
    assert (RL3 : rep_list bt M3 (IB bt + 888) (a_gq st3)).
    { rewrite EGQ3. destruct RL1 as (L1 & L2 & L3 & L4). pose proof (thread_dyn bt st2 Lc FF W2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
      assert (QK : forall i, IB bt + 888 <= i < IB bt + 920 -> M3 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)).
      { intros i Hi. apply XK3. left. (lazymatch goal with |- ?G => let G' := eval unfold qhdr in G in change_no_check G' end). unfold IB in *. rewrite BT_ia in *. cbn [ia_instance both_addrs] in *. clear - Hi. unorm. lia. }
      (lazymatch goal with |- ?G => let G' := eval unfold rep_list in G in change_no_check G' end). unfold IB in *. rewrite BT_ia in *. cbn [ia_instance both_addrs] in *.
      split; [eapply cellZ_frame; [exact L1 | clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply QK; clear - Hi; cbn in Hi; lia]|].
      split; [eapply cellZ_frame; [exact L2 | clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply QK; clear - Hi; cbn in Hi; lia]|].
      split; [eapply cellZ_frame; [exact L3 | clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply QK; clear - Hi; cbn in Hi; lia]|].
      eapply cellZ_frame; [exact L4 | clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply QK; clear - Hi; cbn in Hi; lia]. }
    assert (RX9 : AsAinvOpsRc73.AsAinvRepX3.RepX bt (XP bt pb0) st3 Lc FF M3 mdl9) by (exists M03; split; [exact RP9 | exact DX3]).
    pose proof (RepX_resync_qhdr bt (XP bt pb0) st3 Lc FF M3 mdl9 _ _ W3 RX9 RL3 QDEF3) as RXq.
    assert (NDgq : List.NoDup (map ba_addr (pb0 ++ rest))).
    { pose proof W2 as (_ & _ & (_ & _ & _ & _ & ND & _) & _). rewrite ETQ, EGQ in ND. exact ND. }
    assert (REP9 : Rep bt st3 Lc FF M3 mdl9).
    { apply (RepX_close bt _ st3 Lc FF M3 mdl9 W3 RXq). intros z ([Q | (b & Hb & Hz)] & NQ) RCELL; [exact (NQ Q)|].
      destruct (XSUB3 z ltac:(right; exists b; split; [exact Hb | exact Hz])) as [Q | (a & (CVa & KIND) & Ha)]; [exact (NQ Q)|].
      (* [comment removed for export] *)
      destruct (batch_facts bt st2 Lc FF W2 b ltac:(apply in_app_iff; right; rewrite EGQ; apply in_app_iff; left; exact Hb)) as ((jb & Hjb0 & _ & Ejb) & _).
      destruct CVa as (ja & Hja0 & Hja1 & Eja). unfold chunk_addr in Ejb, Eja. change (csize BATCHCLASS) with 8192 in Ejb, Eja. unfold BATCHSZ in Hz, Ha.
      assert (Eab : a = ba_addr b) by (clear - Ejb Eja Hz Ha; lia).
      destruct KIND as [(b' & Hb' & Eb') | KIND].
      - (* [comment removed for export] *)
        rewrite ETQ3, ETQ, EGQ3 in Hb'. cbn [app] in Hb'.
        apply (nodup_app_disj (map ba_addr pb0) (map ba_addr rest) (ba_addr b)); [rewrite <- map_app; exact NDgq | apply in_map; exact Hb |].
        rewrite <- Eab, <- Eb'. apply in_map. exact Hb'.
      - exact (XB_free_not_cells bt st3 Lc FF _ _ a z W3 (ex_intro _ ja (conj Hja0 (conj Hja1 Eja))) KIND ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); exact Ha) RCELL). }
    assert (WF9 : WF bt st3 Lc FF).
    { (lazymatch goal with |- ?G => let G' := eval unfold WF in G in change_no_check G' end). apply (WFq_mono_bytes bt st3 Lc FF _ _ _ _ W3); [rewrite ETQ3, ETQ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia | rewrite EGQ3; clear - RESTB G_min; lia]. }
    (* [comment removed for export] *)
    apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold drain_post in G in change_no_check G' end). exists fx2, st3, M3, mdl9, r9.
    split; [reflexivity|]. split; [exact HFX3|]. split; [exact HH9|]. split; [exact WF9|]. split; [exact REP9|]. split; [exact EKA3|]. split; [exact HO3|].
    split.
    { intros a NE. destruct (decide (M3 a = M1 a)) as [E | N].
      - rewrite E in NE |- *. destruct (CH1 a NE) as [C D]. split; [| left; exact D]. (lazymatch goal with |- ?G => let G' := eval unfold drain_changed in G in change_no_check G' end).
        destruct C as [C | [C | C]]; [left; clear - C US; lia | right; left; exact C | right; right; exact C].
      - destruct (CHA3 a N) as [C D]. split; [| exact D]. unfold acc_changed in C. (lazymatch goal with |- ?G => let G' := eval unfold drain_changed in G in change_no_check G' end).
        destruct C as [C | [C | C]]; [left; clear - C US; lia | right; left; exact C | right; right; exact C]. }
    split.
    { intros a Ha. transitivity (lzb mdl3 a); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz9; reflexivity|]. transitivity (lzb mdl1 a); [exact (LZ3 a Ha) | exact (LZ1 a Ha)]. }
    split.
    { destruct DK1 as (K3 & K4 & K26 & K27). destruct DK3 as (L3 & L4 & L26 & L27).
      apply regs_kept_intro; rewrite ?Z2, ?Z3, ?Z4, ?Z8, ?Z9, ?Z18, ?Z19, ?Z20, ?Z21, ?Z22, ?Z23, ?Z24, ?Z25, ?Z26, ?Z27,
                                     ?Y21, ?Y22, ?Y23, ?Y24, ?Y25, ?L3, ?L4, ?L26, ?L27, ?K3, ?K4, ?K26, ?K27; try reflexivity.
      rewrite ES. symmetry. exact X2. }
    split; [| exact (model_ivs_wf_sbm mdl3 mdl9 SBM9 MW3)].
    eapply same_except_vm_trans; [exact SEV1|]. eapply same_except_vm_trans; [exact SEV3 | apply same_but_materialized_except_vm; exact SBM9].
  Qed.

  (* [comment removed for export] *)
  Hypothesis HYP_MERGE : HYP_RECYCLE_arm (fun st => ~ arm_nomerge st).

  Theorem hyp_recycle_pf : HYP_RECYCLE_stmt bt FXOK 1376.
  Proof using HYP_MERGE HBFREE HITEM G_min CELL_min CELLNB BT_ia BT_segs MINSZ.
    (lazymatch goal with |- ?G => let G' := eval unfold HYP_RECYCLE_stmt in G in change_no_check G' end).
    intros fx st2 Lc FF M M0 mdl R sp ret stk A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24.
    assert (DEC : arm_nomerge st2 \/ ~ arm_nomerge st2).
    { (lazymatch goal with |- ?G => let G' := eval unfold arm_nomerge in G in change_no_check G' end). destruct (Z_le_dec (q_bytes (a_gq st2)) (8192 * Z.of_nat (length (a_gq st2)))) as [L | L]; [left; left; exact L|].
      destruct (Z_le_dec (1638400 * Z.of_nat (length (a_gq st2))) (100 * q_bytes (a_gq st2))) as [L2 | L2]; [left; right; exact L2 | right; intros [X | X]; [exact (L X) | exact (L2 X)]]. }
    destruct DEC as [NM | MG].
    - exact (hyp_recycle_nomerge fx st2 Lc FF M M0 mdl R sp ret stk A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 NM).
    - exact (HYP_MERGE fx st2 Lc FF M M0 mdl R sp ret stk A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 MG).
  Qed.
End K5.
End BoAllocFRcK5.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc43 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRtPriv3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcK6b.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4U OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p.BoAllocFRc4V.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc43 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRtPriv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK6a.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation up8 := AsAinvOpsPf3d.AsAinvFreeS.up8.

Section K6B.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variable TSDP : Z.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis RCF : rc_cells_full bt.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  Theorem rc_bfree_full_room_pf : rc_bfree_stmt bt FXOK arm_full24_room.
  Proof using RCF RCC CELLNB BT_ia BT_segs TSDP.
    (lazymatch goal with |- ?G => let G' := eval unfold rc_bfree_stmt in G in change_no_check G' end).
    intros fx X Xd qt qg st Lc FF M mdl R S ret ba rest HFX HH MW W RX EGQ (FULL & FAR) XSUB XQ XOBJ QDEF
           R1 RET R2 R10 R11 R12 R13r R4 S16 Slo Shi SOK _.
    pose proof ceil_rng as CR. pose proof (u64_range S) as HSr.
    pose proof RX as (M0 & RP & DX).
    assert (EQ0 : forall a : word, ~ X (U a) -> M a = M0 a).
    { intros a Ha. destruct (decide (M a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX a N))). }
    assert (GR0 : mem_grows M0 M) by (intros a Ha; destruct (decide (M a = M0 a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (DX a N))]).
    unfold free_cells_nb in CELLNB. unfold arm_full24 in FULL. unfold fa_room in FAR.
    destruct RCC as (CELL_rib & _ & _). destruct RCF as (CELL_int & CELL_gpg & CELL_pg & CELL_470).
    assert (Hnth : nth_error (a_gq st) 0 = Some (BATCH ba [])) by (rewrite EGQ; reflexivity).
    assert (Hb : In (BATCH ba []) (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite EGQ; left; reflexivity).
    pose proof (cinit_of_batch bt st Lc FF qt qg _ W Hb) as CINIT.
    destruct (batch_facts bt st Lc FF W _ Hb) as (CV & _ & B1' & B2'). cbn [ba_addr] in CV, B1', B2'.
    assert (Hc : 1 <= BATCHCLASS <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia).
    pose proof W as (_ & WC & _). destruct (WC BATCHCLASS Hc) as (CLEN & _ & CKS). clear WC.
    pose proof (region_facts bt st Lc FF W BATCHCLASS Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & _ & _ & _ & _ & _ & _ & SB0 & SB1 & SBH & SB16).
    pose proof (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _).
    pose proof (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as SPT.
    destruct CV as (j & Hj0 & Hj1 & Eab). change (csize BATCHCLASS) with 8192 in Hj1, Eab.
    assert (T16 : T mod 16 = 0) by (clear - TPG; unfold PG in TPG; Z.div_mod_to_equations; lia).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    assert (SB8 : SBEG mod 8 = 0) by (clear - SB16; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    change (cache_max BATCHCLASS) with 2 in *. change (2 / 2) with 1 in FAR.
    set (ks := skipn (Z.to_nat (Z.of_nat (length (a_cache st BATCHCLASS)) - 1)) (a_cache st BATCHCLASS)).
    assert (LEN : Z.of_nat (length (a_cache st BATCHCLASS)) = 2) by (clear - FULL CLEN; lia).
    assert (LKS : Z.of_nat (length ks) = 1) by ((lazymatch goal with |- ?G => let G' := eval unfold ks in G in change_no_check G' end); rewrite length_skipn; clear - LEN; lia).
    assert (FKS : Forall (fun k => 0 <= k < 2 ^ 31) ks).
    { apply Forall_forall. intros k Hk. assert (Hin : In k (a_cache st BATCHCLASS)) by (unfold ks in Hk; rewrite <- (firstn_skipn (Z.to_nat (Z.of_nat (length (a_cache st BATCHCLASS)) - 1)) (a_cache st BATCHCLASS)); apply in_or_app; right; exact Hk).
      destruct (CKS k Hin) as (Kr & CVk). destruct (carved_range bt st Lc FF W BATCHCLASS _ Hc CVk) as (C1 & C2 & _).
      change (csize BATCHCLASS) with 8192 in C2. unfold chunk_of_compact, fa_beg, region_beg, KREGION, KFAOFF in *. clear - C1 C2 Q2 Q3 Kr. lia. }
    (* [comment removed for export] *)
    set (st1 := op_drain_top st BATCHCLASS 1).
    assert (W1 : WFq bt st1 Lc FF qt qg) by (apply (OPS_WFq_drain_top_pf bt st Lc FF BATCHCLASS 1 qt qg W Hc); [clear - LEN; lia | exact FAR]).
    assert (GQ1 : a_gq st1 = a_gq st) by reflexivity.
    assert (CA1 : a_cache st1 BATCHCLASS = firstn (Z.to_nat (Z.of_nat (length (a_cache st BATCHCLASS)) - 1)) (a_cache st BATCHCLASS)).
    { (lazymatch goal with |- ?G => let G' := eval unfold st1, op_drain_top in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache set_reg] in G in change_no_check G' end). apply fupdZ_same. }
    assert (LEN1 : Z.of_nat (length (a_cache st1 BATCHCLASS)) = 1) by (rewrite CA1, length_firstn; clear - LEN; lia).
    rewrite BT_ia in GTI. cbn [ia_img_lo ia_img_hi both_addrs] in GTI.
    unfold IB in *. rewrite BT_ia in *. cbn [ia_instance both_addrs] in *.
    (* [comment removed for export] *)
    pose proof RP as (Rc & _ & Rt & Rr & _ & _ & _ & _ & _ & _ & _ & _ & R13 & R14 & _).
    destruct Rt as (_ & _ & _ & _ & _ & _ & _ & TPC & TW & _).
    destruct (TPC BATCHCLASS Hc) as (PCcnt & PCmax & _ & PCks). rewrite CINIT in PCmax.
    destruct (Rr BATCHCLASS Hc) as [(RImu & _ & RInf & RImfa & _ & _ & _ & _ & _ & RIW) (_ & FAW & _)].
    destruct R14 as (B1 & B2 & _).
    rewrite BT_segs in *. 
    set (nf := Z.of_nat (length (r_free (a_reg st BATCHCLASS)))) in *.
    unfold T_PC, PC_SZ, PG in *.
    unfold reginfo, chunk_addr, fa_beg, region_beg, KREGION, KFAOFF, KSPACE, PG, AS_HEAPLO, AS_LO, PTRHI, BATCHSZ in *.
    change (cache_max BATCHCLASS) with 2 in *. change BATCHCLASS with 24 in *. change (csize 24) with 8192 in *.
    set (e := j * 8192).
    assert (He : 0 <= e < 2 ^ 32 /\ ba = SBEG + 24 * 2 ^ 32 + e) by ((lazymatch goal with |- ?G => let G' := eval unfold e in G in change_no_check G' end); clear - Hj0 Hj1 Q3 Q2 Eab; lia).
    assert (NF0 : 0 <= nf) by ((lazymatch goal with |- ?G => let G' := eval unfold nf in G in change_no_check G' end); lia).
    assert (XZ : forall z, X z -> (0x10ab58 + 888 <= z < 0x10ab58 + 920) \/ SBEG <= z < SBEG + 2 ^ 37).
    { intros z Hz. destruct (XB_zone bt st Lc FF W z (XSUB z Hz)) as [Q | Q]; [left; unfold qhdr, IB in Q; rewrite BT_ia in Q; exact Q | right; exact Q]. }
    assert (NXF : forall z, foot_drain_top bt st 24 1 z -> ~ X z).
    { intros z Hf Hx. exact (foot_drain_top_not_XB bt st Lc FF qt qg 24 1 z W Hc ltac:(clear; lia) FAR Hf (XSUB z Hx)). }
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHT : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GT0 GTC CR; lia|]. apply (rep_nolazy_thread bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    assert (NHR : forall z, SBEG + 2 ^ 37 <= z < SBEG + 2 ^ 37 + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz SB0 SB1 CR; lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). exact Hz. }
    assert (NHF : forall z, SBEG + 24 * 2 ^ 32 + 3758096384 <= z < SBEG + 24 * 2 ^ 32 + 3758096384 + r_mapped_fa (a_reg st 24) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz SB0 SB1 Q5 Q6 CR; lia|]. apply (rep_nolazy_fa bt st Lc FF M0 mdl W RP 24 z Hc).
      (lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end). exact Hz. }
    idtac "PROGRESS K6b: facts".
    (* [comment removed for export] *)
    pose (memD := mrestrict Hd M).
    Ltac cimg6 XZ SBH NHs := intros z Hz; split; [ intros Hx; destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q; lia | clear - Hz Q SBH; lia]
                                                  | apply NHs; [clear - Hz; lia | right; clear - Hz; lia] ].
    Ltac czl6 := first [ reflexivity | (vm_compute; discriminate) | (vm_compute; reflexivity) ].
    Ltac konst6 Hd M M0 X Rc EQ0 XZ SBH NHs C := apply (cellX Hd M M0 X _ _ _ (const_cell bt _ _ _ _ Rc C) EQ0); [czl6 | czl6 | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); cimg6 XZ SBH NHs].
    assert (K_spb : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SBEG))) by konst6 Hd M M0 X Rc EQ0 XZ SBH NHs CELLNB.
    assert (K_rib : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 48)) 8 = Some (LE8 (Z_to_bv 64 (SBEG + 2 ^ 37)))) by konst6 Hd M M0 X Rc EQ0 XZ SBH NHs CELL_rib.
    assert (K_int : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 40)) 4 = Some (LE4 0xffffffff)) by konst6 Hd M M0 X Rc EQ0 XZ SBH NHs CELL_int.
    assert (K_gpg : rdn BSEGS memD (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 0x19dc60))) by konst6 Hd M M0 X Rc EQ0 XZ SBH NHs CELL_gpg.
    assert (K_pg : rdn BSEGS memD (Z_to_bv 64 0x19dc60) 8 = Some (LE8 (Z_to_bv 64 4096))) by konst6 Hd M M0 X Rc EQ0 XZ SBH NHs CELL_pg.
    assert (K_470 : rdn BSEGS memD (Z_to_bv 64 0x10468) 8 = Some (LE8 (Z_to_bv 64 0xafffff00000fffff))) by konst6 Hd M M0 X Rc EQ0 XZ SBH NHs CELL_470.
    assert (OFFT : forall z, T <= z < T + 4096 -> ~ X z /\ Hd (Z_to_bv 64 z) = false).
    { intros z Hz. split; [| apply NHT; exact Hz]. intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q GTI; lia | clear - Hz Q SPT; lia]. }
    assert (OFFR : forall z, SBEG + 2 ^ 37 <= z < SBEG + 2 ^ 37 + 4096 -> ~ X z /\ Hd (Z_to_bv 64 z) = false).
    { intros z Hz. split; [| apply NHR; exact Hz]. intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q SBH; lia | clear - Hz Q; lia]. }
    assert (OFFF : forall z, SBEG + 24 * 2 ^ 32 + 3758096384 + 4 * nf <= z < SBEG + 24 * 2 ^ 32 + 3758096384 + 4 * (nf + 1) -> ~ X z /\ Hd (Z_to_bv 64 z) = false).
    { intros z Hz. split; [| apply NHF; clear - Hz FAR NF0; lia]. apply NXF. (lazymatch goal with |- ?G => let G' := eval unfold foot_drain_top, fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end). fold nf. do 4 right; left. exact Hz. }
    assert (K_mx : rdn BSEGS memD (Z_to_bv 64 (T + 208 + 80 * 24 + 4)) 4 = Some (LE4 2)).
    { apply (cellX Hd M M0 X _ _ _ PCmax EQ0); [clear - GT0; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFT. clear - Hz. lia. }
    assert (K_cnt : rdn BSEGS memD (Z_to_bv 64 (T + 208 + 80 * 24)) 4 = Some (LE4 2)).
    { rewrite <- LEN. apply (cellX Hd M M0 X _ _ _ PCcnt EQ0); [clear - GT0; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFT. clear - Hz. lia. }
    assert (K_src : forall i k, nth_error ks i = Some k -> rdn BSEGS memD (Z_to_bv 64 (T + 208 + 80 * 24 + 16 + 4 * (2 - 2 / 2) + 4 * Z.of_nat i)) 4 = Some (LE4 k)).
    { intros i k Hik. assert (Hi : Z.of_nat i < 1) by (rewrite <- LKS; apply Nat2Z.inj_lt; apply nth_error_Some; rewrite Hik; discriminate).
      unfold ks in Hik. rewrite nth_error_skipn in Hik. specialize (PCks _ _ Hik).
      replace (T + 208 + 80 * 24 + 16 + 4 * (2 - 2 / 2) + 4 * Z.of_nat i) with (T + 208 + 80 * 24 + 16 + 4 * Z.of_nat (Z.to_nat (Z.of_nat (length (a_cache st 24)) - 1) + i))
        by (rewrite Nat2Z.inj_add, Z2Nat.id by (clear - LEN; lia); rewrite LEN; change (2 / 2) with 1; clear; lia).
      apply (cellX Hd M M0 X _ _ _ PCks EQ0); [clear - GT0; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC CR LEN Hi; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFT. clear - Hz LEN Hi. lia. }
    assert (K_mu : rdn BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * 24)) 8 = Some (LE8 (Z_to_bv 64 0))).
    { apply (cellX Hd M M0 X _ _ _ RImu EQ0); [clear - SB0; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - SB1 CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFR. clear - Hz. lia. }
    assert (K_nf : rdn BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * 24 + 16)) 8 = Some (LE8 (Z_to_bv 64 nf))).
    { apply (cellX Hd M M0 X _ _ _ RInf EQ0); [clear - SB0; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - SB1 CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFR. clear - Hz. lia. }
    assert (K_mfa : rdn BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * 24 + 24)) 8 = Some (LE8 (Z_to_bv 64 (r_mapped_fa (a_reg st 24))))).
    { apply (cellX Hd M M0 X _ _ _ RImfa EQ0); [clear - SB0; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - SB1 CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFR. clear - Hz. lia. }
    assert (TDEF : forall i, T <= i < T + 4096 -> memD (Z_to_bv 64 i) <> None).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite mrestrict_off by (apply NHT; exact Hi). apply GR0. apply (writableZ_def M0 _ _ _ TW). exact Hi. }
    assert (RDEF : forall i, SBEG + 2 ^ 37 + 128 * 24 <= i < SBEG + 2 ^ 37 + 128 * 24 + 128 -> memD (Z_to_bv 64 i) <> None).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite mrestrict_off by (apply NHR; clear - Hi; lia). apply GR0. apply (writableZ_def M0 _ _ _ RIW). exact Hi. }
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 2784)) 8) as (bst & Cst & Lst);
      [intros i Hi; apply TDEF; clear - Hi GT0 GTC CR; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 208 + 80 * 24 + 8)) 8) as (bcs & Ccs & Lcs);
      [intros i Hi; apply TDEF; clear - Hi GT0 GTC CR; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * 24 + 80)) 8) as (b80 & C80 & L80);
      [intros i Hi; apply RDEF; clear - Hi SB0 SB1 CR; revert Hi; unorm; intros Hi; lia | clear - SB0 SB1 CR; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * 24 + 88)) 8) as (b88 & C88 & L88);
      [intros i Hi; apply RDEF; clear - Hi SB0 SB1 CR; revert Hi; unorm; intros Hi; lia | clear - SB0 SB1 CR; wd_ulia |].
    (* [comment removed for export] *)
    assert (SOKstk : store_ok BSEGS memD (at_ S (-2720)) 320 = true).
    { replace (at_ S (-2720)) with (Z_to_bv 64 (U S - 2720) : word) by (clear - HSr Slo Shi CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - Slo CR; lia | clear - HSr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - apply (SOK (Z_to_bv 64 z)). clear - Hz HSr Slo CR. unorm. lia.
      - apply NHs; [clear - Hz HSr Slo CR; lia | left; clear - Hz Slo; lia]. }
    assert (SOKT : store_ok BSEGS memD (Z_to_bv 64 T) (Z.to_nat 4096) = true).
    { apply (sokX Hd M M0 _ _ T _ TW GR0); [clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | clear - GTC CR; lia | clear - GT0; lia |].
      intros z Hz. apply NHT. clear - Hz. cbn in Hz. lia. }
    assert (SOKRI : store_ok BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * 24)) 128 = true).
    { apply (sokX Hd M M0 _ _ _ _ RIW GR0); [clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | clear - SB1 CR; lia | clear - SB0; lia |].
      intros z Hz. apply NHR. clear - Hz. cbn in Hz. lia. }
    assert (SOKfa : store_ok BSEGS memD (Z_to_bv 64 (SBEG + 24 * 2 ^ 32 + 3758096384 + 4 * nf)) (4 * length ks) = true).
    { apply (sokX Hd M M0 _ _ _ _ FAW GR0); [clear - NF0; lia | clear - LKS FAR; lia | clear - SB1 Q5 Q6 CR; lia | clear - SB0 NF0; lia |].
      intros z Hz. apply NHF. clear - Hz LKS FAR NF0. lia. }
    idtac "PROGRESS K6b: cells".
    (* [comment removed for export] *)
    pose proof W as ((WR1 & _) & _). destruct (WR1 24 Hc) as (_ & _ & _ & _ & _ & MFA18 & _). clear WR1. unfold KFAMAP in MFA18.
    assert (P_GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (clear - Slo Shi CR; lia).
    assert (P_GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0).
    { split; [exact GT4|]. split; [split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - GTI GTB; lia | clear - GTC Slo; lia] | exact T16]. }
    assert (P_Gspb : 0x10007fff8000 <= SBEG /\ SBEG + 2 ^ 37 + 4096 <= U S - 3584 /\ SBEG mod 8 = 0) by (split; [clear - SBH; lia | split; [clear - SB1 Slo; lia | exact SB8]]).
    assert (P_GTsp : hideW (T + 4096 <= SBEG \/ SBEG + 2 ^ 37 + 4096 <= T)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); exact SPT).
    assert (P_13 : getr R 13 = Z_to_bv 64 (SBEG + 24 * 2 ^ 32 + e)) by (rewrite R13r; f_equal; clear - He; lia).
    assert (P_nf : 0 <= nf /\ 4 * (nf + 2 / 2) <= r_mapped_fa (a_reg st 24)) by (change (2 / 2) with 1; split; [exact NF0 | exact FAR]).
    destruct (run_dfull memD (seg_rom BSEGS) R S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20)
                (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)
                T SBEG 24 e 2 nf (r_mapped_fa (a_reg st 24)) 0x19dc60 ks b80 b88 (LE8 (Z_to_bv 64 0xafffff00000fffff)) bst bcs
                R1 R2 R10 R11 R12 P_13 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                P_GS P_GT P_Gspb P_GTsp (conj Hc (proj1 He)) ltac:(clear; lia) P_nf (conj Q6 MFA18) LKS FKS ltac:(clear; lia) RET L80 L88 (length_N_to_le_bytes 8 _) Lst Lcs
                SOKstk SOKT SOKRI SOKfa K_mx K_cnt Ccs Cst K_src K_spb K_rib K_int K_gpg K_pg K_470 K_mu K_nf K_mfa C80 C88)
      as (rf & w9 & w22 & RUN & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z3 & Z4 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
    match type of RUN with msteps _ _ (mkst _ _ ?mf _) => remember mf as MF eqn:EMF end.
    assert (I_GT : 4096 <= T /\ T + 4096 <= U S - 3584) by (clear - GT4 GTC Slo; lia).
    assert (I_Gspb : 0x10007fff8000 <= SBEG /\ SBEG + 2 ^ 37 + 4096 <= U S - 3584) by (clear - P_Gspb; lia).
    assert (I_nf : 0 <= nf /\ 4 * (nf + 2 / 2) <= 2 ^ 29) by (clear - P_nf Q6; lia).
    match type of EMF with
    | MF = fr_full ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 ?a18 ?a19 ?a20 ?a21 ?a22 ?a23 ?a24 ?a25 ?a26 =>
        pose proof (fr_full_foot a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 P_GS I_GT I_Gspb Hc ltac:(clear; lia) I_nf LKS) as FT;
        pose proof (fr_full_grows a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26) as GRF;
        pose proof (fr_full_cnt a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 P_GS I_GT Hc ltac:(clear; lia) I_nf) as FCNT;
        pose proof (fr_full_slot a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 P_GS I_GT Hc ltac:(clear; lia) I_nf) as FSLOT;
        pose proof (fr_full_mu a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 P_GS I_GT I_Gspb P_GTsp Hc ltac:(clear; lia) I_nf) as FMU;
        pose proof (fr_full_nf a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 P_GS I_GT I_Gspb P_GTsp Hc ltac:(clear; lia) I_nf) as FNF;
        pose proof (fr_full_fa a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 P_GS I_GT I_Gspb P_GTsp Hc ltac:(clear; lia) I_nf LKS) as FFA
    end.
    rewrite <- EMF in FT, GRF, FCNT, FSLOT, FMU, FNF, FFA.
    change (2 - 2 / 2) with 1 in FT, FCNT, FSLOT. change (2 / 2) with 1 in FT, FNF.
    idtac "PROGRESS K6b: run".
    (* [comment removed for export] *)
    replace (0x4eca8%bv : word) with (Z_to_bv 64 0x4eca8 : word) in RUN by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x4eca8) M (seg_rom BSEGS)) (@mkst fx rf ret MF (seg_rom BSEGS)) mdl).
    { apply lazy_cover_HID. } { exact B1. } { exact B2. } { exact HH. } { rewrite restrict_mkstK. exact RUN. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x4eca8) M (seg_rom BSEGS))) with M by reflexivity.
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
    destruct SF1 as (_ & Evm1 & Elz1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh1 & _).
    set (M1 := munrestrict Hd M MF).
    assert (VIS : forall a : word, Hd a = false -> M1 a = MF a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (HIDv : forall a : word, Hd a = true -> M1 a = M a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_on; exact Ha).
    assert (MrM : forall a : word, Hd a = false -> memD a = M a) by (intros a Ha; apply mrestrict_off; exact Ha).
    assert (GR1 : mem_grows M M1).
    { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply GRF. rewrite (MrM a Eh). exact Ha. }
    assert (FOOT1 : forall a : word, M1 a <> M a ->
              (U S - 2720 <= U a < U S - 2400) \/ (T + 208 + 80 * 24 <= U a < T + 208 + 80 * 24 + 4)
              \/ (T + 208 + 80 * 24 + 16 + 4 * 1 <= U a < T + 208 + 80 * 24 + 16 + 4 * 1 + 4) \/ (T + 2784 <= U a < T + 2792)
              \/ (SBEG + 2 ^ 37 + 128 * 24 <= U a < SBEG + 2 ^ 37 + 128 * 24 + 8) \/ (SBEG + 2 ^ 37 + 128 * 24 + 16 <= U a < SBEG + 2 ^ 37 + 128 * 24 + 24)
              \/ (SBEG + 2 ^ 37 + 128 * 24 + 80 <= U a < SBEG + 2 ^ 37 + 128 * 24 + 88)
              \/ (SBEG + 24 * 2 ^ 32 + 3758096384 + 4 * nf <= U a < SBEG + 24 * 2 ^ 32 + 3758096384 + 4 * nf + 4 * 1)).
    { intros a NE. destruct (Hd a) eqn:Eh; [exfalso; apply NE; apply HIDv; exact Eh|].
      rewrite (VIS a Eh) in NE. rewrite <- (MrM a Eh) in NE. exact (FT a NE). }
    assert (DEF1 : forall a : word, M1 a <> M a -> M1 a <> None).
    { intros a NE E1. apply NE. rewrite E1. destruct (M a) eqn:E0; [|reflexivity]. exfalso.
      assert (D : M a <> None) by (rewrite E0; discriminate). apply GR1 in D. exact (D E1). }
    assert (Ek : compact_of SBEG 24 ba = e / 16).
    { (lazymatch goal with |- ?G => let G' := eval unfold compact_of, region_beg, KREGION in G in change_no_check G' end). f_equal. clear - He. lia. }
    assert (NOX : forall a : word, M1 a <> M a -> ~ X (U a) /\ U a < U S - 2400).
    { intros a NE. destruct (FOOT1 a NE) as [F|[F|[F|[F|[F|[F|[F|F]]]]]]].
      - split; [| clear - F; lia]. intros Hx. destruct (XZ _ Hx) as [Q|Q]; [clear - F Q Slo CR; lia | clear - F Q SB1 Slo; lia].
      - split; [apply (OFFT (U a)); clear - F; lia | clear - F GTC Slo; lia].
      - split; [apply (OFFT (U a)); clear - F; lia | clear - F GTC Slo; lia].
      - split; [apply (OFFT (U a)); clear - F; lia | clear - F GTC Slo; lia].
      - split; [apply (OFFR (U a)); clear - F; lia | clear - F SB1 Slo; lia].
      - split; [apply (OFFR (U a)); clear - F; lia | clear - F SB1 Slo; lia].
      - split; [apply (OFFR (U a)); clear - F; lia | clear - F SB1 Slo; lia].
      - split; [apply (OFFF (U a)); clear - F; lia | clear - F SB1 Slo Q5 Q6 FAR NF0; lia]. }
    (* [comment removed for export] *)
    assert (VISZ : forall lo n, (forall z, lo <= z < lo + n -> 0 <= z < 2 ^ 64 /\ Hd (Z_to_bv 64 z) = false) -> forall x : word, lo <= U x < lo + n -> M1 x = MF x).
    { intros lo n F x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). exact (proj2 (F (U x) Hx)). }
    idtac "PROGRESS K6b: lift".
    (* [comment removed for export] *)
    assert (RXa : RepX bt X st1 Lc FF (mid_mem bt st 24 1 M M1) mdl1).
    { apply (drain_mid bt st Lc FF qt qg 24 1 W Hc ltac:(clear; lia) FAR X Xd M M1 mdl mdl1 RX ltac:(clear - LEN; lia) XSUB).
      - intros a _ NE. exact (DEF1 a NE).
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end).
        eapply rd_same; [| clear - SB0 SB1 CR; wd_ulia_c | exact FMU].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHR. clear - Hx SB0 SB1 CR. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end). fold nf.
        eapply rd_same; [| clear - SB0 SB1 CR; wd_ulia_c | exact FNF].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHR. clear - Hx SB0 SB1 CR. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
      - intros i k Hik. fold ks in Hik.
        assert (Hi : Z.of_nat i < 1) by (rewrite <- LKS; apply Nat2Z.inj_lt; apply nth_error_Some; rewrite Hik; discriminate).
        (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end). fold nf.
        replace (SBEG + 24 * 2 ^ 32 + 3758096384 + 4 * (nf + Z.of_nat i)) with (SBEG + 24 * 2 ^ 32 + 3758096384 + 4 * nf + 4 * Z.of_nat i) by (clear; lia).
        eapply rd_same; [| clear - SB0 SB1 CR Q5 Q6 FAR NF0 Hi; wd_ulia_c | exact (FFA i k Hik)].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHF. clear - Hx SB0 SB1 CR Q5 Q6 FAR NF0 Hi. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
      - exact SBM1.
      - exact MI1. }
    idtac "PROGRESS K6b: drain_mid".
    (* [comment removed for export] *)
    assert (Hnth1 : nth_error (a_gq st1) 0 = Some (BATCH ba [])) by (rewrite GQ1; exact Hnth).
    assert (XSUB1 : forall z, X z -> XB bt st1 z) by (intros z Hz; apply XB_drain_top; exact (XSUB z Hz)).
    assert (ROOM1 : Z.of_nat (length (a_cache st1 BATCHCLASS)) < cache_max BATCHCLASS) by (change BATCHCLASS with 24; rewrite LEN1; change (cache_max 24) with 2; clear; lia).
    assert (MDEFT : forall a : word, T <= U a < T + 4096 -> M a <> None).
    { intros a Ha. apply GR0. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (writableZ_def M0 _ _ _ TW). exact Ha. }
    assert (RX1 : RepX bt X (op_qbatch_free SBEG st1 0) Lc FF M1 mdl1).
    { apply (OPS_REPX_qbatch_free_pf bt X Xd st1 Lc FF (mid_mem bt st 24 1 M M1) M1 mdl1 mdl1 0%nat ba qt qg W1 RXa Hnth1 ROOM1 XSUB1 XQ).
      - intros i' bp E. discriminate E.
      - intros a Ha. apply GR1. exact (QDEF a Ha).
      - intros a NE. (lazymatch goal with |- ?G => let G' := eval unfold foot_qbatch_free, T_PC, PC_SZ in G in change_no_check G' end). change BATCHCLASS with 24. rewrite LEN1.
        destruct (mid_mem_diff bt st Lc FF qt qg 24 1 W Hc ltac:(clear; lia) FAR M M1 a NE) as [I | [NE' NFd]].
        + unfold T_PC, PC_SZ in I. split; [left; left; exact I | apply GR1; apply MDEFT; clear - I; lia].
        + split; [| exact (DEF1 a NE')]. left.
          destruct (FOOT1 a NE') as [F|[F|[F|[F|[F|[F|[F|F]]]]]]];
            [ do 3 right; clear - F Slo; lia | left; clear - F; lia | right; left; clear - F; lia | right; right; left; clear - F; lia
            | exfalso; apply NFd; (lazymatch goal with |- ?G => let G' := eval unfold Fdr, reginfo, KSPACE in G in change_no_check G' end); left; exact F
            | exfalso; apply NFd; (lazymatch goal with |- ?G => let G' := eval unfold Fdr, reginfo, KSPACE in G in change_no_check G' end); right; left; exact F
            | exfalso; apply NFd; (lazymatch goal with |- ?G => let G' := eval unfold Fdr, reginfo, KSPACE in G in change_no_check G' end); right; right; left; clear - F; lia
            | exfalso; apply NFd; (lazymatch goal with |- ?G => let G' := eval unfold Fdr, fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end); fold nf; do 3 right; clear - F; lia ].
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). change BATCHCLASS with 24. rewrite LEN1.
        eapply rd_same; [| clear - GT0 GTC CR; wd_ulia_c | exact FCNT].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHT. clear - Hx GT0 GTC CR. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). change BATCHCLASS with 24. rewrite LEN1, Ek.
        eapply rd_same; [| clear - GT0 GTC CR; wd_ulia_c | exact FSLOT].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHT. clear - Hx GT0 GTC CR. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
      - apply same_but_materialized_refl.
      - exact MI1. }
    idtac "PROGRESS K6b: RX1".
    apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold rc_step_post in G in change_no_check G' end). exists fx, (op_qbatch_free SBEG st1 0), M1, mdl1, rf.
    split; [reflexivity|]. split; [exact HFX|]. split; [rewrite Eh1; exact HH|]. split; [exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW)|].
    split; [exact (OPS_WFq_qbatch_free_pf bt st1 Lc FF 0%nat ba qt qg W1 Hnth1 ROOM1)|].
    split; [exact RX1|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_qbatch_free in G in change_no_check G' end); rewrite Hnth1; (lazymatch goal with |- ?G => let G' := eval cbn [a_gq set_cache set_gq] in G in change_no_check G' end); rewrite GQ1, EGQ; reflexivity|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_qbatch_free in G in change_no_check G' end); rewrite Hnth1; reflexivity|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_qbatch_free in G in change_no_check G' end); rewrite Hnth1; reflexivity|].
    split.
    { split; [| exact (fk_trans _ _ _ (fk_drain_top bt st BATCHCLASS 1 (or_introl eq_refl)) (fk_qbatch_free SBEG st1 0))].          (* [comment removed for export] *)
      intros h HL. unfold holes_le in *. (lazymatch goal with |- ?G => let G' := eval unfold op_qbatch_free in G in change_no_check G' end). rewrite Hnth1. (lazymatch goal with |- ?G => let G' := eval cbn [a_reg set_cache set_gq] in G in change_no_check G' end). intros c' Hc'. apply HL.
      unfold st1, op_drain_top in Hc'. cbn [a_reg set_cache set_reg] in Hc'. unfold fupdZ in Hc'.
      destruct (Z.eqb c' 24) eqn:E; [apply Z.eqb_eq in E; subst c'; cbn [r_uhole r_fhole] in Hc'; exact Hc' | exact Hc']. }
    split; [intros z Hz; exact (XB_qbatch_free bt st1 Lc FF qt qg 0%nat ba z W1 Hnth1 (XSUB1 z Hz))|].
    split.
    { intros a Ha. destruct (decide (M1 a = M a)) as [E|NE]; [exact E|]. exfalso. destruct (NOX a NE) as [N1 N2].
      destruct Ha as [Ha|Ha]; [exact (N1 Ha) | clear - Ha N2; lia]. }
    split.
    { intros a NE. split; [| left; exact (DEF1 a NE)]. (lazymatch goal with |- ?G => let G' := eval unfold rc_changed in G in change_no_check G' end).
      destruct (FOOT1 a NE) as [F|[F|[F|[F|[F|[F|[F|F]]]]]]].
      - left. clear - F. lia.
      - right; left. apply (OBL_rt_private_pf bt st Lc FF W (U a)). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - F. lia.
      - right; left. apply (OBL_rt_private_pf bt st Lc FF W (U a)). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - F. lia.
      - right; left. apply (OBL_rt_private_pf bt st Lc FF W (U a)). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - F. lia.
      - right; left. apply (rt_priv_reginfo bt st Lc FF W 24 (U a) Hc). (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end). clear - F. lia.
      - right; left. apply (rt_priv_reginfo bt st Lc FF W 24 (U a) Hc). (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end). clear - F. lia.
      - right; left. apply (rt_priv_reginfo bt st Lc FF W 24 (U a) Hc). (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end). clear - F. lia.
      - right; left. apply (rt_priv_fa bt st Lc FF W 24 (U a) Hc). (lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end). clear - F FAR NF0 Q6. lia. }
    split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz1; reflexivity|].
    split; [apply same_but_materialized_except_vm; exact SBM1|].
    apply regs_kept_intro; rewrite ?Z2, ?Z3, ?Z4, ?Z8, ?Z9, ?Z18, ?Z19, ?Z20, ?Z21, ?Z22, ?Z23, ?Z24, ?Z25, ?Z26, ?Z27; try reflexivity. symmetry; exact R2.
  Qed.
End K6B.
End BoAllocFRcK6b.
Require Stdlib.NArith.NArith Stdlib.Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcMW.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcM5.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition gq_merge (cur : batch) (l : list batch) : list batch := snd (mergeF cur l) ++ fst (mergeF cur l).
Definition st_merge (st : ast) (cur : batch) (l : list batch) : ast := set_gq st (gq_merge cur l).

Lemma gq_merge_bytes : forall cur l, q_bytes (gq_merge cur l) = q_bytes (cur :: l).
Proof.
  intros cur l. (lazymatch goal with |- ?G => let G' := eval unfold gq_merge in G in change_no_check G' end). rewrite q_bytes_appM, (q_bytes_empties _ (mf_empties l cur)). pose proof (mf_bytes l cur) as E.
  change (q_bytes (cur :: l)) with (ba_bytes cur + q_bytes l). lia.
Qed.

Section MergeW.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.

  Theorem WFq_st_merge : forall st Lc FF cur l (qt qg : Z),
    WFq bt st Lc FF qt qg -> a_gq st = cur :: l -> WFq bt (st_merge st cur l) Lc FF qt qg.
  Proof using.
    intros st Lc FF cur l qt qg W Hgq. set (st' := st_merge st cur l).
    pose proof W as ((WR1 & WR2) & WC & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6) & WS & WL & WK & WD & WM & WMP & G).
    assert (EQ : quar st' = quar st).
    { (lazymatch goal with |- ?G => let G' := eval unfold quar, st', st_merge, gq_merge in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_tq a_gq set_gq] in G in change_no_check G' end). rewrite Hgq, !(flat_map_app ba_items (a_tq st)), mf_items_all. reflexivity. }
    assert (PA : Permutation (map ba_addr (a_tq st' ++ a_gq st')) (map ba_addr (a_tq st ++ a_gq st))).
    { (lazymatch goal with |- ?G => let G' := eval unfold st', st_merge, gq_merge in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_tq a_gq set_gq] in G in change_no_check G' end). rewrite Hgq, !(map_app ba_addr (a_tq st)). apply Permutation_app_head. apply mf_addrs. }
    assert (HB : forall a, in_batch st' a <-> in_batch st a).
    { intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_batch in G in change_no_check G' end). split; intros (b & Hin & Eb); apply (in_map ba_addr) in Hin; rewrite Eb in Hin;
        [apply (Permutation_in _ PA) in Hin | apply (Permutation_in _ (Permutation_sym PA)) in Hin]; apply in_map_iff in Hin as (b' & Eb' & Hin'); exists b'; split; assumption. }
    assert (HQ : forall c a, in_quar_c st' c a <-> in_quar_c st c a) by (intros c a; (lazymatch goal with |- ?G => let G' := eval unfold in_quar_c in G in change_no_check G' end); rewrite EQ; tauto).
    (lazymatch goal with |- ?G => let G' := eval unfold WFq in G in change_no_check G' end).
    split; [| split; [exact WC | split; [| split; [| split; [exact WL | split; [exact WK | split; [exact WD | split; [exact WM | split; [exact WMP | exact G]]]]]]]]].
    - split; [| exact WR2]. intros c Hc. destruct (WR1 c Hc) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & PART & FHK).
      (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end). change (a_reg st' c) with (a_reg st c). do 8 (split; [assumption|]). split; [exact Z9|]. split; [| exact FHK].
      apply partition_part5. apply partition_part5 in PART. destruct PART as (PP & PN1 & PN2). split; [| exact (conj PN1 PN2)].
      apply (part5_ext _ _ _ _ _ _ _ _ _ _ _ PP). intros a. split; [tauto|]. split; [exact (HQ c a)|]. split; [tauto|]. split; [tauto|]. rewrite (HB a). tauto.
    - (lazymatch goal with |- ?G => let G' := eval unfold wf_quarantine_q in G in change_no_check G' end). change (a_tq st') with (a_tq st). split; [exact Q1|].
      split.
      { (lazymatch goal with |- ?G => let G' := eval unfold st', st_merge in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_gq set_gq] in G in change_no_check G' end). rewrite Hgq in Q2. rewrite Forall_forall in Q2. apply Forall_forall. intros b Hb.
        destruct (mf_forall (fun a => carved bt st BATCHCLASS a)
                    (fun it => 1 <= snd it <= NMAX /\ ((is_primary (snd it) = true /\ carved bt st (blk_class (snd it)) (prim_alloc_beg (fst it + 16) (snd it)))
                                                      \/ (is_primary (snd it) = false /\ registered st (fst it + 16) (snd it)))) l cur) with (b := b) as (P1 & P2 & P3).
        - intros b0 Hb0. destruct (Q2 b0 Hb0) as (L0 & CV0 & IT0). split; [exact CV0|]. split; [intros [m n] Hit; exact (IT0 m n Hit) | unfold blen, BATCHCAP in *; lia].
        - exact Hb.
        - split; [unfold blen, BATCHCAP in *; lia|]. split; [exact P1|]. intros m n Hin. exact (P2 (m, n) Hin). }
      split; [exact Q3|].
      split. { (lazymatch goal with |- ?G => let G' := eval unfold st', st_merge in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_gq set_gq] in G in change_no_check G' end). rewrite gq_merge_bytes, <- Hgq. exact Q4. }
      split. { exact (Permutation_NoDup (Permutation_sym PA) Q5). }
      rewrite EQ. exact Q6.
    - destruct WS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8). (lazymatch goal with |- ?G => let G' := eval unfold wf_secondary in G in change_no_check G' end). change (a_sec st') with (a_sec st). change (a_nres st') with (a_nres st). rewrite EQ.
      repeat (split; [assumption|]). exact S8.
  Qed.
End MergeW.
End BoAllocFRcMW.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc1L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcMI.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK1a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc1L OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcM5 BoAllocFRcMW.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation IBq := 0x10ab58 (only parsing).

Section MI.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.

  (* [comment removed for export] *)
  Lemma rep_batches_of_chain : forall (m : mem) q, chainR m q 0 ->
    (forall b, In b q -> writableZ (bt_segs bt) m (ba_addr b) (ba_addr b + BATCHSZ)) -> rep_batches bt m q.
  Proof using BT_segs.
    intros m q CH WR i b Hb. pose proof (nth_error_In _ _ Hb) as Hin. destruct (chainR_nth m q 0 i b CH Hb) as (C1 & C2 & C3 & C4).
    rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite hda_nxaddr, nxaddr_skipn in C1.
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. rewrite <- BT_segs. exact (WR b Hin).
  Qed.

  (* [comment removed for export] *)
  Definition ideal_mg (M1 : mem) (pb0 rest : list batch) : mem :=
    wbytes (wbytes (wbytes (wbytes (wbytes M1
      (Z_to_bv 64 (lasta pb0 0)) (LE8 (Z_to_bv 64 (hda rest 0))))
      (Z_to_bv 64 (IBq + 888)) (LE8 (Z_to_bv 64 (Z.of_nat (length (pb0 ++ rest))))))
      (Z_to_bv 64 (IBq + 896)) (LE8 (Z_to_bv 64 (hda (pb0 ++ rest) 0))))
      (Z_to_bv 64 (IBq + 904)) (LE8 (Z_to_bv 64 (lasta (pb0 ++ rest) 0))))
      (Z_to_bv 64 (IBq + 912)) (LE8 (Z_to_bv 64 (q_bytes (pb0 ++ rest)))).

  Theorem repx_merge : forall st2 Lc FF (M0 M1 : mem) mdl mdl1 cur l pb0 rest (qt qg : Z),
    WFq bt st2 Lc FF qt qg -> Rep bt st2 Lc FF M0 mdl -> a_gq st2 = cur :: l ->
    pb0 ++ rest = gq_merge cur l -> pb0 <> [] ->
    mem_grows M0 M1 ->
    (forall a : word, M1 a <> M0 a -> qhdr bt (U a) \/ gq_objs st2 (U a) \/ CEIL <= U a) ->
    chainR M1 pb0 0 -> chainR M1 rest 0 ->
    (forall a : word, qhdr bt (U a) -> M1 a <> None) ->
    same_but_materialized mdl mdl1 -> MInv (a_aa st2) mdl1 ->
    AsAinvOpsRc73.AsAinvRepX3.RepX bt (XP bt pb0) (st_merge st2 cur l) Lc FF M1 mdl1.
  Proof using BT_ia BT_segs.
    intros st2 Lc FF M0 M1 mdl mdl1 cur l pb0 rest qt qg W RP EGQ EPR NEpb GR01 FOOTI CHT CHR QDEF SBM MI.
    pose proof ceil_rng as CR.
    pose proof (thread_dyn bt st2 Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & _ & _ & _ & _ & _ & _ & SB0 & SB1 & SBH & _).
    unfold KSPACE, PG, AS_HEAPLO in *.
    (* [comment removed for export] *)
    assert (PAD : Permutation (map ba_addr (pb0 ++ rest)) (map ba_addr (cur :: l))) by (rewrite EPR; apply mf_addrs).
    assert (ORIG : forall b, In b (pb0 ++ rest) -> exists b0, In b0 (cur :: l) /\ ba_addr b0 = ba_addr b).
    { intros b Hb. apply (in_map ba_addr) in Hb. apply (Permutation_in _ PAD) in Hb. apply in_map_iff in Hb. destruct Hb as (b0 & E0 & H0). exists b0. split; assumption. }
    assert (BF0 : forall b0, In b0 (cur :: l) -> SBEG <= ba_addr b0 /\ ba_addr b0 + 8192 <= SBEG + 2 ^ 37 /\ Z.of_nat (length (ba_items b0)) <= 1021).
    { intros b0 Hb0. destruct (batch_facts bt st2 Lc FF W b0 ltac:(apply in_app_iff; right; rewrite EGQ; exact Hb0)) as (_ & L0 & G1 & G2).
      unfold KSPACE, BATCHSZ, BATCHCAP in *. clear - L0 G1 G2. lia. }
    assert (BFm : forall b, In b (pb0 ++ rest) -> SBEG <= ba_addr b /\ ba_addr b + 8192 <= SBEG + 2 ^ 37 /\ blen b <= 1021).
    { intros b Hb. destruct (ORIG b Hb) as (b0 & Hb0 & Ea). destruct (BF0 b0 Hb0) as (G1 & G2 & _). rewrite Ea in G1, G2. split; [exact G1|]. split; [exact G2|].
      rewrite EPR in Hb. destruct (mf_forall (fun _ => True) (fun _ => True) l cur) with (b := b) as (_ & _ & P3); [| exact Hb | exact (proj2 P3)].
      intros b1 Hb1. split; [exact I|]. split; [intros; exact I | destruct (BF0 b1 Hb1) as (_ & _ & G3); exact G3]. }
    assert (BGm : forall b, In b (pb0 ++ rest) -> bgeo b).
    { intros b Hb. destruct (BFm b Hb) as (G1 & G2 & G3). (lazymatch goal with |- ?G => let G' := eval unfold bgeo in G in change_no_check G' end). clear - G1 G2 G3 SB0 SB1 CR. lia. }
    assert (NDm : List.NoDup (map ba_addr (pb0 ++ rest))).
    { apply (Permutation_NoDup (Permutation_sym PAD)). pose proof W as (_ & _ & (_ & _ & _ & _ & ND & _) & _). rewrite map_app in ND. rewrite <- EGQ. exact (NoDup_app_remove_l _ _ ND). }
    assert (SEPm : forall b1 b2, In b1 (pb0 ++ rest) -> In b2 (pb0 ++ rest) -> ba_addr b1 <> ba_addr b2 -> bsep (ba_addr b1) (ba_addr b2)).
    { intros b1 b2 H1 H2 NE. destruct (ORIG b1 H1) as (x1 & Hx1 & E1). destruct (ORIG b2 H2) as (x2 & Hx2 & E2). rewrite <- E1, <- E2 in *.
      destruct (batch_facts bt st2 Lc FF W x1 ltac:(apply in_app_iff; right; rewrite EGQ; exact Hx1)) as (CV1 & _).
      destruct (batch_facts bt st2 Lc FF W x2 ltac:(apply in_app_iff; right; rewrite EGQ; exact Hx2)) as (CV2 & _).
      destruct (chunk_cases bt st2 Lc FF W BATCHCLASS (ba_addr x1) BATCHCLASS (ba_addr x2) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CV1 CV2) as [[_ E] | D];
        [exfalso; exact (NE E) | change (csize BATCHCLASS) with 8192 in D; (lazymatch goal with |- ?G => let G' := eval unfold bsep in G in change_no_check G' end); exact D]. }
    (* [comment removed for export] *)
    set (lp := lasta pb0 0). set (nx := hda rest 0).
    assert (LPin : In lp (map ba_addr pb0)) by (apply lasta_in0; exact NEpb).
    apply in_map_iff in LPin. destruct LPin as (blp & Elp & Hblp).
    assert (Hblp' : In blp (pb0 ++ rest)) by (apply in_app_iff; left; exact Hblp).
    destruct (BFm blp Hblp') as (Glp1 & Glp2 & _). rewrite Elp in Glp1, Glp2.
    assert (Gnx : 0 <= nx < 2 ^ 64).
    { (lazymatch goal with |- ?G => let G' := eval unfold nx in G in change_no_check G' end). destruct rest as [|r0 rr]; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [hda] in G in change_no_check G' end). destruct (BFm r0 ltac:(apply in_app_iff; right; left; reflexivity)) as (G1 & G2 & _). clear - G1 G2 SB0 SB1 CR. lia. }
    set (Mi := ideal_mg M1 pb0 rest).
    assert (GRi : mem_grows M1 Mi) by ((lazymatch goal with |- ?G => let G' := eval unfold Mi, ideal_mg in G in change_no_check G' end); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (OUTi : forall x : word, ~ (lp <= U x < lp + 8) -> ~ (IBq + 888 <= U x < IBq + 920) -> Mi x = M1 x).
    { intros x N1 N2. (lazymatch goal with |- ?G => let G' := eval unfold Mi, ideal_mg in G in change_no_check G' end). fold lp nx.
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try (clear - N1 N2 Glp1 Glp2 SB0 SB1 CR; lia). reflexivity. }
    assert (GR0i : mem_grows M0 Mi) by (eapply mem_grows_trans; [exact GR01 | exact GRi]).
    assert (DEFi : forall a : word, Mi a <> M0 a -> Mi a <> None).
    { intros a NE E1. apply NE. rewrite E1. destruct (M0 a) eqn:E0; [|reflexivity]. exfalso.
      assert (D : M0 a <> None) by (rewrite E0; discriminate). apply GR0i in D. exact (D E1). }
    (* [comment removed for export] *)
    assert (NLi : rep_list bt Mi (IB bt + 888) (pb0 ++ rest)).
    { (lazymatch goal with |- ?G => let G' := eval unfold rep_list, IB in G in change_no_check G' end). rewrite BT_segs, BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end).
      replace (match rev (pb0 ++ rest) with [] => 0 | b :: _ => ba_addr b end) with (lasta (pb0 ++ rest) 0) by (apply lasta_rev).
      change (match pb0 ++ rest with [] => 0 | b :: _ => ba_addr b end) with (hda (pb0 ++ rest) 0).
      (lazymatch goal with |- ?G => let G' := eval unfold Mi, ideal_mg in G in change_no_check G' end). fold lp nx.
      split; [replace (0x10ab58 + 888) with (IBq + 888) by reflexivity; repeat (wd_rdstep rd8_side)|].
      split; [replace (0x10ab58 + 888 + 8) with (IBq + 896) by reflexivity; repeat (wd_rdstep rd8_side)|].
      split; [replace (0x10ab58 + 888 + 16) with (IBq + 904) by reflexivity; repeat (wd_rdstep rd8_side)|].
      replace (0x10ab58 + 888 + 24) with (IBq + 912) by reflexivity. repeat (wd_rdstep rd8_side). }
    (* [comment removed for export] *)
    assert (INpb : forall b, In b pb0 -> In b (pb0 ++ rest)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    assert (INrs : forall b, In b rest -> In b (pb0 ++ rest)) by (intros b Hb; apply in_app_iff; right; exact Hb).
    assert (NDpb : List.NoDup (map ba_addr pb0)) by (rewrite map_app in NDm; exact (NoDup_app_remove_r _ _ NDm)).
    assert (CHi : chainR Mi (pb0 ++ rest) 0).
    { apply chainR_app. fold nx. split.
      - apply (chainR_relink M1 Mi pb0 0 nx NEpb); [intros b Hb; exact (BGm b (INpb b Hb)) | | | exact NDpb | | exact CHT].
        + intros b x Hb Hx NL. fold lp in NL. apply OUTi; [exact NL|]. destruct (BFm b (INpb b Hb)) as (G1 & _). clear - Hx G1 SBH. lia.
        + intros b Hb NEa. fold lp in NEa |- *. rewrite <- Elp in NEa |- *. exact (SEPm b blp (INpb b Hb) Hblp' NEa).
        + fold lp. (lazymatch goal with |- ?G => let G' := eval unfold Mi, ideal_mg in G in change_no_check G' end). fold lp nx. repeat (wd_rdstep rd8_side).
      - apply (chainR_frame M1 Mi); [intros b Hb; exact (BGm b (INrs b Hb)) | | exact CHR].
        intros b x Hb Hx. destruct (BFm b (INrs b Hb)) as (G1 & G2 & _). apply OUTi; [| clear - Hx G1 SBH; lia].
        assert (NEa : ba_addr b <> ba_addr blp).
        { intros EQa. rewrite map_app in NDm. apply (nd_app_disj _ _ (ba_addr b) NDm); [rewrite EQa; apply in_map; exact Hblp | apply in_map; exact Hb]. }
        pose proof (SEPm b blp (INrs b Hb) Hblp' NEa) as SP. unfold bsep in SP. rewrite Elp in SP. clear - SP Hx. lia. }
    assert (NBi : rep_batches bt Mi (pb0 ++ rest)).
    { intros i b Hb. pose proof (nth_error_In _ _ Hb) as Hin. destruct (chainR_nth Mi (pb0 ++ rest) 0 i b CHi Hb) as (C1 & C2 & C3 & C4).
      rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite hda_nxaddr, nxaddr_skipn in C1.
      split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
      (* [comment removed for export] *)
      destruct (ORIG b Hin) as (b0 & Hb0 & Ea). destruct (In_nth_error _ _ Hb0) as (i0 & Hi0).
      pose proof RP as (_ & _ & _ & _ & _ & RBg & _). rewrite EGQ in RBg. destruct (RBg i0 b0 Hi0) as (_ & _ & _ & _ & BW). rewrite BT_segs in BW. rewrite Ea in BW.
      intros z Hz. destruct (BW z Hz) as [D0 S0]. split; [apply GR0i; exact D0 | eapply store_ok_mono; [exact GR0i | exact S0]]. }
    (* [comment removed for export] *)
    assert (QH : forall a : word, IBq + 888 <= U a < IBq + 920 -> qhdr bt (U a)).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold qhdr, IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). exact Ha. }
    assert (LPO : forall z, lp <= z < lp + 8 -> gq_objs st2 z).
    { intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold gq_objs in G in change_no_check G' end). destruct (ORIG blp Hblp') as (b0 & Hb0 & Ea). exists b0. split; [rewrite EGQ; exact Hb0 | rewrite Ea, Elp; (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); clear - Hz; lia]. }
    assert (AGR4 : forall a : word, Mi a <> M0 a -> (qhdr bt (U a) \/ gq_objs st2 (U a) \/ CEIL <= U a) /\ Mi a <> None).
    { intros a NE. split; [| exact (DEFi a NE)].
      destruct (Z_le_dec (IBq + 888) (U a)) as [H1 | H1]; [destruct (Z_lt_dec (U a) (IBq + 920)) as [H2 | H2]; [left; apply QH; clear - H1 H2; lia|]|];
        (destruct (Z_le_dec lp (U a)) as [L1 | L1]; [destruct (Z_lt_dec (U a) (lp + 8)) as [L2 | L2]; [right; left; apply LPO; clear - L1 L2; lia|]|]);
        (apply FOOTI; rewrite <- OUTi; [exact NE | clear - L1 L2; lia | clear - H1 H2; lia]) || (apply FOOTI; rewrite <- OUTi; [exact NE | clear - L1; lia | clear - H1 H2; lia])
        || (apply FOOTI; rewrite <- OUTi; [exact NE | clear - L1 L2; lia | clear - H1; lia]) || (apply FOOTI; rewrite <- OUTi; [exact NE | clear - L1; lia | clear - H1; lia]). }
    assert (HC1 : 1 <= 1 <= 30) by (clear; lia).
    pose proof RP as (_ & _ & (_ & _ & _ & _ & _ & _ & _ & TP & _) & _).
    assert (RCr : Rep bt (set_cache (set_gq st2 (pb0 ++ rest)) 1 (a_cache st2 1)) Lc FF Mi mdl1).
    { apply (OPS_REP_gqpush_pf bt st2 Lc FF M0 Mi mdl mdl1 (pb0 ++ rest) 1 (a_cache st2 1) None qt qg W RP HC1).
      - intros x. rewrite EPR. (lazymatch goal with |- ?G => let G' := eval unfold gq_merge in G in change_no_check G' end). rewrite mf_items_all, <- EGQ. split; [intros H; split; [exact H | discriminate] | intros [H _]; exact H].
      - intros m0 n0 E. discriminate E.
      - intros a NE. destruct (AGR4 a NE) as [F D]. split; [| exact D]. (lazymatch goal with |- ?G => let G' := eval unfold foot_gqpush in G in change_no_check G' end). destruct F as [F | [F | F]]; [left; exact F | right; left; exact F | do 6 right; exact F].
      - exact NLi.
      - exact NBi.
      - pose proof (cache_len bt st2 Lc FF W 1 HC1) as CL'. pose proof (thread_page_facts bt st2 Lc FF W) as (_ & _ & TP0 & TP1 & TPI & _).
        pose proof (img_lits bt st2 Lc FF W) as [I1 I2].
        pose proof (bt_ok_W bt st2 Lc FF W) as (_ & _ & PRV & QI1 & _).
        destruct QI1 as (plo & phi & Hplo & PP1 & PP2). destruct (PRV plo phi (or_introl Hplo)) as [PP3 PP4].
        pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & INT & _) & _).
        eapply (rep_pclass_frame bt M0 Mi); [exact (TP 1 HC1) | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); clear -TP0; ulia | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); clear -TP1; ulia | exact CL' |].
        intros z Hz Hr. destruct (decide (Mi (Z_to_bv 64 z) = M0 (Z_to_bv 64 z))) as [E | NE]; [exact E | exfalso].
        destruct (AGR4 _ NE) as [F _]. rewrite (Z_to_bv_small 64 z) in F by ((lazymatch goal with |- ?G => let G' := eval unfold bv_modulus in G in change_no_check G' end); lia). unfold T_PC, PC_SZ in Hz. unfold qhdr, gq_objs, IB in F.
        destruct F as [F | [(b & Hb & F) | F]].
        + clear -F Hz TPI PP1 PP2 PP3 PP4. ulia.
        + destruct (batch_facts bt st2 Lc FF W b ltac:(apply in_app_iff; right; exact Hb)) as (_ & _ & BL2 & BL3).
          destruct (space_vs_fixed bt st2 Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG, KSPACE in G in change_no_check G' end); lia)); clear -F Hz BL2 BL3 H; ulia.
        + clear -F Hz TP1. ulia.
      - intros m0 n0 E. discriminate E.
      - exact SBM.
      - exact MI.
      - intros _. left. rewrite EGQ. discriminate. }                                     (* [comment removed for export] *)
    assert (RPm : Rep bt (st_merge st2 cur l) Lc FF Mi mdl1).
    { apply (Rep_proj_ext bt _ (st_merge st2 cur l) Lc FF Mi mdl1) in RCr; try reflexivity; [exact RCr | |].
      - intros c0. (lazymatch goal with |- ?G => let G' := eval unfold st_merge in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache set_gq] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c0 1) as [-> | NE]; reflexivity.
      - (lazymatch goal with |- ?G => let G' := eval unfold st_merge in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_gq set_cache set_gq] in G in change_no_check G' end). symmetry. exact EPR. }
    exists Mi. split; [exact RPm|].
    intros a NE.
    destruct (Z_le_dec (IBq + 888) (U a)) as [H1 | H1]; [destruct (Z_lt_dec (U a) (IBq + 920)) as [H2 | H2]; [split; [left; apply QH; clear - H1 H2; lia | apply QDEF; apply QH; clear - H1 H2; lia]|]|];
      (destruct (Z_le_dec lp (U a)) as [L1 | L1]; [destruct (Z_lt_dec (U a) (lp + 8)) as [L2 | L2] |]);
      try (exfalso; apply NE; symmetry; apply OUTi; [clear - L1 L2; lia | clear - H1 H2; lia]);
      try (exfalso; apply NE; symmetry; apply OUTi; [clear - L1; lia | clear - H1 H2; lia]);
      try (exfalso; apply NE; symmetry; apply OUTi; [clear - L1 L2; lia | clear - H1; lia]);
      try (exfalso; apply NE; symmetry; apply OUTi; [clear - L1; lia | clear - H1; lia]).
    all: split; [right; exists blp; split; [exact Hblp | rewrite Elp; (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); clear - L1 L2; lia]|].
    all: destruct (LPO (U a) ltac:(clear - L1 L2; lia)) as (b0 & Hb0 & Hz0); destruct (In_nth_error _ _ Hb0) as (i0 & Hi0);
         pose proof RP as (_ & _ & _ & _ & _ & RBg & _); destruct (RBg i0 b0 Hi0) as (_ & _ & _ & _ & BW);
         apply GR01; rewrite <- (Z_to_bv_bv_unsigned 64 a); exact (proj1 (BW (U a) Hz0)).
  Qed.
End MI.
End BoAllocFRcMI.
Module BoAllocFRcMK.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcM1U.BoAllocFRc1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc1L OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRc2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRc2U OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcR1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK4a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK1a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcM1U.BoAllocFRcM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcM5 BoAllocFRcMW BoAllocFRcMI.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
Lemma chainR_of_nth : forall (m : mem) q,
  (forall i b, nth_error q i = Some b -> bcell m b (hda (skipn (Datatypes.S i) q) 0)) -> chainR m q 0.
Proof.
  intros m q. induction q as [|b r IH]; intros H; [exact I|]. (lazymatch goal with |- ?G => let G' := eval cbn [chainR] in G in change_no_check G' end). split; [exact (H 0%nat b eq_refl)|].
  apply IH. intros i b0 Hi. exact (H (Datatypes.S i) b0 Hi).
Qed.
Lemma hda_skipn_nth : forall q i, hda (skipn i q) 0 = match nth_error q i with Some b => ba_addr b | None => 0 end.
Proof. intros q i. rewrite hda_nxaddr. apply nxaddr_skipn. Qed.

Section MK.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variable MINSZ : Z.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis G_min : 0 <= MINSZ <= 2 ^ 28.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma FIRST_DEF : forall st Lc FF (M : mem) mdl qt qg, WFq bt st Lc FF qt qg -> Rep bt st Lc FF M mdl -> a_gq st <> [] ->
    forall a : word, IB bt + 896 <= U a < IB bt + 904 -> M a <> None.
  Proof using. intros st Lc FF M mdl qt qg _ RP NE. exact (rep_first_def bt st Lc FF M mdl RP NE). Qed.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation S0' := (Z_to_bv 64 (0x10ab58 + 888) : word).
  #[local] Abbreviation S1' := (Z_to_bv 64 MINSZ : word).
  #[local] Abbreviation S2' := (Z_to_bv 64 (0x10ab58 + 728) : word).

  (* [comment removed for export] *)
  Definition rc_pre_post_m (st2 : ast) (Lc FF : list (Z * Z)) (M : mem) (mdl : Model) (R : bvmap 5 word) (S ret : word) (c' : config) : Prop :=
    exists fx1 (M1 : mem) mdl1 (R1 : bvmap 5 word) stm pb0 rest,
      c' = mkCfg (@mkst fx1 R1 (Z_to_bv 64 0x4e7e4) M1 (seg_rom BSEGS)) mdl1
      /\ a_gq stm = pb0 ++ rest /\ pb0 <> [] /\ q_bytes rest <= MINSZ
      /\ a_tq stm = a_tq st2 /\ a_kact stm = a_kact st2 /\ ((forall h, holes_le h st2 -> holes_le h stm) /\ free_keeps st2 stm)   (* [comment removed for export] *)
      /\ invb bt FXOK S (XP bt pb0) (q_bytes (a_tq st2)) (q_bytes (a_gq st2)) Lc FF stm M1 mdl1 rest (Z_to_bv 64 0x4e574)
              S0' S1' S2' (getr R 13) (getr R 12) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
              fx1 stm M1 mdl1 R1 pb0
      /\ getr R1 10 = Z_to_bv 64 (Z.of_nat (length pb0))
      /\ rep_list bt M1 (IB bt + 888) rest
      /\ (rdn BSEGS M1 (at_ S (-2216)) 8 = Some (LE8 ret) /\ rdn BSEGS M1 (at_ S (-2224)) 8 = Some (LE8 (getr R 8))
          /\ rdn BSEGS M1 (at_ S (-2232)) 8 = Some (LE8 (getr R 9)) /\ rdn BSEGS M1 (at_ S (-2240)) 8 = Some (LE8 (getr R 18))
          /\ rdn BSEGS M1 (at_ S (-2248)) 8 = Some (LE8 (getr R 19)) /\ rdn BSEGS M1 (at_ S (-2256)) 8 = Some (LE8 (getr R 20)))
      /\ dr_keep R R1
      /\ (forall a : word, M1 a <> M a ->
            ((U S - 2400 <= U a < U S - 2208) \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a)) /\ M1 a <> None)
      /\ lazy_kept (bt_ia bt) Lc FF mdl mdl1 /\ same_except_vm mdl mdl1.

  Theorem rc_prefix_kat_m : forall fx st2 Lc FF (M M0 : mem) mdl (R : bvmap 5 word) (sp ret stk : word),
    FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    WFX bt st2 Lc FF -> a_tq st2 = [] -> 2 ^ 28 < q_bytes (a_gq st2) < 2 ^ 41 -> ~ arm_nomerge st2 ->
    Rep bt st2 Lc FF M0 mdl -> (forall a : word, M a <> M0 a -> U a = IB bt + 881) -> M (Z_to_bv 64 (IB bt + 881)) = Some (Z_to_bv 8 1) ->
    (forall a : word, IB bt + 904 <= U a < IB bt + 912 -> M a <> None) ->
    M0 (Z_to_bv 64 (IB bt + 880)) = Some (Z_to_bv 8 0) -> M0 (Z_to_bv 64 (IB bt + 881)) = Some (Z_to_bv 8 0) ->
    getr R 1 = ret -> getr R 2 = sp ->
    getr R 10 = Z_to_bv 64 (IB bt + 728) -> getr R 12 = Z_to_bv 64 (bt_thread bt + T_PC) -> getr R 13 = stk ->
    getr R 11 = Z_to_bv 64 MINSZ ->
    getr R 4 = Z_to_bv 64 (ia_tp (bt_ia bt)) ->
    U sp mod 16 = 0 -> CEIL + 1376 <= U sp -> U sp + 2224 <= PTRHI -> ret_ok ret ->
    (forall a : word, U sp - 1376 <= U a < U sp -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
    katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x4e404) M (seg_rom BSEGS)) mdl)
         (rc_pre_post_m st2 Lc FF M mdl R (at_ sp 2208) ret).
  Proof using G_min BT_ia BT_segs.
    intros fx st2 Lc FF M M0 mdl R sp ret stk HFX HH MW WX ETQ GQB MRG RP DM L881 D904 D880 D881 X1 X2 X10 X12 X13 X11 X4 SP16 SPlo SPhi RET SOK.
    pose proof ceil_rng as CR. pose proof (u64_range sp) as Hsp. unfold PTRHI in SPhi.
    pose proof (WFX_WFq bt st2 Lc FF WX) as W.
    set (S := at_ sp 2208).
    assert (US : U S = U sp + 2208) by ((lazymatch goal with |- ?G => let G' := eval unfold S in G in change_no_check G' end); rewrite at_u by lia; reflexivity).
    assert (ES : at_ S (-2208) = sp) by (apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (HS7 : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47) by (rewrite US; clear - CR SPlo SPhi Hsp; lia).
    pose proof (u64_range S) as HSr.
    (* [comment removed for export] *)
    pose proof (thread_dyn bt st2 Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & _ & _ & _ & _ & _ & _ & SB0 & SB1 & SBH & _).
    assert (SZ : forall b m n, In b (a_gq st2) -> In (m, n) (ba_items b) -> 0 <= n).
    { intros b m n Hb Hin. destruct W as (_ & _ & (_ & QG & _) & _). rewrite Forall_forall in QG.
      destruct (QG b Hb) as (_ & _ & WI). destruct (WI m n Hin) as [Xn _]. clear - Xn. lia. }
    assert (BF : forall b, In b (a_gq st2) -> SBEG <= ba_addr b /\ ba_addr b + 8192 <= SBEG + 2 ^ 37 /\ 8192 <= ba_bytes b /\ Z.of_nat (length (ba_items b)) <= 1021).
    { intros b Hb. destruct (batch_facts bt st2 Lc FF W b ltac:(apply in_app_iff; right; exact Hb)) as (_ & L0 & G1 & G2).
      pose proof (AsAinvOpsRc3.ba_bytes_ge b ltac:(intros m0 n0 Hin0; exact (SZ b m0 n0 Hb Hin0))) as G4.
      unfold KSPACE, BATCHSZ, BATCHCAP in *. clear - L0 G1 G2 G4. lia. }
    unfold KSPACE, PG, AS_HEAPLO in *.
    assert (GLEN : 8192 * Z.of_nat (length (a_gq st2)) <= q_bytes (a_gq st2)).
    { pose proof (AsAinvOpsRc3.q_bytes_ge (a_gq st2) ltac:(intros b0 m0 n0 Hb0 Hin0; exact (SZ b0 m0 n0 Hb0 Hin0))) as G1. unfold BATCHSZ in G1. exact G1. }
    (* [comment removed for export] *)
    assert (MT : 8192 * Z.of_nat (length (a_gq st2)) < q_bytes (a_gq st2) /\ 100 * q_bytes (a_gq st2) < 1638400 * Z.of_nat (length (a_gq st2))).
    { unfold arm_nomerge in MRG. clear - MRG. lia. }
    destruct (a_gq st2) as [|cur l] eqn:EGQ0; [exfalso; cbn in MT; clear - MT; lia|].
    assert (NEl : l <> []) by (intros E; rewrite E in MT, GQB; cbn [length] in MT; clear - MT GQB; lia).
    assert (LEN28 : 1 + Z.of_nat (length l) < 2 ^ 28) by (cbn [length] in GLEN; clear - GLEN GQB; lia).
    change (q_bytes (cur :: l)) with (ba_bytes cur + q_bytes l) in GQB, MT.
    set (A := map ba_addr (cur :: l)).
    assert (GEOA : forall a, In a A -> AIMGHI <= a /\ a + 8192 <= U S - 3584).
    { intros a Ha. apply in_map_iff in Ha. destruct Ha as (b & <- & Hb). destruct (BF b Hb) as (G1 & G2 & _). rewrite US. clear - G1 G2 SBH SB1 SPlo. lia. }
    assert (NDgq : List.NoDup A).
    { pose proof W as (_ & _ & (_ & _ & _ & _ & ND & _) & _). rewrite ETQ, EGQ0 in ND. exact ND. }
    assert (SEPA : forall a1 a2, In a1 A -> In a2 A -> a1 <> a2 -> bsep a1 a2).
    { intros a1 a2 H1 H2 NE. apply in_map_iff in H1. apply in_map_iff in H2. destruct H1 as (bx & <- & Hbx). destruct H2 as (by' & <- & Hby).
      destruct (batch_facts bt st2 Lc FF W bx ltac:(apply in_app_iff; right; rewrite EGQ0; exact Hbx)) as (CVx & _).
      destruct (batch_facts bt st2 Lc FF W by' ltac:(apply in_app_iff; right; rewrite EGQ0; exact Hby)) as (CVy & _).
      destruct (chunk_cases bt st2 Lc FF W BATCHCLASS (ba_addr bx) BATCHCLASS (ba_addr by') ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVx CVy) as [[_ E] | D];
        [exfalso; exact (NE E) | change (csize BATCHCLASS) with 8192 in D; (lazymatch goal with |- ?G => let G' := eval unfold bsep in G in change_no_check G' end); exact D]. }
    assert (INA : forall b, In b (cur :: l) -> In (ba_addr b) A /\ blen b <= 1021).
    { intros b Hb. split; [apply in_map; exact Hb | destruct (BF b Hb) as (_ & _ & _ & G4); exact G4]. }
    assert (SZ8 : forall b, In b (cur :: l) -> 8192 <= ba_bytes b) by (intros b Hb; destruct (BF b Hb) as (_ & _ & G3 & _); exact G3).
    (* [comment removed for export] *)
    pose proof RP as (_ & Ri & _ & _ & _ & RBg & _ & _ & _ & _ & _ & _ & R13 & R14 & _). rewrite EGQ0 in RBg.
    destruct Ri as (_ & _ & _ & I880 & I881 & _ & (Glen & Gfirst & Glast & Gbytes) & _). rewrite EGQ0 in Glen, Gfirst, Glast, Gbytes.
    destruct R14 as (B1 & B2 & _).
    rewrite BT_segs in I880, I881, Glen, Gfirst, Glast, Gbytes.
    unfold IB in I880, I881, Glen, Gfirst, Glast, Gbytes, DM, L881, D904, D880, D881, X10.
    rewrite BT_ia in I880, I881, Glen, Gfirst, Glast, Gbytes, DM, L881, D904, D880, D881, X10.
    cbn [ia_instance both_addrs] in I880, I881, Glen, Gfirst, Glast, Gbytes, DM, L881, D904, D880, D881, X10.
    assert (EQM : forall a : word, ~ (U a = 0x10ab58 + 881) -> M a = M0 a).
    { intros a Ha. destruct (decide (M a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (DM a N)). }
    assert (GR0 : mem_grows M0 M).
    { intros a Ha. destruct (decide (M a = M0 a)) as [E|N]; [rewrite E; exact Ha|].
      replace a with (Z_to_bv 64 (0x10ab58 + 881) : word) by (apply bv_eq; rewrite (DM a N); reflexivity). rewrite L881. discriminate. }
    set (Hd := HID st2 mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st2 mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHB : forall b z, In b (cur :: l) -> ba_addr b <= z < ba_addr b + 8192 -> Hd (Z_to_bv 64 z) = false).
    { intros b z Hb Hz. destruct (BF b Hb) as (G1 & G2 & _). apply HID_notlazy; [clear - Hz G1 G2 SB0 SB1 CR; lia|].
      apply (rep_nolazy_batch bt st2 Lc FF M0 mdl W RP b z ltac:(apply in_app_iff; right; rewrite EGQ0; exact Hb)). (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). exact Hz. }
    pose (memD := mrestrict Hd M).
    pose (XL := fun z : Z => z = 0x10ab58 + 881).
    assert (IMGC : forall c v, cellZ BSEGS M0 c 8 v -> 0x10ab58 + 888 <= c -> c + 8 <= 0x10ab58 + 920 -> rdn BSEGS memD (Z_to_bv 64 c) 8 = Some (LE8 (Z_to_bv 64 v))).
    { intros c v C H1 H2. apply (cellX Hd M M0 XL c 8 v C EQM); [clear - H1; lia | clear - H2; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split; [(lazymatch goal with |- ?G => let G' := eval unfold XL in G in change_no_check G' end); clear - Hz H1; lia | apply NHs; [clear - Hz H1 H2; lia | right; clear - Hz H1 H2; lia]]. }
    assert (K_glen : cellq memD (0x10ab58 + 888) (1 + Z.of_nat (length l))).
    { (lazymatch goal with |- ?G => let G' := eval unfold cellq in G in change_no_check G' end). replace (1 + Z.of_nat (length l)) with (Z.of_nat (length (cur :: l))) by ((lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); clear; lia). apply IMGC; [exact Glen | clear; lia | clear; lia]. }
    assert (K_first : cellq memD (0x10ab58 + 896) (ba_addr cur)).
    { (lazymatch goal with |- ?G => let G' := eval unfold cellq in G in change_no_check G' end). replace (0x10ab58 + 896) with (0x10ab58 + 888 + 8) by (clear; lia). apply IMGC; [exact Gfirst | clear; lia | clear; lia]. }
    assert (K_last : cellq memD (0x10ab58 + 904) (lasta l (ba_addr cur))).
    { (lazymatch goal with |- ?G => let G' := eval unfold cellq in G in change_no_check G' end). replace (0x10ab58 + 904) with (0x10ab58 + 888 + 16) by (clear; lia).
      replace (lasta l (ba_addr cur)) with (match rev (cur :: l) with [] => 0 | b :: _ => ba_addr b end) by (symmetry; apply (lasta_rev (cur :: l) 0)).
      apply IMGC; [exact Glast | clear; lia | clear; lia]. }
    assert (K_gqb : cellq memD (0x10ab58 + 912) (ba_bytes cur + q_bytes l)).
    { (lazymatch goal with |- ?G => let G' := eval unfold cellq in G in change_no_check G' end). replace (0x10ab58 + 912) with (0x10ab58 + 888 + 24) by (clear; lia). apply IMGC; [exact Gbytes | clear; lia | clear; lia]. }
    destruct (rdn1_exK M 0x10aeca (or_introl eq_refl)) as [b2 Hb2]. destruct (rdn1_exK M 0x10aecb (or_intror eq_refl)) as [b3 Hb3].
    assert (K_lock : rdn BSEGS memD (Z_to_bv 64 0x10aec8) 4 = Some [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3]).
    { (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite rdn_mrestrict; [| clear; wd_ulia_c | clear - NHs; unorm; apply hid_off_of; intros z Hz; split; [lia | apply NHs; [lia | right; lia]]].
      apply rdn4_of_bytesK; [clear; wd_ulia | | | |].
      - unfold byteZ, cellN in I880. rewrite w2b1 in I880 by (clear; lia). eapply rd_same; [| clear; wd_ulia_c | exact I880].
        intros x Hx. apply EQM. clear - Hx. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
      - replace (at_ (Z_to_bv 64 0x10aec8) 1) with (Z_to_bv 64 (0x10ab58 + 881) : word) by (clear; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity).
        exact (rdn1_of_someK M _ _ L881).
      - replace (at_ (Z_to_bv 64 0x10aec8) 2) with (Z_to_bv 64 0x10aeca : word) by (clear; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity). exact Hb2.
      - replace (at_ (Z_to_bv 64 0x10aec8) 3) with (Z_to_bv 64 0x10aecb : word) by (clear; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity). exact Hb3. }
    assert (BCELL : forall b c v, In b (cur :: l) -> cellZ BSEGS M0 c 8 v -> ba_addr b <= c -> c + 8 <= ba_addr b + 8192 -> rdn BSEGS memD (Z_to_bv 64 c) 8 = Some (LE8 (Z_to_bv 64 v))).
    { intros b c v Hb C H1 H2. destruct (BF b Hb) as (G1 & G2 & _).
      apply (cellX Hd M M0 XL c 8 v C EQM); [clear - H1 G1 SB0; lia | clear - H2 G2 SB1 CR; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split; [(lazymatch goal with |- ?G => let G' := eval unfold XL in G in change_no_check G' end); clear - Hz H1 G1 SBH; lia | apply (NHB b); [exact Hb | clear - Hz H1 H2; lia]]. }
    assert (CHD : chainR memD (cur :: l) 0).
    { apply chainR_of_nth. intros i b Hb. pose proof (nth_error_In _ _ Hb) as Hin. destruct (BF b Hin) as (G1 & G2 & G3 & G4).
      destruct (RBg i b Hb) as (C1 & C2 & C3 & C4 & _). rewrite BT_segs in C1, C2, C3, C4. (lazymatch goal with |- ?G => let G' := eval unfold bcell in G in change_no_check G' end). rewrite hda_skipn_nth.
      split; [apply (BCELL b); [exact Hin | exact C1 | clear; lia | clear; lia]|].
      split; [apply (BCELL b); [exact Hin | exact C2 | clear; lia | clear; lia]|].
      split; [apply (BCELL b); [exact Hin | exact C3 | clear; lia | clear; lia]|].
      intros j mn Hj. pose proof (nth_error_lt _ _ _ Hj) as Lj. apply (BCELL b); [exact Hin | exact (C4 j mn Hj) | clear; lia | clear - Lj G4; lia]. }
    assert (WRD : forall a k n, In a A -> 0 <= k -> k + Z.of_nat n <= 8192 -> store_ok BSEGS memD (Z_to_bv 64 (a + k)) n = true).
    { intros a k n Ha H0 H1. apply in_map_iff in Ha. destruct Ha as (b & <- & Hb). destruct (BF b Hb) as (G1 & G2 & _).
      destruct (In_nth_error _ _ Hb) as (i & Hi). destruct (RBg i b Hi) as (_ & _ & _ & _ & BW). rewrite BT_segs in BW. unfold BATCHSZ in BW.
      apply (sokX Hd M M0 _ _ (ba_addr b + k) n BW GR0); [clear - H0; lia | clear - H1; lia | clear - G2 SB1 CR H1; lia | clear - G1 SB0 H0; lia |].
      intros z Hz. apply (NHB b); [exact Hb | clear - Hz H0 H1; lia]. }
    assert (SOKstk : store_ok BSEGS memD (at_ S (-2400)) 192 = true).
    { replace (at_ S (-2400)) with (Z_to_bv 64 (U S - 2400) : word) by (clear - HS7; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - HS7; lia | clear - HS7; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - apply (SOK (Z_to_bv 64 z)). clear - Hz US Hsp SPlo CR. unorm. lia.
      - apply NHs; [clear - Hz US Hsp SPlo CR; lia | left; clear - Hz US SPlo; lia]. }
    (* [comment removed for export] *)
    destruct (run_rc_pre_m memD (seg_rom BSEGS) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                (Z_to_bv 64 (T + T_PC)) stk MINSZ b2 b3 cur l A R
                X1 ltac:(rewrite ES; exact X2) X10 X11 X12 X13 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HS7
                ltac:(clear - G_min; lia) NEl LEN28 ltac:(clear - GQB; lia) ltac:(cbn [length] in MT; clear - MT; lia) ltac:(clear - GQB G_min; lia)
                GEOA SEPA INA NDgq SZ8 SOKstk WRD K_lock CHD K_glen K_first K_last K_gqb)
      as (r1 & mem' & RUN & PP & HR1 & A10 & A3 & A4 & A26 & A27).
    set (G' := fst (mergeF cur l)) in *. set (E' := snd (mergeF cur l)) in *. set (kk := mk MINSZ G') in *.
    set (pb0 := E' ++ firstn kk G') in *. set (rest := skipn kk G') in *.
    destruct PP as (PO & PG' & CHT & CHR & Q888 & Q896 & Q904 & Q912 & T88 & T80 & T72 & T64 & Pdef & NEpb & RESTB).
    pose proof (fr_rc0_grows memD S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (Z_to_bv 8 1) b2 b3) as GRa.
    pose proof (fr_rc0_outside memD S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (Z_to_bv 8 1) b2 b3 HS7) as OUTa.
    remember (fr_rc0 memD S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (Z_to_bv 8 1) b2 b3) as Ma eqn:EMa.
    pose proof (fr_dr0_outside (fr_rcu mem') S (Z_to_bv 64 0x4e574) S0' S1' S2' stk (Z_to_bv 64 (T + T_PC)) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                  (Z_to_bv 64 (T + T_PC)) stk HS7) as OUTd.
    pose proof (fr_dr0_grows (fr_rcu mem') S (Z_to_bv 64 0x4e574) S0' S1' S2' stk (Z_to_bv 64 (T + T_PC)) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                  (Z_to_bv 64 (T + T_PC)) stk) as GRd.
    assert (FRM : dr_frame bt S (Z_to_bv 64 0x4e574) S0' S1' S2' stk (Z_to_bv 64 (T + T_PC)) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                    (fr_dr0 (fr_rcu mem') S (Z_to_bv 64 0x4e574) S0' S1' S2' stk (Z_to_bv 64 (T + T_PC)) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                       (Z_to_bv 64 (T + T_PC)) stk)).
    { (lazymatch goal with |- ?G => let G' := eval unfold dr_frame in G in change_no_check G' end). repeat split; [apply fr_dr0_ra | apply fr_dr0_s0 | apply fr_dr0_s1 | apply fr_dr0_s2 | apply fr_dr0_s3 | apply fr_dr0_s4 | apply fr_dr0_s5
                                     | apply fr_dr0_s6 | apply fr_dr0_s7 | apply fr_dr0_s8 | apply fr_dr0_s9 | apply fr_dr0_a2]; exact HS7. }
    remember (fr_dr0 (fr_rcu mem') S (Z_to_bv 64 0x4e574) S0' S1' S2' stk (Z_to_bv 64 (T + T_PC)) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                (Z_to_bv 64 (T + T_PC)) stk) as MF eqn:EMF.
    (* [comment removed for export] *)
    replace (0x4e404%bv : word) with (Z_to_bv 64 0x4e404 : word) in RUN by (apply bv_eq; reflexivity).
    replace (0x4e7e4%bv : word) with (Z_to_bv 64 0x4e7e4 : word) in RUN by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st2 Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st2)
             (@mkst fx R (Z_to_bv 64 0x4e404) M (seg_rom BSEGS)) (@mkst fx r1 (Z_to_bv 64 0x4e7e4) MF (seg_rom BSEGS)) mdl).
    { apply lazy_cover_HID. } { exact B1. } { exact B2. } { exact HH. } { rewrite restrict_mkstK. exact RUN. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x4e404) M (seg_rom BSEGS))) with M by reflexivity.
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
    destruct SF1 as (_ & _ & Elz1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh1 & _).
    set (M1 := munrestrict Hd M MF).
    assert (VIS : forall a : word, Hd a = false -> M1 a = MF a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (HIDv : forall a : word, Hd a = true -> M1 a = M a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_on; exact Ha).
    assert (MrM : forall a : word, Hd a = false -> memD a = M a) by (intros a Ha; apply mrestrict_off; exact Ha).
    assert (GRF : mem_grows memD MF).
    { eapply mem_grows_trans; [exact GRa|]. eapply mem_grows_trans; [exact PG'|]. eapply mem_grows_trans; [apply fr_rcu_grows | exact GRd]. }
    assert (GR1 : mem_grows M M1).
    { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply GRF. rewrite (MrM a Eh). exact Ha. }
    assert (GR01 : mem_grows M0 M1) by (eapply mem_grows_trans; [exact GR0 | exact GR1]).
    (* [comment removed for export] *)
    pose (FOOT := fun z : Z => (U S - 2400 <= z < U S - 2208) \/ (0x10aec8 <= z < 0x10aecc) \/ mfoot S A z).
    assert (OUT1 : forall a : word, ~ FOOT (U a) -> M1 a = M a).
    { intros a NF. destruct (Hd a) eqn:Eh; [exact (HIDv a Eh)|]. rewrite (VIS a Eh), <- (MrM a Eh). unfold FOOT in NF.
      rewrite OUTd by (clear - NF; lia). rewrite fr_rcu_outside by (clear - NF; lia). rewrite (PO a ltac:(clear - NF; tauto)).
      apply OUTa; clear - NF; lia. }
    assert (FOOTd : Xdec FOOT).
    { (lazymatch goal with |- ?G => let G' := eval unfold FOOT, mfoot in G in change_no_check G' end). apply Xdec_or; [apply Xdec_iv|]. apply Xdec_or; [apply Xdec_iv|].
      apply Xdec_or; [apply (Xdec_ex_list A (fun a z0 => a <= z0 < a + 8192)); intros a; apply Xdec_iv|]. apply Xdec_or; apply Xdec_iv. }
    assert (CH1 : forall a : word, M1 a <> M a -> FOOT (U a)).
    { intros a NE. destruct (FOOTd (U a)) as [F | NF]; [exact F | exfalso; exact (NE (OUT1 a NF))]. }
    assert (DEF01 : forall a : word, M1 a <> M0 a -> M1 a <> None).
    { intros a NE E1. apply NE. rewrite E1. destruct (M0 a) eqn:E0; [|reflexivity]. exfalso.
      assert (D : M0 a <> None) by (rewrite E0; discriminate). apply GR01 in D. exact (D E1). }
    assert (MEMP : forall a : word, Hd a = false -> (U a < U S - 2400 \/ U S - 2288 <= U a) -> (U a < 0x10aec8 \/ 0x10aeca <= U a) -> M1 a = mem' a).
    { intros a Eh A1 A2. rewrite (VIS a Eh), OUTd by exact A1. apply fr_rcu_outside. exact A2. }
    assert (STK1 : forall kk0 v, -2400 <= kk0 -> kk0 + 8 <= -2208 -> rdn BSEGS MF (at_ S kk0) 8 = Some v -> rdn BSEGS M1 (at_ S kk0) 8 = Some v).
    { intros kk0 v Hk1 Hk2 Hr. eapply rd_same; [| clear - Hk1 Hk2 HS7; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [apply u64_range | left; clear - Hx Hk1 Hk2 HS7 US SPlo; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (STKP : forall kk0 v, -2288 <= kk0 -> kk0 + 8 <= -2208 -> rdn BSEGS mem' (at_ S kk0) 8 = Some v -> rdn BSEGS M1 (at_ S kk0) 8 = Some v).
    { intros kk0 v Hk1 Hk2 Hr. eapply rd_same; [| clear - Hk1 Hk2 HS7; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. assert (Hx' : U S - 2288 <= U x < U S - 2208) by (clear - Hx Hk1 Hk2 HS7; rewrite at_u in Hx by lia; cbn in Hx; lia).
      apply MEMP; [rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHs; [apply u64_range | left; clear - Hx' US SPlo; lia] | right; clear - Hx'; lia | right; clear - Hx' HS7; lia]. }
    assert (STKA : forall kk0 v, -2256 <= kk0 -> kk0 + 8 <= -2208 -> rdn BSEGS Ma (at_ S kk0) 8 = Some v -> rdn BSEGS M1 (at_ S kk0) 8 = Some v).
    { intros kk0 v Hk1 Hk2 Hr. apply STKP; [clear - Hk1; lia | exact Hk2 |].
      eapply rd_same; [| clear - Hk1 Hk2 HS7; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. assert (Hx' : U S - 2256 <= U x < U S - 2208) by (clear - Hx Hk1 Hk2 HS7; rewrite at_u in Hx by lia; cbn in Hx; lia).
      apply PO. (lazymatch goal with |- ?G => let G' := eval unfold mfoot in G in change_no_check G' end). intros [(a & Ha & Q) | [Q | Q]]; [destruct (GEOA a Ha) as [_ G2]; clear - Q Hx' G2; lia | clear - Q Hx' HS7; lia | clear - Q Hx'; lia]. }
    assert (IMGP : forall c v, 0x10ab58 + 888 <= c -> c + 8 <= 0x10ab58 + 920 -> rdn BSEGS mem' (Z_to_bv 64 c) 8 = Some v -> rdn BSEGS M1 (Z_to_bv 64 c) 8 = Some v).
    { intros c v H1 H2 Hr. eapply rd_same; [| clear - H1 H2; wd_ulia_c | exact Hr].
      intros x Hx. assert (Hx' : c <= U x < c + 8) by (clear - Hx H1 H2; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia).
      apply MEMP; [rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHs; [apply u64_range | right; clear - Hx' H1 H2; lia] | left; clear - Hx' H2 HS7; lia | right; clear - Hx' H1; lia]. }
    (* [comment removed for export] *)
    assert (OBJM : forall a (x : word), In a A -> a <= U x < a + 8192 -> M1 x = mem' x).
    { intros a x Ha Hx. destruct (GEOA a Ha) as [G1 G2]. apply in_map_iff in Ha. destruct Ha as (b & Ea & Hb).
      apply MEMP; [rewrite <- (Z_to_bv_bv_unsigned 64 x); apply (NHB b); [exact Hb | rewrite Ea; exact Hx] | left; clear - Hx G2; lia | right; clear - Hx G1; lia]. }
    (* [comment removed for export] *)
    set (stm := st_merge st2 cur l).
    pose proof (WFq_st_merge bt st2 Lc FF cur l _ _ W EGQ0) as Wm. fold stm in Wm.
    assert (EPR : pb0 ++ rest = gq_merge cur l) by ((lazymatch goal with |- ?G => let G' := eval unfold pb0, rest, gq_merge in G in change_no_check G' end); fold G' E'; rewrite <- app_assoc, firstn_skipn; reflexivity).
    assert (EGQm : a_gq stm = pb0 ++ rest) by ((lazymatch goal with |- ?G => let G' := eval unfold stm, st_merge in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_gq set_gq] in G in change_no_check G' end); symmetry; exact EPR).
    assert (MGA : forall b, In b (pb0 ++ rest) -> In (ba_addr b) A /\ bgeo b).
    { intros b Hb. rewrite EPR in Hb. unfold gq_merge in Hb.
      assert (Ab : In (ba_addr b) A) by (apply (Permutation_in _ (mf_addrs l cur)); apply in_map; exact Hb).
      split; [exact Ab|]. destruct (GEOA _ Ab) as [G1 G2].
      destruct (mf_forall (fun _ => True) (fun _ => True) l cur) with (b := b) as (_ & _ & P3); [| exact Hb |].
      - intros b1 Hb1. split; [exact I|]. split; [intros; exact I | exact (proj2 (INA b1 Hb1))].
      - (lazymatch goal with |- ?G => let G' := eval unfold bgeo in G in change_no_check G' end). clear - G1 G2 P3 HS7 HSr. lia. }
    assert (CHT1 : chainR M1 pb0 0).
    { apply (chainR_frame mem' M1); [intros b Hb; exact (proj2 (MGA b ltac:(apply in_app_iff; left; exact Hb))) | | exact CHT].
      intros b x Hb Hx. exact (OBJM _ x (proj1 (MGA b ltac:(apply in_app_iff; left; exact Hb))) Hx). }
    assert (CHR1 : chainR M1 rest 0).
    { apply (chainR_frame mem' M1); [intros b Hb; exact (proj2 (MGA b ltac:(apply in_app_iff; right; exact Hb))) | | exact CHR].
      intros b x Hb Hx. exact (OBJM _ x (proj1 (MGA b ltac:(apply in_app_iff; right; exact Hb))) Hx). }
    (* [comment removed for export] *)
    assert (QDEF1 : forall a : word, qhdr bt (U a) -> M1 a <> None).
    { intros a Q. unfold qhdr, IB in Q. rewrite BT_ia in Q. cbn [ia_instance both_addrs] in Q.
      assert (MP : M1 a = mem' a).
      { apply MEMP; [rewrite <- (Z_to_bv_bv_unsigned 64 a); apply NHs; [apply u64_range | right; clear - Q; lia] | left; clear - Q HS7; lia | right; clear - Q; lia]. }
      destruct (Z_lt_dec (U a) (0x10ab58 + 896)) as [L1 | L1]; [rewrite MP; apply Pdef; left; clear - Q L1; lia|].
      destruct (Z_lt_dec (U a) (0x10ab58 + 904)) as [L2 | L2].
      - apply GR01. apply (FIRST_DEF st2 Lc FF M0 mdl _ _ W RP ltac:(rewrite EGQ0; discriminate)). (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). clear - L1 L2. lia.
      - destruct (Z_lt_dec (U a) (0x10ab58 + 912)) as [L3 | L3]; [apply GR1; apply D904; clear - L2 L3; lia | rewrite MP; apply Pdef; right; clear - Q L3; lia]. }
    (* [comment removed for export] *)
    assert (LK0 : M1 (Z_to_bv 64 0x10aec8) = Some (Z_to_bv 8 0) /\ M1 (Z_to_bv 64 0x10aec9) = Some (Z_to_bv 8 0)).
    { destruct (fr_rcu_lock mem') as [L0 L1]. split.
      - rewrite VIS by (apply NHs; [clear; lia | right; clear; lia]). rewrite OUTd by (left; clear - HS7; wd_ulia). exact L0.
      - rewrite VIS by (apply NHs; [clear; lia | right; clear; lia]). rewrite OUTd by (left; clear - HS7; wd_ulia). exact L1. }
    assert (PADD : forall a : word, U a = 0x10aeca \/ U a = 0x10aecb -> M1 a <> None).
    { intros a Ha. rewrite MEMP; [| rewrite <- (Z_to_bv_bv_unsigned 64 a); apply NHs; [apply u64_range | right; clear - Ha; lia] | left; clear - Ha HS7; lia | right; clear - Ha; lia].
      apply PG'. destruct (fr_rc0_lock memD S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (Z_to_bv 8 1) b2 b3) as [P2 P3]. rewrite <- EMa in P2, P3.
      destruct Ha as [Ea | Ea]; [replace a with (Z_to_bv 64 0x10aeca : word) by (apply bv_eq; rewrite Ea; reflexivity); rewrite P2; discriminate
                                | replace a with (Z_to_bv 64 0x10aecb : word) by (apply bv_eq; rewrite Ea; reflexivity); rewrite P3; discriminate]. }
    (* [comment removed for export] *)
    set (M0b := fun a : word => if (U a =? 0x10aeca) || (U a =? 0x10aecb) then M1 a else M0 a).
    assert (RPb : Rep bt st2 Lc FF M0b mdl).
    { apply (Rep_frame_q bt st2 Lc FF M0 M0b mdl W RP). intros a NE. unfold M0b in NE |- *.
      destruct ((U a =? 0x10aeca) || (U a =? 0x10aecb)) eqn:EP; [| exfalso; exact (NE eq_refl)].
      apply orb_true_iff in EP. rewrite !Z.eqb_eq in EP. split; [| exact (PADD a EP)].
      intros RCELL. apply (instpad_not_cells bt st2 Lc FF W (U a)); [| exact RCELL]. (lazymatch goal with |- ?G => let G' := eval unfold instpad, IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). clear - EP. lia. }
    assert (GRb : mem_grows M0b M1).
    { intros a Ha. unfold M0b in Ha. destruct ((U a =? 0x10aeca) || (U a =? 0x10aecb)); [exact Ha | exact (GR01 a Ha)]. }
    assert (FOOTIb : forall a : word, M1 a <> M0b a -> qhdr bt (U a) \/ gq_objs st2 (U a) \/ CEIL <= U a).
    { intros a NE. unfold M0b in NE. destruct ((U a =? 0x10aeca) || (U a =? 0x10aecb)) eqn:EP; [exfalso; exact (NE eq_refl)|].
      apply orb_false_iff in EP. rewrite !Z.eqb_neq in EP. destruct EP as [NP1 NP2].
      destruct (decide (M1 a = M a)) as [E | N].
      - exfalso. rewrite E in NE. pose proof (DM a NE) as E881. rewrite <- E in NE. apply NE.
        replace a with (Z_to_bv 64 0x10aec9 : word) by (apply bv_eq; rewrite E881; reflexivity). rewrite (proj2 LK0). symmetry. exact D881.
      - destruct (CH1 a N) as [F | [F | F]].
        + right; right. clear - F US SPlo. lia.
        + exfalso. apply NE.
          destruct (Z.eq_dec (U a) 0x10aec8) as [E0 | N0]; [replace a with (Z_to_bv 64 0x10aec8 : word) by (apply bv_eq; rewrite E0; reflexivity); rewrite (proj1 LK0); symmetry; exact D880|].
          destruct (Z.eq_dec (U a) 0x10aec9) as [E1 | N1]; [replace a with (Z_to_bv 64 0x10aec9 : word) by (apply bv_eq; rewrite E1; reflexivity); rewrite (proj2 LK0); symmetry; exact D881|].
          exfalso. clear - F N0 N1 NP1 NP2. lia.
        + unfold mfoot in F. destruct F as [(a0 & Ha0 & Hr) | [F | F]].
          * right; left. apply in_map_iff in Ha0. destruct Ha0 as (b0 & Eb0 & Hb0). exists b0. split; [rewrite EGQ0; exact Hb0 | rewrite Eb0; (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); exact Hr].
          * left. (lazymatch goal with |- ?G => let G' := eval unfold qhdr, IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). exact F.
          * right; right. clear - F US SPlo. lia. }
    pose proof (repx_merge bt BT_segs BT_ia st2 Lc FF M0b M1 mdl mdl1 cur l pb0 rest _ _ W RPb EGQ0 EPR NEpb GRb FOOTIb CHT1 CHR1 QDEF1 SBM1 MI1) as RX1. fold stm in RX1.
    assert (XSUB : forall z, XP bt pb0 z -> XB bt stm z).
    { intros z [Q | (b & Hb & Hz)]; [left; exact Q | right]. exists (ba_addr b). split; [| exact Hz].
      assert (Hbm : In b (a_tq stm ++ a_gq stm)) by (apply in_app_iff; right; rewrite EGQm; apply in_app_iff; left; exact Hb).
      destruct (batch_facts bt stm Lc FF Wm b Hbm) as (CVb & _). split; [exact CVb | left; exists b; split; [exact Hbm | reflexivity]]. }
    (* [comment removed for export] *)
    assert (WRm : forall b, In b (pb0 ++ rest) -> writableZ (bt_segs bt) M1 (ba_addr b) (ba_addr b + BATCHSZ)).
    { intros b Hb. destruct (MGA b Hb) as [Ab _]. apply in_map_iff in Ab. destruct Ab as (b0 & Ea & Hb0). destruct (In_nth_error _ _ Hb0) as (i0 & Hi0).
      destruct (RBg i0 b0 Hi0) as (_ & _ & _ & _ & BW). rewrite Ea in BW. intros z Hz. destruct (BW z Hz) as [D0 S0]. split; [apply GR01; exact D0 | eapply store_ok_mono; [exact GR01 | exact S0]]. }
    assert (RB1 : rep_batches bt M1 pb0).
    { apply (rep_batches_of_chain bt BT_segs M1 pb0 CHT1). intros b Hb. apply WRm. apply in_app_iff. left. exact Hb. }
    assert (PEND1 : pend bt S (Z_to_bv 64 0x4e574) S0' S1' S2' stk (Z_to_bv 64 (T + T_PC)) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) M1 pb0).
    { (lazymatch goal with |- ?G => let G' := eval unfold pend in G in change_no_check G' end). split; [exact RB1|].
      split; [apply STKP; [clear; lia | clear; lia | exact T88]|].
      split; [apply STKP; [clear; lia | clear; lia | exact T80]|].
      split; [apply STKP; [clear; lia | clear; lia | exact T64]|].
      split; [intros a Ha; apply GR1; apply (proj1 (SOK a ltac:(clear - Ha US; lia)))|].
      rewrite EMF in FRM. destruct FRM as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11). rewrite <- EMF in F0, F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11.
      (lazymatch goal with |- ?G => let G' := eval unfold dr_frame in G in change_no_check G' end). repeat split; (apply STK1; [clear; lia | clear; lia | assumption]). }
    assert (RL1 : rep_list bt M1 (IB bt + 888) rest).
    { (lazymatch goal with |- ?G => let G' := eval unfold rep_list, IB in G in change_no_check G' end). rewrite BT_segs, BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end).
      replace (match rev rest with [] => 0 | b :: _ => ba_addr b end) with (lasta rest 0) by (apply lasta_rev).
      split; [apply IMGP; [clear; lia | clear; lia | exact Q888]|].
      split; [replace (0x10ab58 + 888 + 8) with (0x10ab58 + 896) by (clear; lia); apply IMGP; [clear; lia | clear; lia | exact Q896]|].
      split; [replace (0x10ab58 + 888 + 16) with (0x10ab58 + 904) by (clear; lia); apply IMGP; [clear; lia | clear; lia | exact Q904]|].
      replace (0x10ab58 + 888 + 24) with (0x10ab58 + 912) by (clear; lia). apply IMGP; [clear; lia | clear; lia | exact Q912]. }
    assert (SOK1 : forall a : word, U S - 3584 <= U a < U S - 2400 -> M1 a <> None /\ store_ok BSEGS M1 a 1%nat = true).
    { intros a Ha. assert (D : M1 a <> None) by (apply GR1; apply (proj1 (SOK a ltac:(clear - Ha US; lia)))). exact (conj D (store_ok1_defK M1 a D)). }
    (* [comment removed for export] *)
    apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold rc_pre_post_m in G in change_no_check G' end). rewrite EGQ0. exists fx, M1, mdl1, r1, stm, pb0, rest.
    split; [reflexivity|]. split; [exact EGQm|]. split; [exact NEpb|]. split; [exact RESTB|].
    split; [reflexivity|]. split; [reflexivity|]. split; [split; [intros h Hh; exact Hh | (lazymatch goal with |- ?G => let G' := eval unfold stm, st_merge in G in change_no_check G' end); apply fk_set_gq]|].
    split.
    { rewrite X12. rewrite X13. (lazymatch goal with |- ?G => let G' := eval unfold invb in G in change_no_check G' end). split; [exact HFX|]. split; [rewrite Eh1; exact HH|]. split; [exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW)|]. split; [exact Wm|].
      split; [exact RX1|]. split; [exact EGQm|]. split; [exact XSUB|]. split; [exact QDEF1|]. split; [exact PEND1|]. split; [exact SOK1|].
      split; [exact HR1|]. split; [rewrite A4; exact X4|]. apply rc_acc_refl. }
    split; [exact A10|].
    split; [exact RL1|].
    split.
    { repeat split; (apply STKA; [clear; lia | clear; lia | rewrite EMa]);
        [apply fr_rc0_ra | apply fr_rc0_s0 | apply fr_rc0_s1 | apply fr_rc0_s2 | apply fr_rc0_s3 | apply fr_rc0_s4]; exact HS7. }
    split; [exact (conj A3 (conj A4 (conj A26 A27)))|].
    split.
    { intros a NE. split.
      - destruct (CH1 a NE) as [F | [F | F]]; [left; exact F | right; right; rewrite BT_ia; exists 0x10ab58, 0x10b9b8; split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | clear - F; lia]|].
        unfold mfoot in F. destruct F as [(a0 & Ha0 & Hr) | [F | F]].
        + right; left. apply in_map_iff in Ha0. destruct Ha0 as (b0 & Eb0 & Hb0). apply (OBL_rt_private_pf bt st2 Lc FF W (U a)). right. exists b0.
          split; [apply in_app_iff; right; rewrite EGQ0; exact Hb0 | (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); rewrite Eb0; exact Hr].
        + right; right. rewrite BT_ia. exists 0x10ab58, 0x10b9b8. split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | clear - F; lia].
        + left. clear - F. lia.
      - intros E1. apply NE. rewrite E1. destruct (M a) eqn:E0; [|reflexivity]. exfalso.
        assert (D : M a <> None) by (rewrite E0; discriminate). apply GR1 in D. exact (D E1). }
    split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz1; reflexivity | apply same_but_materialized_except_vm; exact SBM1].
  Qed.
End MK.
End BoAllocFRcMK.
Module BoAllocFRcMK5.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcM1U.BoAllocFRc1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRc2.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK4a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK1a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 BoAllocFRcK5 BoAllocFRcMW BoAllocFRcMK.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).


Section MK5.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variable MINSZ : Z.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis CELL_min : In (0x10ab58 + 800, 8%nat, MINSZ) (bt_consts bt).
  Hypothesis G_min : 0 <= MINSZ <= 2 ^ 28.
  Hypothesis HITEM : rc_item_stmt bt FXOK arm_any.
  Hypothesis HBFREE : rc_bfree_stmt bt FXOK arm_any24.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  Theorem hyp_recycle_merge : HYP_RECYCLE_arm bt FXOK (fun st => ~ arm_nomerge st).
  Proof using HBFREE HITEM G_min CELL_min CELLNB BT_ia BT_segs MINSZ.
    (lazymatch goal with |- ?G => let G' := eval unfold HYP_RECYCLE_arm in G in change_no_check G' end).
    intros fx st2 Lc FF M M0 mdl R sp ret stk HFX HH MW WX ETQ GQB RP DM L881 D904 D880 D881 X1 X2 X10 X12 X13 (mn & X11 & CMN) X4 SP16 SPlo SPhi RET SOK NOM.
    pose proof ceil_rng as CR. pose proof (u64_range sp) as Hsp.
    (* [comment removed for export] *)
    assert (X11' : getr R 11 = Z_to_bv 64 MINSZ).
    { rewrite X11. pose proof RP as (Rc & _). rewrite BT_segs in Rc.
      pose proof (const_cell bt _ _ _ _ Rc CMN) as C1. unfold IB in C1. rewrite BT_ia in C1. cbn [ia_instance both_addrs] in C1.
      pose proof (const_cell bt _ _ _ _ Rc CELL_min) as C2. unfold cellZ, cellN in C1, C2. rewrite C1 in C2.
      pose proof (f_equal (fun o : option (list byte) => match o with Some bs => bytes_le_to_Z bs | None => 0 end) C2) as E2. cbv beta iota in E2.
      apply bv_eq. rewrite !bytes_le_to_Z_8 in E2. exact E2. }
    apply (katD_bind BSEGS _ _ _ (rc_prefix_kat_m bt FXOK MINSZ BT_segs BT_ia G_min fx st2 Lc FF M M0 mdl R sp ret stk HFX HH MW WX ETQ GQB NOM RP DM L881 D904 D880 D881
                                     X1 X2 X10 X12 X13 X11' X4 SP16 SPlo SPhi RET SOK)).
    intros c1 (fx1 & M1 & mdl1 & R1 & stm & pb0 & rest & -> & EGQ & NEpb & RESTB & ETQm & EKAm & HOm & INV1 & A10 & RL1 & (Fra & Fs0 & Fs1 & Fs2 & Fs3 & Fs4) & DK1 & CH1 & LZ1 & SEV1).
    set (S := at_ sp 2208) in *.
    unfold PTRHI in SPhi.
    assert (US : U S = U sp + 2208) by ((lazymatch goal with |- ?G => let G' := eval unfold S in G in change_no_check G' end); rewrite at_u by lia; reflexivity).
    assert (ES : at_ S (-2208) = sp) by (apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (S16 : U S mod 16 = 0) by (rewrite US; clear - SP16; Z.div_mod_to_equations; lia).
    assert (Slo : CEIL + 3584 <= U S) by (rewrite US; clear - SPlo; lia).
    assert (Shi : U S + 16 <= PTRHI) by ((lazymatch goal with |- ?G => let G' := eval unfold PTRHI in G in change_no_check G' end); rewrite US; clear - SPhi; lia).
    pose proof INV1 as (_ & _ & _ & W2 & _).
    apply (katD_bind BSEGS _ _ _
             (rc_batch_loop bt FXOK BT_segs BT_ia CELLNB HITEM HBFREE S (XP bt pb0) (XP_dec bt pb0) (q_bytes (a_tq st2)) (q_bytes (a_gq st2)) Lc FF stm M1 mdl1 rest
                (Z_to_bv 64 0x4e574) (Z_to_bv 64 (0x10ab58 + 888)) (Z_to_bv 64 MINSZ) (Z_to_bv 64 (0x10ab58 + 728)) (getr R 13) (getr R 12) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                ltac:(intros z Q; left; exact Q) S16 Slo Shi (proj2 GQB) ltac:(apply ret_ok_lit; [clear; lia | reflexivity])
                (conj (WFX_qroom bt st2 Lc FF WX) (eq_ind_r (fun k => k <= KCAP) (WFX_kact bt st2 Lc FF WX) EKAm))
                pb0 fx1 stm M1 mdl1 R1 NEpb INV1 A10 ltac:(intros b z Hb Hz; right; exists b; split; [exact Hb | exact Hz]))).
    intros c2 (fx2 & st3 & M3 & mdl3 & R3 & -> & HFX3 & HH3 & MW3 & W3 & RX3 & EGQ3 & XSUB3 & QDEF3 & ACC3 & REGS3 & DK3 & KEPT3).
    destruct REGS3 as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25).
    destruct ACC3 as (ETQ3 & EKA3 & HO3 & XK3 & CHA3 & LZ3 & SEV3).
    pose proof RX3 as (M03 & RP3 & DX3).
    pose proof RP3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13 & (_ & MI3 & _) & _).
    (* [comment removed for export] *)
    assert (NHs3 : forall z, 0 <= z < 2 ^ 64 -> CEIL <= z -> HID st3 mdl3 (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st3 mdl3 z R13 Hz). left. exact Hr. }
    assert (FRC : forall kk v, -2256 <= kk -> kk + 8 <= -2208 -> rdn BSEGS M1 (at_ S kk) 8 = Some v -> rdn BSEGS (mrestrict (HID st3 mdl3) M3) (at_ S kk) 8 = Some v).
    { intros kk v Hk1 Hk2 Hr. rewrite rdn_mrestrict; [| clear - Hk1 Hk2 US Hsp SPhi Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      - eapply rd_same; [| clear - Hk1 Hk2 US Hsp SPhi Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
        intros x Hx. apply KEPT3. clear - Hx Hk1 Hk2 US Hsp SPhi Slo CR. rewrite at_u in Hx by lia. cbn in Hx. lia.
      - rewrite at_u by (clear - Hk1 Hk2 US Hsp SPhi Slo CR; lia). apply hid_off_of. intros z Hz. split; [clear - Hz Hk1 Hk2 US Hsp SPhi Slo CR; lia | apply NHs3; clear - Hz Hk1 Hk2 US Hsp SPhi Slo CR; lia]. }
    destruct (rc_epilogue (mrestrict (HID st3 mdl3) M3) (seg_rom BSEGS) S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) R3 Y2 RET
                (FRC (-2216) _ ltac:(clear; lia) ltac:(clear; lia) Fra) (FRC (-2224) _ ltac:(clear; lia) ltac:(clear; lia) Fs0) (FRC (-2232) _ ltac:(clear; lia) ltac:(clear; lia) Fs1)
                (FRC (-2240) _ ltac:(clear; lia) ltac:(clear; lia) Fs2) (FRC (-2248) _ ltac:(clear; lia) ltac:(clear; lia) Fs3) (FRC (-2256) _ ltac:(clear; lia) ltac:(clear; lia) Fs4))
      as (r9 & RUN9 & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z3 & Z4 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
    replace (0x4e574%bv : word) with (Z_to_bv 64 0x4e574 : word) in RUN9 by (apply bv_eq; reflexivity).
    apply (katD_loadsX bt BT_ia fx2 st3 Lc FF M3 M03 mdl3 R3 r9 _ _ _ RP3 HH3 RUN9). intros mdl9 RP9 HH9 SBM9.
    pose proof RP9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & MI9 & _) & _).
    pose proof (same_but_materialized_frame mdl3 mdl9 SBM9) as (_ & _ & Elz9 & _).
    (* [comment removed for export] *)
    assert (XQ : forall z, qhdr bt z -> XP bt pb0 z) by (intros z Q; left; exact Q).
    assert (RL3 : rep_list bt M3 (IB bt + 888) (a_gq st3)).
    { rewrite EGQ3. destruct RL1 as (L1 & L2 & L3 & L4). pose proof (thread_dyn bt stm Lc FF W2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
      assert (QK : forall i, IB bt + 888 <= i < IB bt + 920 -> M3 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)).
      { intros i Hi. apply XK3. left. (lazymatch goal with |- ?G => let G' := eval unfold qhdr in G in change_no_check G' end). unfold IB in *. rewrite BT_ia in *. cbn [ia_instance both_addrs] in *. clear - Hi. unorm. lia. }
      (lazymatch goal with |- ?G => let G' := eval unfold rep_list in G in change_no_check G' end). unfold IB in *. rewrite BT_ia in *. cbn [ia_instance both_addrs] in *.
      split; [eapply cellZ_frame; [exact L1 | clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply QK; clear - Hi; cbn in Hi; lia]|].
      split; [eapply cellZ_frame; [exact L2 | clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply QK; clear - Hi; cbn in Hi; lia]|].
      split; [eapply cellZ_frame; [exact L3 | clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply QK; clear - Hi; cbn in Hi; lia]|].
      eapply cellZ_frame; [exact L4 | clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply QK; clear - Hi; cbn in Hi; lia]. }
    assert (RX9 : AsAinvOpsRc73.AsAinvRepX3.RepX bt (XP bt pb0) st3 Lc FF M3 mdl9) by (exists M03; split; [exact RP9 | exact DX3]).
    pose proof (RepX_resync_qhdr bt (XP bt pb0) st3 Lc FF M3 mdl9 _ _ W3 RX9 RL3 QDEF3) as RXq.
    assert (NDgq : List.NoDup (map ba_addr (pb0 ++ rest))).
    { pose proof W2 as (_ & _ & (_ & _ & _ & _ & ND & _) & _). rewrite ETQm, ETQ, EGQ in ND. exact ND. }
    assert (REP9 : Rep bt st3 Lc FF M3 mdl9).
    { apply (RepX_close bt _ st3 Lc FF M3 mdl9 W3 RXq). intros z ([Q | (b & Hb & Hz)] & NQ) RCELL; [exact (NQ Q)|].
      destruct (XSUB3 z ltac:(right; exists b; split; [exact Hb | exact Hz])) as [Q | (a & (CVa & KIND) & Ha)]; [exact (NQ Q)|].
      (* [comment removed for export] *)
      destruct (batch_facts bt stm Lc FF W2 b ltac:(apply in_app_iff; right; rewrite EGQ; apply in_app_iff; left; exact Hb)) as ((jb & Hjb0 & _ & Ejb) & _).
      destruct CVa as (ja & Hja0 & Hja1 & Eja). unfold chunk_addr in Ejb, Eja. change (csize BATCHCLASS) with 8192 in Ejb, Eja. unfold BATCHSZ in Hz, Ha.
      assert (Eab : a = ba_addr b) by (clear - Ejb Eja Hz Ha; lia).
      destruct KIND as [(b' & Hb' & Eb') | KIND].
      - (* [comment removed for export] *)
        rewrite ETQ3, ETQm, ETQ, EGQ3 in Hb'. cbn [app] in Hb'.
        apply (nodup_app_disj (map ba_addr pb0) (map ba_addr rest) (ba_addr b)); [rewrite <- map_app; exact NDgq | apply in_map; exact Hb |].
        rewrite <- Eab, <- Eb'. apply in_map. exact Hb'.
      - exact (XB_free_not_cells bt st3 Lc FF _ _ a z W3 (ex_intro _ ja (conj Hja0 (conj Hja1 Eja))) KIND ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); exact Ha) RCELL). }
    assert (WF9 : WF bt st3 Lc FF).
    { (lazymatch goal with |- ?G => let G' := eval unfold WF in G in change_no_check G' end). apply (WFq_mono_bytes bt st3 Lc FF _ _ _ _ W3); [rewrite ETQ3, ETQm, ETQ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia | rewrite EGQ3; clear - RESTB G_min; lia]. }
    (* [comment removed for export] *)
    apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold drain_post in G in change_no_check G' end). exists fx2, st3, M3, mdl9, r9.
    split; [reflexivity|]. split; [exact HFX3|]. split; [exact HH9|]. split; [exact WF9|]. split; [exact REP9|]. split; [rewrite EKA3; exact EKAm|]. split; [split; [intros h Hh; exact (proj1 HO3 h (proj1 HOm h Hh)) | exact (fk_trans _ _ _ (proj2 HOm) (proj2 HO3))]|].
    split.
    { intros a NE. destruct (decide (M3 a = M1 a)) as [E | N].
      - rewrite E in NE |- *. destruct (CH1 a NE) as [C D]. split; [| left; exact D]. (lazymatch goal with |- ?G => let G' := eval unfold drain_changed in G in change_no_check G' end).
        destruct C as [C | [C | C]]; [left; clear - C US; lia | right; left; exact C | right; right; exact C].
      - destruct (CHA3 a N) as [C D]. split; [| exact D]. unfold acc_changed in C. (lazymatch goal with |- ?G => let G' := eval unfold drain_changed in G in change_no_check G' end).
        destruct C as [C | [C | C]]; [left; clear - C US; lia | right; left; exact C | right; right; exact C]. }
    split.
    { intros a Ha. transitivity (lzb mdl3 a); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz9; reflexivity|]. transitivity (lzb mdl1 a); [exact (LZ3 a Ha) | exact (LZ1 a Ha)]. }
    split.
    { destruct DK1 as (K3 & K4 & K26 & K27). destruct DK3 as (L3 & L4 & L26 & L27).
      apply regs_kept_intro; rewrite ?Z2, ?Z3, ?Z4, ?Z8, ?Z9, ?Z18, ?Z19, ?Z20, ?Z21, ?Z22, ?Z23, ?Z24, ?Z25, ?Z26, ?Z27,
                                     ?Y21, ?Y22, ?Y23, ?Y24, ?Y25, ?L3, ?L4, ?L26, ?L27, ?K3, ?K4, ?K26, ?K27; try reflexivity.
      rewrite ES. symmetry. exact X2. }
    split; [| exact (model_ivs_wf_sbm mdl3 mdl9 SBM9 MW3)].
    eapply same_except_vm_trans; [exact SEV1|]. eapply same_except_vm_trans; [exact SEV3 | apply same_but_materialized_except_vm; exact SBM9].
  Qed.

End MK5.
End BoAllocFRcMK5.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFTop0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i.BoAllocF0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI.BoAllocF2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i.BoAllocFZ OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRun OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i.BoAllocFRun0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i.BoAllocFTopA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
(* [comment removed for export] *)
#[local] Abbreviation up8 := AsAinvOpsPf3d.AsAinvFreeS.up8.

Section TOP0.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis HTP : TP = ia_tp both_addrs.
  (* [comment removed for export] *)
  Variables (HP HPc : option Z -> ast -> Prop).
  Hypothesis FAM : hp_fam bt HP HPc.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).

  (* [comment removed for export] *)
  Definition free_null_stmt : Prop :=
    forall (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp : Z) (p : word) (st : ast),
      FXOK fx -> m_halted mdl = None ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> HP h st -> BackingAlgebra.model_ivs_wf mdl ->
      call_pre BSEGS both_addrs R M ret sp MSTK_A -> getr R 10 = p -> fpc M (U (getr R 8)) sp DMAX ->
      a_ialloc st = true -> p = Z_to_bv 64 0 ->
      katD BSEGS (cfg BSEGS fx R (ia_free both_addrs) M mdl) (free_post BSEGS FXOK both_addrs (AAINV_F bt HP) h MSTK_A R M mdl Lc FF B C K ret sp).

  Theorem free_null : free_null_stmt.
  Proof using HTP GEOM CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    (lazymatch goal with |- ?G => let G' := eval unfold free_null_stmt in G in change_no_check G' end).
    intros h fx R M mdl Lc FF B C K ret sp p st HFX HH W RP BD HLE MW CP HR10 FPC IA Hp0.
    pose proof ceil_rng as CR.
    set (S := getr R 2) in *. set (ra0 := getr R 1). set (tp := getr R 4).
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S ra0 tp in CP1, CP2, CP4.
    assert (Utp : U tp = 0x641380) by (rewrite CP4; vm_compute; reflexivity).
    assert (ETP : TP = 0x641380) by (rewrite HTP; reflexivity).
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CELL_hook
                      & CELL_mcsz & CELL_msz & CELL_gfl & CELL_mff & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he
                      & CELL_grm & CELL_rm & CELL_cpm & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9 & Gc10).
    destruct GEOM as (GCT & Gtop & Gbot).
    pose proof (free_obls_pf bt) as (OBL_nolazy_rt & _ & OBL_rt_private & _ & _ & _ & _ & _ & _).
    unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt. unfold OBL_rt_private_stmt in OBL_rt_private.
    assert (Hpz : U p = 0) by (rewrite Hp0; reflexivity).
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & CPG' & GCT' & SB0 & SB1 & SBH & SB16).
    clear GCT' GCB. hidehyp GCT. hidehyp GTB.
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    destruct R11 as (IAf & IAl & IAz & _). rewrite IA in IAf.
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi both_addrs] in GTI, GCI.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG, KSPACE, NMAX, PTRLO in *.
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHrt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st Lc FF M mdl z W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). destruct Hz as [Hz|Hz]; [am_tauto | am_tauto]. }
    destruct R14 as (B1 & B2 & B3 & B4 & B5).
    set (Mr := mrestrict Hd M).
    Ltac hoff NH := apply hid_off_of; intros z Hz; unfold T_UNW, T_QC, T_PC, PC_SZ in *; split; [lia | apply NH; lia].
    (* [comment removed for export] *)
    Ltac konst Hd M R1 NHs C := apply (cellZ_restrict Hd M _ _ _ (const_cell bt M _ _ _ R1 C)); [lia | lia | hoff NHs].
    assert (K_mcs : rdn BSEGS Mr (Z_to_bv 64 0x10eebc) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 30))) by konst Hd M R1 NHs CELL_mcs.
    assert (K_gcf : rdn BSEGS Mr (Z_to_bv 64 0x105f08) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x19fce8))) by konst Hd M R1 NHs CELL_gcf.
    assert (K_fum : rdn BSEGS Mr (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_fum.
    assert (K_inited : rdn BSEGS Mr (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_inited.
    assert (K_pg : rdn BSEGS Mr (Z_to_bv 64 0x105ef8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 PGP))) by konst Hd M R1 NHs CELL_pg.
    assert (K_P : rdn BSEGS Mr (Z_to_bv 64 PGP) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096))) by konst Hd M R1 NHs CELL_P.
    assert (K_kif : rdn BSEGS Mr (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_kif.
    assert (K_key : rdn BSEGS Mr (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))).
    { replace (at_ (Z_to_bv 64 0x10da20) 4) with (Z_to_bv 64 0x10da24) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_key. }
    assert (K_tsdp : rdn BSEGS Mr (at_ tp (-88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 TSDP))).
    { replace (at_ tp (-88)) with (Z_to_bv 64 (TP - 88)) by (apply bv_eq; rewrite at_u by (rewrite Utp; lia); rewrite Utp, ETP; reflexivity). rewrite ETP. rewrite ETP in CELL_tsdp. konst Hd M R1 NHs CELL_tsdp. }
    assert (K_tctx : rdn BSEGS Mr (Z_to_bv 64 TSDP) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 CTX))) by konst Hd M R1 NHs CELL_tctx.
    assert (K_hook : rdn BSEGS Mr (Z_to_bv 64 0x19fc88) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by konst Hd M R1 NHs CELL_hook.
    (* [comment removed for export] *)
    Ltac thr_cell Hd M NHrt C := apply (cellZ_restrict Hd M _ _ _ C); [(lazymatch goal with |- ?G => let G' := eval unfold T_UNW, T_QC in G in change_no_check G' end); lia | unfold T_UNW, T_QC in *; lia | hoff NHrt].
    assert (K_thr : rdn BSEGS Mr (at_ (Z_to_bv 64 CTX) 152) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 T))).
    { replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tback. }
    assert (K_T0 : rdn BSEGS Mr (Z_to_bv 64 T) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 CTX))) by thr_cell Hd M NHrt Tctx.
    assert (K_tid : rdn BSEGS Mr (Z_to_bv 64 (CTX + 8)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))) by thr_cell Hd M NHrt Ttid.
    assert (K_unw : rdn BSEGS Mr (at_ (Z_to_bv 64 T) 3168) 1 = Some [Z_to_bv 8 0]).
    { replace (at_ (Z_to_bv 64 T) 3168) with (Z_to_bv 64 (T + T_UNW)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_UNW in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tunw. }
    assert (K_sw : rdn BSEGS Mr (at_ (Z_to_bv 64 T) 40) 1 = Some [Z_to_bv 8 0]).
    { replace (at_ (Z_to_bv 64 T) 40) with (Z_to_bv 64 (T + 40)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tsw. }
    assert (K_top : rdn BSEGS Mr (at_ (Z_to_bv 64 T) 8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bt_stack_top bt)))).
    { replace (at_ (Z_to_bv 64 T) 8) with (Z_to_bv 64 (T + 8)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Ttop. }
    assert (K_bot : rdn BSEGS Mr (at_ (Z_to_bv 64 T) 16) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bt_stack_bottom bt)))).
    { replace (at_ (Z_to_bv 64 T) 16) with (Z_to_bv 64 (T + 16)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tbot. }
    (* [comment removed for export] *)
    unfold IA_FLAG, IA_INST in IAf, IAl, IAz. rewrite BT_ia in IAf, IAl, IAz. cbn [ia_ialloc_flag ia_ialloc_inst both_addrs] in IAf, IAl, IAz.
    assert (K_iaflag : rdn BSEGS Mr (Z_to_bv 64 0x19dc48) 1 = Some [Z_to_bv 8 1]).
    { apply (cellZ_restrict Hd M _ _ _ IAf); [lia | lia | hoff NHs]. }
    destruct (p_div_facts (U p) ltac:(lia)) as [Q47 Q32].
    set (q32 := U p / 2 ^ 32) in Q32.
    assert (K_pim : rdn BSEGS Mr (Z_to_bv 64 (0x10f3c8 + 8 * q32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
    { apply (cellZ_restrict Hd M _ _ _); [| lia | lia | hoff NHs].
      apply (fill_cellZ_zero BSEGS M _ _ IAz); (lazymatch goal with |- ?G => let G' := eval cbn [ia_ialloc_inst both_addrs Z.of_nat] in G in change_no_check G' end); lia. }
    (* [comment removed for export] *)
    assert (SOKstk : store_ok BSEGS Mr (at_ S (-2304)) 2304 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. apply CPstk. cbn in Hx. lia. }
    assert (SOKunw : store_ok BSEGS Mr (at_ (Z_to_bv 64 T) 3168) 1 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia_c | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; hoff NHrt].
      apply (writableZ_store_ok M _ _ _ _ TW); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia_c. }
    (* [comment removed for export] *)
    assert (FPCr : fpc Mr (U (getr R 8)) (U S) DMAX).
    { rewrite CP2. apply (fpc_kept_gen M _ _ _ FPC Mr). destruct (fpc_shape _ _ _ _ FPC) as [ST|FR]; [left; exact ST | right].
      intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply mrestrict_off. apply NHs; unfold PTRHI in *; lia. }
    (* [comment removed for export] *)
    assert (RETOK : ret_ok ra0) by (rewrite CP1; apply ret_ok_lit; [lia | exact CPe]).
    assert (GS12 : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0) by (rewrite CP2; lia).
    assert (GT12 : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)).
    { split; [exact GT4|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); unfold hide in GTB; split; lia | rewrite CP2; lia]. }
    assert (Gctx12 : 1 <= CTX /\ CTX + 4096 <= U S - 3584 /\ (CTX + 4096 <= T \/ T + 4096 <= CTX)) by (unfold hide in GCT; rewrite CP2; lia).
    assert (Gtp12 : AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI) by (rewrite Utp; lia).
    assert (Gtsdp12 : AIMGLO <= U (Z_to_bv 64 TSDP) /\ U (Z_to_bv 64 TSDP) + 8 <= AIMGHI) by (wd_ulia).
    assert (GP12 : AIMGLO <= U (Z_to_bv 64 PGP) /\ U (Z_to_bv 64 PGP) + 8 <= AIMGHI) by (wd_ulia).
    assert (Gtop12 : 4096 <= U (Z_to_bv 64 (bt_stack_top bt)) <= 2 ^ 47) by (wd_ulia).
    assert (Gbot12 : U (Z_to_bv 64 (bt_stack_bottom bt)) < U (Z_to_bv 64 (bt_stack_top bt))) by (wd_ulia).
    assert (Gq12 : U p / 2 ^ 32 = q32 /\ 0 <= q32 < 2 ^ 15 /\ U p / 2 ^ 47 = 0) by (repeat split; try reflexivity; lia).
    assert (Ciab : U (Z_to_bv 8 1) <> 0) by (change (U (Z_to_bv 8 1)) with 1; lia).
    assert (Cpim0 : bytes_le_to_Z (word_to_le_bytes 8 (Z_to_bv 64 0)) = 0) by (rewrite bytes_le_to_Z_8; reflexivity).
    (* [comment removed for export] *)
    destruct (run_p0 Mr (seg_rom BSEGS) R S p ra0 tp (Z_to_bv 64 TSDP) (Z_to_bv 64 PGP) (Z_to_bv 64 (bt_stack_top bt)) (Z_to_bv 64 (bt_stack_bottom bt))
                T CTX q32 DMAX (Z_to_bv 8 1) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      as (rZ & MU & sz & RUNZ & X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X3 & X4 & X23 & X24 & X25 & X26 & X27 & SZ1 & FOOTU & GRU & UUNW).
    all: try assumption.
    all: try reflexivity.
    all: let k := numgoals in guard k = 1.
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold cfg in G in change_no_check G' end). replace (Z_to_bv 64 (ia_free both_addrs)) with (Z_to_bv 64 0x6ed6c : word) by (apply bv_eq; reflexivity).
    replace (0x6ed6c%bv : word) with (Z_to_bv 64 0x6ed6c : word) in RUNZ by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x6ed6c) M (seg_rom BSEGS))
             (@mkst fx rZ ra0 (fr_b1 MU S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22)) (seg_rom BSEGS)) mdl).
    { apply lazy_cover_HID. }
    { exact B1. }
    { exact B2. }
    { exact HH. }
    { rewrite restrict_mkstF. exact RUNZ. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x6ed6c) M (seg_rom BSEGS))) with M by reflexivity.
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
    destruct SF1 as (_ & Evm & Elz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl & _ & _ & _ & Eeg).
    remember (fr_b1 MU S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22)) as Mz eqn:EMz.
    remember (fr_P1 Mr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as M3 eqn:EM3 in FOOTU, GRU.
    set (Mfin := munrestrict Hd M Mz).
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (rewrite CP2; lia).
    assert (Mb3210 : M (at_ (Z_to_bv 64 T) 3168) = Some (Z_to_bv 8 0)).
    { replace (at_ (Z_to_bv 64 T) 3168) with (Z_to_bv 64 (T + T_UNW)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_UNW in G in change_no_check G' end); wd_ulia).
      change (Z_to_bv 8 0) with (Z_to_bv 8 (U (Z_to_bv 64 0))). apply rdn1_offimg; [(lazymatch goal with |- ?G => let G' := eval unfold T_UNW in G in change_no_check G' end); wd_ulia | exact Tunw]. }
    assert (MUb3210 : MU (at_ (Z_to_bv 64 T) 3168) = Some (Z_to_bv 8 0)) by (apply rdn1_offimg; [(lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia | exact UUNW]).
    pose proof (fr_P1_grows' Mr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as GRr3. feed GRr3. rewrite <- EM3 in GRr3.
    assert (GRz : mem_grows Mr Mz).
    { eapply mem_grows_trans; [exact GRr3|]. eapply mem_grows_trans; [exact GRU|]. subst Mz. (lazymatch goal with |- ?G => let G' := eval unfold fr_b1 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
    assert (GRfin : mem_grows M Mfin).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Mfin, munrestrict in G in change_no_check G' end). destruct (Hd x) eqn:Ex; [exact Hx|]. apply GRz. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off by exact Ex. exact Hx. }
    (* [comment removed for export] *)
    pose proof (fr_P1_foot Mr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as P1F. feed P1F. rewrite <- EM3 in P1F.
    assert (DIFF : forall a : word, Mfin a <> M a -> U S - 2304 <= U a < U S).
    { intros a NE. pose proof (u64_range a) as Ha. unfold Mfin, munrestrict in NE. destruct (Hd a) eqn:Eh; [exfalso; exact (NE eq_refl)|].
      assert (EMr : Mr a = M a) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); apply mrestrict_off; exact Eh).
      destruct (decide (Mz a = MU a)) as [Ez|Nz].
      - rewrite Ez in NE. destruct (decide (MU a = M3 a)) as [EU|NU].
        + rewrite EU in NE. rewrite <- EMr in NE. pose proof (P1F a NE). lia.
        + destruct (FOOTU a NU) as [F|[F|[F|F]]]; try lia.
          exfalso. apply NE. replace a with (at_ (Z_to_bv 64 T) 3168) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). rewrite MUb3210, Mb3210. reflexivity.
      - subst Mz. unfold fr_b1 in Nz.
        assert (OUT : (U a < U S - 2192 \/ U S - 2128 <= U a) -> False).
        { intros Hx. apply Nz. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity. }
        destruct (decide (U S - 2192 <= U a < U S - 2128)); [lia | exfalso; apply OUT; lia]. }
    (* [comment removed for export] *)
    apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold free_post, cfg in G in change_no_check G' end). rewrite <- CP1.
    exists fx, rZ, Mfin, mdl1.
    split; [reflexivity|]. split; [exact HFX|].
    split; [apply regs_kept_intro; rewrite ?X2, ?X3, ?X4, ?X8, ?X9, ?X18, ?X19, ?X20, ?X21, ?X22, ?X23, ?X24, ?X25, ?X26, ?X27; reflexivity|].
    split; [intros a NE; (lazymatch goal with |- ?G => let G' := eval unfold as_changed in G in change_no_check G' end); left; rewrite <- CP2; (lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end); pose proof (DIFF a NE); lia|].
    split; [intros a _ Da; apply GRfin; exact Da|].
    split.
    { intros a Ha. rewrite <- CP2 in Ha. unfold MSTK_A in Ha. split.
      + apply GRfin. apply store_ok1_heap; [lia|]. apply CPstk. rewrite <- CP2. lia.
      + eapply store_ok_mono; [exact GRfin|]. apply CPstk. rewrite <- CP2. lia. }
    split.
    { (* [comment removed for export] *)
      exists st. split; [exact W|]. split; [| split; [split; [exact BD | exact HLE] | exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW)]].
      apply (Rep_frame bt st Lc FF M Mfin mdl1 W (Rep_sbm bt st Lc FF M mdl mdl1 RP MI1 SBM1)).
      intros a NE. split; [| apply GRfin; apply store_ok1_heap; [pose proof (DIFF a NE); lia|]; apply CPstk; pose proof (DIFF a NE); rewrite <- CP2; lia].
      intros RCL. apply (ceil_not_cells bt st Lc FF W (U a)); [| exact RCL]. pose proof (DIFF a NE). lia. }
    split; [apply same_but_materialized_except_vm; exact SBM1|].
    split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz; reflexivity|].
    rewrite Ehl. exact HH.
  Qed.
End TOP0.
End BoAllocFTop0.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopA0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutB OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutN OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutNf OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsI4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutRe OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutRf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFTopW6.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsD3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i.BoAllocFHypI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i.BoAllocFTopA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopA0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutB OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutN OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutNf BoAllocFTop0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFArms OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFTopD OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsI4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutRe.BoAllocFPutR1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutRe OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutRf.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.


Section W6.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1408.
  Hypothesis HYP_DEPOT : HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Variable MINSZ : Z.
  Hypothesis CELL_min : In (0x10ab58 + 800, 8%nat, MINSZ) (bt_consts bt).     (* [comment removed for export] *)
  Hypothesis G_min : 0 <= MINSZ < 2 ^ 64.
  Hypothesis HYP_RECYCLE : HYP_RECYCLE_stmt bt FXOK 1376.
  Variable KR : Z.                                   (* [comment removed for export] *)
  Hypothesis G_KR : 0 <= KR <= 1312.
  Hypothesis HYP_REFILL : HYP_REFILL24K_stmt bt FXOK KR.
  Hypothesis CELLSPIN : free_cells_spin bt.
  (* [comment removed for export] *)
  Variables (HP HPc : option Z -> ast -> Prop).
  Hypothesis FAM : hp_fam bt HP HPc.
  (* [comment removed for export] *)
  Lemma OPS_IA4 : OPS_REP_ialloc_init4_stmt bt.
  Proof using. exact (AsAinvOpsI4.OPS_REP_ialloc_init4_pf bt). Qed.
  #[local] Definition KDR : Z := 1376.
  #[local] Lemma G_KDR : 0 <= KDR <= 1376. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold KDR in G in change_no_check G' end). lia. Qed.
  #[local] Lemma HYP_DRAIN : HYP_DRAIN_stmt bt FXOK KDR.
  Proof using HYP_RECYCLE G_min CELL_min MINSZ CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    destruct CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CELL_msz & _).
    exact (hyp_drain_pf bt FXOK MINSZ BT_segs BT_ia CELL_msz CELL_min G_min HYP_RECYCLE).
  Qed.
  (* [comment removed for export] *)
  Lemma OPS_WFX_append : forall st Lc FF L1 L2 p n tq' b,
    WF bt st Lc FF -> a_kact st <= KCAP -> Lc = L1 ++ (p, n) :: L2 -> a_tq st = tq' ++ [b] ->
    Z.of_nat (length (ba_items b)) < BATCHCAP -> WFX bt (op_quar_append st (p - 16) n) (L1 ++ L2) FF.
  Proof using.
    intros st Lc FF L1 L2 p n tq' b W KC HL HT HC.
    apply (WFX_intro bt _ _ _ _ _ (OPS_WFq_quar_append_pf bt st Lc FF L1 L2 p n tq' b _ _ W HL HT HC)).
    - pose proof (AsKSys7b.qroom_WF bt st Lc FF W) as Q. destruct W as (_ & _ & (_ & _ & Q3 & _) & _).
      unfold AsKSys7b.qroom in *. rewrite HL in Q. rewrite PHI_app in Q |- *. cbn [PHI snd] in Q. unfold MBLK in Q. clear - Q Q3. lia.
    - rewrite (op_quar_append_eq st tq' b) by exact HT. exact KC.
  Qed.
  Lemma OPS_WFX_newbatch : forall st Lc FF L1 L2 p n k ks,
    WF bt st Lc FF -> a_kact st <= KCAP -> Lc = L1 ++ (p, n) :: L2 -> a_cache st BATCHCLASS = ks ++ [k] ->
    WFX bt (op_quar_newbatch (op_cache_pop st BATCHCLASS) (chunk_of_compact (bt_spacebeg bt) BATCHCLASS k) (p - 16) n) (L1 ++ L2) FF.
  Proof using.
    intros st Lc FF L1 L2 p n k ks W KC HL HC.
    apply (WFX_intro bt _ _ _ _ _ (AsAinvOpsQ23.AsAinvOpsQ3.OPS_WFq_quar_newbatch2_pf bt st Lc FF L1 L2 p n k ks _ _ W HL HC)).
    - pose proof (AsKSys7b.qroom_WF bt st Lc FF W) as Q. destruct W as (_ & _ & (_ & _ & Q3 & _) & _).
      unfold AsKSys7b.qroom in *. rewrite HL in Q. rewrite PHI_app in Q |- *. cbn [PHI snd] in Q. unfold MBLK, BATCHSZ in *. clear - Q Q3. lia.
    - rewrite (AsAinvOpsQ23.AsAinvOpsQ3.op_quar_newbatch_eq bt st k ks (p - 16) n HC). exact KC.
  Qed.

  #[local] Notation FPOST := (free_post BSEGS FXOK both_addrs (AAINV_F bt HP)) (only parsing).
  #[local] Notation ENTRY fx R M mdl := (cfg BSEGS fx R (ia_free both_addrs) M mdl) (only parsing).

  (* [comment removed for export] *)
  Definition ARM2G (cond : ast -> Z -> Prop) : Prop :=
    forall (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF L1 L2 : list (Z * Z)) (B C K ret sp m : Z) (p : word) (st : ast),
      m_halted mdl = None -> FXOK fx ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> HP h st -> BackingAlgebra.model_ivs_wf mdl ->
      call_pre BSEGS both_addrs R M ret sp MSTK_A -> getr R 10 = p -> fpc M (U (getr R 8)) sp DMAX ->
      Lc = L1 ++ (U p, m) :: L2 -> K + kcost_free <= KCAP -> cond st m ->
      katD BSEGS (ENTRY fx R M mdl) (FPOST h MSTK_A R M mdl (L1 ++ L2) FF (Z.max 0 (B - (m + MBLK))) (Z.max 0 (C - 1)) (K + kcost_free) ret sp).
  #[local] Notation ARM := ARM2G.

  Lemma set_ialloc_id : forall st, a_ialloc st = true -> set_ialloc st = st.
  Proof using HTP CELLS CPM MIDEND FL PGP TSDP TP bt. intros st H. destruct st; cbn in H |- *. subst. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma free_runA' : forall fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp m : Z) (p : word) (st : ast),
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K ->
      call_pre BSEGS both_addrs R M ret sp MSTK_A -> getr R 10 = p -> fpc M (U (getr R 8)) sp DMAX ->
      In (U p, m) Lc -> K + kcost_free <= KCAP -> (exists h : option Z, holes_le h st) ->
      katD BSEGS (ENTRY fx R M mdl) (runA_post bt FXOK KD (set_ialloc st) Lc FF R M mdl p).
  Proof using HTP HYP_DEPOT G_KD GEOM CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    intros fx R M mdl Lc FF B C K ret sp m p st HFX HH MW W RP BD CP HR10 FPC HinP HK HLEX.
    destruct (a_ialloc st) eqn:IA.
    - rewrite (set_ialloc_id st IA).
      exact (free_runA bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS GEOM G_KD HYP_DEPOT HTP fx R M mdl Lc FF B C K ret sp m p st HFX HH MW W RP BD CP HR10 FPC HinP HK HLEX IA).
    - exact (free_runA0 bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS GEOM G_KD HYP_DEPOT HTP OPS_IA4 fx R M mdl Lc FF B C K ret sp m p st HFX HH MW W RP BD CP HR10 FPC HinP HK HLEX IA).
  Qed.

  (* [comment removed for export] *)
  Lemma free_null' : forall (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp : Z) (p : word) (st : ast),
      FXOK fx -> m_halted mdl = None ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> HP h st -> BackingAlgebra.model_ivs_wf mdl ->
      call_pre BSEGS both_addrs R M ret sp MSTK_A -> getr R 10 = p -> fpc M (U (getr R 8)) sp DMAX ->
      p = Z_to_bv 64 0 ->
      katD BSEGS (ENTRY fx R M mdl) (FPOST h MSTK_A R M mdl Lc FF B C K ret sp).
  Proof using FAM HPc HTP GEOM CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    intros h fx R M mdl Lc FF B C K ret sp p st HFX HH W RP BD HLE MW CP HR10 FPC Hp0.
    destruct (a_ialloc st) eqn:IA.
    - exact (free_null bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS GEOM HTP HP h fx R M mdl Lc FF B C K ret sp p st HFX HH W RP BD HLE MW CP HR10 FPC IA Hp0).
    - exact (free_null0 bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS GEOM HTP OPS_IA4 HP HPc FAM h fx R M mdl Lc FF B C K ret sp p st HFX HH W RP BD HLE MW CP HR10 FPC IA Hp0).
  Qed.
  (* [comment removed for export] *)
  Definition cond_put (st : ast) (m : Z) : Prop :=
    m <= 2 ^ 28 /\ exists tq' b, a_tq st = tq' ++ [b] /\ Z.of_nat (length (ba_items b)) < BATCHCAP.

  (* [comment removed for export] *)
  Lemma arm_put : ARM cond_put.
  Proof using FAM HPc HYP_RECYCLE G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP.
    intros h fx R M mdl Lc FF L1 L2 B C K ret sp m p st HH HFX W RP BD HLE MW CP HR10 FPC ELc HK (M28 & tq' & b & ETQ & CNT).
    assert (HinP : In (U p, m) Lc) by (rewrite ELc; apply in_app_iff; right; left; reflexivity).
    apply (katD_bind BSEGS _ (runA_post bt FXOK KD (set_ialloc st) Lc FF R M mdl p)).
    { exact (free_runA' fx R M mdl Lc FF B C K ret sp m p st HFX HH MW W RP BD CP HR10 FPC HinP HK (ex_intro _ h (hp_le bt HP HPc FAM h st HLE))). }
    intros c' POST.
    destruct POST as (fx' & R' & M' & M0 & mdl' & d' & naa & id & Ec' & HFX' & HH' & W2 & RP2 & DX & CHG & Hb16
                      & Cq0 & Cq1 & Cq2 & Cq3 & Cq4 & Cq5 & Ci0 & Ci1 & Ci2 & Ci3 & Ci4 & Ci5 & Ci6
                      & Y2 & Y8 & Y9 & Y10 & Y18 & Y19 & Y20 & Y21 & Y22 & Y3 & Y4 & Y23 & Y24 & Y25 & Y26 & Y27 & Hid & SEV & LZ & MW2).
    subst c'.
    assert (HLEc : HPc h (runA_st (set_ialloc st) d' naa)) by (apply (hp_chg bt HP HPc FAM h st _ Lc FF (U p) m W HinP HLE); [intros c0; split; reflexivity | reflexivity | reflexivity | exact (Z.le_trans _ _ _ (Zplus_le_compat_r _ _ _ (proj2 (proj2 (proj2 BD)))) HK)]).
    apply (free_putB bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS GEOM G_KD KDR G_KDR HYP_DRAIN OPS_WFX_append HP HPc FAM
             h fx' R R' M M' M0 mdl mdl' Lc FF L1 L2 B C (K + kcost_free) ret sp m p (runA_st (set_ialloc st) d' naa) id tq' b
             CP HR10 ELc W2 RP2).
    all: try assumption.
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold runA_st, set_ialloc in G in change_no_check G' end). destruct BD as (B1 & B2 & B3). (lazymatch goal with |- ?G => let G' := eval unfold bounds in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_kact a_reg a_tq a_cache] in G in change_no_check G' end). unfold kcost_free, EVT in *. repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  Definition cond_nbe (st : ast) (m : Z) : Prop :=
    m <= 2 ^ 28 /\ a_tq st = [] /\ exists ks k, a_cache st BATCHCLASS = ks ++ [k].
  Definition cond_nbf (st : ast) (m : Z) : Prop :=
    m <= 2 ^ 28 /\ (exists tq' b, a_tq st = tq' ++ [b] /\ Z.of_nat (length (ba_items b)) = BATCHCAP) /\ exists ks k, a_cache st BATCHCLASS = ks ++ [k].
  (* [comment removed for export] *)
  Definition cond_refill (st : ast) (m : Z) : Prop :=
    m <= 2 ^ 28 /\ (a_tq st = [] \/ exists tq' b, a_tq st = tq' ++ [b] /\ Z.of_nat (length (ba_items b)) = BATCHCAP) /\ a_cache st BATCHCLASS = [].

  Lemma arm_nbe : ARM cond_nbe.
  Proof using FAM HPc HYP_RECYCLE G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP.
    intros h fx R M mdl Lc FF L1 L2 B C K ret sp m p st HH HFX W RP BD HLE MW CP HR10 FPC ELc HK (M28 & ETQ & ks & k & ECA).
    assert (HinP : In (U p, m) Lc) by (rewrite ELc; apply in_app_iff; right; left; reflexivity).
    apply (katD_bind BSEGS _ (runA_post bt FXOK KD (set_ialloc st) Lc FF R M mdl p)).
    { exact (free_runA' fx R M mdl Lc FF B C K ret sp m p st HFX HH MW W RP BD CP HR10 FPC HinP HK (ex_intro _ h (hp_le bt HP HPc FAM h st HLE))). }
    intros c' POST.
    destruct POST as (fx' & R' & M' & M0 & mdl' & d' & naa & id & Ec' & HFX' & HH' & W2 & RP2 & DX & CHG & Hb16
                      & Cq0 & Cq1 & Cq2 & Cq3 & Cq4 & Cq5 & Ci0 & Ci1 & Ci2 & Ci3 & Ci4 & Ci5 & Ci6
                      & Y2 & Y8 & Y9 & Y10 & Y18 & Y19 & Y20 & Y21 & Y22 & Y3 & Y4 & Y23 & Y24 & Y25 & Y26 & Y27 & Hid & SEV & LZ & MW2).
    subst c'.
    assert (HLEc : HPc h (runA_st (set_ialloc st) d' naa)) by (apply (hp_chg bt HP HPc FAM h st _ Lc FF (U p) m W HinP HLE); [intros c0; split; reflexivity | reflexivity | reflexivity | exact (Z.le_trans _ _ _ (Zplus_le_compat_r _ _ _ (proj2 (proj2 (proj2 BD)))) HK)]).
    apply (free_putNe bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD KDR G_KDR HYP_DRAIN OPS_WFX_newbatch HP HPc FAM
             h fx' R R' M M' M0 mdl mdl' Lc FF L1 L2 B C (K + kcost_free) ret sp m p (runA_st (set_ialloc st) d' naa) id ks k
             CP HR10 ELc W2 RP2).
    all: try assumption.
    (lazymatch goal with |- ?G => let G' := eval unfold runA_st, set_ialloc in G in change_no_check G' end). destruct BD as (B1 & B2 & B3). (lazymatch goal with |- ?G => let G' := eval unfold bounds in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_kact a_reg a_tq a_cache] in G in change_no_check G' end). unfold kcost_free, EVT in *. repeat split; try assumption; lia.
  Qed.

  Lemma arm_nbf : ARM cond_nbf.
  Proof using FAM HPc HYP_RECYCLE G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP.
    intros h fx R M mdl Lc FF L1 L2 B C K ret sp m p st HH HFX W RP BD HLE MW CP HR10 FPC ELc HK (M28 & (tq' & b & ETQ & FULL) & ks & k & ECA).
    assert (HinP : In (U p, m) Lc) by (rewrite ELc; apply in_app_iff; right; left; reflexivity).
    apply (katD_bind BSEGS _ (runA_post bt FXOK KD (set_ialloc st) Lc FF R M mdl p)).
    { exact (free_runA' fx R M mdl Lc FF B C K ret sp m p st HFX HH MW W RP BD CP HR10 FPC HinP HK (ex_intro _ h (hp_le bt HP HPc FAM h st HLE))). }
    intros c' POST.
    destruct POST as (fx' & R' & M' & M0 & mdl' & d' & naa & id & Ec' & HFX' & HH' & W2 & RP2 & DX & CHG & Hb16
                      & Cq0 & Cq1 & Cq2 & Cq3 & Cq4 & Cq5 & Ci0 & Ci1 & Ci2 & Ci3 & Ci4 & Ci5 & Ci6
                      & Y2 & Y8 & Y9 & Y10 & Y18 & Y19 & Y20 & Y21 & Y22 & Y3 & Y4 & Y23 & Y24 & Y25 & Y26 & Y27 & Hid & SEV & LZ & MW2).
    subst c'.
    assert (HLEc : HPc h (runA_st (set_ialloc st) d' naa)) by (apply (hp_chg bt HP HPc FAM h st _ Lc FF (U p) m W HinP HLE); [intros c0; split; reflexivity | reflexivity | reflexivity | exact (Z.le_trans _ _ _ (Zplus_le_compat_r _ _ _ (proj2 (proj2 (proj2 BD)))) HK)]).
    apply (free_putNf bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD KDR G_KDR HYP_DRAIN OPS_WFX_newbatch HP HPc FAM
             h fx' R R' M M' M0 mdl mdl' Lc FF L1 L2 B C (K + kcost_free) ret sp m p (runA_st (set_ialloc st) d' naa) id ks k tq' b
             CP HR10 ELc W2 RP2).
    all: try assumption.
    (lazymatch goal with |- ?G => let G' := eval unfold runA_st, set_ialloc in G in change_no_check G' end). destruct BD as (B1 & B2 & B3). (lazymatch goal with |- ?G => let G' := eval unfold bounds in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_kact a_reg a_tq a_cache] in G in change_no_check G' end). unfold kcost_free, EVT in *. repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma arm_refill : ARM cond_refill.
  Proof using FAM HPc CELLSPIN HYP_REFILL G_KR KR HYP_RECYCLE G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP.
    intros h fx R M mdl Lc FF L1 L2 B C K ret sp m p st HH HFX W RP BD HLE MW CP HR10 FPC ELc HK (M28 & TQC & ECA).
    assert (HinP : In (U p, m) Lc) by (rewrite ELc; apply in_app_iff; right; left; reflexivity).
    apply (katD_bind BSEGS _ (runA_post bt FXOK KD (set_ialloc st) Lc FF R M mdl p)).
    { exact (free_runA' fx R M mdl Lc FF B C K ret sp m p st HFX HH MW W RP BD CP HR10 FPC HinP HK (ex_intro _ h (hp_le bt HP HPc FAM h st HLE))). }
    intros c' POST.
    destruct POST as (fx' & R' & M' & M0 & mdl' & d' & naa & id & Ec' & HFX' & HH' & W2 & RP2 & DX & CHG & Hb16
                      & Cq0 & Cq1 & Cq2 & Cq3 & Cq4 & Cq5 & Ci0 & Ci1 & Ci2 & Ci3 & Ci4 & Ci5 & Ci6
                      & Y2 & Y8 & Y9 & Y10 & Y18 & Y19 & Y20 & Y21 & Y22 & Y3 & Y4 & Y23 & Y24 & Y25 & Y26 & Y27 & Hid & SEV & LZ & MW2).
    subst c'.
    destruct TQC as [ETQ | (tq' & b & ETQ & FULL)].
    - assert (HLEc : HPc h (runA_st (set_ialloc st) d' naa)) by (apply (hp_chg bt HP HPc FAM h st _ Lc FF (U p) m W HinP HLE); [intros c0; split; reflexivity | reflexivity | reflexivity | exact (Z.le_trans _ _ _ (Zplus_le_compat_r _ _ _ (proj2 (proj2 (proj2 BD)))) HK)]).
    apply (free_putRe bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD KR G_KR HYP_REFILL CELLSPIN KDR G_KDR HYP_DRAIN OPS_WFX_newbatch HP HPc FAM
               h fx' R R' M M' M0 mdl mdl' Lc FF L1 L2 B C (K + kcost_free) ret sp m p (runA_st (set_ialloc st) d' naa) id
               CP HR10 ELc W2 RP2).
      all: try assumption.
      all: try (apply (AsAinvRoom3.mu_room_charged bt st Lc FF); [exact W | reflexivity | reflexivity]).            (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold runA_st, set_ialloc in G in change_no_check G' end). destruct BD as (B1 & B2 & B3). (lazymatch goal with |- ?G => let G' := eval unfold bounds in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_kact a_reg a_tq a_cache] in G in change_no_check G' end). unfold kcost_free, EVT in *. repeat split; try assumption; lia.
    - assert (HLEc : HPc h (runA_st (set_ialloc st) d' naa)) by (apply (hp_chg bt HP HPc FAM h st _ Lc FF (U p) m W HinP HLE); [intros c0; split; reflexivity | reflexivity | reflexivity | exact (Z.le_trans _ _ _ (Zplus_le_compat_r _ _ _ (proj2 (proj2 (proj2 BD)))) HK)]).
    apply (free_putRf bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD KR G_KR HYP_REFILL CELLSPIN KDR G_KDR HYP_DRAIN OPS_WFX_newbatch HP HPc FAM
               h fx' R R' M M' M0 mdl mdl' Lc FF L1 L2 B C (K + kcost_free) ret sp m p (runA_st (set_ialloc st) d' naa) id tq' b
               CP HR10 ELc W2 RP2).
      all: try assumption.
      all: try (apply (AsAinvRoom3.mu_room_charged bt st Lc FF); [exact W | reflexivity | reflexivity]).            (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold runA_st, set_ialloc in G in change_no_check G' end). destruct BD as (B1 & B2 & B3). (lazymatch goal with |- ?G => let G' := eval unfold bounds in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_kact a_reg a_tq a_cache] in G in change_no_check G' end). unfold kcost_free, EVT in *. repeat split; try assumption; lia.
  Qed.

  Theorem free_kat_G6 :
    ARM cond_big ->
    FREE_KAT BSEGS FXOK both_addrs (AAINV_F bt HP) MSTK_A (ia_free both_addrs).
  Proof using FAM HPc CELLSPIN HYP_REFILL G_KR KR HYP_RECYCLE G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP.
    intros ABIG. pose proof arm_refill as ARF.
    (lazymatch goal with |- ?G => let G' := eval unfold FREE_KAT in G in change_no_check G' end). intros h fx R M mdl Lc Lc' FF B C K B' C' K' ret sp p PRE.
    destruct PRE as (HH & HFX & AI & CP & HR10 & FPC & CASES).
    destruct AI as (st & W & RP & (BD & HLE) & MW).
    destruct CASES as [(Hp0 & -> & -> & -> & ->) | (m & L1 & L2 & ELc & -> & -> & -> & -> & HK)].
    { exact (free_null' h fx R M mdl Lc FF B C K ret sp p st HFX HH W RP BD HLE MW CP HR10 FPC Hp0). }
    assert (HK' : K + kcost_free <= KCAP) by lia.
    destruct (Z.lt_ge_cases (2 ^ 28) m) as [BIG | M28].
    { exact (ABIG h fx R M mdl Lc FF L1 L2 B C K ret sp m p st HH HFX W RP BD HLE MW CP HR10 FPC ELc HK' BIG). }
    destruct (list_nil_or_snoc (a_cache st BATCHCLASS)) as [EC0 | (ks & k & ECA)].
    { (* [comment removed for export] *)
      destruct (list_nil_or_snoc (a_tq st)) as [E0 | (tq' & b & ETQ)].
      { apply (ARF h fx R M mdl Lc FF L1 L2 B C K ret sp m p st HH HFX W RP BD HLE MW CP HR10 FPC ELc HK'). split; [lia | split; [left; exact E0 | exact EC0]]. }
      assert (HinB : In b (a_tq st ++ a_gq st)) by (apply in_app_iff; left; rewrite ETQ; apply in_app_iff; right; left; reflexivity).
      pose proof (batch_facts bt st Lc FF W b HinB) as (_ & BL & _).
      destruct (Z.eq_dec (Z.of_nat (length (ba_items b))) BATCHCAP) as [FULL | NF].
      { apply (ARF h fx R M mdl Lc FF L1 L2 B C K ret sp m p st HH HFX W RP BD HLE MW CP HR10 FPC ELc HK'). split; [lia | split; [right; exists tq', b; split; assumption | exact EC0]]. }
      apply (arm_put h fx R M mdl Lc FF L1 L2 B C K ret sp m p st HH HFX W RP BD HLE MW CP HR10 FPC ELc HK'). split; [lia|]. exists tq', b. split; [assumption | lia]. }
    destruct (list_nil_or_snoc (a_tq st)) as [E0 | (tq' & b & ETQ)].
    { apply (arm_nbe h fx R M mdl Lc FF L1 L2 B C K ret sp m p st HH HFX W RP BD HLE MW CP HR10 FPC ELc HK'). split; [lia | split; [exact E0 | exists ks, k; exact ECA]]. }
    assert (HinB : In b (a_tq st ++ a_gq st)) by (apply in_app_iff; left; rewrite ETQ; apply in_app_iff; right; left; reflexivity).
    pose proof (batch_facts bt st Lc FF W b HinB) as (_ & BL & _).
    destruct (Z.eq_dec (Z.of_nat (length (ba_items b))) BATCHCAP) as [FULL | NF].
    { apply (arm_nbf h fx R M mdl Lc FF L1 L2 B C K ret sp m p st HH HFX W RP BD HLE MW CP HR10 FPC ELc HK'). split; [lia | split; [exists tq', b; split; assumption | exists ks, k; exact ECA]]. }
    apply (arm_put h fx R M mdl Lc FF L1 L2 B C K ret sp m p st HH HFX W RP BD HLE MW CP HR10 FPC ELc HK'). split; [lia|]. exists tq', b. split; [assumption | lia].
  Qed.
End W6.

End BoAllocFTopW6.
Module BoAllocFTopW7.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFArms BoAllocFTopW6 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 BoAllocFRcK2 BoAllocFRcK3 BoAllocFRcK5.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section W7.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1408.
  Hypothesis HYP_DEPOT : HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Variable MINSZ : Z.
  Hypothesis CELL_min : In (0x10ab58 + 800, 8%nat, MINSZ) (bt_consts bt).     (* [comment removed for export] *)
  Hypothesis G_min : 0 <= MINSZ <= 2 ^ 28.
  Hypothesis RCC : rc_cells bt TSDP.
  Variable KR : Z.
  Hypothesis G_KR : 0 <= KR <= 1312.
  Hypothesis HYP_REFILL : HYP_REFILL24K_stmt bt FXOK KR.
  Hypothesis CELLSPIN : free_cells_spin bt.
  (* [comment removed for export] *)
  Variables (HP HPc : option Z -> ast -> Prop).
  Hypothesis FAM : hp_fam bt HP HPc.
  (* [comment removed for export] *)
  Hypothesis HYP_ITEM_FULL : rc_item_stmt bt FXOK arm_prim_full.
  Hypothesis HYP_ITEM_SEC : rc_item_stmt bt FXOK arm_sec.
  Hypothesis HYP_BFREE_FULL : rc_bfree_stmt bt FXOK arm_full24.
  Hypothesis HYP_MERGE : HYP_RECYCLE_arm bt FXOK (fun st => ~ arm_nomerge st).

  Lemma HYP_RECYCLE7 : HYP_RECYCLE_stmt bt FXOK 1376.
  Proof using HYP_MERGE HYP_BFREE_FULL HYP_ITEM_SEC HYP_ITEM_FULL RCC G_min CELL_min MINSZ HTP CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    apply (hyp_recycle_pf bt FXOK MINSZ BT_segs BT_ia CELLNB CELL_min G_min); [| | exact HYP_MERGE].
    - exact (rc_item_of_arms bt FXOK (rc_item_prim_pf bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB RCC HTP) HYP_ITEM_FULL HYP_ITEM_SEC).
    - exact (rc_bfree_of_arms bt FXOK (rc_bfree_room_pf bt FXOK BT_segs BT_ia CELLNB) HYP_BFREE_FULL).
  Qed.

  Theorem free_kat_G7 :
    BoAllocFTopW6.ARM2G bt FXOK HP cond_big ->
    FREE_KAT BSEGS FXOK both_addrs (AAINV_F bt HP) MSTK_A (ia_free both_addrs).
  Proof using HYP_MERGE HYP_BFREE_FULL HYP_ITEM_SEC HYP_ITEM_FULL FAM HPc CELLSPIN HYP_REFILL G_KR KR RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP.
    exact (free_kat_G6 bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD HYP_DEPOT HTP MINSZ CELL_min
             ltac:(clear - G_min; lia) HYP_RECYCLE7 KR G_KR HYP_REFILL CELLSPIN HP HPc FAM).
  Qed.
End W7.
End BoAllocFTopW7.
Module BoAllocFTopW8.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFArms BoAllocFTopW6 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 BoAllocFRcK2 BoAllocFRcK3 BoAllocFRcK5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK6a BoAllocFRcK6b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p.BoAllocFRcK6c BoAllocFTopW7.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section W8.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1408.
  Hypothesis HYP_DEPOT : HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Variable MINSZ : Z.
  Hypothesis CELL_min : In (0x10ab58 + 800, 8%nat, MINSZ) (bt_consts bt).     (* [comment removed for export] *)
  Hypothesis G_min : 0 <= MINSZ <= 2 ^ 28.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis RCF : rc_cells_full bt.
  Variable KR : Z.
  Hypothesis G_KR : 0 <= KR <= 1312.
  Hypothesis HYP_REFILL : HYP_REFILL24K_stmt bt FXOK KR.
  Hypothesis CELLSPIN : free_cells_spin bt.
  (* [comment removed for export] *)
  Variables (HP HPc : option Z -> ast -> Prop).
  Hypothesis FAM : hp_fam bt HP HPc.
  (* [comment removed for export] *)
  Hypothesis HYP_ITEM_FULL_MAP : rc_item_stmt bt FXOK arm_prim_full_map.
  Hypothesis HYP_ITEM_SEC : rc_item_stmt bt FXOK arm_sec.
  Hypothesis HYP_BFREE_FULL_MAP : rc_bfree_stmt bt FXOK arm_full24_map.
  Hypothesis HYP_MERGE : HYP_RECYCLE_arm bt FXOK (fun st => ~ arm_nomerge st).

  Theorem free_kat_G8 :
    BoAllocFTopW6.ARM2G bt FXOK HP cond_big ->
    FREE_KAT BSEGS FXOK both_addrs (AAINV_F bt HP) MSTK_A (ia_free both_addrs).
  Proof using HYP_MERGE HYP_BFREE_FULL_MAP HYP_ITEM_SEC HYP_ITEM_FULL_MAP FAM HPc CELLSPIN HYP_REFILL G_KR KR RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP.
    apply (free_kat_G7 bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD HYP_DEPOT HTP MINSZ CELL_min G_min RCC KR G_KR HYP_REFILL CELLSPIN HP HPc FAM).
    - exact (rc_item_full_of_arms bt FXOK (rc_item_full_room_pf bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB RCC RCF HTP) HYP_ITEM_FULL_MAP).
    - exact HYP_ITEM_SEC.
    - exact (rc_bfree_full_of_arms bt FXOK (rc_bfree_full_room_pf bt FXOK TSDP BT_segs BT_ia CELLNB RCC RCF) HYP_BFREE_FULL_MAP).
    - exact HYP_MERGE.
  Qed.
End W8.
End BoAllocFTopW8.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFTopW9.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFArms BoAllocFTopW6 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcHS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 BoAllocFRcK5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK6a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS BoAllocFTopW8.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section W9.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1408.
  Hypothesis HYP_DEPOT : HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Variable MINSZ : Z.
  Hypothesis CELL_min : In (0x10ab58 + 800, 8%nat, MINSZ) (bt_consts bt).     (* [comment removed for export] *)
  Hypothesis G_min : 0 <= MINSZ <= 2 ^ 28.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis RCF : rc_cells_full bt.
  Hypothesis SECC : sec_cells bt TSDP.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Hypothesis SHGATE : HYP_SHADOW_GATE_stmt bt.
  Variable KR : Z.
  Hypothesis G_KR : 0 <= KR <= 1312.
  Hypothesis HYP_REFILL : HYP_REFILL24K_stmt bt FXOK KR.
  Hypothesis CELLSPIN : free_cells_spin bt.
  (* [comment removed for export] *)
  Variables (HP HPc : option Z -> ast -> Prop).
  Hypothesis FAM : hp_fam bt HP HPc.
  (* [comment removed for export] *)
  Hypothesis HYP_ITEM_FULL_MAP : rc_item_stmt bt FXOK arm_prim_full_map.
  Hypothesis HYP_BFREE_FULL_MAP : rc_bfree_stmt bt FXOK arm_full24_map.
  Hypothesis HYP_MERGE : HYP_RECYCLE_arm bt FXOK (fun st => ~ arm_nomerge st).

  Theorem free_kat_G9 :
    BoAllocFTopW6.ARM2G bt FXOK HP cond_big ->
    FREE_KAT BSEGS FXOK both_addrs (AAINV_F bt HP) MSTK_A (ia_free both_addrs).
  Proof using HYP_MERGE HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP FAM HPc CELLSPIN HYP_REFILL G_KR KR SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP.
    apply (free_kat_G8 bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD HYP_DEPOT HTP MINSZ CELL_min G_min RCC RCF KR G_KR HYP_REFILL CELLSPIN HP HPc FAM
             HYP_ITEM_FULL_MAP (rc_item_sec_pf bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB RCC SECC HTP BOOTG SHGATE) HYP_BFREE_FULL_MAP HYP_MERGE).
  Qed.
End W9.
End BoAllocFTopW9.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMThunk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFTopW10.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFArms BoAllocFTopW6 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcHS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 BoAllocFRcK2 BoAllocFRcK3 BoAllocFRcK5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK6a BoAllocFRcK6b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p.BoAllocFRcK6c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS BoAllocFRcMK5 BoAllocFTopW7 BoAllocFTopW8 BoAllocFTopW9.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMThunk.BoAllocFThunk.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section W10.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1408.
  Hypothesis HYP_DEPOT : HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Variable MINSZ : Z.
  Hypothesis CELL_min : In (0x10ab58 + 800, 8%nat, MINSZ) (bt_consts bt).     (* [comment removed for export] *)
  Hypothesis G_min : 0 <= MINSZ <= 2 ^ 28.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis RCF : rc_cells_full bt.
  Hypothesis SECC : sec_cells bt TSDP.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Hypothesis SHGATE : HYP_SHADOW_GATE_stmt bt.
  Variable KR : Z.
  Hypothesis G_KR : 0 <= KR <= 1312.
  Hypothesis HYP_REFILL : HYP_REFILL24K_stmt bt FXOK KR.
  Hypothesis CELLSPIN : free_cells_spin bt.
  (* [comment removed for export] *)
  Variables (HP HPc : option Z -> ast -> Prop).
  Hypothesis FAM : hp_fam bt HP HPc.
  (* [comment removed for export] *)
  Hypothesis HYP_ITEM_FULL_MAP : rc_item_stmt bt FXOK arm_prim_full_map.
  Hypothesis HYP_BFREE_FULL_MAP : rc_bfree_stmt bt FXOK arm_full24_map.
  (* [comment removed for export] *)

  Lemma HITEM10 : rc_item_stmt bt FXOK arm_any.
  Proof using HYP_ITEM_FULL_MAP SHGATE BOOTG SECC RCF RCC HTP CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    exact (rc_item_of_arms bt FXOK (rc_item_prim_pf bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB RCC HTP)
             (rc_item_full_of_arms bt FXOK (rc_item_full_room_pf bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB RCC RCF HTP) HYP_ITEM_FULL_MAP)
             (rc_item_sec_pf bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB RCC SECC HTP BOOTG SHGATE)).
  Qed.
  Lemma HBFREE10 : rc_bfree_stmt bt FXOK arm_any24.
  Proof using HYP_BFREE_FULL_MAP RCF RCC CELLNB BT_ia BT_segs TSDP.
    exact (rc_bfree_of_arms bt FXOK (rc_bfree_room_pf bt FXOK BT_segs BT_ia CELLNB)
             (rc_bfree_full_of_arms bt FXOK (rc_bfree_full_room_pf bt FXOK TSDP BT_segs BT_ia CELLNB RCC RCF) HYP_BFREE_FULL_MAP)).
  Qed.

  Theorem free_kat_G10 :
    BoAllocFTopW6.ARM2G bt FXOK HP cond_big ->
    FREE_KAT BSEGS FXOK both_addrs (AAINV_F bt HP) MSTK_A (ia_free both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP FAM HPc CELLSPIN HYP_REFILL G_KR KR SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP.
    exact (free_kat_G9 bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD HYP_DEPOT HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE KR G_KR HYP_REFILL CELLSPIN HP HPc FAM
             HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP
             (hyp_recycle_merge bt FXOK MINSZ BT_segs BT_ia CELLNB CELL_min G_min HITEM10 HBFREE10)).
  Qed.
End W10.

Section W10H.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1408.
  Hypothesis HYP_DEPOT : HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Variable MINSZ : Z.
  Hypothesis CELL_min : In (0x10ab58 + 800, 8%nat, MINSZ) (bt_consts bt).     (* [comment removed for export] *)
  Hypothesis G_min : 0 <= MINSZ <= 2 ^ 28.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis RCF : rc_cells_full bt.
  Hypothesis SECC : sec_cells bt TSDP.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Hypothesis SHGATE : HYP_SHADOW_GATE_stmt bt.
  Variable KR : Z.
  Hypothesis G_KR : 0 <= KR <= 1312.
  Hypothesis HYP_REFILL : HYP_REFILL24K_stmt bt FXOK KR.
  Hypothesis CELLSPIN : free_cells_spin bt.
  (* [comment removed for export] *)
  Hypothesis HYP_ITEM_FULL_MAP : rc_item_stmt bt FXOK arm_prim_full_map.
  Hypothesis HYP_BFREE_FULL_MAP : rc_bfree_stmt bt FXOK arm_full24_map.


  (* [comment removed for export] *)
  Theorem free_kat_n_drx :
    BoAllocFTopW6.ARM2G bt FXOK HPd cond_big ->
    FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_free both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP CELLSPIN HYP_REFILL G_KR KR SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP.
    intros ABIG. apply (FREE_KAT_N_of_KAT BSEGS FXOK both_addrs (AAINV_F bt HPd)).
    exact (free_kat_G10 bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD HYP_DEPOT HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE KR G_KR HYP_REFILL CELLSPIN HPd HPdc (hp_fam_drv bt) HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP ABIG).
  Qed.
  (* [comment removed for export] *)
  Lemma free_kat_drx_all : BoAllocFTopW6.ARM2G bt FXOK HPd cond_big -> FREE_KAT BSEGS FXOK both_addrs (fun h => AAINVP (HPd h) bt) MSTK_A (ia_free both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP CELLSPIN HYP_REFILL G_KR KR SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP.
    intros ABIG.
    exact (free_kat_G10 bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD HYP_DEPOT HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE KR G_KR HYP_REFILL CELLSPIN HPd HPdc (hp_fam_drv bt) HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP ABIG).
  Qed.
  Theorem free_kat_n_drx_thunk : BoAllocFTopW6.ARM2G bt FXOK HPd cond_big -> FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_free_thunk both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP CELLSPIN HYP_REFILL G_KR KR SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP. intros ABIG. apply (FREE_KAT_N_of_KAT BSEGS FXOK both_addrs (fun h => AAINVP (HPd h) bt)). exact (free_kat_thunk_P bt FXOK BT_ia HPd MSTK_A (free_kat_drx_all ABIG)). Qed.
  Theorem free_kat_n_drx_opdel : BoAllocFTopW6.ARM2G bt FXOK HPd cond_big -> FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP CELLSPIN HYP_REFILL G_KR KR SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP. intros ABIG. apply (FREE_KAT_N_of_KAT BSEGS FXOK both_addrs (fun h => AAINVP (HPd h) bt)). exact (free_kat_opdel_P bt FXOK BT_ia HPd MSTK_A (free_kat_drx_all ABIG)). Qed.
  Theorem free_kat_n_drx_opdel_sz : BoAllocFTopW6.ARM2G bt FXOK HPd cond_big -> FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel_sz both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP CELLSPIN HYP_REFILL G_KR KR SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP. intros ABIG. apply (FREE_KAT_N_of_KAT BSEGS FXOK both_addrs (fun h => AAINVP (HPd h) bt)). exact (free_kat_opdel_sz_P bt FXOK BT_ia HPd MSTK_A (free_kat_drx_all ABIG)). Qed.
End W10H.
End BoAllocFTopW10.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutBg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFTopBg.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFArms BoAllocFTopW6 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcHS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 BoAllocFRcK2 BoAllocFRcK3 BoAllocFRcK5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK6a BoAllocFRcK6b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p.BoAllocFRcK6c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS BoAllocFRcMK5 BoAllocFTopW7 BoAllocFTopW8 BoAllocFTopW9.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMThunk.BoAllocFThunk.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i.BoAllocFTopA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutBg BoAllocFTopW10.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.


Section ARMBIG.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis SECC : sec_cells bt TSDP.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1408.
  Hypothesis HYP_DEPOT : HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Hypothesis SHGATE : HYP_SHADOW_GATE_stmt bt.
  Variables (HP HPc : option Z -> ast -> Prop).
  Hypothesis FAM : hp_fam bt HP HPc.

  Theorem arm_big : BoAllocFTopW6.ARM2G bt FXOK HP cond_big.
  Proof using FAM HPc SHGATE BOOTG HTP HYP_DEPOT G_KD GEOM SECC RCC CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP.
    (lazymatch goal with |- ?G => let G' := eval unfold BoAllocFTopW6.ARM2G in G in change_no_check G' end).
    intros h fx R M mdl Lc FF L1 L2 B C K ret sp m p st HH HFX W RP BD HLE MW CP HR10 FPC ELc HK BIG. unfold cond_big in BIG.
    assert (HinP : In (bv_unsigned p, m) Lc) by (rewrite ELc; apply in_app_iff; right; left; reflexivity).
    apply (katD_bind BSEGS _ (runA_post bt FXOK KD (set_ialloc st) Lc FF R M mdl p)).
    { exact (BoAllocFTopW6.free_runA' bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS GEOM G_KD HYP_DEPOT HTP
               fx R M mdl Lc FF B C K ret sp m p st HFX HH MW W RP BD CP HR10 FPC HinP HK (ex_intro _ h (hp_le bt HP HPc FAM h st HLE))). }
    intros c' POST.
    destruct POST as (fx' & R' & M' & M0 & mdl' & d' & naa & id & Ec' & HFX' & HH' & W2 & RP2 & DX & CHG & Hb16
                      & Cq0 & Cq1 & Cq2 & Cq3 & Cq4 & Cq5 & Ci0 & Ci1 & Ci2 & Ci3 & Ci4 & Ci5 & Ci6
                      & Y2 & Y8 & Y9 & Y10 & Y18 & Y19 & Y20 & Y21 & Y22 & Y3 & Y4 & Y23 & Y24 & Y25 & Y26 & Y27 & Hid & SEV & LZ & MW2).
    subst c'.
    assert (HLEc : HPc h (runA_st (set_ialloc st) d' naa)) by (apply (hp_chg bt HP HPc FAM h st _ Lc FF (bv_unsigned p) m W HinP HLE); [intros c0; split; reflexivity | reflexivity | reflexivity | exact (Z.le_trans _ _ _ (Zplus_le_compat_r _ _ _ (proj2 (proj2 (proj2 BD)))) HK)]).
    apply (free_putBg bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB RCC SECC G_KD HTP BOOTG SHGATE HP HPc FAM
             h fx' R R' M M' M0 mdl mdl' Lc FF L1 L2 B C (K + kcost_free) ret sp m p (runA_st (set_ialloc st) d' naa) id
             CP HR10 ELc W2 RP2).
    all: try assumption.
    (lazymatch goal with |- ?G => let G' := eval unfold runA_st, set_ialloc in G in change_no_check G' end). destruct BD as (B1 & B2 & B3). (lazymatch goal with |- ?G => let G' := eval unfold bounds in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_kact a_reg a_tq a_cache] in G in change_no_check G' end). unfold kcost_free, EVT in *. repeat split; try assumption; lia.
  Qed.
End ARMBIG.

Section W11.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1408.
  Hypothesis HYP_DEPOT : HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Variable MINSZ : Z.
  Hypothesis CELL_min : In (0x10ab58 + 800, 8%nat, MINSZ) (bt_consts bt).     (* [comment removed for export] *)
  Hypothesis G_min : 0 <= MINSZ <= 2 ^ 28.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis RCF : rc_cells_full bt.
  Hypothesis SECC : sec_cells bt TSDP.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Hypothesis SHGATE : HYP_SHADOW_GATE_stmt bt.
  Variable KR : Z.
  Hypothesis G_KR : 0 <= KR <= 1312.
  Hypothesis HYP_REFILL : HYP_REFILL24K_stmt bt FXOK KR.
  Hypothesis CELLSPIN : free_cells_spin bt.
  (* [comment removed for export] *)
  Hypothesis HYP_ITEM_FULL_MAP : rc_item_stmt bt FXOK arm_prim_full_map.
  Hypothesis HYP_BFREE_FULL_MAP : rc_bfree_stmt bt FXOK arm_full24_map.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem free_kat_W11 : FREE_KAT BSEGS FXOK both_addrs (AAINV_H bt) MSTK_A (ia_free both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP CELLSPIN HYP_REFILL G_KR KR SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP.
    exact (free_kat_G10 bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD HYP_DEPOT HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE KR G_KR HYP_REFILL CELLSPIN holes_le (HPlc) (hp_fam_le bt) HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP
             (arm_big bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB RCC SECC GEOM G_KD HYP_DEPOT HTP BOOTG SHGATE holes_le (HPlc) (hp_fam_le bt))).
  Qed.
  (* [comment removed for export] *)
  Lemma ARM_BIG_DRX : BoAllocFTopW6.ARM2G bt FXOK HPd cond_big.
  Proof using SHGATE BOOTG SECC RCC HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP. exact (arm_big bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB RCC SECC GEOM G_KD HYP_DEPOT HTP BOOTG SHGATE HPd HPdc (hp_fam_drv bt)). Qed.
  Theorem free_kat_n_drx11 : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_free both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP CELLSPIN HYP_REFILL G_KR KR SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD HYP_DEPOT HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE KR G_KR HYP_REFILL CELLSPIN HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP ARM_BIG_DRX). Qed.
  Theorem free_kat_n_drx11_thunk : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_free_thunk both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP CELLSPIN HYP_REFILL G_KR KR SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx_thunk bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD HYP_DEPOT HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE KR G_KR HYP_REFILL CELLSPIN HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP ARM_BIG_DRX). Qed.
  Theorem free_kat_n_drx11_opdel : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP CELLSPIN HYP_REFILL G_KR KR SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx_opdel bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD HYP_DEPOT HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE KR G_KR HYP_REFILL CELLSPIN HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP ARM_BIG_DRX). Qed.
  Theorem free_kat_n_drx11_opdel_sz : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel_sz both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP CELLSPIN HYP_REFILL G_KR KR SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx_opdel_sz bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD HYP_DEPOT HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE KR G_KR HYP_REFILL CELLSPIN HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP ARM_BIG_DRX). Qed.
End W11.
End BoAllocFTopBg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFTopRf.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFArms BoAllocFTopW6 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcHS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 BoAllocFRcK2 BoAllocFRcK3 BoAllocFRcK5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK6a BoAllocFRcK6b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p.BoAllocFRcK6c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS BoAllocFRcMK5 BoAllocFTopW7 BoAllocFTopW8 BoAllocFTopW9.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMThunk.BoAllocFThunk.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i.BoAllocFTopA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutBg BoAllocFTopW10.
Import BoAllocFTopBg OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1.BoAllocFRefillG OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1.BoAllocM8Ls.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.



Section W12.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1408.
  Hypothesis HYP_DEPOT : HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Variable MINSZ : Z.
  Hypothesis CELL_min : In (0x10ab58 + 800, 8%nat, MINSZ) (bt_consts bt).     (* [comment removed for export] *)
  Hypothesis G_min : 0 <= MINSZ <= 2 ^ 28.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis RCF : rc_cells_full bt.
  Hypothesis SECC : sec_cells bt TSDP.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Hypothesis SHGATE : HYP_SHADOW_GATE_stmt bt.
  Hypothesis CELLSPIN : free_cells_spin bt.
  (* [comment removed for export] *)
  Variables (TPm TSDPm PGPm FLm MIDENDm : Z).
  Hypothesis HTPm : TPm = ia_tp both_addrs.
  Hypothesis CELLSM : malloc_cells bt TPm TSDPm PGPm FLm MIDENDm.
  Hypothesis PCELLS : pop_cells bt.
  (* [comment removed for export] *)
  Hypothesis HYP_ITEM_FULL_MAP : rc_item_stmt bt FXOK arm_prim_full_map.
  Hypothesis HYP_BFREE_FULL_MAP : rc_bfree_stmt bt FXOK arm_full24_map.
  (* [comment removed for export] *)


  Lemma G640 : 0 <= 672 <= 1312.  Proof using. lia. Qed.
  Lemma HYP_REFILL_PF : HYP_REFILL24K_stmt bt FXOK 672.
  Proof using PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm BOOTG BT_ia BT_segs.
    apply (hyp_refill24k_pf bt FXOK BT_ia TPm HTPm).
    intros fx X. exact (@refill_katD_dm_b _ fx bt BT_segs BT_ia BOOTG TPm TSDPm PGPm FLm MIDENDm CELLSM PCELLS X).
  Qed.

  Theorem free_kat_W12 : FREE_KAT BSEGS FXOK both_addrs (AAINV_H bt) MSTK_A (ia_free both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP. exact (free_kat_W11 bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD HYP_DEPOT HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE 672 G640 HYP_REFILL_PF CELLSPIN HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP). Qed.
  Theorem free_kat_n_drx12 : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_free both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx11 bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD HYP_DEPOT HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE 672 G640 HYP_REFILL_PF CELLSPIN HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP). Qed.
  Theorem free_kat_n_drx12_thunk : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_free_thunk both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx11_thunk bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD HYP_DEPOT HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE 672 G640 HYP_REFILL_PF CELLSPIN HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP). Qed.
  Theorem free_kat_n_drx12_opdel : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx11_opdel bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD HYP_DEPOT HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE 672 G640 HYP_REFILL_PF CELLSPIN HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP). Qed.
  Theorem free_kat_n_drx12_opdel_sz : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel_sz both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP HYP_DEPOT G_KD GEOM CELLNB CELLS BT_ia BT_segs KD CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx11_opdel_sz bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS CELLNB GEOM G_KD HYP_DEPOT HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE 672 G640 HYP_REFILL_PF CELLSPIN HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP). Qed.
End W12.
End BoAllocFTopRf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFArms BoAllocFTopW6 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcHS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 BoAllocFRcK2 BoAllocFRcK3 BoAllocFRcK5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK6a BoAllocFRcK6b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p.BoAllocFRcK6c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS BoAllocFRcMK5 BoAllocFTopW7 BoAllocFTopW8 BoAllocFTopW9.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMThunk. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMThunk.BoAllocFThunk.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutBg. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i.BoAllocFTopA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutBg BoAllocFTopW10.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc. Import BoAllocFTopBg OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1.BoAllocFRefillG OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1.BoAllocM8Ls.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop6. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop6 BoAllocFTopRf.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.




Section W13.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis GEOM : free_boot_geom bt.
  (* [comment removed for export] *)
  Hypothesis BF : AsKSys10.AsAinvBootF3.boot_facts bt.
  Hypothesis BTOT : AsKSys10.AsKSys11.boot_totals bt.
  Hypothesis DC1 : BoDepotTop3.BoDepotTop1.depot_cells bt.
  Hypothesis DC2 : BoDepotTopN1b.BoDepotTopN1a.depot_cells2 bt.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Variable MINSZ : Z.
  Hypothesis CELL_min : In (0x10ab58 + 800, 8%nat, MINSZ) (bt_consts bt).     (* [comment removed for export] *)
  Hypothesis G_min : 0 <= MINSZ <= 2 ^ 28.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis RCF : rc_cells_full bt.
  Hypothesis SECC : sec_cells bt TSDP.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Hypothesis SHGATE : HYP_SHADOW_GATE_stmt bt.
  Hypothesis CELLSPIN : free_cells_spin bt.
  (* [comment removed for export] *)
  Variables (TPm TSDPm PGPm FLm MIDENDm : Z).
  Hypothesis HTPm : TPm = ia_tp both_addrs.
  Hypothesis CELLSM : malloc_cells bt TPm TSDPm PGPm FLm MIDENDm.
  Hypothesis PCELLS : pop_cells bt.
  (* [comment removed for export] *)
  Hypothesis HYP_ITEM_FULL_MAP : rc_item_stmt bt FXOK arm_prim_full_map.
  Hypothesis HYP_BFREE_FULL_MAP : rc_bfree_stmt bt FXOK arm_full24_map.
  (* [comment removed for export] *)



  Lemma G1376 : 0 <= 1376 <= 1408.  Proof using. lia. Qed.
  Lemma HYP_DEPOT_PF : HYP_DEPOT_stmt bt FXOK 1376.
  Proof using DC2 DC1 BTOT BF BT_ia BT_segs. apply (hyp_depot_closed bt FXOK BF BTOT BT_segs BT_ia DC1 DC2 1376). lia. Qed.

  Theorem free_kat_W13 : FREE_KAT BSEGS FXOK both_addrs (AAINV_H bt) MSTK_A (ia_free both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP DC2 DC1 BTOT BF GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP. exact (free_kat_W12 bt FXOK TP TSDP PGP FL MIDEND CPM 1376 BT_segs BT_ia CELLS CELLNB GEOM G1376 HYP_DEPOT_PF HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE CELLSPIN TPm TSDPm PGPm FLm MIDENDm HTPm CELLSM PCELLS HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP). Qed.
  Theorem free_kat_n_drx13 : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_free both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP DC2 DC1 BTOT BF GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx12 bt FXOK TP TSDP PGP FL MIDEND CPM 1376 BT_segs BT_ia CELLS CELLNB GEOM G1376 HYP_DEPOT_PF HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE CELLSPIN TPm TSDPm PGPm FLm MIDENDm HTPm CELLSM PCELLS HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP). Qed.
  Theorem free_kat_n_drx13_thunk : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_free_thunk both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP DC2 DC1 BTOT BF GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx12_thunk bt FXOK TP TSDP PGP FL MIDEND CPM 1376 BT_segs BT_ia CELLS CELLNB GEOM G1376 HYP_DEPOT_PF HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE CELLSPIN TPm TSDPm PGPm FLm MIDENDm HTPm CELLSM PCELLS HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP). Qed.
  Theorem free_kat_n_drx13_opdel : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP DC2 DC1 BTOT BF GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx12_opdel bt FXOK TP TSDP PGP FL MIDEND CPM 1376 BT_segs BT_ia CELLS CELLNB GEOM G1376 HYP_DEPOT_PF HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE CELLSPIN TPm TSDPm PGPm FLm MIDENDm HTPm CELLSM PCELLS HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP). Qed.
  Theorem free_kat_n_drx13_opdel_sz : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel_sz both_addrs).
  Proof using HYP_BFREE_FULL_MAP HYP_ITEM_FULL_MAP PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP DC2 DC1 BTOT BF GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx12_opdel_sz bt FXOK TP TSDP PGP FL MIDEND CPM 1376 BT_segs BT_ia CELLS CELLNB GEOM G1376 HYP_DEPOT_PF HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE CELLSPIN TPm TSDPm PGPm FLm MIDENDm HTPm CELLSM PCELLS HYP_ITEM_FULL_MAP HYP_BFREE_FULL_MAP). Qed.
End W13.
