(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanMainEntryKit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts AsanMainEntryLemmas.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Cells Step Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX AW_Populate HMLib HM AH0Spec0 AH0Facts AH0Base AH0Layout AH0Mem1.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Blist AW_FakeDefs AH0Rom. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AH0Mem2 () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_wf"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.cell_ok"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanCertDefs.ASEGS"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.CZero"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.CWr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.v_addi"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.winst"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WMd"; "LinuxProcessSemantics.Riscv.Instr.M_MUL"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WLit"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WVar"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_prim"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_pslack"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Facts.qbase"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Facts.fchkd"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Mem1.CT_COMMON"; "Corelib.Init.Nat.mul"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Facts.fwr"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Facts.qaddr"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Facts.QLit"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Peano.lt"; "Corelib.Lists.ListDef.map"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)
Definition ct_silent (q : qbase) (c : ct) (z n : Z) : bool :=
  match c with
  | TWord a w v => match apos q a with Some o => (o + Z.of_nat w <=? z) || (z + n <=? o) | None => true end
  | TZero a len | TFill a len _ => match apos q a, wlitu len with
                                 | Some o, Some l => (o + l <=? z) || (z + n <=? o)
                                 | Some _, None => true
                                 | None, _ => true end
  | TImg lo hi => match q with QLit => (hi <=? z) || (z + n <=? lo) | QTpl _ => true end
  | _ => true
  end%bool.
Fixpoint img_first (q : qbase) (L : list ct) (z n : Z) : bool :=
  match L with
  | [] => false
  | c :: L' => match c, q with
               | TImg lo hi, QLit => if ((lo <=? z) && (z + n <=? hi))%bool then true
                                    else if ct_silent q c z n then img_first q L' z n else false
               | _, _ => if ct_silent q c z n then img_first q L' z n else false
               end
  end.
Lemma ct_silent_sound : forall q c z n i, ct_silent q c z n = true -> z <= i < z + n ->
  match c with TImg _ _ => match q with QLit => cbyte q c i = None | _ => True end | _ => cbyte q c i = None end.
Proof.
  intros q c z n i H Hi. destruct c as [a w v|a len|a len c8|a len|a len|lo hi]; cbn [ct_silent] in H; cbn [cbyte].
  - destruct (apos q a) as [o|]; [|reflexivity]. destruct (wlit v); [|reflexivity].
    destruct ((o <=? i) && (i <? o + Z.of_nat w))%bool eqn:E; [|reflexivity]. exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
  - destruct (apos q a) as [o|]; [|reflexivity]. destruct (wlitu len) as [l|]; [|reflexivity].
    destruct ((o <=? i) && (i <? o + l))%bool eqn:E; [|reflexivity]. exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
  - destruct (apos q a) as [o|]; [|reflexivity]. destruct (wlitu len) as [l|]; [|reflexivity].
    destruct ((o <=? i) && (i <? o + l))%bool eqn:E; [|reflexivity]. exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
  - reflexivity.
  - reflexivity.
  - destruct q; [|exact I]. destruct ((lo <=? i) && (i <? hi))%bool eqn:E; [|reflexivity]. exfalso.
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.
Lemma img_first_sound : forall L z n i b, img_first QLit L z n = true -> z <= i < z + n -> rom_byte i = Some b -> fbyte QLit L i = Some b.
Proof.
  induction L as [|c L IH]; intros z n i b H Hi Rb; [discriminate H|].
  cbn [img_first] in H. cbn [fbyte].
  assert (STEP : ct_silent QLit c z n = true -> img_first QLit L z n = true -> match cbyte QLit c i with Some b => Some b | None => fbyte QLit L i end = Some b).
  { intros S R. pose proof (ct_silent_sound QLit c z n i S Hi) as X. destruct c; cbn beta iota in X; rewrite X; exact (IH z n i b R Hi Rb). }
  destruct c as [a w v|a len|a len c8|a len|a len|lo hi]; try (destruct (ct_silent QLit _ z n) eqn:S; [exact (STEP eq_refl H)| discriminate H]).
  destruct ((lo <=? z) && (z + n <=? hi))%bool eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. cbn [cbyte].
    replace ((lo <=? i) && (i <? hi))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    rewrite Rb. reflexivity.
  - destruct (ct_silent QLit (TImg lo hi) z n) eqn:S; [exact (STEP eq_refl H)| discriminate H].
Qed.
Lemma fbytes_rom_zero : forall L n z, img_first QLit L z (Z.of_nat n) = true ->
  (forall i, z <= i < z + Z.of_nat n -> rom_byte i = Some (Z_to_bv 8 0)) ->
  fbytes QLit L z n = Some (repeat (Z_to_bv 8 0) n).
Proof.
  intros L n. induction n as [|n IH]; intros z H R; [reflexivity|].
  cbn [fbytes repeat]. rewrite (img_first_sound L z (Z.of_nat (S n)) z (Z_to_bv 8 0) H ltac:(lia) (R z ltac:(lia))).
  rewrite (IH (z + 1)); [reflexivity| |intros i Hi; apply R; lia].
  revert H. clear. induction L as [|c L IHL]; intros H; [discriminate H|]. cbn [img_first] in H |- *.
  assert (SIL : ct_silent QLit c z (Z.of_nat (S n)) = true -> ct_silent QLit c (z + 1) (Z.of_nat n) = true).
  { destruct c; cbn [ct_silent]; try reflexivity.
    - destruct (apos QLit a); [|reflexivity]. intros X. apply orb_prop in X. apply orb_true_intro. destruct X as [X|X]; apply Z.leb_le in X; [left|right]; apply Z.leb_le; lia.
    - destruct (apos QLit a); [|reflexivity]. destruct (wlitu n0); [|reflexivity]. intros X. apply orb_prop in X. apply orb_true_intro. destruct X as [X|X]; apply Z.leb_le in X; [left|right]; apply Z.leb_le; lia.
    - destruct (apos QLit a); [|reflexivity]. destruct (wlitu n0); [|reflexivity]. intros X. apply orb_prop in X. apply orb_true_intro. destruct X as [X|X]; apply Z.leb_le in X; [left|right]; apply Z.leb_le; lia.
    - intros X. apply orb_prop in X. apply orb_true_intro. destruct X as [X|X]; apply Z.leb_le in X; [left|right]; apply Z.leb_le; lia. }
  destruct c as [a w v|a len|a len c8|a len|a len|lo hi];
    try (destruct (ct_silent QLit _ z (Z.of_nat (S n))) eqn:S; [rewrite (SIL eq_refl); exact (IHL H)| discriminate H]).
  destruct ((lo <=? z) && (z + Z.of_nat (S n) <=? hi))%bool eqn:E.
  + apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    replace ((lo <=? z + 1) && (z + 1 + Z.of_nat n <=? hi))%bool with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia). reflexivity.
  + destruct ((lo <=? z + 1) && (z + 1 + Z.of_nat n <=? hi))%bool; [reflexivity|].
    destruct (ct_silent QLit (TImg lo hi) z (Z.of_nat (S n))) eqn:S; [rewrite (SIL eq_refl); exact (IHL H)| discriminate H].
Qed.
Lemma bytes_eqb_refl : forall bs, bytes_eqb bs bs = true.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn [bytes_eqb]. rewrite IH, Z.eqb_refl. reflexivity. Qed.
Lemma fchkw_zero_fast : forall L z n,
  img_first QLit L z (Z.of_nat n) = true -> bss_check ASEGS z (z + Z.of_nat n) = true -> fwr QLit L z (Z.of_nat n) = true ->
  fchkw QLit L z [CB n (repeat (Z_to_bv 8 0) n)] = true.
Proof.
  intros L z n H B W. unfold fchkw, fchk. cbn [cells_size csize cells_bytes cbytes app]. rewrite app_nil_r, Nat.add_0_r.
  rewrite (fbytes_rom_zero L n z H).
  - rewrite bytes_eqb_refl. exact W.
  - intros i Hi. exact (proj2 (bss_check_sound ASEGS z (z + Z.of_nat n) B i Hi)).
Qed.
Lemma fchkd_zero_fast : forall L z n,
  img_first QLit L z (Z.of_nat n) = true -> bss_check ASEGS z (z + Z.of_nat n) = true -> fchkd QLit L z n = true.
Proof.
  intros L z n H B. unfold fchkd. rewrite (fbytes_rom_zero L n z H); [reflexivity|].
  intros i Hi. exact (proj2 (bss_check_sound ASEGS z (z + Z.of_nat n) B i Hi)).
Qed.
(* [comment removed for export] *)
Lemma firstn_skipn_repeat : forall {A} (x : A) n i k, (i + k <= n)%nat -> firstn k (skipn i (repeat x n)) = repeat x k.
Proof.
  intros A x n i k H. rewrite skipn_repeat || idtac.
  revert n H. induction i as [|i IH]; intros n H.
  - cbn. revert n H. induction k as [|k IHk]; intros n H; [reflexivity|]. destruct n as [|n]; [lia|]. cbn. f_equal. apply IHk. lia.
  - destruct n as [|n]; [lia|]. cbn. apply IH. lia.
Qed.
Lemma u64s_repeat0 : forall k, u64s (repeat (Z_to_bv 64 0) k) = repeat (Z_to_bv 8 0) (8 * k).
Proof. induction k as [|k IH]; [reflexivity|]. cbn [repeat u64s]. rewrite IH. replace (8 * S k)%nat with (8 + 8 * k)%nat by lia. rewrite repeat_app. reflexivity. Qed.
Lemma u32s_repeat0 : forall k, u32s (repeat (Z_to_bv 64 0) k) = repeat (Z_to_bv 8 0) (4 * k).
Proof. induction k as [|k IH]; [reflexivity|]. cbn [repeat u32s]. rewrite IH. replace (4 * S k)%nat with (4 + 4 * k)%nat by lia. rewrite repeat_app. reflexivity. Qed.
(* [comment removed for export] *)
Fixpoint unchunk8 (k : nat) (bs : list byte) : list word :=
  match k with O => [] | S k' => le_bytes_to_word (firstn 8 bs) :: unchunk8 k' (skipn 8 bs) end.
Lemma unchunk8_length : forall k bs, length (unchunk8 k bs) = k.
Proof. induction k; intros bs; cbn; [reflexivity| rewrite IHk; reflexivity]. Qed.
Lemma u64s_unchunk8 : forall k bs, length bs = (8 * k)%nat -> u64s (unchunk8 k bs) = bs.
Proof.
  induction k as [|k IH]; intros bs Hl.
  - destruct bs; [reflexivity| cbn in Hl; lia].
  - cbn [unchunk8 u64s]. rewrite le8_le_bytes_to_word by (rewrite firstn_length; lia). rewrite IH by (rewrite skipn_length; lia). apply firstn_skipn.
Qed.

Lemma le_by_eq : forall x y b : Z, x = y -> y + b <= 2 ^ 64 -> x + b <= 2 ^ 64.
Proof. intros x y b -> H. exact H. Qed.

(* [comment removed for export] *)
Lemma bytes_at_sub : ltac2:(CDefT.buildp (gd_tbl_AH0Mem2 ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Pbs,(0.(2.&8.))Pi,$5.Pk,$5.P,(6.R6.R5.R4.R3.)P,(7.(8.R3.R2.)(9.(2.&8.)R4.))(6.R8.R7.(:.R6.(;.R4.))(<.(2.&8.)R3.(=.(2.&8.)R4.R5.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A bs i k H Hik.
  rewrite <- (firstn_skipn i bs) in H. apply bytes_at_app in H as [_ H]. rewrite firstn_length_le in H by lia.
  rewrite <- (firstn_skipn k (skipn i bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma nth_error_repeat' : forall {A} (x : A) n i, (i < n)%nat -> nth_error (repeat x n) i = Some x.
Proof. intros A x n. induction n as [|n IH]; intros i Hi; [lia|]. destruct i; cbn; [reflexivity | apply IH; lia]. Qed.

Section ZR.
  Context {hAR : arun}.
  Variable mem : word -> option byte.
    Variables (B zoff : Z) (zlen : nat) (wlen : Z).
    Hypothesis ZB : bytes_at asegs mem (B + zoff) (repeat (Z_to_bv 8 0) zlen).
    Hypothesis WB : wr_at asegs mem B wlen.
    #[using="ZB"] Lemma zr_bytes : ltac2:(CDefT.buildp (gd_tbl_AH0Mem2 ()) "Poff,$4.Pk,$5.P,(>.Vzoff,R2.)P,(>.(:.R3.(;.R2.))(:.Vzoff,(;.Vzlen,)))(6.$?.Vmem,(:.VB,R4.)(10.(2.&8.)(11.&8.=)R3.))")
(* [comment removed for export] *).
    Proof.
      intros off k H1 H2. pose proof (bytes_at_sub asegs mem (B + zoff) _ (Z.to_nat (off - zoff)) k ZB ltac:(rewrite repeat_length; lia)) as X.
      rewrite firstn_skipn_repeat in X by lia. replace (B + zoff + Z.of_nat (Z.to_nat (off - zoff))) with (B + off) in X by lia. exact X.
    Qed.
    #[using="WB"] Lemma zr_wr : forall off n, 0 <= off -> 0 <= n -> off + n <= wlen -> wr_at asegs mem (B + off) n.
    Proof.
      intros off n H1 H2 H3. pose proof WB as W.
      replace wlen with (off + (n + (wlen - off - n))) in W by lia.
      apply (proj1 (wr_at_app asegs mem B off (n + (wlen - off - n)) ltac:(lia) ltac:(lia))) in W as [_ W].
      apply (proj1 (wr_at_app asegs mem (B + off) n (wlen - off - n) ltac:(lia) ltac:(lia))) in W as [W _]. exact W.
    Qed.
    #[using="ZB WB"] Lemma zr_rw : ltac2:(CDefT.buildp (gd_tbl_AH0Mem2 ()) "Poff,$4.Pcs,(0.$12.)P,(13.R1.)P,(14.(0.(2.&8.))(15.R2.)(10.(2.&8.)(11.&8.=)(16.R2.)))P,(>.Vzoff,R4.)P,(>.(:.R5.(;.(16.R4.)))(:.Vzoff,(;.Vzlen,)))P,(>.=Vzoff,)P,(>.(:.Vzoff,(;.Vzlen,))Vwlen,)(17.$?.Vmem,(:.VB,R8.)R7.)")
(* [comment removed for export] *).
    Proof.
      intros off cs Hwf Hb H1 H2 H3 H4. split; [split; [exact Hwf | rewrite Hb; apply zr_bytes; lia] | apply zr_wr; lia].
    Qed.
    #[using="ZB WB"] Lemma zr_u64arr : ltac2:(CDefT.buildp (gd_tbl_AH0Mem2 ()) "Poff,$4.Pk,$5.P,(>.Vzoff,R2.)P,(>.(:.R3.(18.+8.(;.R2.)))(:.Vzoff,(;.Vzlen,)))P,(>.=Vzoff,)P,(>.(:.Vzoff,(;.Vzlen,))Vwlen,)(19.$?.Vmem,(:.VB,R6.)(10.(2.&40.)(11.&40.=)R5.))")
(* [comment removed for export] *).
    Proof. intros off k H1 H2 H3 H4. split; [rewrite u64s_repeat0; apply zr_bytes; lia | rewrite repeat_length; apply zr_wr; lia]. Qed.
    #[using="ZB WB"] Lemma zr_u32arr : ltac2:(CDefT.buildp (gd_tbl_AH0Mem2 ()) "Poff,$4.Pk,$5.P,(>.Vzoff,R2.)P,(>.(:.R3.(18.+4.(;.R2.)))(:.Vzoff,(;.Vzlen,)))P,(>.=Vzoff,)P,(>.(:.Vzoff,(;.Vzlen,))Vwlen,)(1:.$?.Vmem,(:.VB,R6.)(10.(2.&40.)(11.&40.=)R5.))")
(* [comment removed for export] *).
    Proof. intros off k H1 H2 H3 H4. split; [rewrite u32s_repeat0; apply zr_bytes; lia | rewrite repeat_length; apply zr_wr; lia]. Qed.
    #[using="ZB WB"] Lemma zr_u8arr : ltac2:(CDefT.buildp (gd_tbl_AH0Mem2 ()) "Poff,$4.Pk,$5.P,(>.Vzoff,R2.)P,(>.(:.R3.(;.R2.))(:.Vzoff,(;.Vzlen,)))P,(>.=Vzoff,)P,(>.(:.Vzoff,(;.Vzlen,))Vwlen,)(1;.$?.Vmem,(:.VB,R6.)(10.(2.&8.)(11.&8.=)R5.))")
(* [comment removed for export] *).
    Proof. intros off k H1 H2 H3 H4. split; [apply zr_bytes; lia | rewrite repeat_length; apply zr_wr; lia]. Qed.
End ZR.

Section Mem2.
  Context {hAR : arun}.
  Variable mem : word -> option byte.
  Variable p : me_params.
  Hypothesis HCN : Forall cnst_ok (me_cnsts p).
  Hypothesis HCOM : Forall (cell_ok ASEGS mem) (cells_common p).
  Variable STKHI : Z.
  Variable FOG : list (Z * Z).
  Variable TF : Z.
  Let bp := bp_of p STKHI FOG TF.
  Let h0 := h0_of bp.
  Let HF := HF mem p HCOM.
  Local Ltac pv := cbn; tauto.
  Local Ltac zdec := repeat match goal with |- _ /\ _ => split end;
    first [ apply Z.leb_le; vm_compute; reflexivity | apply Z.ltb_lt; vm_compute; reflexivity | apply Z.eqb_eq; vm_compute; reflexivity ].
  Local Ltac orw :=
    lazymatch goal with |- rw_cells asegs ?m ?A ?cs =>
      lazymatch cs with context [p] => fail "orw: symbolic cell" | _ =>
      lazymatch A with context [p] => fail "orw: symbolic address" | _ =>
      apply (chk_rw_cells m p CT_COMMON HF QLit A cs);
      [ vm_compute; reflexivity | cbn; repeat split; reflexivity | zdec | zdec ] end end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma zrun_of : ltac2:(CDefT.buildp (gd_tbl_AH0Mem2 ()) "Pa,(2.&40.)Pn,(2.&40.)PB,$4.Pzoff,$4.Pzlen,$5.P,(1<.$1=.Vmem,(1>.R5.R4.))P,(14.$4.(1?.&40.R6.)(:.R4.R3.))P,(14.$4.(1?.&40.R6.)(;.R3.))(6.$?.Vmem,(:.R6.R5.)(10.(2.&8.)(11.&8.=)R4.))")
(* [comment removed for export] *).
  Proof. intros a n B zoff zlen X Ha Hn. rewrite <- Ha. apply (czero_bytes_at mem a n zlen X). lia. Qed.
  #[using="Type"] Lemma wrun_of : ltac2:(CDefT.buildp (gd_tbl_AH0Mem2 ()) "Pa,(2.&40.)Pn,(2.&40.)PB,$4.Pwlen,$4.P,(1<.$1=.Vmem,(20.R4.R3.))P,(14.$4.(1?.&40.R5.)R3.)P,(14.$4.(1?.&40.R5.)R3.)(21.$?.Vmem,R5.R4.)")
(* [comment removed for export] *).
  Proof. intros a n B wlen X <- <-. exact (cwr_wr_at mem a n X). Qed.

  (* [comment removed for export] *)
  Let T := PG p v_thr.
  #[using="HCN"] Lemma Gthr : 4096 <= T <= 0x7fffff7ff000. Proof. exact (proj1 (PG_range p HCN v_thr ltac:(pv))). Qed.
  #[using="HCN HCOM HF"] Lemma T_zero : bytes_at asegs mem (T + 80) (repeat (Z_to_bv 8 0) 3088).
  Proof.
    pose proof Gthr. me_zrun HF ((#0x1000 * v_thr) .+ 80)%tm XZ. eapply (zrun_of _ _ T 80 3088%nat XZ); [| rewrite u_zbv; apply Z.mod_small; lia].
    etransitivity; [exact (u_addi_Page p HCN v_thr 80 ltac:(pv) ltac:(lia)) | reflexivity].
  Qed.
  #[using="HCN HCOM HF"] Lemma T_wr : wr_at asegs mem T 4096.
  Proof.
    pose proof Gthr. me_wr HF ((#0x1000 * v_thr) .+ 0)%tm XW. eapply (wrun_of _ _ T 4096 XW); [| rewrite u_zbv; apply Z.mod_small; lia].
    etransitivity; [exact (u_addi_Page p HCN v_thr 0 ltac:(pv) ltac:(lia)) | unfold T; lia].
  Qed.
  Definition tz_rw := zr_rw mem T 80 3088%nat 4096 T_zero T_wr.
  Definition tz_wr := zr_wr mem T 4096 T_wr.
  Definition tz_u64arr := zr_u64arr mem T 80 3088%nat 4096 T_zero T_wr.
  Definition tz_u32arr := zr_u32arr mem T 80 3088%nat 4096 T_zero T_wr.

  (* [comment removed for export] *)
  Let RI := SB p + 2 ^ 37.
  #[using="HCN T"] Lemma Gri : 0x10000 <= RI /\ RI + 4096 <= 2 ^ 47.
  Proof. pose proof (r_prim p HCN). pose proof (r_pslack p HCN). unfold RI, SB, PG. lia. Qed.
    (* [comment removed for export] *)
  #[using="HCN T"] Lemma u_ri_b : ltac2:(CDefT.buildp (gd_tbl_AH0Mem2 ()) "(14.$4.(1?.&40.(22.(23.Vp,(24.$25.(26.$27.(28.+1000.)(29.$2:.))(26.$27.(28.-1000.)(29.$2;.))))+2000010000.))VRI,)")
(* [comment removed for export] *).
  Proof.
    pose proof Gri. pose proof (r_prim p HCN). pose proof (r_pslack p HCN). unfold ABoot.PropExec.v_addi. rewrite u_zbv.
    rewrite zev_exact by (cbn [zev]; lia). cbn [zev]. unfold RI, SB, PG. rewrite Z.mod_small; lia.
  Qed.
  #[using="HCN HCOM HF T"] Lemma RI_zero : bytes_at asegs mem (RI + 0) (repeat (Z_to_bv 8 0) 4096).
  Proof.
    pose proof Gri. me_zrun HF (((#0x1000 * v_prim) + (#(-0x1000) * v_pslack)) .+ 0x2000010000)%tm XZ.
    eapply (zrun_of _ _ RI 0 4096%nat XZ); [etransitivity; [exact u_ri_b | lia] | rewrite u_zbv; apply Z.mod_small; lia].
  Qed.
  #[using="HCN HCOM HF T"] Lemma RI_wr : wr_at asegs mem RI 4096.
  Proof.
    pose proof Gri. me_wr HF (((#0x1000 * v_prim) + (#(-0x1000) * v_pslack)) .+ 0x2000010000)%tm XW.
    eapply (wrun_of _ _ RI 4096 XW); [exact u_ri_b | rewrite u_zbv; apply Z.mod_small; lia].
  Qed.
  Definition rz_rw := zr_rw mem RI 0 4096%nat 4096 RI_zero RI_wr.
  Definition rz_wr := zr_wr mem RI 4096 RI_wr.
  Definition rz_u32arr := zr_u32arr mem RI 0 4096%nat 4096 RI_zero RI_wr.

  (* [comment removed for export] *)
  Let FS := PG p v_fstk.
  #[using="HCN"] Lemma Gfs : 4096 <= FS <= 0x7fffff7ff000. Proof. exact (proj1 (PG_range p HCN v_fstk ltac:(pv))). Qed.
  #[using="HCN HCOM HF T RI"] Lemma FS_zero1 : bytes_at asegs mem (FS + 0) (repeat (Z_to_bv 8 0) 88).
  Proof.
    pose proof Gfs. me_zrun HF ((#0x1000 * v_fstk) .+ 0)%tm XZ. eapply (zrun_of _ _ FS 0 88%nat XZ); [| rewrite u_zbv; apply Z.mod_small; lia].
    exact (u_addi_Page p HCN v_fstk 0 ltac:(pv) ltac:(lia)).
  Qed.
  #[using="HCN HCOM HF T RI"] Lemma FS_zero2 : bytes_at asegs mem (FS + 96) (repeat (Z_to_bv 8 0) (Z.to_nat 0xb08fa0)).
  Proof.
    pose proof Gfs. me_zrun HF ((#0x1000 * v_fstk) .+ 96)%tm XZ. eapply (zrun_of _ _ FS 96 _ XZ); [| rewrite u_zbv, Z2Nat.id by (clear; lia); apply Z.mod_small; lia (* [comment removed for export] *)].
    exact (u_addi_Page p HCN v_fstk 96 ltac:(pv) ltac:(lia)).
  Qed.
  #[using="HCN HCOM HF T RI"] Lemma FS_wr : wr_at asegs mem FS kFakeBytes.
  Proof.
    pose proof Gfs. me_wr HF ((#0x1000 * v_fstk) .+ 0)%tm XW. eapply (wrun_of _ _ FS kFakeBytes XW); [| unfold kFakeBytes; rewrite u_zbv; apply Z.mod_small; lia].
    etransitivity; [exact (u_addi_Page p HCN v_fstk 0 ltac:(pv) ltac:(lia)) | unfold FS; lia].
  Qed.

  (* [comment removed for export] *)
  Let NB := PG p v_dnodes.
  #[using="HCN"] Lemma Gnb : 4096 <= NB <= 0x7fffff7ff000. Proof. exact (proj1 (PG_range p HCN v_dnodes ltac:(pv))). Qed.
  #[using="HCN HCOM HF T RI FS"] Lemma NB_zero1 : bytes_at asegs mem (NB + 0) (repeat (Z_to_bv 8 0) 16).
  Proof.
    pose proof Gnb. me_zrun HF ((#0x1000 * v_dnodes) .+ 0)%tm XZ. eapply (zrun_of _ _ NB 0 16%nat XZ); [| rewrite u_zbv; apply Z.mod_small; lia].
    exact (u_addi_Page p HCN v_dnodes 0 ltac:(pv) ltac:(lia)).
  Qed.
  #[using="HCN HCOM HF T RI FS"] Lemma NB_zero2 : bytes_at asegs mem (NB + 32) (repeat (Z_to_bv 8 0) (Z.to_nat 0xfffe0)).
  Proof.
    pose proof Gnb. me_zrun HF ((#0x1000 * v_dnodes) .+ 32)%tm XZ. eapply (zrun_of _ _ NB 32 _ XZ); [| rewrite u_zbv, Z2Nat.id by (clear; lia); apply Z.mod_small; lia (* [comment removed for export] *)].
    exact (u_addi_Page p HCN v_dnodes 32 ltac:(pv) ltac:(lia)).
  Qed.
  #[using="HCN HCOM HF T RI FS"] Lemma NB_wr : wr_at asegs mem NB (2 ^ 20).
  Proof.
    pose proof Gnb. me_wr HF ((#0x1000 * v_dnodes) .+ 0)%tm XW. eapply (wrun_of _ _ NB (2 ^ 20) XW); [| rewrite u_zbv; apply Z.mod_small; lia].
    etransitivity; [exact (u_addi_Page p HCN v_dnodes 0 ltac:(pv) ltac:(lia)) | unfold NB; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCOM HF"] Lemma ex_u64arr : ltac2:(CDefT.buildp (gd_tbl_AH0Mem2 ()) "Pq,$2<.Pz,$4.Pk,$5.P,(14.$2=.(2>.R3.$2?.R2.(30.#8.R1.))$31.)P,(14.$2=.(32.R4.$2?.R3.(18.+8.(;.R2.)))$31.)P,(>.=(33.Vp,R5.R4.))P,(>.(:.(33.Vp,R6.R5.)(18.+8.(;.R4.)))(34.+2.+40.))(35.(0.(2.&40.))Lws,(0.(2.&40.))(36.(19.$?.Vmem,(33.Vp,R8.R7.)R1.)(14.$5.(9.(2.&40.)R1.)R6.)))")
(* [comment removed for export] *).
  Proof.
    intros q z k Hd Hw Hlo Hhi. unfold fchkd in Hd. destruct (fbytes q CT_COMMON z (8 * k)) as [bs|] eqn:Hf; [|discriminate Hd].
    pose proof (fbytes_length CT_COMMON q _ z bs Hf) as LEN.
    exists (unchunk8 k bs). split; [| apply unchunk8_length].
    apply (facts_u64arr mem p CT_COMMON HF q z (unchunk8 k bs) bs); rewrite ?unchunk8_length; [exact Hf | apply u64s_unchunk8; exact LEN | exact Hw | exact Hlo | exact Hhi].
  Qed.
  #[using="HCOM HF T RI FS NB"] Lemma ex_cells : ltac2:(CDefT.buildp (gd_tbl_AH0Mem2 ()) "Pq,$2<.Pz,$4.Pn,$5.P,(14.$2=.(2>.R3.$2?.R2.R1.)$31.)P,(14.$2=.(32.R4.$2?.R3.(;.R2.))$31.)P,(>.=(33.Vp,R5.R4.))P,(>.(:.(33.Vp,R6.R5.)(;.R4.))(34.+2.+40.))(35.(0.$12.)Lcs,(0.$12.)(36.(17.$?.Vmem,(33.Vp,R8.R7.)R1.)(14.$4.(;.(16.R1.))(;.R6.))))")
(* [comment removed for export] *).
  Proof.
    intros q z n Hd Hw Hlo Hhi. unfold fchkd in Hd. destruct (fbytes q CT_COMMON z n) as [bs|] eqn:Hf; [|discriminate Hd].
    pose proof (fbytes_length CT_COMMON q _ z bs Hf) as LEN.
    exists [CB n bs]. split; [| cbn; lia].
    apply (facts_rw_cells mem p CT_COMMON HF q z [CB n bs] bs); cbn [cells_size cells_bytes csize cbytes]; rewrite ?Nat.add_0_r, ?app_nil_r;
      [exact Hf | reflexivity | cbn; auto | exact Hw | exact Hlo | exact Hhi].
  Qed.
  #[using="p HCOM HF T RI FS NB"] Lemma ex_C8w2 : ltac2:(CDefT.buildp (gd_tbl_AH0Mem2 ()) "Pz,$4.P,(14.$2=.(2>.$37.$2?.R1.#8.)$31.)P,(14.$2=.(32.$37.$2?.R2.+8.)$31.)P,(14.$2=.(2>.$37.$2?.(:.R3.+8.)#8.)$31.)P,(14.$2=.(32.$37.$2?.(:.R4.+8.)+8.)$31.)P,(>.=R5.)P,(>.(:.R6.+10.)(34.+2.+40.))(35.(2.&40.)Lg0,(2.&40.)(35.(2.&40.)Lg1,(2.&40.)(17.$?.Vmem,R9.(38.$12.(39.R2.)(38.$12.(39.R1.)(3:.$12.))))))")
(* [comment removed for export] *).
  Proof.
    intros z D1 W1 D2 W2 Hlo Hhi.
    destruct (chk_ex_C8w mem p CT_COMMON HF QLit z D1 W1 ltac:(cbn [qaddr]; lia) ltac:(cbn [qaddr]; lia)) as [g0 H0].
    destruct (chk_ex_C8w mem p CT_COMMON HF QLit (z + 8) D2 W2 ltac:(cbn [qaddr]; lia) ltac:(cbn [qaddr]; lia)) as [g1 H1].
    dexists g0, g1. change [C8 g0; C8 g1] with ([C8 g0] ++ [C8 g1]). apply rw_cells_app2; cbn [qaddr cells_size csize Z.of_nat Pos.of_succ_nat Nat.add] in *; [exact H0 | exact H1].
  Qed.
  #[using="p HCOM HF T RI FS NB"] Lemma ex_C8s4 : ltac2:(CDefT.buildp (gd_tbl_AH0Mem2 ()) "Pz,$4.P,Pi,$5.P,(3;.R1.#4.)(36.(14.$2=.(2>.$37.$2?.(:.R3.(18.+8.(;.R2.)))#8.)$31.)(14.$2=.(32.$37.$2?.(:.R3.(18.+8.(;.R2.)))+8.)$31.))P,(>.=R2.)P,(>.(:.R3.+20.)(34.+2.+40.))(35.(0.(2.&40.))Lst,(0.(2.&40.))(36.(17.$?.Vmem,R5.(3<.(2.&40.)$12.$39.R1.))(14.$5.(9.(2.&40.)R1.)#4.)))")
(* [comment removed for export] *).
  Proof.
    intros z H Hlo Hhi.
    destruct (H 0%nat ltac:(lia)) as [D0 W0]. destruct (H 1%nat ltac:(lia)) as [D1 W1]. destruct (H 2%nat ltac:(lia)) as [D2 W2]. destruct (H 3%nat ltac:(lia)) as [D3 W3].
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *. rewrite ?Z.mul_1_r, ?Z.add_0_r in *.
    destruct (chk_ex_C8w mem p CT_COMMON HF QLit z D0 W0 ltac:(cbn [qaddr]; lia) ltac:(cbn [qaddr]; lia)) as [g0 H0].
    destruct (chk_ex_C8w mem p CT_COMMON HF QLit (z + 8) D1 W1 ltac:(cbn [qaddr]; lia) ltac:(cbn [qaddr]; lia)) as [g1 H1].
    destruct (chk_ex_C8w mem p CT_COMMON HF QLit (z + 8 * 2) D2 W2 ltac:(cbn [qaddr]; lia) ltac:(cbn [qaddr]; lia)) as [g2 H2].
    destruct (chk_ex_C8w mem p CT_COMMON HF QLit (z + 8 * 3) D3 W3 ltac:(cbn [qaddr]; lia) ltac:(cbn [qaddr]; lia)) as [g3 H3].
    exists [g0; g1; g2; g3]. split; [| reflexivity]. cbn [map qaddr] in *.
    change [C8 g0; C8 g1; C8 g2; C8 g3] with ([C8 g0] ++ ([C8 g1] ++ ([C8 g2] ++ [C8 g3]))).
    repeat (apply rw_cells_app2; cbn [cells_size csize Z.of_nat Pos.of_succ_nat Nat.add]; rewrite <- ?Z.add_assoc; cbn [Z.add Pos.add Pos.succ]);
      first [exact H0 | exact H1 | exact H2 | exact H3
            | match goal with |- rw_cells _ _ ?a _ => first [replace a with (z + 8) by lia; exact H1 | replace a with (z + 8 * 2) by lia; exact H2 | replace a with (z + 8 * 3) by lia; exact H3] end].
  Qed.

  (* [comment removed for export] *)
  Local Ltac znum := cbn [cells_size csize Nat.add Nat.mul length repeat Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; try lia.
  Local Ltac zrw L := apply L; [cbn; tauto | reflexivity | | | |]; znum.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCN HCOM HF T RI FS NB"] Theorem h0_hm_thread : hm_thread h0 mem.
  Proof.
    pose proof Gthr as G.
    unfold hm_thread. cbn [h_L l_T h_cinit h_cache h0 h0_of L0_of bp bp_of bp_T]. fold T.
    split; [| split; [| split]].
    - (* [comment removed for export] *)
      me_word HF ((#0x1000 * v_thr) .+ 3168)%tm 1%nat X.
      split; [| change (Z.of_nat (cells_size [C1 (b8 0)])) with 1; apply tz_wr; lia].
      pose proof (u_addi_Page p HCN v_thr 3168 ltac:(pv) ltac:(lia)) as UA.
        pose proof (cword_ro_cells mem _ 1%nat _ [C1 (b8 0)] X ltac:(reflexivity) ltac:(cbn; tauto) ltac:(apply (le_by_eq _ _ _ UA); unfold T in *; lia)) as R.
        replace (bv_unsigned (ABoot.PropExec.v_addi _ _)) with (PG p v_thr + 3168) in R by (symmetry; exact UA). exact R.
    - (* [comment removed for export] *)
      exists (fun _ => repeat (Z_to_bv 64 0) 16). intros c Hc. unfold hm_pclass. cbn [pc_count pc_max pc_csize pc_chunks pcl0 length map firstn].
      split; [| split; [| split; [reflexivity | split; [reflexivity | repeat split; reflexivity]]]].
      + replace (T + 208 + 80 * c) with (T + (208 + 80 * c)) by lia. zrw tz_rw.
      + replace (T + 208 + 80 * c + 16) with (T + (224 + 80 * c)) by lia. apply tz_u32arr; znum.
    - (* [comment removed for export] *) dexists (Z_to_bv 64 0), (Z_to_bv 64 0). zrw tz_rw.
    - (* [comment removed for export] *) dexists (repeat (Z_to_bv 64 0) 16), (repeat (Z_to_bv 64 0) 32). rewrite !repeat_length.
      split; [apply tz_u64arr; znum|]. split; [reflexivity|]. split; [apply tz_u64arr; znum | reflexivity].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Theorem h0_hm_chunks : hm_chunks h0 mem.
  Proof. unfold hm_chunks. cbn. constructor. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCN HCOM HF T RI FS NB"] Theorem h0_hm_quar : hm_quar h0 mem.
  Proof.
    pose proof Gthr as G.
    unfold hm_quar. cbn [h_L l_T h_tq h_gq q_batches q_bytes h0 h0_of L0_of bp bp_of bp_T qcache0 map app]. fold T.
    unfold hm_qhead. cbn [length hd_addr hd_addrT last_addr bsum Z.of_nat].
    split; [zrw tz_rw|].
    split; [exact I|].
    split; [orw|].
    split; [exact I|].
    split; [split; [constructor | split; [constructor | intros x y [] ]]|].
    split; [orw|]. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCN HCOM HF T RI FS NB"] Theorem h0_hm_sec : hm_sec h0 mem.
  Proof.
    pose proof (proj1 (PG_range p HCN v_secv ltac:(pv))) as Gs.
    unfold hm_sec. cbn [h_L l_pa h_sec s_chunks s_nres h_pa_committed h0 h0_of L0_of bp bp_of bp_pa sec0 length Z.of_nat map].
    split; [orw|].
    split; [destruct (chk_ex_C1w mem p CT_COMMON HF QLit (A_INSTANCE + 128) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(zdec) ltac:(zdec)) as [s Hs]; exists s; exact Hs|].
    split; [apply ex_C8s4; [intros i Hi; destruct i as [|[|[|[|i]]]]; try lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; split; vm_compute; reflexivity | zdec | zdec]|].
    split; [destruct (ex_u64arr QLit (A_INSTANCE + 168) 64 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(zdec) ltac:(zdec)) as [ws Hws]; exists ws; exact Hws|].
    split; [orw|].
    split; [apply ex_C8w2; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | zdec | zdec]|].
    split; [split; [split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]] | split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]]|].
    split; [exists []; split; [split; [split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]] | split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]] | reflexivity]|].
    intros i sh Hn. destruct i; discriminate Hn.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCN HCOM HF T RI FS NB"] Theorem h0_hm_regions : hm_regions h0 mem.
  Proof.
    pose proof Gri as GR. pose proof (r_prim p HCN) as PR. pose proof (r_pslack p HCN) as PS.
    intros c Hc. unfold hm_region. cbn [h_L h_reg h0 h0_of region0 r_nfreed r_mapped_fa r_alloc_user r_mapped_user r_fa map length Z.of_nat].
    unfold ri_addr. change (ri_base (L0_of bp)) with RI. change (h_reg h0 c) with region0.
    unfold r_nfreed, region0. cbn [r_fa r_mapped_fa r_alloc_user r_mapped_user length Z.of_nat map].
    assert (FAB : 0 <= fa_beg (L0_of bp) c /\ fa_beg (L0_of bp) c <= 2 ^ 63).
    { unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset. cbn [l_sb L0_of bp bp_of bp_sb]. unfold SB, PG. lia. }
    assert (RBB : 0 <= region_beg (L0_of bp) c /\ region_beg (L0_of bp) c <= 2 ^ 63).
    { unfold region_beg, kRegionSize. cbn [l_sb L0_of bp bp_of bp_sb]. unfold SB, PG. lia. }
    Ltac rz cc o := replace (RI + 128 * cc + o) with (RI + (128 * cc + o)) by lia; zrw rz_rw.
    split; [replace (RI + 128 * c) with (RI + (128 * c + 0)) by lia; zrw rz_rw|].
    split; [rz c 16|]. split; [rz c 24|]. split; [rz c 32|]. split; [rz c 40|]. split; [rz c 48|]. split; [rz c 56|].
    split; [change (b8 (if a_exh (h_acct h0) c then 1 else 0)) with (Z_to_bv 8 0); rz c 68|]. split; [exists (Z_to_bv 64 0); rz c 72|]. split; [dexists (Z_to_bv 64 0), (Z_to_bv 64 0); rz c 80|].
    split; [split; [split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]] | cbn [length Z.of_nat]; split; [lia | split; [lia | intros i Hi; cbn in Hi; lia]]]|].
    split; [exists []; split; [split; [split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]] | cbn [length Z.of_nat]; split; [lia | split; [lia | intros i Hi; cbn in Hi; lia]]] | reflexivity]|].
    split; [split; [lia | split; [lia | intros i Hi; cbn in Hi; lia]]|].
    split.
    { rewrite ?Z.sub_0_r, ?Z.add_0_r. change (0 / 8) with 0. cbn [Z.to_nat fill repeat].
      assert (SH : 0 <= shad (region_beg (L0_of bp) c) <= 2 ^ 63) by (unfold shad; split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | pose proof (Z.div_le_upper_bound (region_beg (L0_of bp) c) 8 (2 ^ 62) ltac:(lia) ltac:(lia)); lia]).
      unfold fill. change (Z.to_nat 0) with 0%nat. cbn [repeat].
      split; [split; [cbn; tauto | split; [exact (proj1 SH) | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]] | cbn -[shad Z.le Z.lt Z.add]; split; [exact (proj1 SH) | split; [lia | intros i Hi; lia]]]. }
    intros k Hk. rewrite Zdiv_0_l in Hk. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="HCN HCOM HF T RI FS NB"] Theorem h0_hm_fake : hm_fake h0 [] mem.
  Proof.
    pose proof Gfs as GF.
    unfold hm_fake, fake_rep. cbn [h_L l_fs h0 h0_of L0_of bp bp_of bp_fs]. fold FS.
    split; [| split; [| split; [| split; [intros fb [] | constructor]]]].
    - (* [comment removed for export] *)
      change [C8 (Z_to_bv 64 20); C1 (Z_to_bv 8 0)] with ([C8 (Z_to_bv 64 20)] ++ [C1 (Z_to_bv 8 0)]). apply ro_cells_app.
      + me_word HF ((#0x1000 * v_fstk) .+ 88)%tm 8%nat X.
        pose proof (u_addi_Page p HCN v_fstk 88 ltac:(pv) ltac:(lia)) as UA.
        pose proof (cword_ro_cells mem _ 8%nat _ [C8 (Z_to_bv 64 20)] X ltac:(reflexivity) ltac:(cbn; tauto) ltac:(apply (le_by_eq _ _ _ UA); unfold FS in *; lia)) as R.
        replace (bv_unsigned (ABoot.PropExec.v_addi _ _)) with (PG p v_fstk + 88) in R by (symmetry; exact UA). exact R.
      + match goal with |- ro_cells _ _ ?a _ => replace a with (FS + 96) by (cbn [cells_size csize Nat.add]; lia) end.
        split; [cbn; tauto|]. cbn [cells_bytes cbytes app].
        pose proof (zr_bytes mem FS 96 (Z.to_nat 0xb08fa0) FS_zero2 96 1%nat) as B. cbn [repeat] in B. apply B; znum.
    - (* [comment removed for export] *) intros k Hk. exists (Z_to_bv 64 0). unfold fsk_hint. destruct (Z.eqb_spec k 0).
      + replace FS with (FS + 0) by lia. zrw (zr_rw mem FS 0 88%nat kFakeBytes FS_zero1 FS_wr); unfold kFakeBytes; lia.
      + zrw (zr_rw mem FS 0 88%nat kFakeBytes FS_zero1 FS_wr); unfold kFakeBytes; lia.
    - (* [comment removed for export] *) intros k Hk.
      assert (K : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
      exists (repeat (Z_to_bv 8 0) (Z.to_nat (fsk_n k))). split; [| split].
      + apply (zr_u8arr mem FS 96 (Z.to_nat 0xb08fa0) kFakeBytes FS_zero2 FS_wr); unfold fsk_foff, fsk_n, kFakeBytes;
          destruct K as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; cbn -[Z.add Z.le Z.mul Z.of_nat FS]; znum.
      + rewrite repeat_length. unfold fsk_n. destruct K as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; cbn; lia.
      + intros i Hi. exists (Z_to_bv 8 0). split; [apply nth_error_repeat'; lia|]. split; [intros _ []|].
        intros NZ. exfalso. apply NZ. reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCOM HF T RI FS NB"] Theorem h0_hm_ia : hm_ia h0 mem.
  Proof.
    unfold hm_ia. cbn [h_ia h0 h0_of].
    split; [orw|]. split; [orw|].
    split. { unfold zeros. apply (chk_rw_cells mem p CT_COMMON HF QLit (A_IA + 8) [CB (Z.to_nat 0x40000) (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000))]);
             [ apply fchkw_zero_fast; vm_compute; reflexivity (* [comment removed for export] *) | cbn [cells_wf cell_wf]; rewrite repeat_length; split; [reflexivity | exact I] | zdec | zdec ]. }
    split; [destruct (ex_cells QLit (A_IA + 0x40040) (Z.to_nat 0xd80) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(zdec) ltac:(zdec)) as [cs Hcs]; exists cs; exact Hcs|].
    split; [ddestruct (ex_C8w2 (A_IA + 0x40dc0) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(zdec) ltac:(zdec)) as (p0 & p1 & Hp); dexists p0, p1; split; [exact Hp | intros X; discriminate X]|].
    split; [destruct (ex_cells QLit (A_IA + 0x40dd0) (Z.to_nat (0x40248 - 16)) ltac:(apply fchkd_zero_fast; vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(zdec) ltac:(zdec)) as [cs Hcs]; exists cs; exact Hcs|].
    destruct (ex_cells QLit (A_IA + 0x81008) 40%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(zdec) ltac:(zdec)) as [cs Hcs]; exists cs; exact Hcs.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCOM HF"] Theorem h0_hm_emb : hm_emb h0 mem.
  Proof.
    unfold hm_emb, emb_cells. change (a_emb (h_acct h0)) with 0. change (a_esz (h_acct h0)) with 0. unfold emb_P, emb_cap. cbn [Z.eqb].
    split; [orw|]. split; [orw|]. split; [orw|]. intros X. exfalso. apply X. reflexivity.
  Qed.

End Mem2.
