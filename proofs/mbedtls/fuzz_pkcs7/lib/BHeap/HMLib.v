(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Cells CellsX Arr Asn1Aux Frame Step.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_HMLib () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Numbers.BinNums.Z"; "Corelib.Lists.ListDef.Forall"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_base"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_size"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment"; "Corelib.Init.Datatypes.None"; "stdpp.bitvector.definitions.bv"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Peano.lt"; "Stdlib.Lists.List.nth_error"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.nil"; "ARUN_1.wsum"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_wf"; "ARUN_1.decode_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_bytes"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.csize"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "ARUN_1.Keep.kept"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Lemma asegs_hi : Forall (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 0x65f000) asegs.
Proof.
  assert (E : List.map (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s)) asegs = [286720; 987136; 1011712; 6680576]) by (vm_compute; reflexivity).
  assert (G : forall l, List.map (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s)) l = [286720; 987136; 1011712; 6680576] ->
              Forall (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 0x65f000) l).
  { intros l H. destruct l as [|s1 [|s2 [|s3 [|s4 [|s5 l]]]]]; cbn in H; try discriminate.
    injection H as E1 E2 E3 E4. repeat constructor; lia. }
  exact (G _ E).
Qed.

#[using="Type"] Lemma find_segment_none_ge : ltac2:(CDefT.buildp (gd_tbl_HMLib ()) "Pl,(0.$1.)Pz,$2.Pn,$2.P,(3.$1.Ls,$1.(4.(5.(6.(7.R1.))(6.(8.R1.)))+65?000.)R3.)P,(4.+65?000.R3.)P,(9.=R3.)(:.(;.$1.)(<.R6.R5.R4.)(=.$1.))")
(* [comment removed for export] *).
Proof.
  induction l as [|s l IH]; intros z n HF Hz Hn; cbn; [reflexivity|].
  apply Forall_cons_iff in HF. destruct HF as [HS HL].
  destruct ((Z.of_N (seg_base s) <=? z) && (z + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E2. exfalso. lia.
  - apply IH; assumption.
Qed.

#[using="Type"] Lemma wview_high : forall m x, 0x65f000 <= bv_unsigned x -> wview asegs m x = m x.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [reflexivity|].
  rewrite (find_segment_none_ge asegs (bv_unsigned x) 1 asegs_hi Hx ltac:(lia)). reflexivity.
Qed.

#[using="Type"] Lemma seg_rom_high : forall x, 0x65f000 <= bv_unsigned x -> seg_rom asegs x = None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  rewrite (find_segment_none_ge asegs (bv_unsigned x) 1 asegs_hi Hx ltac:(lia)). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wr_high_byte : ltac2:(CDefT.buildp (gd_tbl_HMLib ()) "Pm,P,(>.&40.)(;.(>.&8.))Pa,$2.P,(4.+65?000.R1.)P,(9.R2.(?.+2.+40.))P,(10.(:.(;.(>.&8.))(11.$12.R4.(13.R3.))(=.(>.&8.))))(14.(>.&8.)Lb,(>.&8.)(:.(;.(>.&8.))A1.R6.(13.R5.)(15.(>.&8.)R1.)))")
(* [comment removed for export] *).
Proof.
  intros m a H0 H1 W. rewrite wview_high in W by (unfold wa; rewrite unsigned_lit by lia; lia).
  destruct (m (wa a)) as [b|]; [exists b; reflexivity| congruence].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma asegs_lohi : ltac2:(CDefT.buildp (gd_tbl_HMLib ()) "(3.$1.Ls,$1.(16.(4.+10000.(6.(7.R1.)))(4.(5.(6.(7.R1.))(6.(8.R1.)))+65?000.))$12.)")
(* [comment removed for export] *).
Proof.
  assert (E : List.map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_base s) + Z.of_N (seg_size s))) asegs = [(65536, 286720); (286720, 987136); (987136, 1011712); (1011712, 6680576)]) by (vm_compute; reflexivity).
  assert (G : forall l, List.map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_base s) + Z.of_N (seg_size s))) l = [(65536, 286720); (286720, 987136); (987136, 1011712); (1011712, 6680576)] ->
              Forall (fun s => 0x10000 <= Z.of_N (seg_base s) /\ Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 0x65f000) l).
  { intros l H. destruct l as [|s1 [|s2 [|s3 [|s4 [|s5 l]]]]]; cbn in H; try discriminate.
    injection H as E1 E1' E2 E2' E3 E3' E4 E4'. repeat constructor; lia. }
  exact (G _ E).
Qed.

#[using="Type"] Lemma find_segment_none_off : ltac2:(CDefT.buildp (gd_tbl_HMLib ()) "Pl,(0.$1.)Pz,$2.Pn,$2.P,(3.$1.Ls,$1.(16.(4.+10000.(6.(7.R1.)))(4.(5.(6.(7.R1.))(6.(8.R1.)))+65?000.))R3.)P,(17.(4.(5.R3.R2.)+10000.)(4.+65?000.R3.))P,(9.=R3.)(:.(;.$1.)(<.R6.R5.R4.)(=.$1.))")
(* [comment removed for export] *).
Proof.
  induction l as [|s l IH]; intros z n HF Hz Hn; cbn; [reflexivity|].
  apply Forall_cons_iff in HF. destruct HF as [[HS1 HS2] HL].
  destruct ((Z.of_N (seg_base s) <=? z) && (z + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. exfalso. pose proof (N2Z.is_nonneg (seg_size s)). lia.
  - apply IH; assumption.
Qed.

#[using="Type"] Lemma wview_off : forall m x, (bv_unsigned x + 1 <= 0x10000 \/ 0x65f000 <= bv_unsigned x) -> wview asegs m x = m x.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [reflexivity|].
  rewrite (find_segment_none_off asegs (bv_unsigned x) 1 asegs_lohi Hx ltac:(lia)). reflexivity.
Qed.


#[using="Type"] Lemma wr_off_byte : ltac2:(CDefT.buildp (gd_tbl_HMLib ()) "Pm,P,(>.&40.)(;.(>.&8.))Pa,$2.P,(4.=R1.)P,(17.(4.(5.R2.+1.)+10000.)(4.+65?000.R2.))P,(9.R3.(?.+2.+40.))P,(10.(:.(;.(>.&8.))(11.$12.R5.(13.R4.))(=.(>.&8.))))(14.(>.&8.)Lb,(>.&8.)(:.(;.(>.&8.))A1.R7.(13.R6.)(15.(>.&8.)R1.)))")
(* [comment removed for export] *).
Proof.
  intros m a Ha H0 H1 W. rewrite wview_off in W by (unfold wa; rewrite unsigned_lit by lia; lia).
  destruct (m (wa a)) as [b|]; [exists b; reflexivity| congruence].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithM.
  Variable m : mem.

  (* [comment removed for export] *)
  #[using="Type"] Lemma wr_at_off_bytes_nat : ltac2:(CDefT.buildp (gd_tbl_HMLib ()) "PA,$2.Pk,$18.P,(19.$12.Vm,R2.(1:.R1.))P,(17.(4.(5.R3.(1:.R2.))+10000.)(4.+65?000.R3.))(14.(0.(>.&8.))Lbs,(0.(>.&8.))(16.(:.$18.(1;.(>.&8.)R1.)R4.)Pi,$18.P,(1<.R1.R5.)(:.(;.(>.&8.))A1.Vm,(13.(5.R7.(1:.R2.)))(1=.(>.&8.)R3.R2.))))")
(* [comment removed for export] *).
  Proof.
    intros A k. induction k as [|k IH]; intros W HA.
    - exists []. split; [reflexivity|]. intros i Hi. lia.
    - dpose W as (W0 & W1 & W2).
      ddestruct (IH ltac:(split; [lia|]; split; [lia|]; intros i Hi; apply W2; lia) ltac:(lia)) as (bs & L & B).
      destruct (wr_off_byte m (A + Z.of_nat k) ltac:(lia) ltac:(lia) ltac:(lia) (W2 (Z.of_nat k) ltac:(lia))) as (b & Hb).
      exists (bs ++ [b]). split; [rewrite length_app; cbn; lia|].
      intros i Hi. destruct (Nat.lt_ge_cases i k) as [Hik|Hik].
      + rewrite nth_error_app1 by lia. apply B. exact Hik.
      + assert (i = k) as -> by lia. rewrite nth_error_app2 by lia. rewrite L, Nat.sub_diag. cbn. exact Hb.
  Qed.

  #[using="Type"] Lemma wr_at_off_CB : ltac2:(CDefT.buildp (gd_tbl_HMLib ()) "PA,$2.Pn,$2.P,(19.$12.Vm,R2.R1.)P,(17.(4.(5.R3.R2.)+10000.)(4.+65?000.R3.))P,(4.=R3.)(14.(0.(>.&8.))Lbs,(0.(>.&8.))(1>.$12.Vm,R6.(1?.$20.(21.(22.R5.)R1.)(23.$20.))))")
(* [comment removed for export] *).
  Proof.
    intros A n W HA Hn. ddestruct (wr_at_off_bytes_nat A (Z.to_nat n) ltac:(rewrite Z2Nat.id by lia; exact W) ltac:(rewrite Z2Nat.id by lia; exact HA)) as (bs & L & B). dpose W as (W0 & W1 & W2).
    exists bs. split.
    - split; [cbn; split; [exact L| exact I]|]. cbn [cells_bytes cbytes app]. rewrite app_nil_r.
      split; [lia|]. rewrite L. split; [lia|]. intros i Hi. unfold mrd. rewrite (B i Hi).
      destruct (nth_error bs i) eqn:E; [reflexivity|]. exfalso. apply nth_error_None in E. lia.
    - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact W.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma wr_at_high_bytes_nat : ltac2:(CDefT.buildp (gd_tbl_HMLib ()) "PA,$2.Pk,$18.P,(19.$12.Vm,R2.(1:.R1.))P,(4.+65?000.R3.)(14.(0.(>.&8.))Lbs,(0.(>.&8.))(16.(:.$18.(1;.(>.&8.)R1.)R4.)Pi,$18.P,(1<.R1.R5.)(:.(;.(>.&8.))A1.Vm,(13.(5.R7.(1:.R2.)))(1=.(>.&8.)R3.R2.))))")
(* [comment removed for export] *).
  Proof.
    intros A k. induction k as [|k IH]; intros W HA.
    - exists []. split; [reflexivity|]. intros i Hi. lia.
    - dpose W as (W0 & W1 & W2).
      ddestruct (IH ltac:(split; [lia|]; split; [lia|]; intros i Hi; apply W2; lia) HA) as (bs & L & B).
      destruct (wr_high_byte m (A + Z.of_nat k) ltac:(lia) ltac:(lia) (W2 (Z.of_nat k) ltac:(lia))) as (b & Hb).
      exists (bs ++ [b]). split; [rewrite length_app; cbn; lia|].
      intros i Hi. destruct (Nat.lt_ge_cases i k) as [Hik|Hik].
      + rewrite nth_error_app1 by lia. apply B. exact Hik.
      + assert (i = k) as -> by lia. rewrite nth_error_app2 by lia. rewrite L, Nat.sub_diag. cbn. exact Hb.
  Qed.

  #[using="Type"] Lemma wr_at_high_bytes : ltac2:(CDefT.buildp (gd_tbl_HMLib ()) "PA,$2.Pn,$2.P,(19.$12.Vm,R2.R1.)P,(4.+65?000.R3.)P,(4.=R3.)(14.(0.(>.&8.))Lbs,(0.(>.&8.))(16.(:.$18.(1;.(>.&8.)R1.)(22.R5.))Pi,$18.P,(1<.R1.(22.R6.))(:.(;.(>.&8.))A1.Vm,(13.(5.R8.(1:.R2.)))(1=.(>.&8.)R3.R2.))))")
(* [comment removed for export] *).
  Proof.
    intros A n W HA Hn. apply wr_at_high_bytes_nat; [| exact HA]. rewrite Z2Nat.id by lia. exact W.
  Qed.

  #[using="Type"] Lemma wr_at_high_CB : ltac2:(CDefT.buildp (gd_tbl_HMLib ()) "PA,$2.Pn,$2.P,(19.$12.Vm,R2.R1.)P,(4.+65?000.R3.)P,(4.=R3.)(14.(0.(>.&8.))Lbs,(0.(>.&8.))(1>.$12.Vm,R6.(1?.$20.(21.(22.R5.)R1.)(23.$20.))))")
(* [comment removed for export] *).
  Proof.
    intros A n W HA Hn. ddestruct (wr_at_high_bytes A n W HA Hn) as (bs & L & B). dpose W as (W0 & W1 & W2).
    exists bs. split.
    - split; [cbn; split; [exact L| exact I]|]. cbn [cells_bytes cbytes app]. rewrite app_nil_r.
      split; [lia|]. rewrite L. split; [lia|]. intros i Hi. unfold mrd. rewrite (B i Hi).
      destruct (nth_error bs i) eqn:E; [reflexivity|]. exfalso. apply nth_error_None in E. lia.
    - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact W.
  Qed.

  #[using="Type"] Lemma wr_at_high_stk : forall lo hi, wr_at asegs m lo (hi - lo) -> 0x65f000 <= lo -> lo <= hi -> stk asegs m lo hi.
  Proof.
    intros lo hi W HA Hle. dpose W as (W0 & W1 & W2). split; [lia|]. split; [lia|]. intros a Ha.
    pose proof (W2 (a - lo) ltac:(lia)) as Wa. replace (lo + (a - lo)) with a in Wa by lia. split; [exact Wa|].
    destruct (wr_high_byte m a ltac:(lia) ltac:(lia) Wa) as (b & Hb). exists b. unfold mrd. rewrite Hb. reflexivity.
  Qed.
End WithM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma le4_le_bytes_to_word' : forall bs, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le4, le_bytes_to_word. rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64).
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite Hl in B.
  rewrite Z.mod_small by (cbn in B; pose proof (bytes_le_to_Z_nonneg bs); lia). rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.
#[using="Type"] Lemma le2_le_bytes_to_word' : forall bs, length bs = 2%nat -> le2 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le2, le_bytes_to_word. rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64).
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite Hl in B.
  rewrite Z.mod_small by (cbn in B; pose proof (bytes_le_to_Z_nonneg bs); lia). rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

(* [comment removed for export] *)
Fixpoint decode_cells (ws : list nat) (bs : list byte) : list cell :=
  match ws with
  | [] => []
  | w :: ws' =>
      let c := match w, bs with
               | 1%nat, b :: _ => C1 b
               | 2%nat, _ => C2 (le_bytes_to_word (firstn 2 bs))
               | 4%nat, _ => C4 (le_bytes_to_word (firstn 4 bs))
               | 8%nat, _ => C8 (le_bytes_to_word (firstn 8 bs))
               | _, _ => CB w (firstn w bs)
               end in
      c :: decode_cells ws' (skipn w bs)
  end.

Fixpoint wsum (ws : list nat) : nat := match ws with [] => 0 | w :: ws' => w + wsum ws' end%nat.

#[using="Type"] Lemma decode_cells_ok : ltac2:(CDefT.buildp (gd_tbl_HMLib ()) "Pws,(0.$18.)Pbs,(0.(>.&8.))P,(:.$18.(1;.(>.&8.)R1.)(24.R2.))(16.(25.(26.R3.R2.))(16.(:.(0.(>.&8.))(27.(26.R3.R2.))R2.)(:.(0.$18.)(28.$20.$18.$29.(26.R3.R2.))R3.)))")
(* [comment removed for export] *).
Proof.
  induction ws as [|w ws IH]; intros bs Hl; cbn in Hl.
  - destruct bs; [| cbn in Hl; lia]. cbn. auto.
  - ddestruct (IH (skipn w bs) ltac:(rewrite length_skipn; lia)) as (WF & BY & SZ).
    assert (FL : length (firstn w bs) = w) by (rewrite length_firstn; lia).
    assert (SPLIT : firstn w bs ++ skipn w bs = bs) by apply firstn_skipn.
    cbn [decode_cells].
    destruct w as [|[|[|[|[|[|[|[|[|w]]]]]]]]].
    all: try (cbn [cells_wf cells_bytes cbytes map csize cell_wf]; rewrite ?BY, ?SZ; split; [split; [exact FL| exact WF]|]; split; [exact SPLIT| reflexivity]).
    + (* [comment removed for export] *) destruct bs as [|b r]; [cbn in Hl; lia|]. cbn [decode_cells cells_wf cells_bytes cbytes map csize cell_wf skipn app] in *.
      rewrite BY, SZ. split; [split; [exact I| exact WF]|]. split; reflexivity.
    + (* [comment removed for export] *) cbn [cells_wf cells_bytes cbytes map csize cell_wf]. rewrite BY, SZ, (le2_le_bytes_to_word' _ FL). auto.
    + (* [comment removed for export] *) cbn [cells_wf cells_bytes cbytes map csize cell_wf]. rewrite BY, SZ, (le4_le_bytes_to_word' _ FL). auto.
    + (* [comment removed for export] *) cbn [cells_wf cells_bytes cbytes map csize cell_wf]. rewrite BY, SZ, (le8_le_bytes_to_word _ FL). auto.
  Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma wr_at_high_hdr : ltac2:(CDefT.buildp (gd_tbl_HMLib ()) "Pm,P,(>.&40.)(;.(>.&8.))PA,$2.P,(19.$12.R2.R1.+10.)P,(4.+65?000.R2.)(14.(>.&8.)Lb0,(>.&8.)(14.(>.&8.)Lb1,(>.&8.)(14.(>.&40.)Lw2,(>.&40.)(14.(>.&40.)Lw4,(>.&40.)(14.(>.&40.)Lw8,(>.&40.)(1>.$12.R9.R8.(1?.$20.(2:.R5.)(1?.$20.(2:.R4.)(1?.$20.(2;.R3.)(1?.$20.(2<.R2.)(1?.$20.(2=.R1.)(23.$20.))))))))))))")
(* [comment removed for export] *).
Proof.
  intros m A W HA. destruct (wr_at_high_CB m A 16 W HA ltac:(lia)) as (bs & RW).
  dpose RW as [[[L _] _] _]. cbn in L.
  ddestruct (decode_cells_ok [1;1;2;4;8]%nat bs L) as (WF & BY & SZ).
  destruct bs as [|x0 [|x1 bs]]; try (cbn in L; lia).
  cbn [decode_cells skipn firstn] in WF, BY, SZ.
  deexists 5. eapply rw_cells_reshape; [exact RW| exact WF| etransitivity; [exact BY|]; cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
Qed.

#[using="Type"] Lemma wr_at_high_C8C8 : forall m A, wr_at asegs m A 16 -> 0x65f000 <= A -> exists w0 w1, rw_cells asegs m A [C8 w0; C8 w1].
Proof.
  intros m A W HA. destruct (wr_at_high_CB m A 16 W HA ltac:(lia)) as (bs & RW).
  dpose RW as [[[L _] _] _]. cbn in L.
  ddestruct (decode_cells_ok [8;8]%nat bs L) as (WF & BY & SZ). cbn [decode_cells] in WF, BY, SZ.
  deexists 2. eapply rw_cells_reshape; [exact RW| exact WF| etransitivity; [exact BY|]; cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
Qed.

#[using="Type"] Lemma wr_at_high_C1 : forall m A, wr_at asegs m A 1 -> 0x65f000 <= A -> exists b, rw_cells asegs m A [C1 b].
Proof.
  intros m A W HA. destruct (wr_at_high_CB m A 1 W HA ltac:(lia)) as (bs & RW).
  dpose RW as [[[L _] _] _]. cbn in L. destruct bs as [|b [|? ?]]; try (cbn in L; lia).
  exists b. eapply rw_cells_reshape; [exact RW| cbn; tauto| reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wr_at_sub : forall m A n k j, wr_at asegs m A n -> 0 <= k -> 0 <= j -> k + j <= n -> wr_at asegs m (A + k) j.
Proof.
  (intros m A n k j dd_H; ddestruct dd_H as (W0 & W1 & W); intros Hk Hj Hkj). split; [lia|]. split; [lia|]. intros i Hi.
  replace (A + k + i) with (A + (k + i)) by lia. apply W. lia.
Qed.

(* [comment removed for export] *)
Fixpoint words_of (k : nat) (bs : list byte) : list word :=
  match k with O => [] | S k' => le_bytes_to_word (firstn 8 bs) :: words_of k' (skipn 8 bs) end.
#[using="Type"] Lemma words_of_ok : forall k bs, length bs = (8 * k)%nat -> u64s (words_of k bs) = bs /\ length (words_of k bs) = k.
Proof.
  induction k as [|k IH]; intros bs L; cbn [words_of u64s length].
  - destruct bs; [auto| cbn in L; lia].
  - destruct (IH (skipn 8 bs) ltac:(rewrite length_skipn; lia)) as [E1 E2]. rewrite E1, E2, le8_le_bytes_to_word by (rewrite length_firstn; lia).
    split; [apply firstn_skipn| reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wr_at_off_C8C8 : ltac2:(CDefT.buildp (gd_tbl_HMLib ()) "Pm,P,(>.&40.)(;.(>.&8.))PA,$2.P,(19.$12.R2.R1.+10.)P,(17.(4.(5.R2.+10.)+10000.)(4.+65?000.R2.))(14.(>.&40.)Lw0,(>.&40.)(14.(>.&40.)Lw1,(>.&40.)(1>.$12.R6.R5.(1?.$20.(2=.R2.)(1?.$20.(2=.R1.)(23.$20.))))))")
(* [comment removed for export] *).
Proof.
  intros m A W HA. destruct (wr_at_off_CB m A 16 W HA ltac:(lia)) as (bs & RW).
  dpose RW as [[[L _] _] _]. cbn in L.
  ddestruct (decode_cells_ok [8;8]%nat bs L) as (WF & BY & SZ). cbn [decode_cells] in WF, BY, SZ.
  deexists 2. eapply rw_cells_reshape; [exact RW| exact WF| etransitivity; [exact BY|]; cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
Qed.
#[using="Type"] Lemma wr_at_off_u64arr : ltac2:(CDefT.buildp (gd_tbl_HMLib ()) "Pm,P,(>.&40.)(;.(>.&8.))PA,$2.Pk,$18.P,(19.$12.R3.R2.(2>.+8.(1:.R1.)))P,(17.(4.(5.R3.(2>.+8.(1:.R2.)))+10000.)(4.+65?000.R3.))(14.(0.(>.&40.))Lws,(0.(>.&40.))(16.(2?.$12.R6.R5.R1.)(:.$18.(1;.(>.&40.)R1.)R4.)))")
(* [comment removed for export] *).
Proof.
  intros m A k W HA. destruct (wr_at_off_CB m A _ W HA ltac:(lia)) as (bs & [[[L _] BY] WR]). cbn in L.
  destruct (words_of_ok k bs ltac:(lia)) as [E1 E2]. exists (words_of k bs). split; [| exact E2].
  split; [| rewrite E2; exact W]. cbn [cells_bytes cbytes app] in BY. rewrite app_nil_r in BY. rewrite E1. exact BY.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Keep.
  Variables (m m' : mem).
  Definition kept (A n : Z) : Prop := forall x : word, A <= bv_unsigned x < A + n -> m' x = m x.

  #[using="Type"] Lemma kept_munch : forall A n, 0 <= A -> kept A n -> munch [(0, A); (A + n, 2^64)] m m'.
  Proof.
    intros A n HA K x OUT. cbn [outside] in OUT. pose proof (u64_range x). apply K. lia.
  Qed.
  #[using="Type"] Lemma keep_rw : ltac2:(CDefT.buildp (gd_tbl_HMLib ()) "PA,$2.Pcs,(0.$20.)P,(1>.$12.Vm,R2.R1.)P,(30.R3.(1:.(31.R2.)))P,(32.$12.Vm,Vm',)(1>.$12.Vm',R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros A cs RW K WM. pose proof (rw_cells_bound _ _ _ _ RW) as B.
    eapply (rw_cells_transport _ [(0, A); (A + Z.of_nat (cells_size cs), 2^64)]); [exact RW| apply kept_munch; [lia| exact K]| exact WM| cbn [disjoint_from]; repeat split; lia].
  Qed.
  #[using="Type"] Lemma keep_ro : forall A cs, ro_cells asegs m A cs -> kept A (Z.of_nat (cells_size cs)) -> ro_cells asegs m' A cs.
  Proof.
    intros A cs RO K. pose proof (ro_cells_bound _ _ _ _ RO) as B.
    eapply (ro_cells_transport _ [(0, A); (A + Z.of_nat (cells_size cs), 2^64)]); [exact RO| apply kept_munch; [lia| exact K]| cbn [disjoint_from]; repeat split; lia].
  Qed.
  #[using="Type"] Lemma keep_u32arr : ltac2:(CDefT.buildp (gd_tbl_HMLib ()) "PA,$2.Pws,(0.(>.&40.))P,(33.$12.Vm,R2.R1.)P,(30.R3.(2>.+4.(1:.(1;.(>.&40.)R2.))))P,(32.$12.Vm,Vm',)(33.$12.Vm',R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros A ws U K WM. pose proof (u32arr_bound _ _ _ _ U) as B.
    eapply (u32arr_transport _ [(0, A); (A + 4 * Z.of_nat (length ws), 2^64)]); [exact U| apply kept_munch; [lia| exact K]| exact WM| cbn [disjoint_from]; repeat split; lia].
  Qed.
  #[using="Type"] Lemma keep_u64arr : ltac2:(CDefT.buildp (gd_tbl_HMLib ()) "PA,$2.Pws,(0.(>.&40.))P,(2?.$12.Vm,R2.R1.)P,(30.R3.(2>.+8.(1:.(1;.(>.&40.)R2.))))P,(32.$12.Vm,Vm',)(2?.$12.Vm',R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros A ws U K WM. pose proof (u64arr_bound _ _ _ _ U) as B.
    eapply (u64arr_transport _ [(0, A); (A + 8 * Z.of_nat (length ws), 2^64)]); [exact U| apply kept_munch; [lia| exact K]| exact WM| cbn [disjoint_from]; repeat split; lia].
  Qed.
  #[using="Type"] Lemma kept_sub : forall A n A' n', kept A n -> A <= A' -> A' + n' <= A + n -> kept A' n'.
  Proof. intros A n A' n' K H1 H2 x Hx. apply K. lia. Qed.
End Keep.

(* [comment removed for export] *)
#[using="Type"] Lemma u64s_cells_bytes : forall ws, cells_bytes (map C8 ws) = u64s ws.
Proof. induction ws; cbn; [reflexivity|]. rewrite IHws. reflexivity. Qed.
#[using="Type"] Lemma u64arr_cells : forall m A ws, u64arr asegs m A ws -> rw_cells asegs m A (map C8 ws).
Proof.
  intros m A ws [B W]. split; [split|].
  - clear. induction ws; cbn; auto.
  - rewrite u64s_cells_bytes. exact B.
  - replace (Z.of_nat (cells_size (map C8 ws))) with (8 * Z.of_nat (length ws)); [exact W|]. clear. induction ws; cbn [cells_size map csize length]; lia.
Qed.
#[using="Type"] Lemma cells_u64arr : forall m A ws, rw_cells asegs m A (map C8 ws) -> u64arr asegs m A ws.
Proof.
  intros m A ws [[_ B] W]. split.
  - rewrite <- u64s_cells_bytes. exact B.
  - replace (8 * Z.of_nat (length ws)) with (Z.of_nat (cells_size (map C8 ws))); [exact W|]. clear. induction ws; cbn [cells_size map csize length]; lia.
Qed.

#[using="Type"] Lemma rw_C1_inj : forall m A b b', rw_cells asegs m A [C1 b] -> rw_cells asegs m A [C1 b'] -> b = b'.
Proof.
  (intros m A b b' dd_H; ddestruct dd_H as [[_ (_ & _ & B)] _]; intros dd_H; ddestruct dd_H as [[_ (_ & _ & B')] _]).
  specialize (B 0%nat ltac:(cbn; lia)). specialize (B' 0%nat ltac:(cbn; lia)). cbn in B, B'. rewrite B in B'. injection B' as E. exact E.
Qed.

End ARUN_1.
