(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
(* AD_handoff0 at : argv pointers from asan_argv_facts; StringBlock / ArgPack over 's entry block *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem Mem Cells Frame.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Common Require Import DrvAgree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound Require Import AsanMain.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.AsanW Require Import AImg ABytes StdioFiles Stdio_kit Stdio_iface F_syscalls AExit F_module_dtor AHarness_iface ADriver_iface.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition ho_pfact_eqb (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | _, _ => false
  end.
Lemma ho_pfact_eqb_eq : forall f g, ho_pfact_eqb f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn in H; try discriminate;
    repeat (apply andb_prop in H as [H ?X]);
    repeat match goal with
    | K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
    | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
    | K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
    end; subst; reflexivity.
Qed.
Lemma ho_pfact_find : forall V (l : list pfact) f,
  Forall (pfact_ok V) l -> existsb (ho_pfact_eqb f) l = true -> pfact_ok V f.
Proof.
  intros V l f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply ho_pfact_eqb_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.

End CANSEC1.
Ltac mf V m HM f H := pose proof (mfact_find asegs V m _ f HM ltac:(vm_compute; reflexivity)) as H; cbn [mfact_ok zv cellw] in H.
Ltac pf V HP f H := pose proof (ho_pfact_find V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.

Section CANSEC2. Context {rc : runConstT}.
Lemma aimg_chunk : forall V m (l : list mfact) A cs,
  Forall (mfact_ok asegs V m) l ->
  existsb (fun f => match f with MImg lo' hi' => (lo' <=? A) && (A + Z.of_nat (cells_size cs) <=? hi') | _ => false end) l = true ->
  cells_wf cs -> rw_bytes_b asegs A (cells_bytes cs) = true -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2^64 ->
  rw_cells asegs m A cs.
Proof.
  intros V m l A cs HM HE WF HB HA HHI.
  pose proof (cells_bytes_length cs WF) as LEN.
  assert (R : forall i, A <= i < A + Z.of_nat (cells_size cs) -> m (wa i) = None).
  { eapply mimg_cover; [exact HM| exact HE]. }
  eapply rw_cells_recast; [apply (rw_cells_image0 asegs m A (cells_bytes cs))| exact WF| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| cbn; rewrite LEN, Nat.add_0_r; reflexivity].
  - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply R. rewrite LEN in Ha. lia.
  - exact HB.
  - exact HA.
  - rewrite LEN. exact HHI.
Qed.

End CANSEC2.
Ltac aimg V m HM A cs H :=
  pose proof (aimg_chunk V m _ A cs HM ltac:(vm_compute; reflexivity) ltac:(cbn; repeat split; exact I)
                ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as H.

Notation z64 := (Z_to_bv 64 0).

Section CANSEC3. Context {rc : runConstT}.
Lemma stderr_wfile0_init : forall V m, Forall (mfact_ok asegs V m) asan_mem_facts -> stderr_wfile0 m.
Proof.
  intros V m HM. exists (Z_to_bv 64 5), z64, 0, 0, (repeat (Z_to_bv 8 0) 80).
  split; [| split; [vm_compute; reflexivity| split; [left; reflexivity| lia]]].
  aimg V m HM 0x9dd38 (file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE 0x5f5098 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) H. exact H.
Qed.

Lemma stdout_file_init : forall V m, Forall (mfact_ok asegs V m) asan_mem_facts -> stdout_file m stdout_init.
Proof.
  intros V m HM. exists (Z_to_bv 64 5), z64, (repeat (Z_to_bv 8 0) 80), (repeat (Z_to_bv 8 0) 1024).
  cbn [so_active so_buf so_lbf_nl so_first stdout_init Prelim.zlength length Z.of_nat Z.add].
  split. { aimg V m HM 0x9de28 (file_cells (Z_to_bv 64 5) 0 0 0 F_STDOUT_WRITE 0x5f50a0 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) H. exact H. }
  split; [vm_compute; reflexivity|].
  split. { aimg V m HM 0x5f50a0 [CB 1024 (repeat (Z_to_bv 8 0) 1024)] H. exact H. }
  split; [reflexivity|]. split; [unfold zlength; cbn; lia| intros _; reflexivity].
Qed.

Lemma canary_seg_bytes : forall k, (k < 8)%nat ->
  segment_byte_at (seg_bytes Tgt_checksum_fuzzer_asan_segment_003) (0x5f49d0 - 0x9b000 + N.of_nat k)%N = Some (Z_to_bv 8 0).
Proof. intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.
Lemma canary_wr_at : forall m, wr_at asegs m 0x5f49d0 8.
Proof.
  intros m. split; [lia|]. split; [lia|]. intros i Hi. unfold wview.
  destruct (m (wa (0x5f49d0 + i))) as [b|] eqn:E; [discriminate|].
  rewrite wa_unsigned by lia. rewrite a_find_segment_1 by lia.
  destruct (Z.leb_spec0 0x10000 (0x5f49d0 + i)); destruct (Z.leb_spec0 (0x5f49d0 + i + 1) 0x31000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0x31000 (0x5f49d0 + i)); destruct (Z.leb_spec0 (0x5f49d0 + i + 1) 0x99000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0x99000 (0x5f49d0 + i)); destruct (Z.leb_spec0 (0x5f49d0 + i + 1) 0x9b000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0x9b000 (0x5f49d0 + i)); destruct (Z.leb_spec0 (0x5f49d0 + i + 1) 0x5f7000); cbn [andb]; try lia.
  replace (seg_writable Tgt_checksum_fuzzer_asan_segment_003) with true by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Tgt_checksum_fuzzer_asan_segment_003)) with 0x9b000 by (vm_compute; reflexivity).
  replace (Z.to_N (0x5f49d0 + i - 0x9b000)) with (0x5f49d0 - 0x9b000 + N.of_nat (Z.to_nat i))%N by lia.
  rewrite canary_seg_bytes by lia. discriminate.
Qed.
Lemma ssp_guard_init : forall V m, Forall (mfact_ok asegs V m) asan_mem_facts -> rw_cells asegs m ssp_guard [C8 (Z_to_bv 64 (V 45%nat))].
Proof.
  intros V m HM. mf V m HM (MRo (ZLit 6244816) 8 (ZV 45)) H. unfold ssp_guard.
  pose proof (cellw_bytes 8 (V 45%nat) eq_refl) as (Cb & Cs & Cwf). change (cellw 8 (V 45%nat)) with (C8 (Z_to_bv 64 (V 45%nat))) in Cb, Cs, Cwf.
  split.
  - split; [cbn; split; [exact Cwf| exact I]|]. cbn [cells_bytes]. rewrite app_nil_r, Cb. exact H.
  - cbn [cells_size]. rewrite Cs. apply canary_wr_at.
Qed.

Lemma errno_init : forall V m, Forall (mfact_ok asegs V m) asan_mem_facts -> rw_cells asegs m 0x5d48ec [C4 z64].
Proof. intros V m HM. aimg V m HM 0x5d48ec [C4 z64] H. exact H. Qed.
Lemma run_rw_cells : forall m A n (b : byte),
  0 <= n -> (forall i, 0 <= i < n -> m (wa (A + i)) = Some b) -> wr_at asegs m A n ->
  rw_cells asegs m A [CB (Z.to_nat n) (repeat b (Z.to_nat n))].
Proof.
  intros m A n b Hn Hz (W1 & W2 & W3). split.
  - split; [cbn; split; [rewrite repeat_length; reflexivity| exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite repeat_length, Z2Nat.id by lia; lia|].
    intros i Hi. rewrite repeat_length in Hi. rewrite (nth_error_repeat b Hi).
    unfold mrd. rewrite (Hz (Z.of_nat i) ltac:(lia)). reflexivity.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|]. exact W3.
Qed.

Lemma rw_cells_join : forall m A n1 n2 (j1 j2 : list byte),
  rw_cells asegs m A [CB n1 j1] -> rw_cells asegs m (A + Z.of_nat n1) [CB n2 j2] ->
  rw_cells asegs m A [CB (n1 + n2)%nat (j1 ++ j2)].
Proof.
  intros m A n1 n2 j1 j2 H1 H2.
  pose proof H1 as [[[L1 _] _] _]. pose proof H2 as [[[L2 _] _] _]. cbn in L1, L2.
  assert (H : rw_cells asegs m A ([CB n1 j1] ++ [CB n2 j2])).
  { apply (proj2 (rw_cells_app asegs m A [CB n1 j1] [CB n2 j2])). split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2. }
  eapply rw_cells_recast; [exact H| cbn; split; [rewrite app_length; lia| exact I]| cbn [cells_bytes cbytes app]; rewrite !app_nil_r; reflexivity| cbn; lia].
Qed.

Lemma rw_C1_CB : forall m A (b : byte), rw_cells asegs m A [C1 b] -> rw_cells asegs m A [CB 1 [b]].
Proof. intros m A b H. eapply rw_cells_recast; [exact H| cbn; split; [reflexivity| exact I]| reflexivity| reflexivity]. Qed.

Lemma bytes_eq_of_unsigned : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hb Hbs. f_equal; [apply bv_eq; exact Hb| apply IH; exact Hbs].
Qed.

Lemma rw_C8_C4 : forall m A (v lo hi : word),
  rw_cells asegs m A [C8 v] -> cells_bytes [C4 lo; C4 hi] = cells_bytes [C8 v] -> rw_cells asegs m A [C4 lo].
Proof.
  intros m A v lo hi H E.
  assert (H' : rw_cells asegs m A ([C4 lo] ++ [C4 hi])).
  { eapply rw_cells_recast; [exact H| cbn; tauto| exact E| reflexivity]. }
  apply (proj1 (rw_cells_app asegs m A _ _)) in H'. exact (proj1 H').
Qed.

Lemma wr_at_sub' : forall m a n a' n', wr_at asegs m a n -> 0 <= a' -> a <= a' -> a' + n' <= a + n -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

End CANSEC3.
Ltac norm_addr := match goal with |- rw_cells _ _ ?A _ => let a := eval vm_compute in A in change A with a end.

Section CANSEC4. Context {rc : runConstT}.
Lemma zchunk_pointwise : forall m A n, rw_cells asegs m A [CB (Z.to_nat n) (zeros n)] -> 0x5f7000 <= A ->
  forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 0).
Proof.
  intros m A n [[_ B] _] HA i Hi. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. destruct B as (B0 & B1 & B).
  unfold zeros in B1, B. rewrite repeat_length in B1, B.
  specialize (B (Z.to_nat i) ltac:(lia)).
  rewrite (nth_error_repeat (Z_to_bv 8 0)) in B by lia. rewrite Z2Nat.id in B by lia.
  rewrite ref_mrd_overlay in B; [exact B|]. right. rewrite wa_unsigned; lia.
Qed.

Definition zlit_of (e : zexp) : option Z := match e with ZLit z => Some z | _ => None end.
Lemma zlit_of_zv : forall V e z, zlit_of e = Some z -> zv V e = z.
Proof. intros V e z H. destruct e; cbn in H; try discriminate. injection H as ->. reflexivity. Qed.
Definition mzero_covb (lo n : Z) (f : mfact) : bool :=
  match f with
  | MZero a n' => match zlit_of a with Some a' => (a' <=? lo) && (lo + n <=? a' + n') | None => false end
  | MZeroC a n' => match zlit_of a with Some a' => (0x5f7000 <=? a') && ((a' <=? lo) && (lo + n <=? a' + n')) | None => false end
  | _ => false
  end.
Lemma mzero_cover : forall V m (l : list mfact) lo n,
  Forall (mfact_ok asegs V m) l -> existsb (mzero_covb lo n) l = true ->
  forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0).
Proof.
  intros V m l lo n HM HE i Hi. apply existsb_exists in HE as (f & Hin & Hf).
  pose proof (proj1 (Forall_forall _ _) HM f Hin) as K.
  destruct f as [? ? ?|a k|? ? ?|a k|? ? ?|? ?|? ?|? ?|? ?]; try discriminate; cbn [mzero_covb] in Hf;
    destruct (zlit_of a) as [a'|] eqn:E; try discriminate; apply (zlit_of_zv V) in E; cbn [mfact_ok] in K; rewrite E in K.
  - apply andb_prop in Hf as [H0 Hf]. apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
    replace (lo + i) with (a' + (lo + i - a')) by lia. apply (zchunk_pointwise m a' k K); lia.
  - apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    replace (lo + i) with (a' + (lo + i - a')) by lia. apply K. lia.
Qed.

Section HandoffFacts.
  Variables (V : nat -> Z) (m : word -> option byte).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.

  Let WSH : wr_at asegs m 0x7fffa000 0xbce00.
  Proof. mf V m HM (MWr (ZLit 2147459072) 773632) H. exact H. Qed.
  Lemma sh_zero1 : forall i, 0 <= i < 8609 -> m (wa (2147459072 + i)) = Some (Z_to_bv 8 0).
  Proof. mf V m HM (MZero (ZLit 2147459072) 8609) H. exact H. Qed.
  Lemma sh_tab1 : forall i, 0 <= i < 128 -> m (wa (2147467788 + i)) = Some (Z_to_bv 8 0).
  Proof. exact (mzero_cover V m _ 2147467788 128 HM ltac:(vm_compute; reflexivity)). Qed.
  Lemma sh_tab2 : forall i, 0 <= i < 512 -> m (wa (2147467948 + i)) = Some (Z_to_bv 8 0).
  Proof. exact (mzero_cover V m _ 2147467948 512 HM ltac:(vm_compute; reflexivity)). Qed.
  Lemma sh_tab3 : forall i, 0 <= i < 16 -> m (wa (2147468588 + i)) = Some (Z_to_bv 8 0).
  Proof. exact (mzero_cover V m _ 2147468588 16 HM ltac:(vm_compute; reflexivity)). Qed.
  Lemma sh_zero4 : forall i, 0 <= i < 2148231832 - 2148206600 -> m (wa (2148206600 + i)) = Some (Z_to_bv 8 0).
  Proof. exact (mzero_cover V m _ 2148206600 (2148231832 - 2148206600) HM ltac:(vm_compute; reflexivity)). Qed.

  Lemma zrun_chunk : forall base len A n,
    (forall i, 0 <= i < len -> m (wa (base + i)) = Some (Z_to_bv 8 0)) ->
    base <= A -> 0 <= n -> A + n <= base + len -> 0x7fffa000 <= A -> A + n <= 0x7fffa000 + 0xbce00 ->
    rw_cells asegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
  Proof.
    intros base len A n Hz H1 H2 H3 H4 H5. apply run_rw_cells; [lia| | eapply wr_at_sub'; [exact WSH| lia| lia| lia]].
    intros i Hi. replace (A + i) with (base + (A - base + i)) by lia. apply Hz. lia.
  Qed.
  Lemma fill_chunk : forall A n c,
    (forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 c)) -> 0 <= n -> 0x7fffa000 <= A -> A + n <= 0x7fffa000 + 0xbce00 ->
    rw_cells asegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].
  Proof. intros A n c Hf H2 H4 H5. apply run_rw_cells; [lia| exact Hf| eapply wr_at_sub'; [exact WSH| lia| lia| lia]]. Qed.

  Lemma astat_shg0 : exists j, rw_cells asegs m 0x7fffc1a0 [CB 4 j].
  Proof.
    mf V m HM (MCell (ZLit 2147467681) 1 (ZLit 5)) K1.
    mf V m HM (MFill (ZLit 2147467682) 2 249) F1.
    eexists. change 4%nat with (1 + (1 + 2))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147467680 1 2147467680 1 (mzero_cover V m _ 2147467680 1 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 2 249 F1); lia.
  Qed.
  Lemma astat_shg1 : exists j, rw_cells asegs m 0x7fffc1a4 [CB 12 j].
  Proof.
    mf V m HM (MCell (ZLit 2147467690) 1 (ZLit 4)) K1.
    mf V m HM (MFill (ZLit 2147467691) 5 249) F1.
    eexists. change 12%nat with (6 + (1 + 5))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147467684 6 2147467684 6 (mzero_cover V m _ 2147467684 6 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 5 249 F1); lia.
  Qed.
  Lemma astat_shg2 : exists j, rw_cells asegs m 0x7fffc1b0 [CB 8 j].
  Proof.
    mf V m HM (MCell (ZLit 2147467698) 1 (ZLit 7)) K1.
    mf V m HM (MFill (ZLit 2147467699) 5 249) F1.
    eexists. change 8%nat with (2 + (1 + 5))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147467696 2 2147467696 2 (mzero_cover V m _ 2147467696 2 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 5 249 F1); lia.
  Qed.
  Lemma astat_shg3 : exists j, rw_cells asegs m 0x7fffc1b8 [CB 4 j].
  Proof.
    mf V m HM (MCell (ZLit 2147467705) 1 (ZLit 5)) K1.
    mf V m HM (MFill (ZLit 2147467706) 2 249) F1.
    eexists. change 4%nat with (1 + (1 + 2))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147467704 1 2147467704 1 (mzero_cover V m _ 2147467704 1 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 2 249 F1); lia.
  Qed.
  Lemma astat_shg4 : exists j, rw_cells asegs m 0x7fffc1bc [CB 16 j].
  Proof.
    mf V m HM (MCell (ZLit 2147467717) 1 (ZLit 1)) K1.
    mf V m HM (MFill (ZLit 2147467718) 6 249) F1.
    eexists. change 16%nat with (9 + (1 + 6))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147467708 9 2147467708 9 (mzero_cover V m _ 2147467708 9 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 6 249 F1); lia.
  Qed.
  Lemma astat_shg5 : exists j, rw_cells asegs m 0x7fffc1cc [CB 16 j].
  Proof.
    mf V m HM (MCell (ZLit 2147467732) 1 (ZLit 5)) K1.
    mf V m HM (MFill (ZLit 2147467733) 7 249) F1.
    eexists. change 16%nat with (8 + (1 + 7))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147467724 8 2147467724 8 (mzero_cover V m _ 2147467724 8 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 7 249 F1); lia.
  Qed.
  Lemma astat_shg6 : exists j, rw_cells asegs m 0x7fffc1dc [CB 16 j].
  Proof.
    mf V m HM (MCell (ZLit 2147467748) 1 (ZLit 7)) K1.
    mf V m HM (MFill (ZLit 2147467749) 7 249) F1.
    eexists. change 16%nat with (8 + (1 + 7))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147467740 8 2147467740 8 (mzero_cover V m _ 2147467740 8 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 7 249 F1); lia.
  Qed.
  Lemma astat_shg7 : exists j, rw_cells asegs m 0x7fffc1ec [CB 8 j].
  Proof.
    mf V m HM (MCell (ZLit 2147467758) 1 (ZLit 1)) K1.
    mf V m HM (MFill (ZLit 2147467759) 5 249) F1.
    eexists. change 8%nat with (2 + (1 + 5))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147467756 2 2147467756 2 (mzero_cover V m _ 2147467756 2 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 5 249 F1); lia.
  Qed.
  Lemma astat_shg8 : exists j, rw_cells asegs m 0x7fffc1f4 [CB 16 j].
  Proof.
    mf V m HM (MCell (ZLit 2147467774) 1 (ZLit 5)) K1.
    mf V m HM (MFill (ZLit 2147467775) 5 249) F1.
    eexists. change 16%nat with (10 + (1 + 5))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147467764 10 2147467764 10 (mzero_cover V m _ 2147467764 10 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 5 249 F1); lia.
  Qed.
  Lemma astat_shg9 : exists j, rw_cells asegs m 0x7fffc20c [CB 160 j].
  Proof.
    mf V m HM (MFill (ZLit 2147467916) 32 249) F1.
    eexists. change 160%nat with (128 + 32)%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147467788 128 2147467788 128 (mzero_cover V m _ 2147467788 128 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. apply (fill_chunk _ 32 249 F1); lia.
  Qed.
  Lemma astat_shg10 : exists j, rw_cells asegs m 0x7fffc2ac [CB 640 j].
  Proof.
    mf V m HM (MFill (ZLit 2147468460) 128 249) F1.
    eexists. change 640%nat with (512 + 128)%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147467948 512 2147467948 512 (mzero_cover V m _ 2147467948 512 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. apply (fill_chunk _ 128 249 F1); lia.
  Qed.
  Lemma astat_shg11 : exists j, rw_cells asegs m 0x7fffc52c [CB 20 j].
  Proof.
    mf V m HM (MFill (ZLit 2147468604) 4 249) F1.
    eexists. change 20%nat with (16 + 4)%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468588 16 2147468588 16 (mzero_cover V m _ 2147468588 16 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. apply (fill_chunk _ 4 249 F1); lia.
  Qed.
  Lemma astat_shd : exists j, rw_cells asegs m 0x8000bc06 [CB 96 j].
  Proof. mf V m HM (MFill (ZLit 2147531782) 96 249) F1. eexists. apply (fill_chunk _ 96 249 F1); lia. Qed.

  Lemma gdesc_init :
       gdesc m 0x9e030 0x20d00 0xd 0x20 0x1bfb6 0x21020 (2^64 - 1)
    /\ gdesc m 0x9e070 0x20d20 0x34 0x60 0x1e701 0x21020 (2^64 - 1)
    /\ gdesc m 0x9e0b0 0x20d80 0x17 0x40 0x1f79a 0x21020 (2^64 - 1)
    /\ gdesc m 0x9e0f0 0x20dc0 0xd 0x20 0x20476 0x21020 (2^64 - 1)
    /\ gdesc m 0x9e130 0x20de0 0x49 0x80 0x1476e 0x21020 (2^64 - 1)
    /\ gdesc m 0x9e170 0x20e60 0x45 0x80 0x136f4 0x21020 (2^64 - 1)
    /\ gdesc m 0x9e1b0 0x20ee0 0x47 0x80 0x1cf5a 0x21020 (2^64 - 1)
    /\ gdesc m 0x9e1f0 0x20f60 0x11 0x40 0x1872c 0x21020 (2^64 - 1)
    /\ gdesc m 0x9e230 0x20fa0 0x55 0x80 0x1a425 0x21020 (2^64 - 1)
    /\ gdesc m 0x9e270 0x21060 0x400 0x500 0x1580c 0x22a00 (2^64 - 1)
    /\ gdesc m 0x9e2b0 0x21560 0x1000 0x1400 0x18733 0x22a00 (2^64 - 1)
    /\ gdesc m 0x9e2f0 0x22960 0x80 0xa0 0x15eb3 0x22a00 (2^64 - 1).
  Proof.
    unfold gdesc. change (2^64 - 1) with 18446744073709551615.
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with |- rw_cells _ _ ?A ?cs => aimg V m HM A cs H; exact H end.
  Qed.

  Lemma astat_cells :
       rw_cells asegs m 0x5d48e8 [C4 (Z_to_bv 64 (V 44%nat))]
    /\ rw_cells asegs m 0x5f4c00 [C4 (Z_to_bv 64 0)]
    /\ (exists cdt thr sec tm1, rw_cells asegs m 0x5f4c20 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
    /\ rw_cells asegs m 0x1338a0 [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m 0x9e390 [C1 (Z_to_bv 8 0)]
    /\ (exists dso, rw_cells asegs m 0x9b480 [C8 dso])
    /\ rw_cells asegs m 0x5f5088 [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m 0x9e000 [C8 (Z_to_bv 64 0x9df18)]
    /\ rw_cells asegs m 0x9df18 stdin_cells
    /\ rw_cells asegs m 0x9df10 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells asegs m 0x9de20 [C8 (Z_to_bv 64 RSTDERR)]
    /\ rw_cells asegs m 0x9f210 [C4 (Z_to_bv 64 1)]
    /\ rw_cells asegs m 0x9e340 [C8 (Z_to_bv 64 1)]
    /\ rw_cells asegs m 0x9f2b0 [C8 (Z_to_bv 64 0)].
  Proof.
    repeat match goal with |- _ /\ _ => split end.
    - mf V m HM (MCell (ZLit 6113512) 4 (ZV 44)) H. exact H.
    - aimg V m HM 0x5f4c00 [C4 (Z_to_bv 64 0)] H. exact H.
    - mf V m HM (MCell (ZLit 6245408) 1 (ZLit 1)) H. aimg V m HM 0x5f4c21 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] H2.
      exists (Z_to_bv 8 1), (Z_to_bv 8 0), (Z_to_bv 8 0), (Z_to_bv 64 0).
      apply (proj2 (rw_cells_app asegs m 0x5f4c20 [C1 (Z_to_bv 8 1)] _)). split; [exact H| exact H2].
    - aimg V m HM 0x1338a0 [C1 (Z_to_bv 8 0)] H. exact H.
    - aimg V m HM 0x9e390 [C1 (Z_to_bv 8 0)] H. exact H.
    - exists (Z_to_bv 64 0x9b480). aimg V m HM 0x9b480 [C8 (Z_to_bv 64 0x9b480)] H. exact H.
    - aimg V m HM 0x5f5088 [C8 (Z_to_bv 64 0)] H. exact H.
    - aimg V m HM 0x9e000 [C8 (Z_to_bv 64 0x9df18)] H. exact H.
    - unfold stdin_cells. aimg V m HM 0x9df18 [C4 (Z_to_bv 64 9); C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0x8e668); C8 z64; C8 z64; C8 z64; C8 z64;
   C8 (Z_to_bv 64 0x8e694); C8 z64; C8 (Z_to_bv 64 0x8e7ac); C8 (Z_to_bv 64 0x5f54a8); C8 (Z_to_bv 64 1024); C8 z64; C8 z64;
   C4 z64; C4 z64; C8 z64; C4 z64; C4 (Z_to_bv 64 0xffffffff)] H. exact H.
    - aimg V m HM 0x9df10 [C8 (Z_to_bv 64 RSTDOUT)] H. exact H.
    - aimg V m HM 0x9de20 [C8 (Z_to_bv 64 RSTDERR)] H. exact H.
    - mf V m HM (MCell (ZLit 651792) 8 (ZLit 72340168526266369)) H. eapply (rw_C8_C4 _ _ _ _ (Z_to_bv 64 0x01010100)); [exact H| apply bytes_eq_of_unsigned; vm_compute; reflexivity].
    - mf V m HM (MCell (ZLit 648000) 8 (ZLit 1)) H. exact H.
    - mf V m HM (MCell (ZLit 651952) 8 (ZLit 0)) H. exact H.
  Qed.
End HandoffFacts.
Section HandoffFacts2.
  Variables (V : nat -> Z) (m : word -> option byte).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Notation usp := (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat)).
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.

  Lemma tid_range : 1 <= V 44%nat <= 4194303.
  Proof. clear HAT. pf V HP (PVar 44 1 4194303) H. exact H. Qed.

  Lemma sh_sub0 : forall base len lo hi,
    (forall i, 0 <= i < len -> m (wa (base + i)) = Some (Z_to_bv 8 0)) ->
    base <= lo -> lo <= hi -> hi <= base + len -> 0 <= base -> base + len <= 2^64 ->
    shadow_bytes m lo hi (fun _ => 0).
  Proof.
    clear HAT. intros base len lo hi Hz H1 H2 H3 H4 H5. split; [lia|]. split; [lia|]. intros s Hs.
    replace s with (base + (s - base)) by lia. apply Hz. lia.
  Qed.

  Lemma harness_sh_init : harness_invA m.
  Proof.
    clear HAT. unfold harness_invA.
    replace (shad 0x21060) with 2147467788 by reflexivity.
    replace (shad 0x21560) with 2147467948 by reflexivity.
    replace (shad 0x22960) with 2147468588 by reflexivity.
    split. { apply (sh_sub0 _ _ _ _ (sh_tab1 V m HM)); lia. }
    split. { apply (sh_sub0 _ _ _ _ (sh_tab2 V m HM)); lia. }
    apply (sh_sub0 _ _ _ _ (sh_tab3 V m HM)); lia.
  Qed.

  Lemma rodata_sh0_init' : rodata_sh0 m.
  Proof.
    clear HAT. unfold rodata_sh0.
    replace (shad 0x10000) with 2147459072 by reflexivity. replace (shad 0x20cc0) with 2147467672 by reflexivity.
    split. { apply (sh_sub0 _ _ _ _ (sh_zero1 V m HM)); lia. }
    mf V m HM (MWr (ZLit 2147459072) 773632) W. eapply wr_at_sub'; [exact W| lia| lia| lia].
  Qed.

  Lemma rclean_stdout_buf_init : rclean m RBstdout.
  Proof.
    clear HAT. unfold RBstdout, rclean, shclean. cbn [r_lo r_hi r_rlo r_rhi].
    mf V m HM (MWr (ZLit 2147459072) 773632) W.
    replace (shad 0x5f5080) with 2148231696 by reflexivity. replace (shad 0x5f54c0) with 2148231832 by reflexivity.
    split; [| lia]. split; [| split; [| split]].
    - eapply (unpoisoned_of_zero m 2148231700 2148231828 (fun _ => 0)); try reflexivity; try lia.
      all: try (rewrite ?shad_div; unfold AsanEmbed.ASHOFF; Z.div_mod_to_equations; lia).
      apply (sh_sub0 _ _ _ _ (sh_zero4 V m HM)); lia.
    - unfold hull64, Shadow.KEND. repeat split; try reflexivity; lia.
    - eapply wr_at_sub'; [exact W| lia| lia| lia].
    - unfold app_blk, Shadow.KLOW, Shadow.KHIGH, Shadow.KEND. lia.
  Qed.

  Lemma rclean_stage_init : rclean m RSTG.
  Proof.
    clear HAT. unfold RSTG, rclean, shclean. cbn [r_lo r_hi r_rlo r_rhi].
    mf V m HM (MWr (ZLit 2147459072) 773632) W.
    replace (shad 0x5c4040) with 2148206600 by reflexivity. replace (shad 0x5d4080) with 2148214800 by reflexivity.
    split; [| lia]. split; [| split; [| split]].
    - eapply (unpoisoned_of_zero m 2148206600 2148214800 (fun _ => 0)); try reflexivity; try lia.
      all: try (rewrite ?shad_div; unfold AsanEmbed.ASHOFF; Z.div_mod_to_equations; lia).
      apply (sh_sub0 _ _ _ _ (sh_zero4 V m HM)); lia.
    - unfold hull64, Shadow.KEND. repeat split; try reflexivity; lia.
    - eapply wr_at_sub'; [exact W| lia| lia| lia].
    - unfold app_blk, Shadow.KLOW, Shadow.KHIGH, Shadow.KEND. lia.
  Qed.

  Lemma astg_init : ASTG m.
  Proof.
    clear HAT. exists (repeat (Z_to_bv 8 0) ASTAGE_LEN). unfold ASTAGE.
    assert (E : ASTAGE_LEN = Z.to_nat 65536) by (apply Nat2Z.inj; rewrite ASTAGE_LEN_Z, Z2Nat.id by lia; reflexivity).
    rewrite E. replace (Z.to_nat 65536) with (length (repeat (Z_to_bv 8 0) (Z.to_nat 65536))) at 1 by (rewrite repeat_length; reflexivity).
    apply (rw_cells_image0 asegs m).
    - intros a Ha. rewrite repeat_length, Z2Nat.id in Ha by lia. rewrite <- (Z_to_bv_bv_unsigned a).
      apply (mimg_cover asegs V m _ 6045770 6111360 HM); [vm_compute; reflexivity| lia].
    - vm_compute. reflexivity.
    - lia.
    - rewrite repeat_length, Z2Nat.id by lia. lia.
  Qed.

  Lemma atx_cells1_init : atx_cells1 m.
  Proof.
    clear HAT. unfold atx_cells1, AATX, AATX_CALL, ACOV_HOOK.
    repeat match goal with |- context [(6244832 + ?b)%Z] => let v := eval vm_compute in (6244832 + b)%Z in change (6244832 + b)%Z with v end.
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - aimg V m HM 0x5f49e0 [C1 (Z_to_bv 8 0)] H. exact H.
    - aimg V m HM 0x5f49e4 [C4 (Z_to_bv 64 0)] H. exact H.
    - mf V m HM (MCell (ZLit 6244840) 4 (ZLit 1)) H. exact H.
    - mf V m HM (MCell (ZLit 6244848) 8 (ZLit 6244856)) H. exact H.
    - aimg V m HM 0x5f49f8 [C8 (Z_to_bv 64 0)] H. exact H.
    - mf V m HM (MCell (ZLit 6244864) 8 (ZLit 561744)) H. exact H.
    - mf V m HM (MCell (ZLit 6245120) 8 (ZLit 457428)) H. exact H.
  Qed.

  Lemma atx_cells1w_init : atx_cells1w m.
  Proof.
    clear HAT. split; [exact atx_cells1_init|]. unfold AATX. split.
    - aimg V m HM 0x5f4a08 [C8 (Z_to_bv 64 0)] H. exact H.
    - aimg V m HM 0x5f4b08 [C8 (Z_to_bv 64 0)] H. exact H.
  Qed.

  Lemma aincb_init : rw_cells asegs m AAEF_INCB [C1 (Z_to_bv 8 0)].
  Proof. clear HAT. unfold AAEF_INCB. aimg V m HM 0x5d4054 [C1 (Z_to_bv 8 0)] H. exact H. Qed.
  Lemma alibc_init : exists cdt thr sec tm1, rw_cells asegs m ALIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
  Proof.
    clear HAT. unfold ALIBC.
    mf V m HM (MCell (ZLit 6245408) 1 (ZLit 1)) H. aimg V m HM 0x5f4c21 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] H2.
    exists (Z_to_bv 8 1), (Z_to_bv 8 0), (Z_to_bv 8 0), (Z_to_bv 64 0).
    apply (proj2 (rw_cells_app asegs m 0x5f4c20 [C1 (Z_to_bv 8 1)] _)). split; [exact H| exact H2].
  Qed.

  Lemma atrun_cells0_init' : rw_cells asegs m 0x5d4050 [C1 (Z_to_bv 8 0)].
  Proof. clear HAT. aimg V m HM 0x5d4050 [C1 (Z_to_bv 8 0)] H. exact H. Qed.

  Lemma stage2_word_init : bytes_at asegs m (usp + -8) (le8 z64).
  Proof.
    clear HAT. mf V m HM (MCell (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8))) 8 (ZLit 0)) H.
    apply rw_cells_bytes_at in H. cbn [cells_bytes cbytes app] in H. rewrite app_nil_r in H. exact H.
  Qed.


  Lemma stack_shclean_init : forall lo hi RLO RHI,
    ATOP <= RLO -> RLO <= lo -> lo < hi -> hi <= RHI -> hi + 8 <= KEND -> RHI <= KEND -> RLO mod 64 = 0 -> RHI mod 64 = 0 ->
    shclean m lo hi RLO RHI.
  Proof.
    intros lo hi RLO RHI H1 H2 H3 H4 H5 H5' H6 H7. unfold KEND in *.
    pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
    mf V m HM (MWrS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))) W0.
    mf V m HM (MZeroS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))) ZW.
    assert (W : wr_at asegs m (shad ATOP) (17594333495296 - shad ATOP)).
    { rewrite shad_div. unfold AsanEmbed.ASHOFF. eapply wr_at_sub'; [exact W0| | |]; clear - HAT P0 P6 P10; Z.div_mod_to_equations; lia. }
    assert (ZR : forall i, 0 <= i < 17594333495296 - shad ATOP -> m (wa (shad ATOP + i)) = Some (Z_to_bv 8 0)).
    { intros i Hi. rewrite shad_div in Hi |- *. unfold AsanEmbed.ASHOFF in Hi |- *.
      match goal with |- m (wa ?a) = _ =>
        replace a with (4096 * V 0%nat + 512 * V 10%nat + 2146402304 + (a - (4096 * V 0%nat + 512 * V 10%nat + 2146402304))) by (clear; lia) end.
      apply ZW. clear - HAT P0 P6 P10 Hi. Z.div_mod_to_equations. lia. }
    clear W0 ZW.
    split; [| split; [| split]].
    - eapply (unpoisoned_of_zero m (shad lo) (shad (hi - 1) + 1) (fun _ => 0)); try reflexivity; try lia.
      all: try (rewrite ?shad_div; unfold AsanEmbed.ASHOFF; Z.div_mod_to_equations; lia).
      apply (sh_sub0 _ _ _ _ ZR); rewrite ?shad_div; unfold AsanEmbed.ASHOFF; Z.div_mod_to_equations; lia.
    - unfold hull64, Shadow.KEND. repeat split; lia.
    - eapply wr_at_sub'; [exact W| ..]; rewrite !shad_div; unfold AsanEmbed.ASHOFF; Z.div_mod_to_equations; lia.
    - unfold app_blk, Shadow.KLOW, Shadow.KHIGH, Shadow.KEND. lia.
  Qed.
End HandoffFacts2.
(* argv[0] / argv[1]'s pointer words now come from asan_argv_facts r (AS/MainFactsAsan
   ; r = the kernel build's rseq bit, amain_at's argv-facts conjunct), not from asan_mem_facts. *)
Section ArgvPtrs727.
  Variables (V : nat -> Z) (m : word -> option byte) (r : Z).
  Hypothesis HAF : Forall (mfact_ok asegs V m) (asan_argv_facts r).
  Notation usp := (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat)).

  Lemma argv_ptrs_init :
       bytes_at asegs m (usp + 8) (word_to_le_bytes 8 (Z_to_bv 64
         (32768 * V 0%nat + (8 * V 1%nat + (8 * V 2%nat + (V 4%nat + (16 * V 6%nat + (4096 * V 10%nat + 8 * V 11%nat)))))
          + (472 + 32 * r))))
    /\ bytes_at asegs m (usp + 16) (word_to_le_bytes 8 (Z_to_bv 64
         (Z.b2z ((1 mod two64) <? (V 1%nat mod two64))
          * (32768 * V 0%nat + (8 * V 1%nat + (8 * V 2%nat + (V 3%nat + (V 4%nat + (16 * V 6%nat + (4096 * V 10%nat + 8 * V 11%nat))))))
             + (473 + 32 * r))))).
  Proof.
    unfold asan_argv_facts, argv0_z, argv1_z, usp_z in HAF.
    apply Forall_cons_iff in HAF as [H0 HAF]. apply Forall_cons_iff in HAF as [H1 _].
    cbn [mfact_ok zv cellw] in H0, H1. split; [exact H0| exact H1].
  Qed.
End ArgvPtrs727.
Lemma firstn_add_split : forall {A} (a b : nat) (l : list A), firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  intros A a b l. revert l. induction a as [|a IH]; intros l; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct b; reflexivity| f_equal; apply IH].
Qed.

Lemma bytes_at_agree : forall (m m' : word -> option byte) a bs,
  bytes_at asegs m a bs -> (forall z, a <= z < a + Z.of_nat (length bs) -> m' (wa z) = m (wa z)) -> bytes_at asegs m' a bs.
Proof.
  intros m m' a bs (A & B & H) AG. split; [exact A|]. split; [exact B|]. intros i Hi.
  unfold mrd. rewrite (AG (a + Z.of_nat i)) by lia. apply (H i Hi).
Qed.

(* the strings block of 's entry block (StackLayout.build_stack_bytes): the argv and
   envp strings, the exec name, its NUL and an 8-byte zero slot, from Lib/InitMem's str_base up to the stack VMA's
   end [ed_top draw]. *)
Section StringBlock.
  Variables (inp : ProcInput) (mbase : word) (ph : PhdrInfo) (entry sp : word) (draw : EntryDraw) (m : word -> option byte).
  Notation usp := (bv_unsigned sp).
  Notation top := (ed_top draw).
  Notation argv := (in_argv inp).
  Notation envp := (in_envp inp).
  Notation execfn := (in_execfn inp).
  Notation m0 := (wrap_mem inp mbase ph entry sp draw).
  Definition SBLK : list byte :=
    flatten_strings argv ++ flatten_strings envp ++ execfn ++ [Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 8.
  Notation SB := (str_base top argv envp execfn).

  Lemma SBLK_length : Z.of_nat (length SBLK) = lsb argv envp execfn + 8.
  Proof.
    unfold SBLK. rewrite !length_app, repeat_length. cbn [length]. rewrite lsb_eq.
    pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp). lia.
  Qed.

  Lemma SBLK_end : SB + Z.of_nat (length SBLK) = bv_unsigned top.
  Proof. rewrite SBLK_length. unfold str_base. lia. Qed.

  Hypothesis G : geom_ok (kb_rseq (in_kernel inp)) sp top argv envp execfn.
  Hypothesis IMGHI : usp + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw)) <= 2^64.
  Hypothesis T8 : bv_unsigned top mod 8 = 0.
  Hypothesis HID : forall z, SB <= z < SB + Z.of_nat (length SBLK) -> m (wa z) = m0 (wa z).

  Lemma SBLK_at : bytes_at asegs m SB SBLK.
  Proof.
    eapply bytes_at_agree; [| exact HID].
    pose proof (init_stack_bytes asegs inp mbase ph entry sp draw IMGHI) as B.
    change (entry_stack_image inp mbase ph entry sp draw) with
      (build_stack_bytes (launch_auxv inp sp mbase) ph entry sp top argv envp execfn (in_uid inp) (in_gid inp) (in_hwcap inp) draw) in B.
    rewrite build_stack_bytes_eq in B.
    do 9 (apply bytes_at_app in B; destruct B as [_ B]).
    unfold SBLK. eapply bytes_at_eqa; [exact B|].
    rewrite !length_le8, !u64s_length, argv_ptrs_length, envp_ptrs_length, auxv_words_length, !repeat_length.
    rewrite at_random_bytes_split, length_app, !length_le8.
    change (la_rseq (launch_auxv inp sp mbase)) with (kb_rseq (in_kernel inp)).
    pose proof (pad_len_eq _ _ _ _ _ _ G) as PL. pose proof (head_len_eq (kb_rseq (in_kernel inp)) argv envp) as HL.
    unfold str_base. unfold argc, envc in HL. lia.
  Qed.

  Lemma arg_string : forall i s, nth_error argv i = Some s ->
    exists off, nth_error (str_ptrs SB argv) i = Some (SB + off) /\ 0 <= off /\
      let P := SB + off in
      let k := (- (P + Z.of_nat (length s) + 1)) mod 8 in
      exists slack : list byte, zlength slack = k /\ P + Z.of_nat (length s) + 1 + k <= bv_unsigned top - 8
        /\ bytes_at asegs m P (s ++ Z_to_bv 8 0 :: slack).
  Proof.
    intros i s Hn. destruct (str_ptrs_nth argv SB i s Hn) as (off & Hp & Ho & Ht & Hf).
    exists off. split; [exact Hp|]. split; [exact Ho|]. cbv zeta.
    pose proof SBLK_length as SL. pose proof (lsb_eq argv envp execfn) as LE.
    pose proof (total_arg_bytes_nonneg envp) as TE.
    set (k := (- (SB + off + Z.of_nat (length s) + 1)) mod 8).
    assert (Hk : 0 <= k < 8) by (subst k; Z.div_mod_to_equations; lia).
    assert (FIT : SB + off + Z.of_nat (length s) + 1 + k <= bv_unsigned top - 8).
    { subst k. unfold str_base in *. Z.div_mod_to_equations. lia. }
    exists (firstn (Z.to_nat k) (skipn (Z.to_nat off + (length s + 1)) SBLK)).
    assert (LS : (Z.to_nat off + (length s + 1) + Z.to_nat k <= length SBLK)%nat) by (unfold str_base in FIT; lia).
    split. { unfold zlength. rewrite firstn_length, length_skipn. lia. }
    split; [exact FIT|].
    pose proof (bytes_at_slice asegs m SB SBLK (Z.to_nat off) (length s + 1 + Z.to_nat k) SBLK_at ltac:(lia)) as B.
    rewrite Z2Nat.id in B by lia. rewrite firstn_add_split in B. rewrite skipn_skipn in B || rewrite <- skipn_add in B || idtac.
    eapply bytes_at_ext; [exact B|].
    replace (length s + 1 + Z.to_nat off)%nat with (Z.to_nat off + (length s + 1))%nat by lia.
    replace (firstn (length s + 1) (skipn (Z.to_nat off) SBLK)) with (s ++ [Z_to_bv 8 0]); [rewrite <- app_assoc; reflexivity|].
    symmetry. unfold SBLK. rewrite skipn_app, firstn_app.
    pose proof (flatten_strings_length argv) as FL.
    rewrite Hf. rewrite length_skipn.
    replace (length s + 1 - (length (flatten_strings argv) - Z.to_nat off))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
  Qed.
End StringBlock.
End CANSEC4.
Ltac lit_divs := repeat match goal with |- context [?a / ?b] =>
  let v := eval vm_compute in (a / b) in lazymatch v with Zpos _ => change (a / b) with v | Z0 => change (a / b) with v end end.

Section CANSEC5. Context {rc : runConstT}.
Section VisRng.
  Variables (lz : list (word * word)) (AL : word -> Prop) (V : nat -> Z).
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.

  Lemma page_base_of_val : forall z, 0 <= z < 2^64 -> bv_unsigned (page_base_of z) = z / 4096 * 4096.
  Proof.
    clear A0I HP HAT. intros z Hz. unfold page_base_of, page_size. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
    unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). Z.div_mod_to_equations. lia.
  Qed.

  Lemma vis_rng_gen : forall b n lo len,
    In (pagedown b, pageup (b + n)) (allow_of 2147450880 V asan_vis) ->
    b <= lo -> lo + len <= b + n -> 0 <= lo -> lo + len <= 2^64 ->
    rng (fp_ok lz AL) lo len.
  Proof.
    clear HP HAT. intros b n lo len HIN H1 H2 H3 H4. apply rng_fp_ok_allowed; [lia| lia|].
    intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(lia)) as PV.
    apply A0I; [rewrite PV; Z.div_mod_to_equations; lia|].
    exists (pagedown b, pageup (b + n)). split; [exact HIN|]. cbn [fst snd]. rewrite PV. unfold pagedown, pageup.
    Z.div_mod_to_equations. nia.
  Qed.

  Lemma allow_in_app : forall k bn, nth_error asan_vis k = Some bn ->
    In (pagedown (zv V (fst bn)), pageup (zv V (fst bn) + zv V (snd bn))) (allow_of 2147450880 V asan_vis)
    /\ In (pagedown (2147450880 + zv V (fst bn) / 8), pageup (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8)) (allow_of 2147450880 V asan_vis).
  Proof.
    clear A0I HP HAT. intros k bn Hk. unfold allow_of. split; apply in_flat_map; exists bn; split; try (eapply nth_error_In; exact Hk); cbn; tauto.
  Qed.

  Lemma vis_rng : forall k bn lo len, nth_error asan_vis k = Some bn ->
    zv V (fst bn) <= lo -> lo + len <= zv V (fst bn) + zv V (snd bn) -> 0 <= lo -> lo + len <= 2^64 -> rng (fp_ok lz AL) lo len.
  Proof. clear HP HAT. intros k bn lo len Hk H1 H2 H3 H4. eapply vis_rng_gen; [exact (proj1 (allow_in_app k bn Hk))| lia| lia| lia| lia]. Qed.

  Lemma vis_rng_sh : forall k bn lo len, nth_error asan_vis k = Some bn ->
    2147450880 + zv V (fst bn) / 8 <= lo -> lo + len <= 2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8 -> 0 <= lo -> lo + len <= 2^64 ->
    rng (fp_ok lz AL) lo len.
  Proof.
    clear HP HAT. intros k bn lo len Hk H1 H2 H3 H4.
    eapply (vis_rng_gen (2147450880 + zv V (fst bn) / 8) ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8));
      [| lia| lia| lia| lia].
    replace (2147450880 + zv V (fst bn) / 8 + ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8)) with (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8) by lia.
    exact (proj2 (allow_in_app k bn Hk)).
  Qed.

  Lemma rng_image : forall lo len, 0x10000 <= lo -> lo + len <= 0x5f7000 -> rng (fp_ok lz AL) lo len.
  Proof. clear HP HAT. intros lo len H1 H2. eapply (vis_rng 11); [reflexivity| cbn; lia| cbn; lia| lia| lia]. Qed.
  Lemma rng_image_sh : forall lo len, 0x7fffa000 <= lo -> lo + len <= 0x800b6e00 -> rng (fp_ok lz AL) lo len.
  Proof. clear HP HAT. intros lo len H1 H2. eapply (vis_rng_sh 11); [reflexivity| cbn; lit_divs; lia| cbn; lit_divs; lia| lia| lia]. Qed.
  Lemma rng_stackside : forall lo len, ATOP <= lo -> lo + len <= 2^47 -> rng (fp_ok lz AL) lo len.
  Proof.
    intros lo len H1 H2. atop_facts. pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
    eapply (vis_rng 12); [reflexivity| cbn; lia| cbn; lia| lia| lia].
  Qed.
  Lemma rng_stackside_sh : forall lo len, shad ATOP <= lo -> lo + len <= 17594333495296 -> rng (fp_ok lz AL) lo len.
  Proof.
    intros lo len H1 H2. atop_facts. pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
    rewrite shad_div in H1. unfold AsanEmbed.ASHOFF in H1.
    eapply (vis_rng_sh 12); [reflexivity| cbn -[Z.div Z.mul Z.add]; Z.div_mod_to_equations; lia| cbn -[Z.div Z.mul Z.add]; Z.div_mod_to_equations; lia| lia| lia].
  Qed.
  Lemma rng_empty : forall b, 0 <= b <= 2^64 -> rng (fp_ok lz AL) b 0.
  Proof. clear A0I HP HAT. intros b Hb. apply rng_fp_ok; [lia| lia|]. intros z Hz. lia. Qed.
End VisRng.
(* ArgPack over 's strings block (StringBlock above): the same conclusion per argv
   string, with SB = Lib/InitMem's str_base of the stack VMA's end. *)
Section ArgPack.
  Variables (V : nat -> Z) (inp : ProcInput) (mbase : word) (ph : PhdrInfo) (entry sp : word) (draw : EntryDraw)
            (m : word -> option byte).
  Notation usp := (bv_unsigned sp).
  Notation top := (ed_top draw).
  Notation argv := (in_argv inp).
  Notation envp := (in_envp inp).
  Notation execfn := (in_execfn inp).
  Notation SB := (str_base top argv envp execfn).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis G : geom_ok (kb_rseq (in_kernel inp)) sp top argv envp execfn.
  Hypothesis IMGHI : usp + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw)) <= 2^64.
  Hypothesis T8 : bv_unsigned top mod 8 = 0.
  Hypothesis THI : bv_unsigned top <= 2^47.
  Hypothesis SPW : ATOP + 8388608 <= usp.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.
  Hypothesis HID : forall z, SB <= z < SB + Z.of_nat (length (SBLK inp)) -> m (wa z) = wrap_mem inp mbase ph entry sp draw (wa z).

  Definition round_dn64 (x : Z) : Z := x / 64 * 64.
  Definition round_up64 (x : Z) : Z := (x + 63) / 64 * 64.

  Lemma sb_ge : usp + 24 <= SB.
  Proof.
    pose proof (str_base_ge _ _ _ _ _ _ G) as SG. pose proof (head_len_ge (kb_rseq (in_kernel inp)) argv envp) as HG.
    unfold argc, envc in HG. lia.
  Qed.

  Lemma arg_pack : forall i s, nth_error argv i = Some s ->
    exists off (slack : list byte) (r : region),
      nth_error (str_ptrs SB argv) i = Some (SB + off) /\ 0 <= off
      /\ bytes_at asegs m (SB + off) (s ++ Z_to_bv 8 0 :: slack)
      /\ (- (SB + off + Z.of_nat (length s) + 1)) mod 8 <= zlength slack
      /\ usp + 24 <= SB + off
      /\ shclean m (r_lo r) (r_hi r) (r_rlo r) (r_rhi r) /\ r_lo r < r_hi r
      /\ inreg r (SB + off) (Z.of_nat (length s) + 1 + zlength slack)
      /\ usp + -112 <= r_rlo r /\ ATOP <= r_rlo r /\ r_rhi r <= 2^47
      /\ SB + off + Z.of_nat (length s) + 1 + zlength slack <= 2^47.
  Proof.
    intros i s Hn.
    destruct (arg_string inp mbase ph entry sp draw m G IMGHI T8 HID i s Hn) as (off & Hp & Ho & slack & SL & FIT & BY).
    cbv zeta in SL, FIT.
    pose proof sb_ge as SG. atop_facts.
    assert (LS : 0 <= zlength slack) by (unfold zlength; lia).
    assert (HE : SB + off + Z.of_nat (length s) + 1 + zlength slack <= 2^47 - 8) by lia.
    assert (D1 : SB + off - 63 <= round_dn64 (SB + off) <= SB + off /\ round_dn64 (SB + off) mod 64 = 0) by (unfold round_dn64; Z.div_mod_to_equations; lia).
    assert (U1 : SB + off + Z.of_nat (length s) + 1 + zlength slack <= round_up64 (SB + off + Z.of_nat (length s) + 1 + zlength slack) <= 2^47
                 /\ round_up64 (SB + off + Z.of_nat (length s) + 1 + zlength slack) mod 64 = 0) by (unfold round_up64; Z.div_mod_to_equations; lia).
    exists off, slack, (mkRegion (SB + off) (SB + off + Z.of_nat (length s) + 1 + zlength slack)
                                 (round_dn64 (SB + off)) (round_up64 (SB + off + Z.of_nat (length s) + 1 + zlength slack))).
    cbn [r_lo r_hi r_rlo r_rhi]. unfold inreg. cbn [r_lo r_hi].
    repeat match goal with |- _ /\ _ => split end; try exact Hp; try exact BY; try lia.
    apply (stack_shclean_init V m HM HP HAT); unfold Shadow.KEND; lia.
  Qed.
End ArgPack.
End CANSEC5.
