(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem Mem Cells Frame.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import DrvAgree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import MainExport MainFactsBoth. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.X1W.AS Require Import MainEntryBoth.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.X1W Require Import BothMain.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg ABytes StdioFiles Stdio_kit Stdio_iface F_syscalls AExit F_module_dtor AHarness_iface ADriver_iface.  (* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From Stdlib Require Uint63.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require HexScanFast RwZeroFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
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
Ltac mf V m HM f H := pose proof (mfact_find bsegs V m _ f HM ltac:(vm_compute; reflexivity)) as H; cbn [mfact_ok zv cellw] in H.
Ltac pf V HP f H := pose proof (ho_pfact_find V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma aimg_chunk : forall V m (l : list mfact) A cs,
  Forall (mfact_ok bsegs V m) l ->
  existsb (fun f => match f with MImg lo' hi' => (lo' <=? A) && (A + Z.of_nat (cells_size cs) <=? hi') | _ => false end) l = true ->
  cells_wf cs -> rw_bytes_b bsegs A (cells_bytes cs) = true -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2^64 ->
  rw_cells bsegs m A cs.
Proof.
  intros V m l A cs HM HE WF HB HA HHI.
  pose proof (cells_bytes_length cs WF) as LEN.
  assert (R : forall i, A <= i < A + Z.of_nat (cells_size cs) -> m (wa i) = None).
  { eapply mimg_cover; [exact HM| exact HE]. }
  eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m A (cells_bytes cs))| exact WF| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| cbn; rewrite LEN, Nat.add_0_r; reflexivity].
  - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply R. rewrite LEN in Ha. lia.
  - exact HB.
  - exact HA.
  - rewrite LEN. exact HHI.
Qed.

(* [comment removed for export] *)
End CANSEC2.
Ltac aimg V m HM A cs H :=
  pose proof (aimg_chunk V m _ A cs HM ltac:(vm_compute; reflexivity) ltac:(cbn; repeat split; exact I)
                ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as H.

Notation z64 := (Z_to_bv 64 0).

(* [comment removed for export] *)
Section CANSEC3. Context {rc : runConstT}.
Lemma stderr_wfile0_init : forall V m, Forall (mfact_ok bsegs V m) both_mem_facts -> stderr_wfile0 m.
Proof.
  intros V m HM. exists (Z_to_bv 64 5), z64, 0, 0, (repeat (Z_to_bv 8 0) 80).
  split; [| split; [vm_compute; reflexivity| split; [left; reflexivity| lia]]].
  aimg V m HM 0xd5958 (file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE 0x67d400 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) H. exact H.
Qed.

Lemma stdout_file_init : forall V m, Forall (mfact_ok bsegs V m) both_mem_facts -> stdout_file m stdout_init.
Proof.
  intros V m HM. exists (Z_to_bv 64 5), z64, (repeat (Z_to_bv 8 0) 80), (repeat (Z_to_bv 8 0) 1024).
  cbn [so_active so_buf so_lbf_nl so_first stdout_init Prelim.zlength length Z.of_nat Z.add].
  split. { aimg V m HM 0xd5a48 (file_cells (Z_to_bv 64 5) 0 0 0 F_STDOUT_WRITE 0x67d408 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) H. exact H. }
  split; [vm_compute; reflexivity|].
  split. { aimg V m HM 0x67d408 [CB 1024 (repeat (Z_to_bv 8 0) 1024)] H. exact H. }
  split; [reflexivity|]. split; [unfold zlength; cbn; lia| intros _; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma canary_seg_bytes : forall k, (k < 8)%nat ->      (* [comment removed for export] *)
  segment_byte_at (seg_bytes Tgt_zlib_uncompress_fuzzer_both_segment_003) (0x67cd38 - 0xd3000 + N.of_nat k)%N = Some (Z_to_bv 8 0).
Proof. intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.
Lemma canary_wr_at : forall m, wr_at bsegs m 0x67cd38 8.
Proof.
  intros m. split; [lia|]. split; [lia|]. intros i Hi. unfold wview.
  destruct (m (wa (0x67cd38 + i))) as [b|] eqn:E; [discriminate|].
  rewrite wa_unsigned by lia. rewrite a_find_segment_1 by lia.
  destruct (Z.leb_spec0 0x10000 (0x67cd38 + i)); destruct (Z.leb_spec0 (0x67cd38 + i + 1) 0x3b000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0x3b000 (0x67cd38 + i)); destruct (Z.leb_spec0 (0x67cd38 + i + 1) 0xcd000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0xcd000 (0x67cd38 + i)); destruct (Z.leb_spec0 (0x67cd38 + i + 1) 0xd3000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0xd3000 (0x67cd38 + i)); destruct (Z.leb_spec0 (0x67cd38 + i + 1) 0x67f000); cbn [andb]; try lia.
  replace (seg_writable Tgt_zlib_uncompress_fuzzer_both_segment_003) with true by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Tgt_zlib_uncompress_fuzzer_both_segment_003)) with 0xd3000 by (vm_compute; reflexivity).
  replace (Z.to_N (0x67cd38 + i - 0xd3000)) with (0x67cd38 - 0xd3000 + N.of_nat (Z.to_nat i))%N by lia.
  rewrite canary_seg_bytes by lia. discriminate.
Qed.
Lemma ssp_guard_init : forall V m, Forall (mfact_ok bsegs V m) both_mem_facts -> rw_cells bsegs m ssp_guard [C8 (Z_to_bv 64 (V 45%nat))].
Proof.
  intros V m HM. mf V m HM (MRo (ZLit 6802744) 8 (ZV 45)) H. unfold ssp_guard.
  pose proof (cellw_bytes 8 (V 45%nat) eq_refl) as (Cb & Cs & Cwf). change (cellw 8 (V 45%nat)) with (C8 (Z_to_bv 64 (V 45%nat))) in Cb, Cs, Cwf.
  split.
  - split; [cbn; split; [exact Cwf| exact I]|]. cbn [cells_bytes]. rewrite app_nil_r, Cb. exact H.
  - cbn [cells_size]. rewrite Cs. apply canary_wr_at.
Qed.

Lemma errno_init : forall V m, Forall (mfact_ok bsegs V m) both_mem_facts -> rw_cells bsegs m 0x65cc54 [C4 z64].
Proof. intros V m HM. aimg V m HM 0x65cc54 [C4 z64] H. exact H. Qed.
(* [comment removed for export] *)
Lemma run_rw_cells : forall m A n (b : byte),
  0 <= n -> (forall i, 0 <= i < n -> m (wa (A + i)) = Some b) -> wr_at bsegs m A n ->
  rw_cells bsegs m A [CB (Z.to_nat n) (repeat b (Z.to_nat n))].
Proof.
  intros m A n b Hn Hz (W1 & W2 & W3). split.
  - split; [cbn; split; [rewrite repeat_length; reflexivity| exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite repeat_length, Z2Nat.id by lia; lia|].
    intros i Hi. rewrite repeat_length in Hi. rewrite (nth_error_repeat b Hi).
    unfold mrd. rewrite (Hz (Z.of_nat i) ltac:(lia)). reflexivity.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|]. exact W3.
Qed.

Lemma rw_cells_join : forall m A n1 n2 (j1 j2 : list byte),
  rw_cells bsegs m A [CB n1 j1] -> rw_cells bsegs m (A + Z.of_nat n1) [CB n2 j2] ->
  rw_cells bsegs m A [CB (n1 + n2)%nat (j1 ++ j2)].
Proof.
  intros m A n1 n2 j1 j2 H1 H2.
  pose proof H1 as [[[L1 _] _] _]. pose proof H2 as [[[L2 _] _] _]. cbn in L1, L2.
  assert (H : rw_cells bsegs m A ([CB n1 j1] ++ [CB n2 j2])).
  { apply (proj2 (rw_cells_app bsegs m A [CB n1 j1] [CB n2 j2])). split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2. }
  eapply rw_cells_recast; [exact H| cbn; split; [rewrite app_length; lia| exact I]| cbn [cells_bytes cbytes app]; rewrite !app_nil_r; reflexivity| cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma rw_C1_CB : forall m A (b : byte), rw_cells bsegs m A [C1 b] -> rw_cells bsegs m A [CB 1 [b]].
Proof. intros m A b H. eapply rw_cells_recast; [exact H| cbn; split; [reflexivity| exact I]| reflexivity| reflexivity]. Qed.

Lemma bytes_eq_of_unsigned : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hb Hbs. f_equal; [apply bv_eq; exact Hb| apply IH; exact Hbs].
Qed.

(* [comment removed for export] *)
Lemma rw_C8_C4 : forall m A (v lo hi : word),
  rw_cells bsegs m A [C8 v] -> cells_bytes [C4 lo; C4 hi] = cells_bytes [C8 v] -> rw_cells bsegs m A [C4 lo].
Proof.
  intros m A v lo hi H E.
  assert (H' : rw_cells bsegs m A ([C4 lo] ++ [C4 hi])).
  { eapply rw_cells_recast; [exact H| cbn; tauto| exact E| reflexivity]. }
  apply (proj1 (rw_cells_app bsegs m A _ _)) in H'. exact (proj1 H').
Qed.

Lemma wr_at_sub' : forall m a n a' n', wr_at bsegs m a n -> 0 <= a' -> a <= a' -> a' + n' <= a + n -> wr_at bsegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

End CANSEC3.
Ltac norm_addr := match goal with |- rw_cells _ _ ?A _ => let a := eval vm_compute in A in change A with a end.

(* [comment removed for export] *)
Section CANSEC4. Context {rc : runConstT}.
Lemma zchunk_pointwise : forall m A n, rw_cells bsegs m A [CB (Z.to_nat n) (zeros n)] -> 0x67f000 <= A ->
  forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 0).
Proof.
  intros m A n [[_ B] _] HA i Hi. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. destruct B as (B0 & B1 & B).
  unfold zeros in B1, B. rewrite repeat_length in B1, B.
  specialize (B (Z.to_nat i) ltac:(lia)).
  rewrite (nth_error_repeat (Z_to_bv 8 0)) in B by lia. rewrite Z2Nat.id in B by lia.
  rewrite ref_mrd_overlay in B; [exact B|]. right. rewrite wa_unsigned; lia.
Qed.

(* [comment removed for export] *)
Definition zlit_of (e : zexp) : option Z := match e with ZLit z => Some z | _ => None end.
Lemma zlit_of_zv : forall V e z, zlit_of e = Some z -> zv V e = z.
Proof. intros V e z H. destruct e; cbn in H; try discriminate. injection H as ->. reflexivity. Qed.
Definition mzero_covb (lo n : Z) (f : mfact) : bool :=
  match f with
  | MZero a n' => match zlit_of a with Some a' => (a' <=? lo) && (lo + n <=? a' + n') | None => false end
  | MZeroC a n' => match zlit_of a with Some a' => (0x67f000 <=? a') && ((a' <=? lo) && (lo + n <=? a' + n')) | None => false end
  | _ => false
  end.
Lemma mzero_cover : forall V m (l : list mfact) lo n,
  Forall (mfact_ok bsegs V m) l -> existsb (mzero_covb lo n) l = true ->
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
  Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) both_pure_facts.

  (* [comment removed for export] *)
  Let WSH : wr_at bsegs m 0x7fffa000 0xcde00.
  Proof. mf V m HM (MWr (ZLit 2147459072) 843264) H. exact H. Qed.
  (* [comment removed for export] *)
  Lemma sh_zero1 : forall i, 0 <= i < 9452 -> m (wa (2147459072 + i)) = Some (Z_to_bv 8 0).
  Proof. mf V m HM (MZero (ZLit 2147459072) 9452) H. exact H. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rwz_fast : forall A n, 0xd3000 <= A -> 0 <= n -> A + n <= 0x67f000 ->
    HexScanFast.scanP (HexScanFast.byte_zeroI Tgt_zlib_uncompress_fuzzer_both_seg_bytes_003) 64 (Uint63.of_Z (A - 0xd3000)) (Uint63.of_Z n) = true ->
    rw_bytes_b bsegs A (repeat (Z_to_bv 8 0) (Z.to_nat n)) = true.
  Proof.
    apply (RwZeroFast.rw_bytes_b_zero_fast bsegs Tgt_zlib_uncompress_fuzzer_both_segment_003 Tgt_zlib_uncompress_fuzzer_both_seg_bytes_003 0xd3000 0x67f000);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | intros z H1 H2; rewrite a_find_segment_1 by lia;
        repeat match goal with |- context [(?a <=? z) && (z + 1 <=? ?b)] =>
          first [ replace ((a <=? z) && (z + 1 <=? b)) with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia)
                | replace ((a <=? z) && (z + 1 <=? b)) with false by (symmetry; apply andb_false_iff; first [left; apply Z.leb_gt; lia | right; apply Z.leb_gt; lia]) ] end;
        reflexivity
      | lia ].
  Qed.
  Lemma img_zero_chunk : forall A n,
    existsb (fun f => match f with MImg lo' hi' => (lo' <=? A) && (A + n <=? hi') | _ => false end) both_mem_facts = true ->
    rw_bytes_b bsegs A (repeat (Z_to_bv 8 0) (Z.to_nat n)) = true -> 0 <= A -> 0 <= n -> A + n <= 2^64 ->
    rw_cells bsegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
  Proof.
    intros A n HE HB HA Hn HHI.
    pose proof (rw_cells_image0 bsegs m A (repeat (Z_to_bv 8 0) (Z.to_nat n))) as K. rewrite repeat_length in K. apply K.
    - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply (mimg_cover bsegs V m _ A (A + n) HM HE). rewrite Z2Nat.id in Ha by lia. lia.
    - exact HB.
    - exact HA.
    - rewrite Z2Nat.id by lia. exact HHI.
  Qed.
  Lemma sh_tab1 : forall i, 0 <= i < 256 -> m (wa (2147469580 + i)) = Some (Z_to_bv 8 0).
  Proof. exact (mzero_cover V m _ 2147469580 256 HM ltac:(vm_compute; reflexivity)). Qed.
  Lemma sh_tab2 : forall i, 0 <= i < 16 -> m (wa (2147469900 + i)) = Some (Z_to_bv 8 0).
  Proof. exact (mzero_cover V m _ 2147469900 16 HM ltac:(vm_compute; reflexivity)). Qed.
  Lemma sh_tab3 : forall i, 0 <= i < 4 -> m (wa (2147468552 + i)) = Some (Z_to_bv 8 0).
  Proof. exact (mzero_cover V m _ 2147468552 4 HM ltac:(vm_compute; reflexivity)). Qed.
  Lemma sh_tab4 : shadow_bytes m 2147468556 2147468557 (fun _ => 6).      (* [comment removed for export] *)
  Proof. mf V m HM (MCell (ZLit 2147468556) 1 (ZLit 6)) K1. apply (shadow_bytes_of_rw_cells_C1 bsegs m 2147468556 6 K1). intros z Hz. apply ref_find_segment_none; lia. Qed.
  Lemma sh_tab5 : forall i, 0 <= i < 7 -> m (wa (2147469532 + i)) = Some (Z_to_bv 8 0).
  Proof. exact (mzero_cover V m _ 2147469532 7 HM ltac:(vm_compute; reflexivity)). Qed.
  Lemma sh_tab6 : shadow_bytes m 2147469539 2147469540 (fun _ => 6).      (* [comment removed for export] *)
  Proof. mf V m HM (MCell (ZLit 2147469539) 1 (ZLit 6)) K1. apply (shadow_bytes_of_rw_cells_C1 bsegs m 2147469539 6 K1). intros z Hz. apply ref_find_segment_none; lia. Qed.
  Lemma sh_tab7 : forall i, 0 <= i < 7 -> m (wa (2147469544 + i)) = Some (Z_to_bv 8 0).
  Proof. exact (mzero_cover V m _ 2147469544 7 HM ltac:(vm_compute; reflexivity)). Qed.
  Lemma sh_tab8 : shadow_bytes m 2147469551 2147469552 (fun _ => 6).      (* [comment removed for export] *)
  Proof. mf V m HM (MCell (ZLit 2147469551) 1 (ZLit 6)) K1. apply (shadow_bytes_of_rw_cells_C1 bsegs m 2147469551 6 K1). intros z Hz. apply ref_find_segment_none; lia. Qed.
  Lemma sh_tab9 : forall i, 0 <= i < 8 -> m (wa (2147469556 + i)) = Some (Z_to_bv 8 0).
  Proof. exact (mzero_cover V m _ 2147469556 8 HM ltac:(vm_compute; reflexivity)). Qed.
  Lemma sh_tab10 : forall i, 0 <= i < 8 -> m (wa (2147469568 + i)) = Some (Z_to_bv 8 0).
  Proof. exact (mzero_cover V m _ 2147469568 8 HM ltac:(vm_compute; reflexivity)). Qed.
  Lemma sh_tab11 : shadow_bytes m 2147468524 2147468525 (fun _ => 4).      (* [comment removed for export] *)
  Proof. mf V m HM (MCell (ZLit 2147468524) 1 (ZLit 4)) K1. apply (shadow_bytes_of_rw_cells_C1 bsegs m 2147468524 4 K1). intros z Hz. apply ref_find_segment_none; lia. Qed.
  Lemma sh_tab12 : forall i, 0 <= i < 32768 -> m (wa (2148243512 + i)) = Some (Z_to_bv 8 0).
  Proof. exact (mzero_cover V m _ 2148243512 32768 HM ltac:(vm_compute; reflexivity)). Qed.
  Lemma sh_zero4 : forall i, 0 <= i < 2148243512 - 2148235312 -> m (wa (2148235312 + i)) = Some (Z_to_bv 8 0).      (* [comment removed for export] *)
  Proof. exact (mzero_cover V m _ 2148235312 (2148243512 - 2148235312) HM ltac:(vm_compute; reflexivity)). Qed.
  Lemma sh_zero5 : forall i, 0 <= i < 2148301576 - 2148301440 -> m (wa (2148301440 + i)) = Some (Z_to_bv 8 0).      (* [comment removed for export] *)
  Proof. exact (mzero_cover V m _ 2148301440 (2148301576 - 2148301440) HM ltac:(vm_compute; reflexivity)). Qed.

  (* [comment removed for export] *)
  Lemma zrun_chunk : forall base len A n,
    (forall i, 0 <= i < len -> m (wa (base + i)) = Some (Z_to_bv 8 0)) ->
    base <= A -> 0 <= n -> A + n <= base + len -> 0x7fffa000 <= A -> A + n <= 0x7fffa000 + 0xcde00 ->
    rw_cells bsegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
  Proof.
    intros base len A n Hz H1 H2 H3 H4 H5. apply run_rw_cells; [lia| | eapply wr_at_sub'; [exact WSH| lia| lia| lia]].
    intros i Hi. replace (A + i) with (base + (A - base + i)) by lia. apply Hz. lia.
  Qed.
  Lemma fill_chunk : forall A n c,
    (forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 c)) -> 0 <= n -> 0x7fffa000 <= A -> A + n <= 0x7fffa000 + 0xcde00 ->
    rw_cells bsegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].
  Proof. intros A n c Hf H2 H4 H5. apply run_rw_cells; [lia| exact Hf| eapply wr_at_sub'; [exact WSH| lia| lia| lia]]. Qed.

  (* [comment removed for export] *)
  Lemma astat_shg0 : exists j, rw_cells bsegs m 0x7fffc4ec [CB 4 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468524) 1 (ZLit 4)) K1.
    mf V m HM (MFill (ZLit 2147468525) 3 249) F1.
    eexists. change 4%nat with (1 + 3)%nat.
    eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 3 249 F1); lia.
  Qed.
  Lemma astat_shg1 : exists j, rw_cells bsegs m 0x7fffc508 [CB 12 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468556) 1 (ZLit 6)) K1.
    mf V m HM (MFill (ZLit 2147468557) 7 249) F1.
    eexists. change 12%nat with (4 + (1 + 7))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468552 4 2147468552 4 (mzero_cover V m _ 2147468552 4 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 7 249 F1); lia.
  Qed.
  Lemma astat_shg2 : exists j, rw_cells bsegs m 0x7fffc514 [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468566) 1 (ZLit 7)) K1.
    mf V m HM (MFill (ZLit 2147468567) 5 249) F1.
    eexists. change 8%nat with (2 + (1 + 5))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468564 2 2147468564 2 (mzero_cover V m _ 2147468564 2 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 5 249 F1); lia.
  Qed.
  Lemma astat_shg3 : exists j, rw_cells bsegs m 0x7fffc51c [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468575) 1 (ZLit 3)) K1.
    mf V m HM (MFill (ZLit 2147468576) 4 249) F1.
    eexists. change 8%nat with (3 + (1 + 4))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468572 3 2147468572 3 (mzero_cover V m _ 2147468572 3 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 4 249 F1); lia.
  Qed.
  Lemma astat_shg4 : exists j, rw_cells bsegs m 0x7fffc524 [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468582) 1 (ZLit 4)) K1.
    mf V m HM (MFill (ZLit 2147468583) 5 249) F1.
    eexists. change 8%nat with (2 + (1 + 5))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468580 2 2147468580 2 (mzero_cover V m _ 2147468580 2 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 5 249 F1); lia.
  Qed.
  Lemma astat_shg5 : exists j, rw_cells bsegs m 0x7fffc52c [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468591) 1 (ZLit 1)) K1.
    mf V m HM (MFill (ZLit 2147468592) 4 249) F1.
    eexists. change 8%nat with (3 + (1 + 4))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468588 3 2147468588 3 (mzero_cover V m _ 2147468588 3 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 4 249 F1); lia.
  Qed.
  Lemma astat_shg6 : exists j, rw_cells bsegs m 0x7fffc534 [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468598) 1 (ZLit 4)) K1.
    mf V m HM (MFill (ZLit 2147468599) 5 249) F1.
    eexists. change 8%nat with (2 + (1 + 5))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468596 2 2147468596 2 (mzero_cover V m _ 2147468596 2 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 5 249 F1); lia.
  Qed.
  Lemma astat_shg7 : exists j, rw_cells bsegs m 0x7fffc53c [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468606) 1 (ZLit 3)) K1.
    mf V m HM (MFill (ZLit 2147468607) 5 249) F1.
    eexists. change 8%nat with (2 + (1 + 5))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468604 2 2147468604 2 (mzero_cover V m _ 2147468604 2 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 5 249 F1); lia.
  Qed.
  Lemma astat_shg8 : exists j, rw_cells bsegs m 0x7fffc544 [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468615) 1 (ZLit 5)) K1.
    mf V m HM (MFill (ZLit 2147468616) 4 249) F1.
    eexists. change 8%nat with (3 + (1 + 4))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468612 3 2147468612 3 (mzero_cover V m _ 2147468612 3 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 4 249 F1); lia.
  Qed.
  Lemma astat_shg9 : exists j, rw_cells bsegs m 0x7fffc54c [CB 12 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468624) 1 (ZLit 4)) K1.
    mf V m HM (MFill (ZLit 2147468625) 7 249) F1.
    eexists. change 12%nat with (4 + (1 + 7))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468620 4 2147468620 4 (mzero_cover V m _ 2147468620 4 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 7 249 F1); lia.
  Qed.
  Lemma astat_shg10 : exists j, rw_cells bsegs m 0x7fffc558 [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468635) 1 (ZLit 1)) K1.
    mf V m HM (MFill (ZLit 2147468636) 4 249) F1.
    eexists. change 8%nat with (3 + (1 + 4))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468632 3 2147468632 3 (mzero_cover V m _ 2147468632 3 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 4 249 F1); lia.
  Qed.
  Lemma astat_shg11 : exists j, rw_cells bsegs m 0x7fffc560 [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468643) 1 (ZLit 2)) K1.
    mf V m HM (MFill (ZLit 2147468644) 4 249) F1.
    eexists. change 8%nat with (3 + (1 + 4))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468640 3 2147468640 3 (mzero_cover V m _ 2147468640 3 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 4 249 F1); lia.
  Qed.
  Lemma astat_shg12 : exists j, rw_cells bsegs m 0x7fffc568 [CB 12 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468652) 1 (ZLit 5)) K1.
    mf V m HM (MFill (ZLit 2147468653) 7 249) F1.
    eexists. change 12%nat with (4 + (1 + 7))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468648 4 2147468648 4 (mzero_cover V m _ 2147468648 4 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 7 249 F1); lia.
  Qed.
  Lemma astat_shg13 : exists j, rw_cells bsegs m 0x7fffc574 [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468663) 1 (ZLit 4)) K1.
    mf V m HM (MFill (ZLit 2147468664) 4 249) F1.
    eexists. change 8%nat with (3 + (1 + 4))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468660 3 2147468660 3 (mzero_cover V m _ 2147468660 3 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 4 249 F1); lia.
  Qed.
  Lemma astat_shg14 : exists j, rw_cells bsegs m 0x7fffc57c [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468670) 1 (ZLit 6)) K1.
    mf V m HM (MFill (ZLit 2147468671) 5 249) F1.
    eexists. change 8%nat with (2 + (1 + 5))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468668 2 2147468668 2 (mzero_cover V m _ 2147468668 2 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 5 249 F1); lia.
  Qed.
  Lemma astat_shg15 : exists j, rw_cells bsegs m 0x7fffc584 [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468679) 1 (ZLit 4)) K1.
    mf V m HM (MFill (ZLit 2147468680) 4 249) F1.
    eexists. change 8%nat with (3 + (1 + 4))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468676 3 2147468676 3 (mzero_cover V m _ 2147468676 3 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 4 249 F1); lia.
  Qed.
  Lemma astat_shg16 : exists j, rw_cells bsegs m 0x7fffc58c [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468686) 1 (ZLit 6)) K1.
    mf V m HM (MFill (ZLit 2147468687) 5 249) F1.
    eexists. change 8%nat with (2 + (1 + 5))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468684 2 2147468684 2 (mzero_cover V m _ 2147468684 2 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 5 249 F1); lia.
  Qed.
  Lemma astat_shg17 : exists j, rw_cells bsegs m 0x7fffc594 [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468695) 1 (ZLit 6)) K1.
    mf V m HM (MFill (ZLit 2147468696) 4 249) F1.
    eexists. change 8%nat with (3 + (1 + 4))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468692 3 2147468692 3 (mzero_cover V m _ 2147468692 3 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 4 249 F1); lia.
  Qed.
  Lemma astat_shg18 : exists j, rw_cells bsegs m 0x7fffc59c [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468702) 1 (ZLit 5)) K1.
    mf V m HM (MFill (ZLit 2147468703) 5 249) F1.
    eexists. change 8%nat with (2 + (1 + 5))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468700 2 2147468700 2 (mzero_cover V m _ 2147468700 2 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 5 249 F1); lia.
  Qed.
  Lemma astat_shg19 : exists j, rw_cells bsegs m 0x7fffc5a4 [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147468710) 1 (ZLit 7)) K1.
    mf V m HM (MFill (ZLit 2147468711) 5 249) F1.
    eexists. change 8%nat with (2 + (1 + 5))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468708 2 2147468708 2 (mzero_cover V m _ 2147468708 2 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 5 249 F1); lia.
  Qed.
  Lemma astat_shg20 : exists j, rw_cells bsegs m 0x7fffc90c [CB 320 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MFill (ZLit 2147469836) 64 249) F1.
    eexists. change 320%nat with (256 + 64)%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147469580 256 2147469580 256 (mzero_cover V m _ 2147469580 256 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. apply (fill_chunk _ 64 249 F1); lia.
  Qed.
  Lemma astat_shg21 : exists j, rw_cells bsegs m 0x7fffca4c [CB 20 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MFill (ZLit 2147469916) 4 249) F1.
    eexists. change 20%nat with (16 + 4)%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147469900 16 2147469900 16 (mzero_cover V m _ 2147469900 16 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. apply (fill_chunk _ 4 249 F1); lia.
  Qed.
  Lemma astat_shg22 : exists j, rw_cells bsegs m 0x7fffc5b4 [CB 160 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MFill (ZLit 2147468852) 32 249) F1.
    eexists. change 160%nat with (128 + 32)%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468724 128 2147468724 128 (mzero_cover V m _ 2147468724 128 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. apply (fill_chunk _ 32 249 F1); lia.
  Qed.
  Lemma astat_shg23 : exists j, rw_cells bsegs m 0x7fffc654 [CB 640 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MFill (ZLit 2147469396) 128 249) F1.
    eexists. change 640%nat with (512 + 128)%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147468884 512 2147468884 512 (mzero_cover V m _ 2147468884 512 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. apply (fill_chunk _ 128 249 F1); lia.
  Qed.
  Lemma astat_shg24 : exists j, rw_cells bsegs m 0x7fffc8dc [CB 12 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147469539) 1 (ZLit 6)) K1.
    mf V m HM (MFill (ZLit 2147469540) 4 249) F1.
    eexists. change 12%nat with (7 + (1 + 4))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147469532 7 2147469532 7 (mzero_cover V m _ 2147469532 7 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 4 249 F1); lia.
  Qed.
  Lemma astat_shg25 : exists j, rw_cells bsegs m 0x7fffc8e8 [CB 12 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147469551) 1 (ZLit 6)) K1.
    mf V m HM (MFill (ZLit 2147469552) 4 249) F1.
    eexists. change 12%nat with (7 + (1 + 4))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147469544 7 2147469544 7 (mzero_cover V m _ 2147469544 7 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 4 249 F1); lia.
  Qed.
  Lemma astat_shg26 : exists j, rw_cells bsegs m 0x7fffc8f4 [CB 12 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MFill (ZLit 2147469564) 4 249) F1.
    eexists. change 12%nat with (8 + 4)%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147469556 8 2147469556 8 (mzero_cover V m _ 2147469556 8 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. apply (fill_chunk _ 4 249 F1); lia.
  Qed.
  Lemma astat_shg27 : exists j, rw_cells bsegs m 0x7fffc900 [CB 12 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MFill (ZLit 2147469576) 4 249) F1.
    eexists. change 12%nat with (8 + 4)%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147469568 8 2147469568 8 (mzero_cover V m _ 2147469568 8 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. apply (fill_chunk _ 4 249 F1); lia.
  Qed.
  Lemma astat_shg28 : exists j, rw_cells bsegs m 0x7fffca68 [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147469931) 1 (ZLit 6)) K1.
    mf V m HM (MFill (ZLit 2147469932) 4 249) F1.
    eexists. change 8%nat with (3 + (1 + 4))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147469928 3 2147469928 3 (mzero_cover V m _ 2147469928 3 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 4 249 F1); lia.
  Qed.
  Lemma astat_shg29 : exists j, rw_cells bsegs m 0x7fffca70 [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147469938) 1 (ZLit 6)) K1.
    mf V m HM (MFill (ZLit 2147469939) 5 249) F1.
    eexists. change 8%nat with (2 + (1 + 5))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147469936 2 2147469936 2 (mzero_cover V m _ 2147469936 2 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 5 249 F1); lia.
  Qed.
  Lemma astat_shg30 : exists j, rw_cells bsegs m 0x7fffca78 [CB 8 j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MCell (ZLit 2147469947) 1 (ZLit 4)) K1.
    mf V m HM (MFill (ZLit 2147469948) 4 249) F1.
    eexists. change 8%nat with (3 + (1 + 4))%nat.
    eapply rw_cells_join; [apply (zrun_chunk 2147469944 3 2147469944 3 (mzero_cover V m _ 2147469944 3 HM ltac:(vm_compute; reflexivity))); lia|]. norm_addr. eapply rw_cells_join; [norm_addr; apply rw_C1_CB; exact K1|]. norm_addr. apply (fill_chunk _ 4 249 F1); lia.
  Qed.
  Lemma astat_shg31 : exists j, rw_cells bsegs m 0x800b9838 [CB (Z.to_nat 40960) j].      (* [comment removed for export] *)
  Proof.
    mf V m HM (MFill (ZLit 2148276280) 8192 249) F1.
    eexists. replace (Z.to_nat 40960) with (Z.to_nat 32768 + Z.to_nat 8192)%nat by (rewrite <- Z2Nat.inj_add by lia; f_equal).
    eapply rw_cells_join; [apply (zrun_chunk 2148243512 32768 2148243512 32768 (mzero_cover V m _ 2148243512 32768 HM ltac:(vm_compute; reflexivity))); lia|]. rewrite Z2Nat.id by lia. norm_addr. apply (fill_chunk _ 8192 249 F1); lia.
  Qed.
  Lemma astat_shd : exists j, rw_cells bsegs m 0x80012b8a [CB 256 j].      (* [comment removed for export] *)
  Proof. mf V m HM (MFill (ZLit 2147560330) 256 249) F1. eexists. apply (fill_chunk _ 256 249 F1); lia. Qed.

  Lemma gdesc_init :
       gdesc m 0xd5c50 0x22760 0x4 0x20 0x1d202 0x22780 (2^64 - 1)
    /\ gdesc m 0xd5c90 0x22840 0x26 0x60 0x19aaa 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd5cd0 0x228a0 0x17 0x40 0x1fcd3 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd5d10 0x228e0 0x1b 0x40 0x21dd6 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd5d50 0x22920 0x14 0x40 0x14bfa 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd5d90 0x22960 0x19 0x40 0x13a96 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd5dd0 0x229a0 0x14 0x40 0x1e2e8 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd5e10 0x229e0 0x13 0x40 0x1937f 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd5e50 0x22a20 0x1d 0x40 0x1b426 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd5e90 0x22a60 0x24 0x60 0x114ed 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd5ed0 0x22ac0 0x19 0x40 0x16df9 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd5f10 0x22b00 0x1a 0x40 0x20fd8 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd5f50 0x22b40 0x25 0x60 0x114f4 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd5f90 0x22ba0 0x1c 0x40 0x1ad36 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd5fd0 0x22be0 0x16 0x40 0x20fe0 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd6010 0x22c20 0x1c 0x40 0x1f1f8 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd6050 0x22c60 0x16 0x40 0x1d207 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd6090 0x22ca0 0x1e 0x40 0x1a532 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd60d0 0x22ce0 0x15 0x40 0x1c946 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd6110 0x22d20 0x17 0x40 0x11d18 0x22d60 (2^64 - 1)
    /\ gdesc m 0xd6150 0x22da0 0x400 0x500 0x15ef5 0x246a0 (2^64 - 1)
    /\ gdesc m 0xd6190 0x232a0 0x1000 0x1400 0x19386 0x246a0 (2^64 - 1)
    /\ gdesc m 0xd61d0 0x246e0 0x3e 0x60 0x11d20 0x25300 (2^64 - 1)
    /\ gdesc m 0xd6210 0x24740 0x3e 0x60 0x1dc16 0x25300 (2^64 - 1)
    /\ gdesc m 0xd6250 0x247a0 0x40 0x60 0x176c3 0x25300 (2^64 - 1)
    /\ gdesc m 0xd6290 0x24800 0x40 0x60 0x15eff 0x25300 (2^64 - 1)
    /\ gdesc m 0xd62d0 0x24860 0x800 0xa00 0x15482 0x25300 (2^64 - 1)
    /\ gdesc m 0xd6310 0x25260 0x80 0xa0 0x11d34 0x25300 (2^64 - 1)
    /\ gdesc m 0xd6350 0x25340 0x1e 0x40 0x1d202 0x25400 (2^64 - 1)
    /\ gdesc m 0xd6390 0x25380 0x16 0x40 0x1fcd3 0x25400 (2^64 - 1)
    /\ gdesc m 0xd63d0 0x253c0 0x1c 0x40 0x21dd6 0x25400 (2^64 - 1)
    /\ gdesc m 0xd6410 0x60c1c0 0x40000 0x50000 0x1c93f 0x22703 (2^64 - 1).
  Proof.
    unfold gdesc. change (2^64 - 1) with 18446744073709551615.
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with |- rw_cells _ _ ?A ?cs => aimg V m HM A cs H; exact H end.
  Qed.

  (* [comment removed for export] *)
  Lemma astat_cells :
       rw_cells bsegs m 0x65cc50 [C4 (Z_to_bv 64 (V 44%nat))]
    /\ rw_cells bsegs m 0x67cf68 [C4 (Z_to_bv 64 0)]
    /\ (exists cdt thr sec tm1, rw_cells bsegs m 0x67cf88 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
    /\ rw_cells bsegs m 0x16b9e0 [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m 0xd64d0 [C1 (Z_to_bv 8 0)]
    /\ (exists dso, rw_cells bsegs m 0xd3070 [C8 dso])
    /\ rw_cells bsegs m 0x67d3f0 [C8 (Z_to_bv 64 0)] /\ rw_cells bsegs m 0xd5c20 [C8 (Z_to_bv 64 0xd5b38)]
    /\ rw_cells bsegs m 0xd5b38 stdin_cells
    /\ rw_cells bsegs m 0xd5b30 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells bsegs m 0xd5a40 [C8 (Z_to_bv 64 RSTDERR)]
    /\ rw_cells bsegs m 0xd7350 [C4 (Z_to_bv 64 1)]
    /\ rw_cells bsegs m 0xd6480 [C8 (Z_to_bv 64 1)]
    /\ rw_cells bsegs m 0xd73f0 [C8 (Z_to_bv 64 0)].
  Proof.
    repeat match goal with |- _ /\ _ => split end.
    - mf V m HM (MCell (ZLit 6671440) 4 (ZV 44)) H. exact H.
    - aimg V m HM 0x67cf68 [C4 (Z_to_bv 64 0)] H. exact H.
    - mf V m HM (MCell (ZLit 6803336) 1 (ZLit 1)) H. aimg V m HM 0x67cf89 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] H2.
      exists (Z_to_bv 8 1), (Z_to_bv 8 0), (Z_to_bv 8 0), (Z_to_bv 64 0).
      apply (proj2 (rw_cells_app bsegs m 0x67cf88 [C1 (Z_to_bv 8 1)] _)). split; [exact H| exact H2].
    - aimg V m HM 0x16b9e0 [C1 (Z_to_bv 8 0)] H. exact H.
    - aimg V m HM 0xd64d0 [C1 (Z_to_bv 8 0)] H. exact H.
    - exists (Z_to_bv 64 0xd3070). aimg V m HM 0xd3070 [C8 (Z_to_bv 64 0xd3070)] H. exact H.
    - aimg V m HM 0x67d3f0 [C8 (Z_to_bv 64 0)] H. exact H.
    - aimg V m HM 0xd5c20 [C8 (Z_to_bv 64 0xd5b38)] H. exact H.
    - unfold stdin_cells. aimg V m HM 0xd5b38 [C4 (Z_to_bv 64 9); C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0xc2ff4); C8 z64; C8 z64; C8 z64; C8 z64;
   C8 (Z_to_bv 64 0xc3020); C8 z64; C8 (Z_to_bv 64 0xc3138); C8 (Z_to_bv 64 0x67d810); C8 (Z_to_bv 64 1024); C8 z64; C8 z64;
   C4 z64; C4 z64; C8 z64; C4 z64; C4 (Z_to_bv 64 0xffffffff)] H. exact H.
    - aimg V m HM 0xd5b30 [C8 (Z_to_bv 64 RSTDOUT)] H. exact H.
    - aimg V m HM 0xd5a40 [C8 (Z_to_bv 64 RSTDERR)] H. exact H.
    - mf V m HM (MCell (ZLit 881488) 8 (ZLit 72340168526266369)) H. eapply (rw_C8_C4 _ _ _ _ (Z_to_bv 64 0x01010100)); [exact H| apply bytes_eq_of_unsigned; vm_compute; reflexivity].
    - mf V m HM (MCell (ZLit 877696) 8 (ZLit 1)) H. exact H.
    - mf V m HM (MCell (ZLit 881648) 8 (ZLit 0)) H. exact H.
  Qed.
End HandoffFacts.
Section HandoffFacts2.
  Variables (V : nat -> Z) (m : word -> option byte).
  Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
  (* [comment removed for export] *)
  Notation usp := (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat)).
  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Lemma harness_sh_init : harness_invA m.
  Proof.
    clear HAT. unfold harness_invA, u2_tabsh, ver_sh.
    split. {
      split. { apply (sh_sub0 _ _ _ _ (sh_tab1 V m HM)); lia. }
      split. { apply (sh_sub0 _ _ _ _ (sh_tab2 V m HM)); lia. }
      split. { apply (sh_sub0 _ _ _ _ (sh_tab3 V m HM)); lia. }
      split. { exact (sh_tab4 V m HM). }
      split. { apply (sh_sub0 _ _ _ _ (sh_tab5 V m HM)); lia. }
      split. { exact (sh_tab6 V m HM). }
      split. { apply (sh_sub0 _ _ _ _ (sh_tab7 V m HM)); lia. }
      split. { exact (sh_tab8 V m HM). }
      split. { apply (sh_sub0 _ _ _ _ (sh_tab9 V m HM)); lia. }
      apply (sh_sub0 _ _ _ _ (sh_tab10 V m HM)); lia. }
    split. { exact (sh_tab11 V m HM). }
    split. { apply (sh_sub0 _ _ _ _ (sh_tab12 V m HM)); lia. }
    exists (repeat (Z_to_bv 8 0) (Z.to_nat 262144)). apply (img_zero_chunk V m HM 0x60c1c0 262144); [vm_compute; reflexivity| apply rwz_fast; [lia | lia | lia | vm_cast_no_check (eq_refl true)]| lia| lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rodata_sh0_init' : rodata_sh0 m.
  Proof.
    clear HAT. unfold rodata_sh0.
    replace (shad 0x10000) with 2147459072 by reflexivity. replace (shad 0x22740) with 2147468520 by reflexivity.
    split. { apply (sh_sub0 _ _ _ _ (sh_zero1 V m HM)); lia. }
    mf V m HM (MWr (ZLit 2147459072) 843264) W. eapply wr_at_sub'; [exact W| lia| lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rclean_stdout_buf_init : rclean m RBstdout.
  Proof.
    clear HAT. unfold RBstdout, rclean, shclean. cbn [r_lo r_hi r_rlo r_rhi].
    mf V m HM (MWr (ZLit 2147459072) 843264) W.
    replace (shad 0x67d400) with 2148301440 by reflexivity. replace (shad 0x67d840) with 2148301576 by reflexivity.
    split; [| lia]. split; [| split; [| split]].
    - eapply (unpoisoned_of_zero m 2148301441 2148301569 (fun _ => 0)); try reflexivity; try lia.
      all: try (rewrite ?shad_div; unfold AsanEmbed.ASHOFF; Z.div_mod_to_equations; lia).
      apply (sh_sub0 _ _ _ _ (sh_zero5 V m HM)); lia.
    - unfold hull64, Shadow.KEND. repeat split; try reflexivity; lia.
    - eapply wr_at_sub'; [exact W| lia| lia| lia].
    - unfold app_blk, Shadow.KLOW, Shadow.KHIGH, Shadow.KEND. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rclean_stage_init : rclean m RSTG.
  Proof.
    clear HAT. unfold RSTG, rclean, shclean. cbn [r_lo r_hi r_rlo r_rhi].
    mf V m HM (MWr (ZLit 2147459072) 843264) W.
    replace (shad 0x5fc180) with 2148235312 by reflexivity. replace (shad 0x60c1c0) with 2148243512 by reflexivity.
    split; [| lia]. split; [| split; [| split]].
    - eapply (unpoisoned_of_zero m 2148235312 2148243512 (fun _ => 0)); try reflexivity; try lia.
      all: try (rewrite ?shad_div; unfold AsanEmbed.ASHOFF; Z.div_mod_to_equations; lia).
      apply (sh_sub0 _ _ _ _ (sh_zero4 V m HM)); lia.
    - unfold hull64, Shadow.KEND. repeat split; try reflexivity; lia.
    - eapply wr_at_sub'; [exact W| lia| lia| lia].
    - unfold app_blk, Shadow.KLOW, Shadow.KHIGH, Shadow.KEND. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma astg_init : ASTG m.
  Proof.
    clear HAT. exists (repeat (Z_to_bv 8 0) ASTAGE_LEN). unfold ASTAGE.
    assert (E : ASTAGE_LEN = Z.to_nat 65536) by (apply Nat2Z.inj; rewrite ASTAGE_LEN_Z, Z2Nat.id by lia; reflexivity).
    rewrite E. replace (Z.to_nat 65536) with (length (repeat (Z_to_bv 8 0) (Z.to_nat 65536))) at 1 by (rewrite repeat_length; reflexivity).
    apply (rw_cells_image0 bsegs m).
    - intros a Ha. rewrite repeat_length, Z2Nat.id in Ha by lia. rewrite <- (Z_to_bv_bv_unsigned a).
      apply (mimg_cover bsegs V m _ 6275466 6341056 HM); [vm_compute; reflexivity| lia].
    - apply rwz_fast; [lia | lia | lia | vm_cast_no_check (eq_refl true)].
    - lia.
    - rewrite repeat_length, Z2Nat.id by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma atx_cells1_init : atx_cells1 m.
  Proof.
    clear HAT. unfold atx_cells1, AATX, AATX_CALL, ACOV_HOOK.
    repeat match goal with |- context [(6802760 + ?b)%Z] => let v := eval vm_compute in (6802760 + b)%Z in change (6802760 + b)%Z with v end.
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - aimg V m HM 0x67cd48 [C1 (Z_to_bv 8 0)] H. exact H.
    - aimg V m HM 0x67cd4c [C4 (Z_to_bv 64 0)] H. exact H.
    - mf V m HM (MCell (ZLit 6802768) 4 (ZLit 1)) H. exact H.
    - mf V m HM (MCell (ZLit 6802776) 8 (ZLit 6802784)) H. exact H.
    - aimg V m HM 0x67cd60 [C8 (Z_to_bv 64 0)] H. exact H.
    - mf V m HM (MCell (ZLit 6802792) 8 (ZLit 777180)) H. exact H.
    - mf V m HM (MCell (ZLit 6803048) 8 (ZLit 507656)) H. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma atx_cells1w_init : atx_cells1w m.
  Proof.
    clear HAT. split; [exact atx_cells1_init|]. unfold AATX. split.
    - aimg V m HM 0x67cd70 [C8 (Z_to_bv 64 0)] H. exact H.
    - aimg V m HM 0x67ce70 [C8 (Z_to_bv 64 0)] H. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma aincb_init : rw_cells bsegs m AAEF_INCB [C1 (Z_to_bv 8 0)].
  Proof. clear HAT. unfold AAEF_INCB. aimg V m HM 0x60c194 [C1 (Z_to_bv 8 0)] H. exact H. Qed.
  Lemma alibc_init : exists cdt thr sec tm1, rw_cells bsegs m ALIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
  Proof.
    clear HAT. unfold ALIBC.
    mf V m HM (MCell (ZLit 6803336) 1 (ZLit 1)) H. aimg V m HM 0x67cf89 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] H2.
    exists (Z_to_bv 8 1), (Z_to_bv 8 0), (Z_to_bv 8 0), (Z_to_bv 64 0).
    apply (proj2 (rw_cells_app bsegs m 0x67cf88 [C1 (Z_to_bv 8 1)] _)). split; [exact H| exact H2].
  Qed.

  (* [comment removed for export] *)
  Lemma atrun_cells0_init' : rw_cells bsegs m 0x60c190 [C1 (Z_to_bv 8 0)].
  Proof. clear HAT. aimg V m HM 0x60c190 [C1 (Z_to_bv 8 0)] H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma stage2_word_init : bytes_at bsegs m (usp + -8) (le8 z64).
  Proof.
    clear HAT. mf V m HM (MCell (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8))) 8 (ZLit 0)) H.
    apply rw_cells_bytes_at in H. cbn [cells_bytes cbytes app] in H. rewrite app_nil_r in H. exact H.
  Qed.


  (* [comment removed for export] *)
  Lemma stack_shclean_init : forall lo hi RLO RHI,
    ATOP <= RLO -> RLO <= lo -> lo < hi -> hi <= RHI -> hi + 8 <= KEND -> RHI <= KEND -> RLO mod 64 = 0 -> RHI mod 64 = 0 ->
    shclean m lo hi RLO RHI.
  Proof.
    intros lo hi RLO RHI H1 H2 H3 H4 H5 H5' H6 H7. unfold KEND in *.
    (* [comment removed for export] *)
    pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
    mf V m HM (MWrS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))) W0.
    mf V m HM (MZeroS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))) ZW.
    assert (W : wr_at bsegs m (shad ATOP) (17594333495296 - shad ATOP)).
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
(* a worker : argv[0] / argv[1]'s pointer words now come from asan_argv_facts r (AS/MainFactsAsan
   ; r = the kernel build's rseq bit, amain_at's argv-facts conjunct), not from asan_mem_facts. *)
Section ArgvPtrs727.
  Variables (V : nat -> Z) (m : word -> option byte) (r : Z).
  Hypothesis HAF : Forall (mfact_ok bsegs V m) (both_argv_facts r).
  Notation usp := (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat)).

  Lemma argv_ptrs_init :
       bytes_at bsegs m (usp + 8) (word_to_le_bytes 8 (Z_to_bv 64
         (32768 * V 0%nat + (8 * V 1%nat + (8 * V 2%nat + (V 4%nat + (16 * V 6%nat + (4096 * V 10%nat + 8 * V 11%nat)))))
          + (472 + 32 * r))))
    /\ bytes_at bsegs m (usp + 16) (word_to_le_bytes 8 (Z_to_bv 64
         (Z.b2z ((1 mod two64) <? (V 1%nat mod two64))
          * (32768 * V 0%nat + (8 * V 1%nat + (8 * V 2%nat + (V 3%nat + (V 4%nat + (16 * V 6%nat + (4096 * V 10%nat + 8 * V 11%nat))))))
             + (473 + 32 * r))))).
  Proof.
    unfold both_argv_facts, argv0_z, argv1_z, usp_z in HAF.
    apply Forall_cons_iff in HAF as [H0 HAF]. apply Forall_cons_iff in HAF as [H1 _].
    cbn [mfact_ok zv cellw] in H0, H1. split; [exact H0| exact H1].
  Qed.
End ArgvPtrs727.
(* [comment removed for export] *)
Lemma firstn_add_split : forall {A} (a b : nat) (l : list A), firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  intros A a b l. revert l. induction a as [|a IH]; intros l; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct b; reflexivity| f_equal; apply IH].
Qed.

Lemma bytes_at_agree : forall (m m' : word -> option byte) a bs,
  bytes_at bsegs m a bs -> (forall z, a <= z < a + Z.of_nat (length bs) -> m' (wa z) = m (wa z)) -> bytes_at bsegs m' a bs.
Proof.
  intros m m' a bs (A & B & H) AG. split; [exact A|]. split; [exact B|]. intros i Hi.
  unfold mrd. rewrite (AG (a + Z.of_nat i)) by lia. apply (H i Hi).
Qed.

(* a worker : the strings block of 's entry block (StackLayout.build_stack_bytes): the argv and
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
  (* [comment removed for export] *)
  Hypothesis HID : forall z, SB <= z < SB + Z.of_nat (length SBLK) -> m (wa z) = m0 (wa z).

  Lemma SBLK_at : bytes_at bsegs m SB SBLK.
  Proof.
    eapply bytes_at_agree; [| exact HID].
    pose proof (init_stack_bytes bsegs inp mbase ph entry sp draw IMGHI) as B.
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

  (* [comment removed for export] *)
  Lemma arg_string : forall i s, nth_error argv i = Some s ->
    exists off, nth_error (str_ptrs SB argv) i = Some (SB + off) /\ 0 <= off /\
      let P := SB + off in
      let k := (- (P + Z.of_nat (length s) + 1)) mod 8 in
      exists slack : list byte, zlength slack = k /\ P + Z.of_nat (length s) + 1 + k <= bv_unsigned top - 8
        /\ bytes_at bsegs m P (s ++ Z_to_bv 8 0 :: slack).
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
    pose proof (bytes_at_slice bsegs m SB SBLK (Z.to_nat off) (length s + 1 + Z.to_nat k) SBLK_at ltac:(lia)) as B.
    rewrite Z2Nat.id in B by lia. rewrite firstn_add_split in B. rewrite skipn_skipn in B || rewrite <- skipn_add in B || idtac.
    eapply bytes_at_ext; [exact B|].
    replace (length s + 1 + Z.to_nat off)%nat with (Z.to_nat off + (length s + 1))%nat by lia.
    replace (firstn (length s + 1) (skipn (Z.to_nat off) SBLK)) with (s ++ [Z_to_bv 8 0]); [rewrite <- app_assoc; reflexivity|].
    (* [comment removed for export] *)
    symmetry. unfold SBLK. rewrite skipn_app, firstn_app.
    pose proof (flatten_strings_length argv) as FL.
    rewrite Hf. rewrite length_skipn.
    replace (length s + 1 - (length (flatten_strings argv) - Z.to_nat off))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
  Qed.
End StringBlock.
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC4.
Ltac lit_divs := repeat match goal with |- context [?a / ?b] =>
  let v := eval vm_compute in (a / b) in lazymatch v with Zpos _ => change (a / b) with v | Z0 => change (a / b) with v end end.

Section CANSEC5. Context {rc : runConstT}.
Section VisRng.
  Variables (lz : list (word * word)) (AL : word -> Prop) (V : nat -> Z).
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V both_vis) p -> AL p.
  (* [comment removed for export] *)
  Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.

  (* [comment removed for export] *)
  Lemma page_base_of_val : forall z, 0 <= z < 2^64 -> bv_unsigned (page_base_of z) = z / 4096 * 4096.
  Proof.
    clear A0I HP HAT. intros z Hz. unfold page_base_of, page_size. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
    unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). Z.div_mod_to_equations. lia.
  Qed.

  Lemma vis_rng_gen : forall b n lo len,
    In (pagedown b, pageup (b + n)) (allow_of 2147450880 V both_vis) ->
    b <= lo -> lo + len <= b + n -> 0 <= lo -> lo + len <= 2^64 ->
    rng (fp_ok lz AL) lo len.
  Proof.
    clear HP HAT. intros b n lo len HIN H1 H2 H3 H4. apply rng_fp_ok_allowed; [lia| lia|].
    intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(lia)) as PV.
    apply A0I; [rewrite PV; Z.div_mod_to_equations; lia|].
    exists (pagedown b, pageup (b + n)). split; [exact HIN|]. cbn [fst snd]. rewrite PV. unfold pagedown, pageup.
    Z.div_mod_to_equations. nia.
  Qed.

  (* [comment removed for export] *)
  Lemma allow_in_app : forall k bn, nth_error both_vis k = Some bn ->      (* [comment removed for export] *)
    In (pagedown (zv V (fst bn)), pageup (zv V (fst bn) + zv V (snd bn))) (allow_of 2147450880 V both_vis)
    /\ In (pagedown (2147450880 + zv V (fst bn) / 8), pageup (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8)) (allow_of 2147450880 V both_vis).
  Proof.
    clear A0I HP HAT. intros k bn Hk. unfold allow_of. split; apply in_flat_map; exists bn; split; try (eapply nth_error_In; exact Hk); cbn; tauto.
  Qed.

  Lemma vis_rng : forall k bn lo len, nth_error both_vis k = Some bn ->
    zv V (fst bn) <= lo -> lo + len <= zv V (fst bn) + zv V (snd bn) -> 0 <= lo -> lo + len <= 2^64 -> rng (fp_ok lz AL) lo len.
  Proof. clear HP HAT. intros k bn lo len Hk H1 H2 H3 H4. eapply vis_rng_gen; [exact (proj1 (allow_in_app k bn Hk))| lia| lia| lia| lia]. Qed.

  Lemma vis_rng_sh : forall k bn lo len, nth_error both_vis k = Some bn ->
    2147450880 + zv V (fst bn) / 8 <= lo -> lo + len <= 2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8 -> 0 <= lo -> lo + len <= 2^64 ->
    rng (fp_ok lz AL) lo len.
  Proof.
    clear HP HAT. intros k bn lo len Hk H1 H2 H3 H4.
    eapply (vis_rng_gen (2147450880 + zv V (fst bn) / 8) ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8));
      [| lia| lia| lia| lia].
    replace (2147450880 + zv V (fst bn) / 8 + ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8)) with (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8) by lia.
    exact (proj2 (allow_in_app k bn Hk)).
  Qed.

  (* [comment removed for export] *)
  Lemma rng_image : forall lo len, 0x10000 <= lo -> lo + len <= 0x67f000 -> rng (fp_ok lz AL) lo len.
  Proof. clear HP HAT. intros lo len H1 H2. eapply (vis_rng 11); [reflexivity| cbn; lia| cbn; lia| lia| lia]. Qed.
  Lemma rng_image_sh : forall lo len, 0x7fffa000 <= lo -> lo + len <= 0x800c7e00 -> rng (fp_ok lz AL) lo len.
  Proof. clear HP HAT. intros lo len H1 H2. eapply (vis_rng_sh 11); [reflexivity| cbn; lit_divs; lia| cbn; lit_divs; lia| lia| lia]. Qed.
  Lemma rng_stackside : forall lo len, ATOP <= lo -> lo + len <= 2^47 -> rng (fp_ok lz AL) lo len.
  Proof.
    intros lo len H1 H2. atop_facts. pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
    eapply (vis_rng 12); [reflexivity| cbn; lia| cbn; lia| lia| lia].
  Qed.
  (* [comment removed for export] *)
  Lemma rng_stackside_sh : forall lo len, shad ATOP <= lo -> lo + len <= 17594333495296 -> rng (fp_ok lz AL) lo len.
  Proof.
    intros lo len H1 H2. atop_facts. pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
    rewrite shad_div in H1. unfold AsanEmbed.ASHOFF in H1.
    eapply (vis_rng_sh 12); [reflexivity| cbn -[Z.div Z.mul Z.add]; Z.div_mod_to_equations; lia| cbn -[Z.div Z.mul Z.add]; Z.div_mod_to_equations; lia| lia| lia].
  Qed.
  (* [comment removed for export] *)
  Lemma rng_fake : forall (P393 : 4096 <= 4096 * V 377%nat /\ 4096 * V 377%nat + 11571200 <= ATOP),
    rng (fp_ok lz AL) (4096 * V 377%nat) 11571200 /\ rng (fp_ok lz AL) (shad (4096 * V 377%nat)) (shlen 11571200).
  Proof.
    clear HP HAT. intros P393. atop_facts. split.
    - eapply (vis_rng 3); [reflexivity| cbn; lia| cbn; lia| lia| lia].
    - rewrite shad_div. unfold shlen, AsanEmbed.ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      eapply (vis_rng_sh 3); [reflexivity| cbn -[Z.div Z.mul]; lia| cbn -[Z.div Z.mul]; Z.div_mod_to_equations; lia| lia| Z.div_mod_to_equations; lia].
  Qed.
  Lemma rng_dtls : forall (P310 : 4096 <= 4096 * V 310%nat /\ 4096 * V 310%nat + 4096 <= ATOP), rng (fp_ok lz AL) (4096 * V 310%nat) 4096.
  Proof. clear HP HAT. intros P310. atop_facts. eapply (vis_rng 4); [reflexivity| cbn; lia| cbn; lia| lia| lia]. Qed.
  Lemma rng_empty : forall b, 0 <= b <= 2^64 -> rng (fp_ok lz AL) b 0.
  Proof. clear A0I HP HAT. intros b Hb. apply rng_fp_ok; [lia| lia|]. intros z Hz. lia. Qed.
End VisRng.
(* [comment removed for export] *)
(* a worker : ArgPack over 's strings block (StringBlock above): the same conclusion per argv
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
  Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
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
      /\ bytes_at bsegs m (SB + off) (s ++ Z_to_bv 8 0 :: slack)
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
