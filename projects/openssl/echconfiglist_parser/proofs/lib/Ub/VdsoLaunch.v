(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11: the ubsan binary's copy of Ref/VdsoLaunch.v: the launch facts Ub/ECH_LibTop.vdso_run_facts, proved from the launch; only what names the binary's segment list, its end 0x358000 or the record is copied, everything else is Ref/VdsoLaunch.v's, used by import; and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* The launch facts the ubsan binary's library is closed under ([ECH_LibTop.vdso_run_facts]),
   proved from the launch.  The run's tail is the vDSO/vvar pair [Run.vdso_segments kb sp mbase]
   (Run.v:290-306 at 20f40762); [vd_lo], [vd_mid] and [vd_top] are the pair's base, text base and
   top as that function computes them (Ref/VdsoLaunch.v).  On a valid stack pointer and mmap base
   the pair is the vvar segment [[vd_lo, vd_mid)] and the text segment [[vd_mid, vd_top)], both
   "r--", the text holding the measured image ([Lib/VdsoImg.vdso_image_of_const]); the binary's own
   segments end below 0x358000 ([RMallocRep.ref_find_segment_none]).
   - Every fact that names neither the binary's segments nor that bound is Ref/VdsoLaunch.v's:
     the pair's form ([vdso_segments_two], [find_two], [tail_two]), the image checks
     ([image_of_bytes_self], [rvdso_cover]), the pair's arithmetic ([top_facts], [top_range],
     [lo_mid], [mid_top], [mid_al]), its ledger entries ([vdso_reserved_pair], [pair_win_lo],
     [pair_win_hi]) and [vdso_text_base_pair].  Those of its Section Launch take the Section's
     variables they use: [kb sp mbase] and, where they use them, [Hsp Hmb].
   - [vdso_text_base_pair] reads AT_SYSINFO_EHDR ([Run.vdso_text_base kb sp mbase], LPS b84e73ef) as
     the pair's text base on every valid launch, with no premise. *)
From Stdlib Require Import String.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Vdso.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec Mem VdsoImg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomStable.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import VdsoLaunch.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RVdsoSegs ECH_LibTop.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require RMallocRep.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require MmVdso.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(** * The measured image *)

(* the binary's own segments hold no vDSO text, as [MainSegs.vdso_image_RSEGS] *)
Lemma find_text_usegs : List.find seg_vdso_text usegs = None.
Proof. reflexivity. Qed.

(* Ref/VdsoLaunch.v's, which is Local there *)
Local Ltac vl_zbool :=
  repeat match goal with
         | |- context [Z.leb ?x ?y] => destruct (Z.leb_spec x y)
         | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y)
         end.

(** * The launch's pair *)

Section Launch.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.
  Variable kb : KernelBuild.
  Variables sp mbase : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hmb : valid_mmap_base mbase.

  Local Notation VLO := (vd_lo kb sp mbase).
  Local Notation VMID := (vd_mid kb sp mbase).
  Local Notation VTOP := (vd_top sp mbase).
  Local Notation VTAIL := (vdso_segments kb sp mbase).

  Lemma lo_bounds : 0x358000 <= VLO /\ page_size <= VLO.
  Proof. pose proof (top_range sp mbase Hsp Hmb). unfold vd_lo. rewrite len_24576. unfold page_size. lia. Qed.

  (* above the binary's segments, the run's list answers with the pair *)
  Lemma find_run : forall x n, 1 <= n -> 0x358000 <= x ->
    find_segment (usegs ++ VTAIL) x n = find_segment VTAIL x n.
  Proof.
    intros x n Hn Hx. rewrite find_segment_app.
    rewrite (Ub.RMallocRep.ref_find_segment_none x n Hn (or_intror Hx)). reflexivity.
  Qed.

  Lemma find_text : forall x n, 1 <= n -> VMID <= x -> x + n <= VTOP ->
    find_segment (usegs ++ VTAIL) x n = Some (vt_seg kb VMID).
  Proof.
    intros x n Hn H1 H2. pose proof lo_bounds as [L1 L2]. pose proof (lo_mid kb sp mbase) as LM.
    rewrite (find_run x n Hn) by lia. rewrite (find_two kb sp mbase Hsp Hmb).
    vl_zbool; cbn [andb]; first [exfalso; lia | reflexivity].
  Qed.

  (** ** The image is read through the text segment *)

  Lemma mr_text : forall o, 0 <= o < RVDSO_SIZE ->
    memory_read (usegs ++ VTAIL) (wa (VMID + o)) 1 = Some [rvdso_byte o].
  Proof.
    intros o Ho. pose proof lo_bounds as [L1 L2]. pose proof (lo_mid kb sp mbase). pose proof (mid_top kb sp mbase).
    pose proof (top_range sp mbase Hsp Hmb) as [T1 T2]. pose proof RVDSO_SIZE_val as HS.
    assert (Hu : bv_unsigned (wa (VMID + o)) = VMID + o) by (apply wa_unsigned; lia).
    assert (Hf : find_segment (usegs ++ VTAIL) (bv_unsigned (wa (VMID + o))) 1 = Some (vt_seg kb VMID))
      by (rewrite Hu; apply find_text; lia).
    rewrite (memory_read_found _ _ _ Hf (vt_r kb sp mbase)), Hu, (vt_base kb sp mbase Hsp Hmb), vt_bytes.
    replace (VMID + o - VMID) with o by ring.
    rewrite srb1, (rvdso_byte_some o Ho). reflexivity.
  Qed.

  Lemma rom_text : forall o, 0 <= o < RVDSO_SIZE ->
    seg_rom (usegs ++ VTAIL) (wa (VMID + o)) = rvdso_peek o.
  Proof. intros o Ho. unfold seg_rom. rewrite (mr_text o Ho), (rvdso_peek_in o Ho). reflexivity. Qed.

  Lemma ro_text : forall o, 0 <= o < RVDSO_SIZE -> ro_addr (usegs ++ VTAIL) (wa (VMID + o)) = true.
  Proof.
    intros o Ho. pose proof lo_bounds as [L1 L2]. pose proof (lo_mid kb sp mbase). pose proof (mid_top kb sp mbase).
    pose proof (top_range sp mbase Hsp Hmb) as [T1 T2]. pose proof RVDSO_SIZE_val as HS.
    assert (Hu : bv_unsigned (wa (VMID + o)) = VMID + o) by (apply wa_unsigned; lia).
    assert (Hf : find_segment (usegs ++ VTAIL) (bv_unsigned (wa (VMID + o))) 1 = Some (vt_seg kb VMID))
      by (rewrite Hu; apply find_text; lia).
    rewrite (ro_addr_found _ _ _ Hf), vt_w. reflexivity.
  Qed.

  Lemma rom_pair : rvdso_rom (rvsegs VTAIL) VMID.
  Proof.
    pose proof lo_bounds as [L1 L2]. pose proof (lo_mid kb sp mbase). pose proof (mid_top kb sp mbase).
    pose proof (top_range sp mbase Hsp Hmb) as [T1 T2].
    unfold rvdso_rom, rvsegs. rewrite RVDSO_SPAN_val.
    split; [lia|]. split; [exact (mid_al kb sp mbase)|]. split; [lia|].
    intros o Ho. exact (conj (rom_text o Ho) (ro_text o Ho)).
  Qed.

  (** ** The machine declines at a pc in the text ([RiscvSemantics.fetch_failure]'s vdso_text_at
      arm, RiscvSemantics.v:1156-1180): no fetch path reads the "r--" text *)

  Lemma code_read_text : forall (a : word) (n : N), 1 <= Z.of_N n -> VMID <= bv_unsigned a ->
    bv_unsigned a + Z.of_N n <= VTOP -> code_read (usegs ++ VTAIL) a n = None.
  Proof.
    intros a n Hn H1 H2. exact (code_read_found _ a n _ (find_text (bv_unsigned a) (Z.of_N n) Hn H1 H2) (vt_x kb sp mbase)).
  Qed.

  Lemma code_read_ov_text : forall m (a : word) (n : N), 1 <= Z.of_N n -> VMID <= bv_unsigned a ->
    bv_unsigned a + Z.of_N n <= VTOP -> code_read_ov (usegs ++ VTAIL) m a n = None.
  Proof.
    intros m a n Hn H1 H2.
    exact (code_read_ov_found _ m a n _ (find_text (bv_unsigned a) (Z.of_N n) Hn H1 H2) (vt_x kb sp mbase)).
  Qed.

  Lemma fw_none : forall (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 4 <= VTOP ->
    fetch_word (usegs ++ VTAIL) a = None.
  Proof.
    intros a H1 H2. unfold fetch_word.
    rewrite (code_read_text a 4 ltac:(cbn [Z.of_N]; lia) H1 ltac:(cbn [Z.of_N]; lia)).
    match goal with |- context [if negb ?b then _ else _] => destruct b end; reflexivity.
  Qed.

  Lemma fwo_none : forall m (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 4 <= VTOP ->
    fetch_word_ov (usegs ++ VTAIL) m a = None.
  Proof.
    intros m a H1 H2. unfold fetch_word_ov.
    rewrite (code_read_ov_text m a 4 ltac:(cbn [Z.of_N]; lia) H1 ltac:(cbn [Z.of_N]; lia)).
    match goal with |- context [if negb ?b then _ else _] => destruct b end; reflexivity.
  Qed.

  Lemma fh_none : forall (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 2 <= VTOP ->
    fetch_half (usegs ++ VTAIL) a = None.
  Proof.
    intros a H1 H2. unfold fetch_half.
    rewrite (code_read_text a 2 ltac:(cbn [Z.of_N]; lia) H1 ltac:(cbn [Z.of_N]; lia)). reflexivity.
  Qed.

  Lemma fho_none : forall m (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 2 <= VTOP ->
    fetch_half_ov (usegs ++ VTAIL) m a = None.
  Proof.
    intros m a H1 H2. unfold fetch_half_ov.
    rewrite (code_read_ov_text m a 2 ltac:(cbn [Z.of_N]; lia) H1 ltac:(cbn [Z.of_N]; lia)). reflexivity.
  Qed.

  Lemma fha_none : forall m (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 2 <= VTOP ->
    fetch_half_any (usegs ++ VTAIL) m a = None.
  Proof. intros m a H1 H2. unfold fetch_half_any. rewrite (fh_none a H1 H2), (fho_none m a H1 H2). reflexivity. Qed.

  Lemma fta_none : forall m (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 2 <= VTOP ->
    fetch_tail_any (usegs ++ VTAIL) m a = None.
  Proof.
    intros m a H1 H2. unfold fetch_tail_any. rewrite (fha_none m a H1 H2).
    match goal with |- context [if negb ?b then _ else _] => destruct b end; reflexivity.
  Qed.

  Lemma ff_unm : forall m (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 1 <= VTOP ->
    fetch_failure (usegs ++ VTAIL) m a = MachineUnmodeled.
  Proof.
    intros m a H1 H2. unfold fetch_failure.
    rewrite (vdso_text_at_found _ a _ (find_text (bv_unsigned a) 1 ltac:(lia) H1 H2)), vt_t. reflexivity.
  Qed.

  Lemma unm_text : forall ms, ms_pc ms = Z_to_bv 64 (VMID + 1460) ->
    RiscvSemantics.step (usegs ++ VTAIL) ms = MachineUnmodeled.
  Proof.
    intros ms Hpc. pose proof lo_bounds as [L1 L2]. pose proof (lo_mid kb sp mbase). pose proof (mid_top kb sp mbase).
    pose proof (top_range sp mbase Hsp Hmb) as [T1 T2].
    assert (Hu : bv_unsigned (Z_to_bv 64 (VMID + 1460)) = VMID + 1460) by (apply wa_unsigned; lia).
    unfold RiscvSemantics.step, RiscvSemantics.step_accesses. rewrite Hpc.
    rewrite (fw_none (Z_to_bv 64 (VMID + 1460))) by (rewrite Hu; lia).
    rewrite (fwo_none (ms_mem ms) (Z_to_bv 64 (VMID + 1460))) by (rewrite Hu; lia).
    rewrite (fta_none (ms_mem ms) (Z_to_bv 64 (VMID + 1460))) by (rewrite Hu; lia).
    rewrite (ff_unm (ms_mem ms) (Z_to_bv 64 (VMID + 1460))) by (rewrite Hu; lia).
    reflexivity.
  Qed.

  (** ** The entry at text base + 1460 is clock_gettime's ([Lib/VdsoImg.rvdso_cgt_off_entry]) *)

  Lemma vimg : vdso_image (usegs ++ VTAIL) = Some (vt_seg kb VMID, RVDSO_IMAGE).
  Proof.
    unfold vdso_image, vdso_text_seg.
    rewrite (find_app_none _ seg_vdso_text usegs VTAIL find_text_usegs), (tail_two kb sp mbase Hsp Hmb).
    change (List.find seg_vdso_text [vv_seg VLO; vt_seg kb VMID]) with (Some (vt_seg kb VMID)).
    cbv beta iota zeta. rewrite vt_bytes, image_of_bytes_self. reflexivity.
  Qed.

  Lemma ent_text : vdso_entry_fn (usegs ++ VTAIL) (Z_to_bv 64 (VMID + 1460)) = Some VdsoClockGettime.
  Proof.
    pose proof lo_bounds as [L1 L2]. pose proof (lo_mid kb sp mbase). pose proof (mid_top kb sp mbase).
    pose proof (top_range sp mbase Hsp Hmb) as [T1 T2].
    pose proof RVDSO_SIZE_val as HS.
    assert (Hu : bv_unsigned (Z_to_bv 64 (VMID + 1460)) = VMID + 1460) by (apply wa_unsigned; lia).
    unfold vdso_entry_fn. rewrite vimg. cbv beta iota zeta.
    rewrite (vt_base kb sp mbase Hsp Hmb), Hu.
    change (Z.of_N (vi_size RVDSO_IMAGE)) with RVDSO_SIZE.
    replace (VMID + 1460 - VMID) with RVDSO_CGT_OFF by (unfold RVDSO_CGT_OFF; ring).
    vl_zbool; cbn [andb]; first [exfalso; lia | exact rvdso_cgt_off_entry].
  Qed.

  (** ** The record *)

  Theorem vdso_run_facts_of :
    hceil = bv_unsigned sp - stack_max_size ->
    hvdso = bv_unsigned (vdso_text_base kb sp mbase) + 1460 ->
    bv_unsigned (vdso_text_base kb sp mbase) = VMID ->
    vdso_run_facts VTAIL VLO VMID VTOP.
  Proof.
    intros HCE HVD HTB.
    pose proof lo_bounds as [L1 L2]. pose proof (lo_mid kb sp mbase) as LM. pose proof (mid_top kb sp mbase) as MT.
    pose proof (top_facts sp mbase) as (_ & _ & T3 & T4).
    assert (HVB : hvdso = VMID + 1460) by (rewrite HVD, HTB; reflexivity).
    split.
    - exact (vdso_segments_nx kb sp mbase).
    - exact (vdso_segments_nw kb sp mbase).
    - reflexivity.
    - lia.
    - lia.
    - intros x s Hf. rewrite (find_two kb sp mbase Hsp Hmb) in Hf. revert Hf.
      vl_zbool; cbn [andb]; intros Hf; first [discriminate Hf | lia].
    - intros x Hx. rewrite (find_two kb sp mbase Hsp Hmb).
      vl_zbool; cbn [andb]; first [discriminate | exfalso; lia].
    - exact rom_pair.
    - exact HVB.
    - rewrite HVB. exact ent_text.
    - intros ms Hpc. rewrite HVB in Hpc. exact (unm_text ms Hpc).
  Qed.

  Theorem vdso_launch_facts :
    hceil = bv_unsigned sp - stack_max_size ->
    hvdso = bv_unsigned (vdso_text_base kb sp mbase) + 1460 ->
    vdso_run_facts VTAIL VLO VMID VTOP.
  Proof. intros HCE HVD. exact (vdso_run_facts_of HCE HVD (Ref.VdsoLaunch.vdso_text_base_pair kb sp mbase Hsp Hmb)). Qed.
End Launch.
