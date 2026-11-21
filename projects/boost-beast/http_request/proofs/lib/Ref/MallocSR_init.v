(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac ITree Nodes SysStep Exec Decode.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim Monad MSafeP STree Malloc MallocCtrl Prog KInv MI_Inv AllocTop MmNodes GapGrid KLink KLink2 KLink3.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs RMallocRep MallocSR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma reserved_top_ref : reserved_top (segments_reserved rsegs) = 0xb4000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition ref_segments : list (Z * Z) := [(0x10000, 0x1a000); (0x2a000, 0x50000); (0x7a000, 0x6000); (0x80000, 0x34000)].
Lemma segments_reserved_ref : segments_reserved rsegs = map (fun p => went (fst p) (snd p)) ref_segments.
Proof. vm_compute. reflexivity. Qed.
Lemma reservedZ_segments : reservedZ rsegs = ref_segments.
Proof. vm_compute. reflexivity. Qed.

(* 08b1429: [init_model] seeds [m_channel_reader] from [in_channel_reader]; the launch's
   [valid_input] pins it true ([Run.valid_input_channel_reader]) *)
Lemma mminv_init : forall tid brk mbase sp lim inp,
  in_channel_reader inp = true ->
  mminv (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp)).
Proof. intros tid brk mbase sp lim inp Hrd. split; [reflexivity | split; [reflexivity | exact Hrd]]. Qed.

Section HC.
Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.False Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.or Sort Prop.

Theorem KM_init : forall tid brk mbase sp lim inp,
  valid_brk rsegs brk -> valid_sp sp -> 2^34 <= lim ->
  bv_unsigned sp - stack_max_size = hceil ->
  (* the revision's [init_model] puts the launch's vDSO/vvar pair in the
     reserved ledger just below [mmap_top]; [valid_mmap_base] (from
     [Run.valid_entry]) keeps it far above the brk guard *)
  valid_mmap_base mbase ->
  in_channel_reader inp = true ->
  KM (ps_init (reservedZ rsegs)) (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp)).
Proof.
  intros tid brk mbase sp lim inp (Hb1 & Hb2 & Hb3) (Hs1 & Hs2 & Hs3) Hlim Hc (Hm1 & Hm2 & Hm3) Hrd.
  set (mo := with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp)).
  rewrite reserved_top_ref in Hb1, Hb2.
  pose proof (hceil_range : 0x7fff7f800000 <= hceil <= 0x7fffff800000) as Hcr.
  assert (Hat : alloc_top (m_vmmaps mo) = hceil) by exact Hc.
  assert (Hsb : bv_unsigned (vm_start_brk (m_vmmaps mo)) = bv_unsigned brk) by reflexivity.
  assert (Hbb : bv_unsigned (vm_brk (m_vmmaps mo)) = bv_unsigned brk) by reflexivity.
  assert (Hlm : vm_limit (m_vmmaps mo) = lim) by reflexivity.
  assert (Hmaps : vm_maps (m_vmmaps mo) = []) by reflexivity.
  assert (Hnacc : vm_noaccess (m_vmmaps mo) = []) by reflexivity.
  assert (Hres : vm_reserved (m_vmmaps mo)
                 = segments_reserved rsegs ++ vdso_reserved (in_kernel inp) (vdso_top (m_vmmaps mo)))
    by exact (vm_reserved_init_model _ _ _ _ _ _).
  assert (Htop : vdso_top (m_vmmaps mo)
                 = page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)))
    by exact (vdso_top_init_model _ _ _ _ _ _).
  (* the pair sits within [[vdso_top - vdso_len, vdso_top)], far above the brk *)
  assert (Hvd : forall a n, In (a, n) (vdso_reserved (in_kernel inp) (vdso_top (m_vmmaps mo))) ->
            bv_unsigned brk + 4 * PGSZ <= bv_unsigned a /\ 0 < bv_unsigned n
            /\ bv_unsigned n <= 2^33).
  { intros a n Hin.
    pose proof (page_round_down_Z_le (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size))) as Pd.
    assert (Pu : Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size) - page_size
                 < vdso_top (m_vmmaps mo)).
    { rewrite Htop. unfold page_round_down_Z, page_size. Z.div_mod_to_equations. lia. }
    assert (Ht64 : vdso_top (m_vmmaps mo) < two_pow_64).
    { rewrite Htop in *. unfold two_pow_64, stack_max_size, sp_window_hi in *. lia. }
    destruct (vdso_reserved_above _ _ _ _ Ht64 Hin) as [A1 A2].
    pose proof (vdso_reserved_nonzero _ _ _ _ Ht64 Hin) as A3.
    pose proof (vdso_len_bounds (in_kernel inp)) as Lb.
    unfold PGSZ, page_size, mmap_base_min, brk_aslr_max, stack_max_size,
      sp_window_lo, two_pow_64 in *. lia. }
  exists (led_init (rband hceil :: reservedZ rsegs)). split; [|split].
  - exact (hreach_init hsecret _ hsecret_range).
  - assert (Elt : ltotal (led_init (rband hceil :: reservedZ rsegs)) = 0) by reflexivity.
    assert (Elc : lcount (led_init (rband hceil :: reservedZ rsegs)) = 0) by reflexivity.
    constructor.
    + exact (mminv_init tid brk mbase sp lim inp Hrd).
    + reflexivity.
    + rewrite Hmaps. split; [intros e [] | constructor].
    + rewrite Hnacc. intros e [].
    + exists (segments_reserved rsegs), (vdso_reserved (in_kernel inp) (vdso_top (m_vmmaps mo))).
      split; [exact Hres|]. cbn [ld_resv led_init]. rewrite Hat. reflexivity.
    + rewrite Hat. unfold CEIL_MIN, CEIL_MAX. lia.
    + exact Hat.
    + intros e He. rewrite Hres in He. apply in_app_or in He as [He|He].
      * left. rewrite Hsb. rewrite segments_reserved_ref in He. unfold ref_segments in He.
        cbn [map fst snd] in He. set (B := bv_unsigned brk) in *. destruct He as [<-|[<-|[<-|[<-|[]]]]];
          unfold ehi, went, wz; cbn [fst snd]; vm_compute bv_unsigned; lia.
      * right. destruct e as [a n]. destruct (Hvd a n He) as (V1 & _ & _).
        unfold elo. cbn [fst]. rewrite Hsb. exact V1.
    + intros e He. rewrite Hres in He. apply in_app_or in He as [He|He].
      * rewrite segments_reserved_ref in He. unfold ref_segments in He.
        cbn [map fst snd] in He. destruct He as [<-|[<-|[<-|[<-|[]]]]];
          unfold elo, ehi, went, wz; cbn [fst snd]; vm_compute bv_unsigned; lia.
      * destruct e as [a n]. destruct (Hvd a n He) as (_ & V2 & V3).
        unfold elo, ehi. cbn [fst snd]. lia.
    + rewrite Hres, segments_reserved_ref. unfold ref_segments. cbn [map app length].
      unfold vdso_reserved. destruct (_ <? _)%Z; cbn [length]; lia.
    + rewrite ?Hsb, ?Hbb, ?Hat.
      unfold PGSZ, page_size, mmap_base_min, brk_aslr_max, stack_max_size, sp_window_lo, two_pow_64 in *.
      repeat split; lia.
    + intros b l [].
    + intros b l k [].
    + constructor.
    + intros b l E. discriminate E.
    + cbn [ld_brk led_init]. split; reflexivity.
    + rewrite Elt. reflexivity.
    + rewrite Elc, Hmaps. reflexivity.
    + rewrite Hlm. unfold BUDCAP. lia.
    + (* [kb_vdso_in]: the pair is the reserved ledger's tail ([vm_reserved_init_model]) *)
      rewrite Hres. intros e He. apply in_or_app. right. exact He.
    + (* [kb_vdso_disj]: no tracked mapping yet *)
      rewrite Hmaps. intros r _ e [].
  - assert (Elt : ltotal (led_init (rband hceil :: reservedZ rsegs)) = 0) by reflexivity.
    assert (Elc : lcount (led_init (rband hceil :: reservedZ rsegs)) = 0) by reflexivity.
    unfold BUD. rewrite Elt, Elc, Hlm. unfold BUDCAP, RESV_MAX, GRID_J. lia.
Qed.

End HC.
