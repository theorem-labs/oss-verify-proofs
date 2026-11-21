(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling Nodes Decode.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import STree Malloc MallocCtrl KInv KStep Prog
  MI_Tree MI_Inv MI_Contracts LB_Tables LB_Inv LB_Sum LB_Kernel LB_QM LB_StmtA LB_Raw.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Unforced.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma zsum_nonneg' l : (forall x, In x l -> 0 <= x) -> 0 <= zsum l.
Proof. induction l as [|a l IH]; intros H; cbn; [lia|]. pose proof (H a (or_introl eq_refl)). specialize (IH ltac:(intros x Hx; apply H; right; exact Hx)). unfold zsum in IH. lia. Qed.

Lemma CAP_lower P c : (forall c, 0 <= P c) -> 0 <= c -> 14 <= CAP P c.
Proof.
  intros HP Hc.
  assert (0 <= HOSTSTD P c).
  { unfold HOSTSTD. apply zsum_nonneg'. intros x Hx. apply in_map_iff in Hx as (c' & <- & Hc').
    assert (G : 0 <= c' < 48) by (unfold guests in Hc'; cbn in Hc'; lia). cbn beta.
    destruct (bighost c' =? c); [| apply Z.le_refl]. pose proof (tab_basic_ok c' G) as (_ & CM & _).
    apply Z.div_pos; [| lia]. unfold CAP0. pose proof (HP c'). destruct (c' <=? 23); lia. }
  unfold CAP, CAP0. pose proof (HP c). destruct (c <=? 23); lia.
Qed.

Lemma NCAP_lower P : (forall c, 0 <= P c) -> 4 <= NCAP P.
Proof.
  intros HP. unfold NCAP, NG.
  assert (0 <= zsum (map (fun c => (CAP P c + 32) / cmax c + 160) classes)).
  { apply zsum_nonneg'. intros x Hx. apply in_map_iff in Hx as (c & <- & Hc). apply In_classes in Hc. cbn beta.
    pose proof (tab_basic_ok c Hc) as (_ & CM & _). pose proof (CAP_lower P c HP ltac:(lia)).
    assert (0 <= (CAP P c + 32) / cmax c) by (apply Z.div_pos; lia). lia. }
  pose proof (HP 63). lia.
Qed.

Lemma SINV_minit secret resv : SINV x0 (minit secret resv) [].
Proof.
  constructor; cbn -[Z.mul Z.add Z.le Z.lt]; try (intros *; intros HH; rewrite lookup_empty in HH; discriminate).
  - intros k [].
  - intros c. unfold MIS, zcount, zlen. cbn. lia.
  - intros c Hc. unfold nsc, gmetas, groups_l. cbn [s_groups minit]. rewrite map_to_list_empty. cbn. lia.
  - unfold apages, ncarved, regions_l. cbn [s_regions s_metas minit]. rewrite !map_to_list_empty. unfold zlen. cbn. lia.
  - intros H. lia.
Qed.

Lemma gcnt_minit secret resv c : gcnt (minit secret resv) c = 0.
Proof. unfold gcnt. cbn [s_groups minit]. rewrite map_to_list_empty. reflexivity. Qed.

Lemma AQ_minit P secret resv : (forall c, 0 <= P c) -> AQ (minit secret resv) [] P.
Proof.
  intros HP. constructor.
  - intros c Hc. unfold LR, zcount, zlen. cbn. apply HP.
  - intros c Hc. rewrite gcnt_minit. pose proof (CAP_lower P c HP ltac:(lia)). lia.
  - unfold n63, zcount, zlen. cbn. apply HP.
  - unfold ncarved. cbn [s_metas minit]. rewrite map_to_list_empty. pose proof (NCAP_lower P HP). unfold zlen. cbn. lia.
  - exact HP.
Qed.

Lemma reserved_top_ge' : forall l e, In e l -> bv_unsigned (fst e) + bv_unsigned (snd e) <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
  cbn [reserved_top]. destruct Hin as [<-|Hin]; cbn [fst snd]; [lia|]. specialize (IH e Hin). lia.
Qed.

Section WithCeiling. Context {CE__ : Ceiling}.

Theorem QI_init : forall P segs brk0 mbase sp lim inp,
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling ->
  bv_unsigned sp - stack_max_size = alloc_ceiling ->
  (forall c, 0 <= P c) -> PHI P <= LBUDGET ->
  reserved_top (segments_reserved segs) + brk_aslr_max <= 2 ^ 33 -> KLIM + SMALLREQ <= lim ->
  (* two launch facts (APPENDED). The one caller, LB_Main prog_noerr_gen, has
     both: in_channel_reader from valid_input_either; mmap_base_min <= mbase from valid_entry, whose
     valid_mmap_base_va reads va_mmap_base_min Sv48 = mmap_base_min because valid_input_either pins Sv48. *)
  in_channel_reader inp = true -> mmap_base_min <= bv_unsigned mbase ->
  QI [] P (ps_init (reservedZ segs)) (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
  intros P segs brk0 mbase sp lim inp (Hlo & Hhi & Hal) Hpos Hceil Htop HP HPHI Hlow Hroom Hrdr Hmb.
  (* the vDSO facts of the launch. THE CONJUNCT start_brk + 4 pages
     <= VLO and the pair at or above VLO are PROVED here from the launch, not assumed. *)
  pose (mo0 := init_model (segments_reserved segs) brk0 mbase sp lim inp).
  pose proof alloc_ceiling_range as Hcr.
  assert (Ekb : m_kernel mo0 = in_kernel inp) by reflexivity.
  assert (Eres : vm_reserved (m_vmmaps mo0)
                 = segments_reserved segs ++ vdso_reserved (in_kernel inp) (vdso_top (m_vmmaps mo0)))
    by (apply vm_reserved_init_model).
  assert (Etop : vdso_top (m_vmmaps mo0) = page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)))
    by (apply vdso_top_init_model).
  assert (Esb : bv_unsigned (vm_start_brk (m_vmmaps mo0)) = bv_unsigned brk0) by reflexivity.
  assert (Hvhi : forall e, In e (vdso_reserved (in_kernel inp) (vdso_top (m_vmmaps mo0))) -> VLO <= elo e).
  { intros [a n] Hin. pose proof (bv_unsigned_in_range 64 mbase) as Hmr. unfold bv_modulus in Hmr.
    assert (Hpd : Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size) - 4096
                  < page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size))
                  <= Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
    { unfold page_round_down_Z, page_size.
      pose proof (Z.div_mod (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)) 4096 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)) 4096 ltac:(lia)) as M.
      lia. }
    assert (Htop2 : (vdso_top (m_vmmaps mo0) < two_pow_64)%Z) by (rewrite Etop; unfold two_pow_64; lia).
    destruct (vdso_reserved_above _ _ _ _ Htop2 Hin) as [A1 _].
    pose proof (vdso_len_bounds (in_kernel inp)) as VL. rewrite Etop in A1.
    unfold elo. cbn [fst]. unfold VLO, mmap_base_min, page_size in *. lia. }
  assert (Hresv' : incl (ld_resv (led_init (reservedZ segs))) (map wwZ (vm_reserved (m_vmmaps mo0)))).
  { intros x Hx. rewrite Eres, map_app. apply in_or_app. left. exact Hx. }
  assert (Hrt' : forall e, In e (vm_reserved (m_vmmaps mo0)) ->
                 ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo0)) \/ VLO <= elo e).
  { intros e Hin. rewrite Eres in Hin. apply in_app_or in Hin as [Hin|Hin].
    - left. pose proof (reserved_top_ge' _ _ Hin). unfold ehi. rewrite Esb. lia.
    - right. exact (Hvhi e Hin). }
  assert (HKV : KLV (led_init (reservedZ segs)) mo0).
  { split; [rewrite Esb; unfold VLO, PGSZ in *; lia|]. split.
    - exists (segments_reserved segs). split; [rewrite Ekb; exact Eres|].
      intros e Hin. pose proof (reserved_top_ge' _ _ Hin). unfold ehi. rewrite Esb. lia.
    - intros b l [Hin | (k & Hin)]; destruct Hin. }
  unfold mo0 in Hresv', Hrt', HKV.
  split; [| unfold R63X, zsum; cbn; lia].
  exists (minit 0 (reservedZ segs)), (led_init (reservedZ segs)), [], (fun _ => []).
  split; [reflexivity|]. split; [apply INVL_init; lia|]. split; [apply SINV_minit|]. split; [apply AQ_minit; exact HP|].
  split; [| split; [| apply Permutation_refl]].
  - constructor; try exact Hresv'; try exact Hrt'; try exact HKV;
      rewrite ?m_vmmaps_init_model, ?m_halted_init_model; cbn -[Z.pow Z.mul Z.add].
    + apply minv_init. exact Hrdr.
    + reflexivity.
    + split; [intros e []| apply pwdisj_nil].
    + unfold PGSZ in *. unfold page_size in Hal. lia.
    + intros b l [].
    + intros b l k [].
    + apply List.NoDup_nil.
    + intros b l H. discriminate.
    + split; reflexivity.
    + exact Htop.
  - split.
    + unfold gm, BB. rewrite m_vmmaps_init_model. cbn. lia.
    +
      rewrite m_vmmaps_init_model. split; [intros e []|]. cbn [vm_limit vm_start_brk]. split; [exact Hroom| lia].
Qed.

End WithCeiling.
