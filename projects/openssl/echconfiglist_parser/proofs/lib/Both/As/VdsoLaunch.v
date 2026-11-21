(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS b84e73ef): the ASan+UBSan binary's copy of As/VdsoLaunch.v (itself the ASan copy of Ub/VdsoLaunch.v).  It proves,
   from the launch, the facts about the vDSO/vvar pair [Run.vdso_segments kb sp mbase] that the
   time() walk at the run instance takes (Both/As/F_timeI.v, [atime_inst_run]), over the run's list
   [asegs ++ Run.vdso_segments kb sp mbase].  Every fact that names neither the binary's segments
   nor their end is Ref/VdsoLaunch.v's, used by import ([vd_lo], [vd_mid], [vd_top], the pair's
   form and arithmetic, [vdso_text_base_pair]); the binary's own segments end at or below
   [AIMG_TOP] ([ASegs.asegs_below_top]), and everything that names them is proved here.
   [vd_lo], [vd_mid] and [vd_top] are the pair's base, text base and top; the time walk's
   window is [[vd_lo, vd_top)], its text base [vd_mid]. *)
From Stdlib Require Import String.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Vdso.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec Mem VdsoImg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomStable.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import VdsoLaunch.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(** * The binary's segments end at or below [AIMG_TOP] *)

Lemma av_find_none : forall (x n : Z), 1 <= n -> AIMG_TOP <= x -> find_segment asegs x n = None.
Proof.
  intros x n Hn Hx.
  assert (Hb := asegs_below_top). revert Hb. generalize asegs as sl.
  induction sl as [|s0 rest IH]; intros Hb; [reflexivity|].
  pose proof (Hb s0 (in_eq s0 rest)) as H0.
  cbn [find_segment].
  match goal with |- (if ?b then _ else _) = None => destruct b eqn:E end.
  - exfalso. apply andb_true_iff in E. destruct E as [_ E2]. apply Z.leb_le in E2. lia.
  - exact (IH (fun s Hs => Hb s (in_cons s0 s rest Hs))).
Qed.

(* the binary's own segments hold no vDSO text *)
Lemma av_find_text_asegs : List.find seg_vdso_text asegs = None.
Proof. reflexivity. Qed.

(* Ref/VdsoLaunch.v's, which is Local there *)
Local Ltac vl_zbool :=
  repeat match goal with
         | |- context [Z.leb ?x ?y] => destruct (Z.leb_spec x y)
         | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y)
         end.

(** * The launch's pair *)

Section Launch.
  Variable kb : KernelBuild.
  Variables sp mbase : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hmb : valid_mmap_base mbase.

  Local Notation VLO := (vd_lo kb sp mbase).
  Local Notation VMID := (vd_mid kb sp mbase).
  Local Notation VTOP := (vd_top sp mbase).
  Local Notation VTAIL := (vdso_segments kb sp mbase).
  Local Notation VS := (asegs ++ VTAIL).

  Lemma av_lo_bounds : AIMG_TOP <= VLO /\ page_size <= VLO /\ AHI_LO <= VLO.
  Proof.
    pose proof (top_range sp mbase Hsp Hmb). unfold vd_lo. rewrite len_24576.
    unfold page_size, AIMG_TOP, AHI_LO. lia.
  Qed.

  Lemma av_order : VLO <= VMID /\ VMID <= VTOP /\ VTOP <= 2 ^ 64.
  Proof.
    pose proof (lo_mid kb sp mbase). pose proof (mid_top kb sp mbase).
    pose proof (top_range sp mbase Hsp Hmb). lia.
  Qed.

  (* above the binary's segments, the run's list answers with the pair *)
  Lemma av_find_run : forall x n, 1 <= n -> AIMG_TOP <= x ->
    find_segment VS x n = find_segment VTAIL x n.
  Proof.
    intros x n Hn Hx. rewrite find_segment_app. rewrite (av_find_none x n Hn Hx). reflexivity.
  Qed.

  Lemma av_find_text : forall x n, 1 <= n -> VMID <= x -> x + n <= VTOP ->
    find_segment VS x n = Some (vt_seg kb VMID).
  Proof.
    intros x n Hn H1 H2. pose proof av_lo_bounds as (L1 & L2 & _). pose proof (lo_mid kb sp mbase) as LM.
    rewrite (av_find_run x n Hn) by lia. rewrite (find_two kb sp mbase Hsp Hmb).
    vl_zbool; cbn [andb]; first [exfalso; lia | reflexivity].
  Qed.

  (** ** The pair's window: every tail byte is in [[VLO, VTOP)], every byte there is a tail byte,
      and both segments have bytes *)

  Lemma av_tail_in_window : forall (x : Z) s, find_segment VTAIL x 1 = Some s -> VLO <= x < VTOP.
  Proof.
    intros x s Hf. rewrite (find_two kb sp mbase Hsp Hmb) in Hf. revert Hf.
    pose proof (lo_mid kb sp mbase). pose proof (mid_top kb sp mbase).
    vl_zbool; cbn [andb]; intros Hf; first [discriminate Hf | lia].
  Qed.

  Lemma av_window_covered : forall (x : Z), VLO <= x < VTOP -> find_segment VTAIL x 1 <> None.
  Proof.
    intros x Hx. rewrite (find_two kb sp mbase Hsp Hmb).
    pose proof (lo_mid kb sp mbase). pose proof (mid_top kb sp mbase).
    vl_zbool; cbn [andb]; first [discriminate | exfalso; lia].
  Qed.

  Lemma av_tail_nonempty : forall s, In s VTAIL -> (0 < seg_size s)%N.
  Proof.
    intros s Hin. rewrite (tail_two kb sp mbase Hsp Hmb) in Hin.
    destruct Hin as [<- | [<- | []]].
    - pose proof (vv_size kb sp mbase) as E. lia.
    - pose proof (vt_size kb sp mbase) as E. lia.
  Qed.

  (** ** The image is read through the text segment *)

  Lemma av_mr_text : forall o, 0 <= o < RVDSO_SIZE ->
    memory_read VS (wa (VMID + o)) 1 = Some [rvdso_byte o].
  Proof.
    intros o Ho. pose proof av_lo_bounds as (L1 & L2 & _). pose proof (lo_mid kb sp mbase). pose proof (mid_top kb sp mbase).
    pose proof (top_range sp mbase Hsp Hmb) as [T1 T2]. pose proof RVDSO_SIZE_val as HS.
    assert (Hu : bv_unsigned (wa (VMID + o)) = VMID + o) by (apply wa_unsigned; lia).
    assert (Hf : find_segment VS (bv_unsigned (wa (VMID + o))) 1 = Some (vt_seg kb VMID))
      by (rewrite Hu; apply av_find_text; lia).
    rewrite (memory_read_found _ _ _ Hf (vt_r kb sp mbase)), Hu, (vt_base kb sp mbase Hsp Hmb), vt_bytes.
    replace (VMID + o - VMID) with o by ring.
    rewrite srb1, (rvdso_byte_some o Ho). reflexivity.
  Qed.

  Lemma av_rom_text : forall o, 0 <= o < RVDSO_SIZE ->
    seg_rom VS (wa (VMID + o)) = rvdso_peek o.
  Proof. intros o Ho. unfold seg_rom. rewrite (av_mr_text o Ho), (rvdso_peek_in o Ho). reflexivity. Qed.

  Lemma av_ro_text : forall o, 0 <= o < RVDSO_SIZE -> ro_addr VS (wa (VMID + o)) = true.
  Proof.
    intros o Ho. pose proof av_lo_bounds as (L1 & L2 & _). pose proof (lo_mid kb sp mbase). pose proof (mid_top kb sp mbase).
    pose proof (top_range sp mbase Hsp Hmb) as [T1 T2]. pose proof RVDSO_SIZE_val as HS.
    assert (Hu : bv_unsigned (wa (VMID + o)) = VMID + o) by (apply wa_unsigned; lia).
    assert (Hf : find_segment VS (bv_unsigned (wa (VMID + o))) 1 = Some (vt_seg kb VMID))
      by (rewrite Hu; apply av_find_text; lia).
    rewrite (ro_addr_found _ _ _ Hf), vt_w. reflexivity.
  Qed.

  Lemma av_rom_pair : rvdso_rom VS VMID.
  Proof.
    pose proof av_lo_bounds as (L1 & L2 & _). pose proof (lo_mid kb sp mbase). pose proof (mid_top kb sp mbase).
    pose proof (top_range sp mbase Hsp Hmb) as [T1 T2].
    unfold rvdso_rom. rewrite RVDSO_SPAN_val.
    split; [lia|]. split; [exact (mid_al kb sp mbase)|]. split; [lia|].
    intros o Ho. exact (conj (av_rom_text o Ho) (av_ro_text o Ho)).
  Qed.

  Lemma av_mid_al : VMID mod 4096 = 0.
  Proof. exact (mid_al kb sp mbase). Qed.

  (** ** The machine declines at a pc in the text (RiscvSemantics.fetch_failure's vdso_text_at
      arm): no fetch path reads the "r--" text *)

  Lemma av_code_read_text : forall (a : word) (n : N), 1 <= Z.of_N n -> VMID <= bv_unsigned a ->
    bv_unsigned a + Z.of_N n <= VTOP -> code_read VS a n = None.
  Proof.
    intros a n Hn H1 H2. exact (code_read_found _ a n _ (av_find_text (bv_unsigned a) (Z.of_N n) Hn H1 H2) (vt_x kb sp mbase)).
  Qed.

  Lemma av_code_read_ov_text : forall m (a : word) (n : N), 1 <= Z.of_N n -> VMID <= bv_unsigned a ->
    bv_unsigned a + Z.of_N n <= VTOP -> code_read_ov VS m a n = None.
  Proof.
    intros m a n Hn H1 H2.
    exact (code_read_ov_found _ m a n _ (av_find_text (bv_unsigned a) (Z.of_N n) Hn H1 H2) (vt_x kb sp mbase)).
  Qed.

  Lemma av_fw_none : forall (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 4 <= VTOP ->
    fetch_word VS a = None.
  Proof.
    intros a H1 H2. unfold fetch_word.
    rewrite (av_code_read_text a 4 ltac:(cbn [Z.of_N]; lia) H1 ltac:(cbn [Z.of_N]; lia)).
    match goal with |- context [if negb ?b then _ else _] => destruct b end; reflexivity.
  Qed.

  Lemma av_fwo_none : forall m (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 4 <= VTOP ->
    fetch_word_ov VS m a = None.
  Proof.
    intros m a H1 H2. unfold fetch_word_ov.
    rewrite (av_code_read_ov_text m a 4 ltac:(cbn [Z.of_N]; lia) H1 ltac:(cbn [Z.of_N]; lia)).
    match goal with |- context [if negb ?b then _ else _] => destruct b end; reflexivity.
  Qed.

  Lemma av_fh_none : forall (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 2 <= VTOP ->
    fetch_half VS a = None.
  Proof.
    intros a H1 H2. unfold fetch_half.
    rewrite (av_code_read_text a 2 ltac:(cbn [Z.of_N]; lia) H1 ltac:(cbn [Z.of_N]; lia)). reflexivity.
  Qed.

  Lemma av_fho_none : forall m (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 2 <= VTOP ->
    fetch_half_ov VS m a = None.
  Proof.
    intros m a H1 H2. unfold fetch_half_ov.
    rewrite (av_code_read_ov_text m a 2 ltac:(cbn [Z.of_N]; lia) H1 ltac:(cbn [Z.of_N]; lia)). reflexivity.
  Qed.

  Lemma av_fha_none : forall m (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 2 <= VTOP ->
    fetch_half_any VS m a = None.
  Proof. intros m a H1 H2. unfold fetch_half_any. rewrite (av_fh_none a H1 H2), (av_fho_none m a H1 H2). reflexivity. Qed.

  Lemma av_fta_none : forall m (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 2 <= VTOP ->
    fetch_tail_any VS m a = None.
  Proof.
    intros m a H1 H2. unfold fetch_tail_any. rewrite (av_fha_none m a H1 H2).
    match goal with |- context [if negb ?b then _ else _] => destruct b end; reflexivity.
  Qed.

  Lemma av_ff_unm : forall m (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 1 <= VTOP ->
    fetch_failure VS m a = MachineUnmodeled.
  Proof.
    intros m a H1 H2. unfold fetch_failure.
    rewrite (vdso_text_at_found _ a _ (av_find_text (bv_unsigned a) 1 ltac:(lia) H1 H2)), vt_t. reflexivity.
  Qed.

  Lemma av_unm_text : forall ms, ms_pc ms = Z_to_bv 64 (VMID + 1460) ->
    RiscvSemantics.step VS ms = MachineUnmodeled.
  Proof.
    intros ms Hpc. pose proof av_lo_bounds as (L1 & L2 & _). pose proof (lo_mid kb sp mbase). pose proof (mid_top kb sp mbase).
    pose proof (top_range sp mbase Hsp Hmb) as [T1 T2].
    assert (Hu : bv_unsigned (Z_to_bv 64 (VMID + 1460)) = VMID + 1460) by (apply wa_unsigned; lia).
    unfold RiscvSemantics.step, RiscvSemantics.step_accesses. rewrite Hpc.
    rewrite (av_fw_none (Z_to_bv 64 (VMID + 1460))) by (rewrite Hu; lia).
    rewrite (av_fwo_none (ms_mem ms) (Z_to_bv 64 (VMID + 1460))) by (rewrite Hu; lia).
    rewrite (av_fta_none (ms_mem ms) (Z_to_bv 64 (VMID + 1460))) by (rewrite Hu; lia).
    rewrite (av_ff_unm (ms_mem ms) (Z_to_bv 64 (VMID + 1460))) by (rewrite Hu; lia).
    reflexivity.
  Qed.

  (** ** The entry at text base + 1460 is clock_gettime's ([Lib/VdsoImg.rvdso_cgt_off_entry]) *)

  Lemma av_vimg : vdso_image VS = Some (vt_seg kb VMID, RVDSO_IMAGE).
  Proof.
    unfold vdso_image, vdso_text_seg.
    rewrite (find_app_none _ seg_vdso_text asegs VTAIL av_find_text_asegs), (tail_two kb sp mbase Hsp Hmb).
    change (List.find seg_vdso_text [vv_seg VLO; vt_seg kb VMID]) with (Some (vt_seg kb VMID)).
    cbv beta iota zeta. rewrite vt_bytes, image_of_bytes_self. reflexivity.
  Qed.

  Lemma av_ent_text : vdso_entry_fn VS (Z_to_bv 64 (VMID + 1460)) = Some VdsoClockGettime.
  Proof.
    pose proof av_lo_bounds as (L1 & L2 & _). pose proof (lo_mid kb sp mbase). pose proof (mid_top kb sp mbase).
    pose proof (top_range sp mbase Hsp Hmb) as [T1 T2].
    pose proof RVDSO_SIZE_val as HS.
    assert (Hu : bv_unsigned (Z_to_bv 64 (VMID + 1460)) = VMID + 1460) by (apply wa_unsigned; lia).
    unfold vdso_entry_fn. rewrite av_vimg. cbv beta iota zeta.
    rewrite (vt_base kb sp mbase Hsp Hmb), Hu.
    change (Z.of_N (vi_size RVDSO_IMAGE)) with RVDSO_SIZE.
    replace (VMID + 1460 - VMID) with RVDSO_CGT_OFF by (unfold RVDSO_CGT_OFF; ring).
    vl_zbool; cbn [andb]; first [exfalso; lia | exact rvdso_cgt_off_entry].
  Qed.

  (** ** The heap-ceiling record's [hvdso] and [aceil] against the pair *)

  Section Ceil.
    Context {HCEIL : HeapCeil}.

    (* [hvdso] is the launch's AT_SYSINFO_EHDR plus 1460 ([AsInstanceMain.main_ceil_vdso]) *)
    Lemma av_hvdso : hvdso = bv_unsigned (vdso_text_base kb sp mbase) + 1460 -> VMID + 1460 = hvdso.
    Proof. intros E. rewrite E, (vdso_text_base_pair kb sp mbase Hsp Hmb). reflexivity. Qed.

    (* the pair's top is at or below the heap ceiling's page *)
    Lemma av_top_aceil : hceil = bv_unsigned sp - stack_max_size -> VTOP <= aceil.
    Proof.
      intros E. pose proof (top_facts sp mbase) as (T1 & _ & _ & T4).
      unfold aceil. rewrite E.
      pose proof (Z.mod_pos_bound (bv_unsigned sp - stack_max_size) 4096 ltac:(lia)) as M.
      pose proof (Z.div_mod (bv_unsigned sp - stack_max_size) 4096 ltac:(lia)) as D.
      pose proof (Z.div_mod VTOP 4096 ltac:(lia)) as D2. rewrite T1 in D2.
      assert (VTOP / 4096 <= (bv_unsigned sp - stack_max_size) / 4096) by (apply Z.div_le_mono; lia).
      lia.
    Qed.
  End Ceil.
End Launch.
