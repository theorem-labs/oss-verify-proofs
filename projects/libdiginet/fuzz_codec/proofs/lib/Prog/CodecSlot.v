(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/U/Prog/LLVMFuzzerTestOneInput_cfb.v
   at bc49657c087aa7d6ab0af1ffb2cb67fa08b15de1; the same text at fuzz_egress's module path, over this unit's
   lib/U/Prog/LLVMFuzzerTestOneInput_c.v and _fr.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/U/Prog/LLVMFuzzerTestOneInput_cfb.v, with its module paths changed; 185 of its 213 lines of code are new or changed and 104 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/CodecSlotCF.v, with its module paths, module names and addresses changed; 85 of its 246 lines of code are new or changed and 52 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO0i YO0f YO0d YO05
  YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Contract KindBGlue FrameAPI.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require MemNorm Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require MState Mem Frame Exec.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require codec_cells LLVMFuzzerTestOneInput_c.
Import ListNotations.
Local Open Scope Z_scope.


Lemma codec_img_check : forall B, ms_segs B = Img0.rsegs -> img_check B 4294967296 = true.
Proof. intros B H. unfold img_check. rewrite H. vm_compute. reflexivity. Qed.

Lemma ret_pc_even_Z : forall z, z mod 2 = 0 -> MState.ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz.
  assert (E : Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64)).
  { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Zmod_mod. reflexivity. }
  rewrite E. apply MState.ret_pc_even; [apply Z.mod_pos_bound; lia|]. rewrite kb_mod2_land. exact Hz.
Qed.

(* main's contract reads the RELRO tables (codec_cells.relro_img); they lie in the frame's frame_RELRO, so the
   frame's G_img_c gives their image bytes, and MemNorm.normalize keeps them (they are not ro_addr). *)
Lemma relro_img_normalize : forall mem,
  (forall a, in_globals frame_RELRO a -> mbyte Img0.rsegs mem a = seg_rom Img0.rsegs (Z_to_bv 64 a)) ->
  codec_cells.relro_img (MemNorm.normalize Img0.rsegs mem).
Proof.
  intros mem HG i Hi. unfold codec_cells.RELRO_LEN in Hi.
  assert (HIN : in_globals frame_RELRO (codec_cells.RELRO_BASE + i)).
  { exists 0x1f1e0, 728. split; [unfold frame_RELRO; cbn; left; reflexivity | unfold codec_cells.RELRO_BASE; lia]. }
  pose proof (HG _ HIN) as E.
  unfold Mem.mrd, MemNorm.normalize.
  destruct (Mem.ro_addr Img0.rsegs (Mem.wa (codec_cells.RELRO_BASE + i))); [reflexivity|].
  exact E.
Qed.

(* main's contract also needs its stack window outside the RELRO tables. The tables lie in a loaded segment of
   the image, so img_low puts them below alloc_ceiling, as codec_slot shows for the addresses of the window
   (STN); the window lies above alloc_ceiling. *)
Lemma relro_in_segment :
  exists seg, find_segment Img0.rsegs (codec_cells.RELRO_BASE + codec_cells.RELRO_LEN - 1) 1 = Some seg.
Proof.
  assert (HS : match find_segment Img0.rsegs (codec_cells.RELRO_BASE + codec_cells.RELRO_LEN - 1) 1 with
               | Some _ => true | None => false end = true) by (vm_compute; reflexivity).
  revert HS. destruct (find_segment Img0.rsegs (codec_cells.RELRO_BASE + codec_cells.RELRO_LEN - 1) 1) as [seg|];
    intros HS; [exists seg; reflexivity | discriminate HS].
Qed.

Section GM.
Context {AM : AllocMode} {fx : FPState}.

Lemma evt_SR_gm : forall segs ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt segs Q ms -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', Q ms' -> @SR segs AM (mkCfg ms' md) P) -> @SR segs AM (mkCfg ms md) P.
Proof.
  intros segs ms Q md P [final [Hs HQ]] Hh Hl K T HK.
  eapply YK15.rz_msteps; [exact Hh | exact Hl | apply lib_msteps_frame; exact Hs |].
  exact (K final HQ T HK).
Qed.

Lemma kb_run_gm : forall (B : malloc_syms) regs pc mem md
    (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt (ms_segs B) (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom (ms_segs B)) /\
      K R pc' mem')
    (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom (ms_segs B))) ->
  (forall R pc' mem' regs', K R pc' mem' -> (forall r, getr regs' r = getr R r) ->
     @SR (ms_segs B) AM (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) P) ->
  @SR (ms_segs B) AM (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros B regs pc mem md K P Hh Hl HE HK.
  eapply (evt_SR_gm (ms_segs B) (mkst regs pc mem (seg_rom (ms_segs B))) _ md P);
    [exact (RegisterBridge.canonical_contract_transport (ms_segs B) _ (mkst regs pc mem (seg_rom (ms_segs B))) HE)
    | exact Hh | exact Hl |].
  intros ms' (can & (R & pc' & mem' & -> & HKR) & Heq).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' HKR). apply kb_getr_eqv. exact HR.
Qed.

End GM.

Section CodecSlot.
Context {AM : AllocMode} {fx : FPState} {rc : RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis HSEGS : ms_segs B = Img0.rsegs.
Hypothesis HLIBK : forall pl fs K, LIBK pl fs K = K (LL 0 fs []).
Hypothesis HDELTA : forall n b, lib_delta n b = b.
Hypothesis HEMPTY : empty = 0x30740.
Hypothesis HHEAD : @sk_ofl_head SH = 0x50ef0.
Hypothesis HLOCK : @sk_ofl_lock SK = 0x50ee8.
Hypothesis HTHR : @sk_threaded SK = 0x50ac0 + 1.
Hypothesis HRA : ra mod 2 = 0.
Hypothesis HMAIN : LLVMFuzzerTestOneInput_c.codec_main_contract.

Lemma codec_slot : forall j,
  @lib_contract_gm AM fx rc LS B API SH SK [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.
Proof.
  intros j L A regs mem md p n pl b K HP _ HGR HRO _ Hfrm HK.
  rewrite HLIBK.
  destruct HP as [HP0 [HLEN [HD [Hres [Hroom [HSink [Hfd [Hsorted Hsp47]]]]]]]].
  destruct HP0 as [HM [HW [HB [Hid [Hra [Hal [Hsp [HspHi [HWstack [Htp [HWerrno
    [Hptr [Hsize [Hlive Hro]]]]]]]]]]]]]].
  pose proof alloc_ceiling_val as Hceil.
  pose proof (img_low_of_check B 4294967296 (codec_img_check B HSEGS)) as IMG0.
  assert (IMG : img_low B) by (apply IMG0; lia). clear IMG0.
  assert (PR : 0 <= p /\ p + n <= alloc_ceiling).
  { destruct Hlive as [[-> ->] | [Hpos [q [Hq <-]]]]; [rewrite HEMPTY; lia |].
    pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q n HM Hq). lia. }
  assert (Hptr' : bv_unsigned (getr regs 10) = p) by (rewrite Hptr; apply MState.unsigned_lit; lia).
  assert (Hsz' : bv_unsigned (getr regs 11) = Z.of_nat (length pl)) by (rewrite Hsize, <- HLEN; apply MState.unsigned_lit; lia).
  unfold SLOT_STACK in *.
  assert (HDB : Mem.bytes_at Img0.rsegs mem p pl).
  { rewrite <- HSEGS. split; [lia|]. split; [lia|].
    intros i Hi. change (Mem.mrd (ms_segs B) mem (Mem.wa (p + Z.of_nat i)) = nth_error pl i).
    change (Mem.mrd (ms_segs B) mem (Mem.wa (p + Z.of_nat i))) with (mbyte (ms_segs B) mem (p + Z.of_nat i)).
    rewrite (HD (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity. }
  rewrite HSEGS in HRO, HWstack, HWerrno.
  assert (HRL : codec_cells.relro_img (MemNorm.normalize Img0.rsegs mem)).
  { apply relro_img_normalize. intros a Ha. rewrite <- HSEGS. exact (HGR a Ha). }
  assert (STN : Frame.stk Img0.rsegs (MemNorm.normalize Img0.rsegs mem) (spZ regs - 16384) (spZ regs)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (FS : find_segment Img0.rsegs a 1 = None).
    { destruct (find_segment Img0.rsegs a 1) as [seg|] eqn:E; [|reflexivity]. exfalso.
      destruct IMG as [_ IMG2]. rewrite HSEGS in IMG2. pose proof (IMG2 a seg E). lia. }
    assert (RO : Mem.ro_addr Img0.rsegs (Z_to_bv 64 a) = false).
    { unfold Mem.ro_addr. rewrite MState.unsigned_lit by lia. rewrite FS. reflexivity. }
    pose proof (HWstack a ltac:(lia)) as Hw.
    unfold writable_at, wview in Hw.
    destruct (mem (Z_to_bv 64 a)) as [bb|] eqn:E.
    - split.
      + unfold wview, MemNorm.normalize, Mem.wa. rewrite RO, E. discriminate.
      + exists bb. unfold Mem.mrd, MemNorm.normalize, Mem.wa. rewrite RO, E. reflexivity.
    - exfalso. rewrite MState.unsigned_lit in Hw by lia. rewrite FS in Hw. apply Hw. reflexivity. }
  assert (HRD : codec_cells.disj (spZ regs - 16384) (spZ regs - (spZ regs - 16384))
                  codec_cells.RELRO_BASE codec_cells.RELRO_LEN).
  { unfold codec_cells.disj. right. destruct relro_in_segment as [seg E].
    destruct IMG as [_ IMG2]. rewrite HSEGS in IMG2. pose proof (IMG2 _ seg E). lia. }
  pose proof HMAIN as MAIN.
  unfold LLVMFuzzerTestOneInput_c.codec_main_contract, LLVMFuzzerTestOneInput_c.LLVM_CODEC,
    LLVMFuzzerTestOneInput_c.LLVM_CODEC_STACK in MAIN.
  specialize (MAIN (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
    (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
    (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
    (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
    (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr (MemNorm.normalize Img0.rsegs mem)
    (spZ regs - 16384) pl).
  rewrite Hptr', Hsz' in MAIN.
  specialize (MAIN (MemNorm.bytes_at_normalize Img0.rsegs mem p pl HRO HDB) eq_refl (MemNorm.mem_inv_normalize Img0.rsegs mem)).
  change (bv_unsigned (getr regs 2)) with (spZ regs) in MAIN.
  specialize (MAIN STN ltac:(lia) Hal ltac:(left; lia) ltac:(pose proof alloc_ceiling_lt; lia) HRL HRD).
  pose proof (MemNorm.evt_normalize Img0.rsegs _ _ _ _ _ _ _ _ wx_apart_rsegs HRO MAIN) as RUN.
  clear MAIN.
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as [Hhalt [Hlazy _]].
  specialize (HK (LL 0 (m_fs md) [])).
  set (SP := spZ regs) in *.
  assert (HSPr : 0 <= SP < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 (getr regs 2)) as R; unfold bv_modulus in R; exact R).
  apply (kb_run_gm B regs (Z_to_bv 64 ENTRY) mem md
    (fun R pc' mem' => pc' = MState.ret_pc (getr regs 1) /\ getr R 10 = Z_to_bv 64 0 /\
       (forall r, callee_saved r -> getr R (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
       Frame.munch [(SP - 0x250, SP)] mem mem' /\ Frame.wmono Img0.rsegs mem mem' /\ MemNorm.ro_same Img0.rsegs mem mem')
    (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
        c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom (ms_segs B))) md' /\
        frm_zero (@fp_csr fx') /\
        lib_post_g B API [] SLOT_STACK L A regs mem md p n b (LL 0 (m_fs md) []) L' A' regs' mem' md' /\ True));
    [exact Hhalt | exact Hlazy | | | exact HK].
  - rewrite HSEGS. eapply Exec.evt_mono; [exact RUN|].
    intros s (s0 & HQ & Hrel & Hsame).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' & Es0 & MU0 & WM0 & _ & _).
    subst s0.
    destruct Hrel as (Er & Ef & Epc & Esv & Ers & Efc & Erom & Emem).
    destruct s as [sr sf spc ssv srs sfc smem srom]. cbn in Er, Ef, Epc, Esv, Ers, Efc, Erom, Emem, Hsame.
    exists sr, spc, smem. split; [subst sf ssv srs sfc srom; reflexivity|].
    split; [exact Epc|].
    split; [rewrite Er; reflexivity|].
    split; [rewrite Er; kb_saved|].
    pose proof (MemNorm.mem_rel_normalize Img0.rsegs mem HRO) as Rn.
    split; [exact (MemNorm.munch_rel Img0.rsegs _ _ _ _ _ Rn Emem Hsame MU0)|].
    split; [exact (MemNorm.wmono_rel Img0.rsegs _ _ _ _ Rn Emem Hsame WM0)|].
    exact Hsame.
  - intros R pc' mem' regs' (Epc & E10 & Esv & MU & WM & Hsame) Hreg.
    unfold SLOT_STACK in *.
    apply SR_ret.
    exists fx, L, A, regs', mem', md.
    split; [rewrite Epc, Hra, (ret_pc_even_Z ra HRA); reflexivity|].
    split; [exact Hfrm|].
    split; [|exact I].
    assert (OUT : forall x, 0 <= x < alloc_ceiling -> Frame.outside [(SP - 0x250, SP)] x)
      by (intros x Hx; apply outside_one; lia).
    assert (MB : forall x, 0 <= x < alloc_ceiling -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x)
      by (intros x Hx; unfold mbyte; rewrite (MU (Z_to_bv 64 x)); [reflexivity|];
          rewrite MState.unsigned_lit by lia; apply OUT; exact Hx).
    unfold lib_post_g. cbn [ll_ret ll_fs ll_out].
    split. { eapply (kb_MR_A B API L A mem mem' md); [exact HM | exact MU |]. intros x Hx _. apply OUT. exact Hx. }
    split; [exact HW|]. split; [exact HB|]. split; [exact Hid|].
    split; [rewrite Hreg; exact E10|].
    split; [intros r Hr; rewrite Hreg; apply Esv; exact Hr|].
    split. { exists (m_vmmaps md), (m_fds md), (m_statpins md). split; [apply os_upd_self | reflexivity]. }
    split. { intros q k0 Hin. exists q. split; [exact Hin | reflexivity]. }
    split.
    { intros a Ha Hns.
      assert (Ho : Frame.outside [(SP - 0x250, SP)] a).
      { apply outside_one. destruct (Z_lt_le_dec a (SP - 0x250)) as [|H1]; [left; lia|]. right.
        destruct (Z_le_gt_dec SP a) as [|H2]; [lia|]. exfalso. apply Hns. left. unfold SP in *. lia. }
      unfold mbyte, writable_at, wview. rewrite (MU (Z_to_bv 64 a)); [split; reflexivity|].
      rewrite MState.unsigned_lit by lia. exact Ho. }
    split.
    { intros a Himg _ _ _ _. destruct IMG as [IMG1 _]. pose proof (IMG1 a Himg) as Ha.
      unfold mbyte, writable_at, wview. rewrite (MU (Z_to_bv 64 a)); [split; reflexivity|].
      rewrite MState.unsigned_lit by lia. apply OUT. exact Ha. }
    split. { intros a (lo & len & Hin & _). destruct Hin. }
    split.
    { intros q k0 i Hin Hneq Hi. pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k0 HM Hin). apply MB. lia. }
    split.
    { intros a Hs. rewrite HSEGS. unfold writable_at. apply WM.
      destruct Hs as [Hs|Hs]; [exact (HWstack a Hs) | exact (HWerrno a Hs)]. }
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsorted|].
    split.
    { destruct HSink as [[T1 T2] [W1 F1]]. split; [split|split; [|exact F1]].
      - intros k0 Hk. rewrite MB; [apply T1; exact Hk|]. rewrite HTHR. lia.
      - intros k0 Hk. rewrite MB; [apply T2; exact Hk|]. rewrite HLOCK. lia.
      - intros k0 Hk. rewrite MB; [apply W1; exact Hk|]. rewrite HHEAD. lia. }
    split. { rewrite HSEGS. exact (MemNorm.ro_agree_same Img0.rsegs mem mem' HRO Hsame). }
    split. { rewrite HDELTA. exact Hres. }
    intros i Hi. apply MB. lia.
Qed.

End CodecSlot.

Ltac last_conj FF :=
  repeat match type of FF with _ /\ _ => let H := fresh "Hf" in destruct FF as [H FF] end.

Theorem plain_halts_of_frame : LLVMFuzzerTestOneInput_c.codec_main_contract -> frame_plain ->
  OSSVerify.libdiginet.fuzz_codec.Statements.plain_halts.
Proof.
  intros HMAIN HFR. destruct (frame_plain_split HFR) as (B & API & LS & SH & SK & ra & empty & HF & HLAST).
  destruct HF as (HSEGS & HRA & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & HHEAD & HLOCK & HTHR & HEMPTY & _ & _ & _ & _ & HLIBK & HDELTA & _ & _).
  apply (HLAST [] (fun _ _ => True)).
  - intros a (lo & len & Hin & _). destruct Hin.
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj. rewrite lib_contract_g_gm. eapply codec_slot; eassumption.
Qed.

Theorem plain_halts_may_fail_of_frame : LLVMFuzzerTestOneInput_c.codec_main_contract -> frame_plain_mf ->
  OSSVerify.libdiginet.fuzz_codec.Statements.plain_halts_may_fail.
Proof.
  intros HMAIN (B & API & LS & SH & SK & ra & empty & FF). last_conj FF.
  apply (FF [] (fun _ _ => True)).
  - intros a (lo & len & Hin & _). destruct Hin.
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj. eapply codec_slot; eassumption.
Qed.
