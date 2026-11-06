(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-29 (PresetStrlenPort, c-libc-stdio lane): fuzz_preset.asan's strlen interceptor, called at
   its trampoline __wrap_strlen 0x42d18, in the contract of the second allocator instance:
   `ps_strlen_realizes_cf : forall B, TfibSyms B -> PsRealStrlen B -> astrlen_realizes_cf tfibsegs B 0x42d18`
   (lib/Reusable/YGcfStr.v, the text of commit 3e37c5476fe), and its CLOSED form `ps_strlen_realizes_cf_closed : forall
   B, TfibSyms B -> astrlen_realizes_cf tfibsegs B 0x42d18` (PsRealStrlen discharged by tfibsyms_real_strlen from the
   generated AF0m.v, 2026-10-29). Image A (fuzz_preset.asan) only.
   2026-10-29 (pstr102, #102 pin A' asan 1be0f53d, twin bff8519b): RelocA's relocation (blob d6ecdc9b0867) plus
   presetstr-ro 45e489ec67c7's memnorm twin `ps_strlen_realizes_cfm` / `ps_strlen_realizes_cfm_closed`
   (astrlen_realizes_cfm, YGcfStr.v), its A' numerals by symbol + offset (only the entry 0x42c84 -> 0x42d18 occurs
   in the added text); pc_strlen_A cites CfImgA's cf_pc_strlen by field name, as YGcfStr.v holds no pc any more.
   rule 24: no function proved. This file is a PORT of an existing composition; it composes:

   DONORS
   - the composition: origin/cold/port-state-rt-str 17818dd9abc, proofs/omx-clap-core/fuzz_state/lib/A/FSstrlen.v
     (fuzz_state's strlen at its interceptor, astrlen_realizesU over cgif's AR). Every lemma below names its donor
     lines FSstrlen.v:N-M;
   - FSsl.v (same ref): msteps_to_bz (:40-45) and evt_to_bz (:47-50), the lib/Lib -> kit run conversion, here
     between preset's lib/Lib and lib/K;
   - FSupoison.v (same ref): aview_at (:69-70);
   - the shadow bridge: A/PSbz_str.v, a port of fuzz_state's FSbz_str.v (same ref), itself a port of port-fm's
     origin/cold/port-fm-rtscan cedf3d02589 proofs/omx-clap-core/fuzz_manifest/lib/A/FMbz_str.v;
   - the walk: this tree's lib/K, bzip2's kit (proofs/bzip2/bzip2_compress_target/lib/K at origin/ossv/recipes
     c8557374ad2e) relocated to preset: K/A/I_strlen_entry.v `istrlen_wrap_closed` (= istrlen_wrap_spec rip_proof:
     the trampoline step, then I_strlen.v istrlen_spec with K/A/R_isPoisoned.v rip_proof; musl's strlen 0x9b904 is
     walked inside, K/A/F_strlen.v, so the donor's SL hypothesis / FSsl.sl_proof has no counterpart here);
   - the evt -> SRr bridge: lib/Reusable/YEvtSRr.v (srr_of_evt, stk_of_apresent), a port of port-fm's
     origin/cold/port-fm-rtscan 10d0c5cd0be FMbz_bridge.v, in place of the donor's FSbz_bridge.v;
   - the transports: c-asan-rt's lib/MemNorm.v (normalize_cj, evt_normalize_cj, ...) and lib/Lib/RegisterBridge.v
     (evt_register_transport) with lib/Lib/Regs6ss.v, already in this tree (byte-identical to the donor's copies
     after the module path fuzz_state -> fuzz_preset; measured with diff).

   WHAT CHANGED, lemma by lemma (P = ported with paths changed; R = re-derived for preset A; S = swapped AR -> ARcf;
   N = new shape, forced by the target text):
     Hwx_ps, wx_apart_ps, tsegs_below, PS_IMG_TOP        R  FSstrlen.v:91-103 (fs.asan's image -> preset's tfibsegs;
                                                            vm_compute; preset's last PT_LOAD ends 0x5ff7d0 < 0x600000)
     seg_tops_below, find_segment_below/_spec            P  :97-98, :105-124
     find_segment_high, cj_keep_high, seg_addr_below,    R  :126-161 (I0.rsegs / BI.asegs -> tfibsegs / asegs;
       bz_mem_inv_normalize                                 the donor's I0.rsegs is fs's Asan image; preset's lib/Img0.v
                                                            rsegs is the PLAIN image, so it is NOT used here)
     bz_msteps_l, bz_evt_l, msteps_to_bz, evt_to_bz,     P  :164-195, FSsl.v:40-50
       st_at, walk_at, bz_transport
     W.tramp_strlen + bz_strlen                          R  :197-243 -> bz_strlen over istrlen_wrap_closed (entry
                                                            0x42d18 = `jal zero, 0x42da8`, I_strlen_entry.v); the kit's
                                                            premises are bzip2's: `kHighShadowEnd + 8 <= lo`, `0 < s`
     getr_nz, land_m2_mod, ret_pc_ok, aregs_of_mkR,      P  :246-302
       a0_of_mkR, option_map_unsigned_inj
     ro_agree_of_rom_view, norm_keep_high,               P  :305-348 (image names only)
       stk_norm_high, chk_norm
     byte_at, mk_slack, slack_len, length_mk_slack,      P  :351-364
       le_byte_1
     cstr_bytes, cstr_nonul                              N  :366-417 -> bytes_at_mk, fb_bytes, fb_nonul: the
                                                            target gives `first_byte ... x (k + 1) 0 k` over aview,
                                                            not the donor's `cstr` over a list, so the string is the
                                                            list of the bytes read (mk_slack at x, Z.to_nat k)
     keep_range, mrd_high, wview_of_mrd, rw_of_ro,       P  :420-515
       nth_Z_to_le_bytes, le_byte_8, ro_c8_of_val_mem,
       ro_cons8
     agree_cells                                         S  :430-441 without the user-poison window U
     fs_tl_cells / fs_rt_rest / fs_walk_cells /          R  :518-573 -> val_mem_of_holds8, c8_norm, c1_norm and
       fs_tl_norm / fs_rest_norm / fs_walk_cells_of         walk_cells: preset's cells are the kit's own (K/A/R_m2s.v
                                                            m2s_cells, I_strnlenw.v icells_sn, I_strlen.v icells_sl)
     FsShadowSyms, tfib_D_shadow_vals, tl_cells, FsRtCells  S  :577-599 -> 14 of the 15 cells come from ARcf's const
                                                            cells (amc_const) under TfibSyms B (ts_const: as_const B =
                                                            Tfib_const, lib/A/AF0m.v), which the donor's theorem
                                                            already took; the one cell left is the named premise
                                                            PsRealStrlen B (below)
     ush_bounds                                          dropped (no U: ARcf carries hidden heads as the ghost list
                                                            Hp, threaded unchanged)
     walk_cells                                          S  :617-628
     cstr_off_frame                                      N  :632-639 -> str_off_frame, from the target's own frame
                                                            premise (2 * ESTACK) in place of cstr_ok's ceiling bound
     post_of_walk                                        S  :643-745, AR -> ARcf: AR_frame_law_cf / AR_stack_law_cf
                                                            from AR_laws_ok_cf (PROVED, YG0lawscf.v; not a premise);
                                                            the user-poison clause is dropped; the window is the walk's
                                                            D = 2224 (ISTRLEN_DEPTH) inside the post's 2 * ESTACK
     fs_strlen_core                                      S  :749-825 -> ps_strlen_core
     fs_strlen_realizesU                                 S  :828-835 -> ps_strlen_realizes_cf (cgif's call form over
                                                            ARcf, YGcfStr.v; S0's ARU form is not used)
     fs_strlen_realizes, ikit_img_end                    dropped (fuzz_state's ARU -> AR step; a fuzz_state image fact)

   PREMISES. The donor's theorem took AR_laws tfibsegs B, TfibSyms B, FsShadowSyms B and FsRtCells B. Here:
   AR_laws_cf is proved (AR_laws_ok_cf), not a premise; TfibSyms B is kept (preset's lib/A/AF0m.v record; its ts_const
   gives the shadow cell and its .got slot, so FsShadowSyms is not needed); FsRtCells B becomes PsRealStrlen B, ONE
   cell, the only premise the donor did not have in this form: __interception::real_strlen at 0xa3d28 holds 0x9b904
   (musl strlen). Measured on the unstripped twin (sha256 bff8519bbe3e): its .symtab has _ZN14__interception11real_strlenE
   at 0xa3d28 (8 bytes, local, .data) and strlen at 0x9b904 (weak); the 8 bytes at 0xa3d28 (file offset 0x90d28) are 0x9b904, the
   same in the pin 1be0f53d96cb; the kit's icells_sl (K/A/I_strlen.v:237) reads the same cell. At the port, lib/A/AF0m.v's
   Tfib_const_abs held real_memchr (0xa3d50) and real_strnlen (0xa3e38) from the same image bytes but omitted
   real_strlen, which is why ARcf did not give it; h-hpreset-7's 977bd48ee806 (AF0m.v blob d14761416c8c) adds it, and
   tfibsyms_real_strlen discharges PsRealStrlen from it, so ps_strlen_realizes_cf_closed takes TfibSyms B alone.
   Every AF0m.v cell is found BY VALUE (cell_in: a vm_compute-decided search for the cell's exact address, width and
   value; 2026-10-29), never by a row index, so a regenerated table that adds, removes or reorders rows breaks nothing
   here while each cell is still in it. The contract text (YGcfStr.v 3e37c5476fe) itself adds, against
   cgif's astrnlen_realizes form, amem_range8 (the kit's region_in_mem) and the 2 * ESTACK window; those are the
   target's, not premises of this file. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.MemNorm.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Exec.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.RegisterBridge.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.Exec.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.Mem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.Frame.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.MState.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.ImageA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.Cells.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.Step.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.D_kit.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.I_consts.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.I_qck.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.R_m2s.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.I_strnlenw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.I_strlen.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.I_strlen_entry.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK14.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YEvtSRr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YP09 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI04 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0d2cf YG0lawscf YGcfStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfImgA PSbz_str.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module NM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.MemNorm.
Module LE := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Exec.
Module LM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.
Module L6 := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Regs6ss.
Module LR := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.RegisterBridge.
Module BE := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.Exec.
Module BM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.Mem.
Module BF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.Frame.
Module BMS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.MState.
Module BI := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.ImageA.
Module BC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.Cells.
Module BSt := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.Step.
Module BD := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.D_kit.
Module BK := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.I_consts.
Module BQ := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.I_qck.
Module BR := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.R_m2s.
Module BN := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.I_strnlenw.
Module BL := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.I_strlen.
Module BW := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.I_strlen_entry.
Module PSS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSbz_str.
Module ESR := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YEvtSRr.

(* the pc of the contract: __wrap_strlen in fuzz_preset.asan, the same number in CfImgA (generated from the ELF; cited
   by field name) and in the kit's entry walk *)
Lemma pc_strlen_A : @cf_pc_strlen CfImgA.CfImg_A = 0x42d18 /\ BW.e_wrap_strlen = 0x42d18.
Proof. split; reflexivity. Qed.

(* ---- the image (fuzz_preset.asan; AB1v.tfibsegs and K ImageA.asegs are both Asan.M.loaded_segments) ---- *)
(* FSstrlen.v:91-92 *)
Lemma Hwx_ps : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* FSstrlen.v:94-95 *)
Lemma wx_apart_ps : NM.wx_apart tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* FSstrlen.v:97-98 *)
Definition seg_tops_below (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

(* FSstrlen.v:101-103: every loaded segment of fuzz_preset.asan ends below 0x600000 (the last PT_LOAD ends 0x5ff7d0) *)
Definition PS_IMG_TOP : Z := 0x600000.
Lemma tsegs_below : seg_tops_below tfibsegs PS_IMG_TOP = true.
Proof. vm_compute. reflexivity. Qed.

(* FSstrlen.v:105-114 *)
Lemma find_segment_below : forall segs top x n s,
  seg_tops_below segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold seg_tops_below in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

(* FSstrlen.v:116-124 *)
Lemma find_segment_spec : forall segs x n s, find_segment segs x n = Some s ->
  In s segs /\ Z.of_N (seg_base s) <= x /\ x + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  induction segs as [|s0 r IH]; intros x n s H; cbn in H; [discriminate H|].
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1, E2.
    split; [left; reflexivity | lia].
  - destruct (IH x n s H) as (Hi & H1 & H2). split; [right; exact Hi | lia].
Qed.

(* FSstrlen.v:126-130 *)
Lemma find_segment_high : forall x, PS_IMG_TOP <= x -> find_segment tfibsegs x 1 = None.
Proof.
  intros x Hx. destruct (find_segment tfibsegs x 1) as [s|] eqn:E; [|reflexivity].
  destruct (find_segment_below tfibsegs PS_IMG_TOP x 1 s tsegs_below E ltac:(lia)) as [L|L]; lia.
Qed.

(* FSstrlen.v:133-140: an address above the image and below TASK_SIZE keeps its byte in the normalized memory *)
Lemma cj_keep_high : forall x, PS_IMG_TOP <= x < TASK_SIZE -> NM.cj_drop tfibsegs (Z_to_bv 64 x) = false.
Proof.
  intros x Hx. unfold TASK_SIZE, PS_IMG_TOP in Hx.
  assert (Ex : bv_unsigned (Z_to_bv 64 x) = x) by (apply BMS.unsigned_lit; lia).
  apply NM.cj_drop_false_intro.
  - unfold LM.ro_addr. rewrite Ex, (find_segment_high x ltac:(unfold PS_IMG_TOP; lia)). reflexivity.
  - right. rewrite Ex. unfold TASK_SIZE. lia.
Qed.

(* FSstrlen.v:142-148 *)
Lemma seg_addr_below : forall a, BM.seg_addr tfibsegs a = true -> bv_unsigned a < BM.UTOP.
Proof.
  intros a H. unfold BM.seg_addr in H.
  destruct (find_segment tfibsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  destruct (find_segment_below tfibsegs PS_IMG_TOP (bv_unsigned a) 1 s tsegs_below E ltac:(lia)) as [L|L];
    [unfold BM.UTOP, PS_IMG_TOP in *; lia | discriminate L].
Qed.

(* FSstrlen.v:151-161: the kit walks' memory invariant holds of every normalized memory *)
Lemma bz_mem_inv_normalize : forall m, BM.mem_inv BI.asegs (NM.normalize_cj tfibsegs m).
Proof.
  intros m. apply BM.mem_inv_intro.
  - exact seg_addr_below.
  - intros a b H. destruct (NM.mem_inv_cj_normalize tfibsegs m a b H) as [R [S|T]]; split.
    + exact R.
    + destruct (find_segment tfibsegs (bv_unsigned a) 1) as [s|] eqn:E; [|congruence].
      apply seg_addr_below. unfold BM.seg_addr. rewrite E. reflexivity.
    + exact R.
    + unfold BM.UTOP, TASK_SIZE in *. lia.
Qed.

(* ---- a kit walk from the canonical register tree on the normalized memory, read on the machine ---- *)
(* FSstrlen.v:164-169 *)
Lemma bz_msteps_l : forall s s', BE.msteps BI.asegs s s' -> LE.msteps tfibsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH].
  - apply LE.msteps_refl.
  - eapply LE.msteps_cons; [exact Hs | exact IH].
Qed.

(* FSstrlen.v:171-172 *)
Lemma bz_evt_l : forall (Q : machine_state -> Prop) ms, BE.evt BI.asegs Q ms -> LE.evt tfibsegs Q ms.
Proof. intros Q ms (ms' & H & HQ). exists ms'. split; [exact (bz_msteps_l ms ms' H) | exact HQ]. Qed.

(* FSsl.v:40-45 *)
Lemma msteps_to_bz : forall s s', LE.msteps tfibsegs s s' -> BE.msteps BI.asegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH].
  - apply BE.msteps_refl.
  - eapply BE.msteps_cons; [exact Hs | exact IH].
Qed.

(* FSsl.v:47-50 *)
Lemma evt_to_bz : forall (Q : machine_state -> Prop) ms, LE.evt tfibsegs Q ms -> BE.evt BI.asegs Q ms.
Proof.
  intros Q ms (ms' & H & HQ). exists ms'. split; [exact (msteps_to_bz ms ms' H) | exact HQ].
Qed.

(* FSstrlen.v:174-176 *)
Definition st_at (regs F : bvmap 5 word) (pc : word) (fc : bv 32) (m : word -> option byte) : machine_state :=
  {| ms_regs := regs; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := None; ms_resv := None; ms_fcsr := fc;
     ms_mem := m; ms_rom := YK11.seg_rom tfibsegs |}.

(* FSstrlen.v:178-179 *)
Definition walk_at (Q : machine_state -> Prop) (m : word -> option byte) (a : machine_state) : Prop :=
  exists c s0, Q s0 /\ NM.ms_rel_cj tfibsegs c s0 /\ NM.cj_same tfibsegs m (ms_mem c) /\ L6.ms_eqv c a.

(* FSstrlen.v:181-195 *)
Lemma bz_transport : forall (Q : machine_state -> Prop) regs F pc fc m,
  NM.ro_agree tfibsegs m ->
  BE.evt BI.asegs Q (BMS.MS (L6.mkR_of regs) F pc fc None (NM.normalize_cj tfibsegs m) (YK11.seg_rom BI.asegs)) ->
  BE.evt BI.asegs (walk_at Q m) (st_at regs F pc fc m).
Proof.
  intros Q regs F pc fc m RO H.
  apply evt_to_bz.
  pose proof (NM.evt_normalize_cj tfibsegs Q (L6.mkR_of regs) F pc fc None m (YK11.seg_rom tfibsegs) wx_apart_ps RO
    (bz_evt_l Q _ H)) as H2.
  assert (EQV : L6.ms_eqv (BMS.MS (L6.mkR_of regs) F pc fc None m (YK11.seg_rom tfibsegs)) (st_at regs F pc fc m)).
  { unfold L6.ms_eqv, st_at, BMS.MS. cbn. split; [apply L6.xregs_eqv_sym, L6.mkR_of_eqv|].
    repeat split; reflexivity. }
  pose proof (LR.evt_register_transport tfibsegs _ _ _ EQV H2) as H3.
  eapply LE.evt_mono; [exact H3|]. intros a (c & (s0 & HQ & Hrel & Hsame) & Heqv). exists c, s0. auto.
Qed.

(* FSstrlen.v:197-243, the trampoline and the interceptor walk in the kit's words: here one lemma of the kit,
   istrlen_wrap_closed (K/A/I_strlen_entry.v: `jal zero, 0x42da8` at 0x42d18, then istrlen_spec rip_proof) *)
Lemma bz_strlen : forall regs F fc m0 (s : Z) (str slack : list byte) (lo : Z),
  reg_get regs 10 = Z_to_bv 64 s ->
  BF.stk BI.asegs m0 lo (bv_unsigned (reg_get regs 2)) -> lo <= bv_unsigned (reg_get regs 2) - 2224 ->
  BR.kHighShadowEnd + 8 <= lo -> bv_unsigned (reg_get regs 2) < 2 ^ 63 ->
  0 < s <= 2 ^ 47 -> Z.of_nat (length str) < 2 ^ 40 -> s + Z.of_nat (length str) + 1 <= 2 ^ 47 ->
  BM.bytes_at BI.asegs m0 s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned (reg_get regs 2) <= s) ->
  BQ.chk_ok m0 s (Z.of_nat (length str) + 1) -> BR.m2s_cells m0 -> BN.icells_sn m0 -> BL.icells_sl m0 ->
  BM.mem_inv BI.asegs m0 ->
  BE.evt BI.asegs
    (BL.istrlen_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
       (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
       (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) F fc
       (Z.of_nat (length str)) lo m0)
    (BMS.MS (L6.mkR_of regs) F (Z_to_bv 64 0x42d18) fc None m0 (YK11.seg_rom BI.asegs)).
Proof.
  intros regs F fc m0 s str slack lo Ha0 ST LO LOLO SPH S0 L40 SH BUF NZ PAD SEPS CS M2S IC ICL MI.
  change (L6.mkR_of regs) with (BF.mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
    (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10)
    (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16)
    (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
    (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28)
    (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)).
  exact (BW.istrlen_wrap_closed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F fc m0 s str slack lo Ha0 ST LO LOLO SPH S0 L40 SH BUF NZ PAD SEPS CS M2S IC ICL MI).
Qed.

(* ---- registers ---- *)
(* FSstrlen.v:246-247 *)
Lemma getr_nz : forall regs (r : bv 5), bv_eqb r 0 = false -> YK11.getr regs r = reg_get regs r.
Proof. intros regs r H. unfold YK11.getr. rewrite H. reflexivity. Qed.

(* FSstrlen.v:250-255 *)
Lemma land_m2_mod : forall u, Z.land u (-2) mod 2 = 0.
Proof.
  intros u. replace (Z.land u (-2)) with (Z.shiftl (Z.shiftr u 1) 1).
  - rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. apply Z.mod_mul. lia.
  - rewrite <- (Z.ldiff_ones_r u 1) by lia. rewrite Z.ldiff_land. reflexivity.
Qed.

(* FSstrlen.v:257-266 *)
Lemma ret_pc_ok : forall k, YK0s.ret_ok k -> BMS.ret_pc k = k.
Proof.
  intros k H. assert (E : bv_unsigned k mod 2 = 0).
  { unfold YK0s.ret_ok, YK14.v_jalr, jalr_tgtZ in H. apply (f_equal bv_unsigned) in H.
    rewrite Z_to_bv_unsigned, Z.add_0_r in H. unfold bv_wrap in H. change (bv_modulus 64) with (2 ^ 64) in H.
    rewrite <- H. pose proof (land_m2_mod (bv_unsigned k)).
    set (w := Z.land (bv_unsigned k) (-2)) in *. Z.div_mod_to_equations. lia. }
  transitivity (BMS.ret_pc (Z_to_bv 64 (bv_unsigned k))); [rewrite Z_to_bv_bv_unsigned; reflexivity|].
  rewrite BMS.ret_pc_even; [apply Z_to_bv_bv_unsigned | apply bv_unsigned_in_range | exact E].
Qed.

(* FSstrlen.v:269-284: the callee-saved registers of a walk's final register tree are the caller's *)
Lemma aregs_of_mkR : forall regs regs' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  L6.xregs_eqv (BF.mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) t0 t1 t2
    (reg_get regs 8) (reg_get regs 9) a0 a1 a2 a3 a4 a5 a6 a7 (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
    (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
    (reg_get regs 27) t3 t4 t5 t6) regs' ->
  aregs_preserved regs regs'.
Proof.
  intros regs regs' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HX r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hc as [->|Hc];
    [ rewrite !getr_nz by reflexivity;
      match goal with |- reg_get _ (Z_to_bv 5 ?k) = _ =>
        rewrite <- (HX (Z_to_bv 5 k)) by reflexivity; reflexivity end |]).
  subst r. rewrite !getr_nz by reflexivity. rewrite <- (HX (Z_to_bv 5 27)) by reflexivity. reflexivity.
Qed.

(* FSstrlen.v:286-294 *)
Lemma a0_of_mkR : forall regs' t1 t2 t3 t4 t5 t6 t7 t8 t9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31,
  L6.xregs_eqv (BF.mkR t1 t2 t3 t4 t5 t6 t7 t8 t9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31) regs' ->
  YK11.getr regs' 10 = a0.
Proof.
  intros. rewrite getr_nz by reflexivity. match goal with H : L6.xregs_eqv _ _ |- _ => rewrite <- (H 10%bv) by reflexivity end.
  reflexivity.
Qed.

(* ---- the memory the walk reads ---- *)
(* FSstrlen.v:297-302 *)
Lemma option_map_unsigned_inj : forall (o1 o2 : option byte),
  option_map (fun b : byte => bv_unsigned b) o1 = option_map (fun b : byte => bv_unsigned b) o2 -> o1 = o2.
Proof.
  intros [b1|] [b2|] H; cbn in H; try discriminate; [|reflexivity].
  injection H as H. f_equal. apply bv_eq. exact H.
Qed.

(* FSupoison.v:69-70 *)
Lemma aview_at : forall H m1 m2 a, m1 (Z_to_bv 64 a) = m2 (Z_to_bv 64 a) -> aview tfibsegs H m1 a = aview tfibsegs H m2 a.
Proof. intros H m1 m2 a E. unfold aview, mbyte, mrestrict. destruct (H (Z_to_bv 64 a)); [reflexivity|]. rewrite E. reflexivity. Qed.

(* FSstrlen.v:305-315: rom_view: the bytes the restricted memory holds at read-only image addresses are the image's *)
Lemma ro_agree_of_rom_view : forall (W : world tfibsegs) mem,
  rom_view tfibsegs W mem -> NM.ro_agree tfibsegs (mrestrict (w_H W) mem).
Proof.
  intros W mem HR a Ha. unfold LM.ro_addr in Ha.
  destruct (find_segment tfibsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate Ha].
  destruct (find_segment_spec _ _ _ _ E) as (Hin & H1 & H2).
  assert (Hro : in_rom tfibsegs (bv_unsigned a)).
  { exists s. split; [exact Hin|]. split; [apply negb_true_iff in Ha; exact Ha | lia]. }
  pose proof (HR _ Hro) as V. unfold aview, mbyte in V. rewrite !Z_to_bv_bv_unsigned in V.
  apply option_map_unsigned_inj. exact V.
Qed.

(* FSstrlen.v:317-322 *)
Lemma norm_keep_high : forall m (a : word), PS_IMG_TOP <= bv_unsigned a < TASK_SIZE ->
  NM.normalize_cj tfibsegs m a = m a.
Proof.
  intros m a Ha. pose proof (cj_keep_high (bv_unsigned a) Ha) as K. rewrite Z_to_bv_bv_unsigned in K.
  unfold NM.normalize_cj. rewrite K. reflexivity.
Qed.

(* FSstrlen.v:325-335: a stack window above the image keeps its bytes in the normalized memory *)
Lemma stk_norm_high : forall m lo hi, PS_IMG_TOP <= lo -> hi <= TASK_SIZE ->
  BF.stk BI.asegs m lo hi -> BF.stk BI.asegs (NM.normalize_cj tfibsegs m) lo hi.
Proof.
  intros m lo hi Hlo Hhi (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb).
  assert (K : NM.normalize_cj tfibsegs m (BM.wa a) = m (BM.wa a)).
  { apply norm_keep_high. rewrite BM.wa_unsigned by (unfold TASK_SIZE in Hhi; lia). lia. }
  split.
  - unfold wview. rewrite K. exact Hw.
  - exists b. unfold BM.mrd. rewrite K. exact Hb.
Qed.

(* FSstrlen.v:338-348: the ASan range check of [x, x + n) on the normalized memory, from the caller's shadow facts *)
Lemma chk_norm : forall (H : word -> bool) mem x n,
  0 <= x -> 0 < n -> x + n <= 2 ^ 47 -> n <= 2 ^ 40 -> BK.region_in_mem x n ->
  range_addressable (aview tfibsegs H mem) SHADOW_OFF x n -> shadow_hull_vis (aview tfibsegs H mem) x n ->
  BQ.chk_ok (NM.normalize_cj tfibsegs (mrestrict H mem)) x n.
Proof.
  intros H mem x n Hx Hn Hxn H40 Hreg Hra Hhull.
  apply (BQ.chk_ok_agree (mrestrict H mem)); [| lia | lia |].
  - apply PSS.chk_ok_of_view; [lia | lia | lia | lia | exact Hreg | exact Hra |].
    apply PSS.hull_of_shadow_hull_vis. exact Hhull.
  - intros a Ha. apply norm_keep_high. unfold PS_IMG_TOP, TASK_SIZE. lia.
Qed.

(* FSstrlen.v:351-358: the bytes read at an address, as a list *)
Definition byte_at (m : word -> option byte) (a : Z) : byte :=
  match BM.mrd BI.asegs m (BM.wa a) with Some b => b | None => Z_to_bv 8 0 end.
Definition mk_slack (m : word -> option byte) (e : Z) (k : nat) : list byte :=
  map (fun j => byte_at m (e + Z.of_nat j)) (seq 0 k).
Definition slack_len (e : Z) : nat := Z.to_nat ((- e) mod 8).

Lemma length_mk_slack : forall m e k, length (mk_slack m e k) = k.
Proof. intros. unfold mk_slack. rewrite length_map, length_seq. reflexivity. Qed.

(* FSstrlen.v:360-364 *)
Lemma le_byte_1 : forall v, 0 <= v < 256 -> Z_to_bv 8 (le_byte v 1 0) = Z_to_bv 8 v.
Proof.
  intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small v 256) by lia. reflexivity.
Qed.

(* NEW SHAPE (FSstrlen.v:366-417 cstr_bytes / cstr_nonul, restated for the target's first_byte): n readable bytes
   at a are the list mk_slack reads there *)
Lemma bytes_at_mk : forall m a n, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall j, 0 <= j < Z.of_nat n -> BM.mrd BI.asegs m (BM.wa (a + j)) <> None) ->
  BM.bytes_at BI.asegs m a (mk_slack m a n).
Proof.
  intros m a n Ha Hn HV. split; [exact Ha|]. split; [rewrite length_mk_slack; exact Hn|].
  intros i Hi. rewrite length_mk_slack in Hi.
  unfold mk_slack. rewrite nth_error_map, nth_error_seq.
  replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi). cbn [option_map Nat.add].
  unfold byte_at. destruct (BM.mrd BI.asegs m (BM.wa (a + Z.of_nat i))) as [b|] eqn:E; [reflexivity|].
  exfalso. apply (HV (Z.of_nat i)); [lia | exact E].
Qed.

(* the string's k bytes, its NUL and the rest of the NUL's 8-byte word *)
Lemma fb_bytes : forall (W : world tfibsegs) mem x k,
  first_byte tfibsegs W mem x (k + 1) 0 k -> 0 <= x -> x + k + 8 <= TASK_SIZE ->
  (forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview tfibsegs (w_H W) mem a <> None) ->
  BM.bytes_at BI.asegs (mrestrict (w_H W) mem) x
    (mk_slack (mrestrict (w_H W) mem) x (Z.to_nat k) ++ Z_to_bv 8 0 ::
       mk_slack (mrestrict (w_H W) mem) (x + k + 1) (slack_len (x + k + 1))).
Proof.
  intros W mem x k (Hk & Hlt & Hat) Hx Htop Hsl.
  assert (Hk1 : k < k + 1) by lia. specialize (Hat Hk1).
  unfold TASK_SIZE in Htop.
  assert (Hsk : Z.of_nat (slack_len (x + k + 1)) = 7 - (x + k) mod 8).
  { unfold slack_len. rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). Z.div_mod_to_equations. lia. }
  assert (VIS : forall a, aview tfibsegs (w_H W) mem a <> None ->
                BM.mrd BI.asegs (mrestrict (w_H W) mem) (BM.wa a) <> None).
  { intros a Ha. unfold aview in Ha. rewrite PSS.mbyte_mrd in Ha.
    revert Ha. destruct (BM.mrd BI.asegs (mrestrict (w_H W) mem) (BM.wa a)); intros Ha;
      [discriminate | exfalso; apply Ha; reflexivity]. }
  apply (proj2 (BM.bytes_at_app BI.asegs (mrestrict (w_H W) mem) x _ _)). split.
  - apply bytes_at_mk; [exact Hx | lia |].
    intros j Hj. rewrite Z2Nat.id in Hj by lia. apply VIS.
    destruct (Hlt j ltac:(lia)) as (b & Hb & _). rewrite Hb. discriminate.
  - rewrite length_mk_slack, Z2Nat.id by lia.
    change (Z_to_bv 8 0 :: mk_slack (mrestrict (w_H W) mem) (x + k + 1) (slack_len (x + k + 1)))
      with ([Z_to_bv 8 0] ++ mk_slack (mrestrict (w_H W) mem) (x + k + 1) (slack_len (x + k + 1))).
    apply (proj2 (BM.bytes_at_app BI.asegs (mrestrict (w_H W) mem) (x + k) _ _)). split.
    + exact (PSS.bytes_at1_of_view (w_H W) mem (x + k) 0 ltac:(lia) Hat).
    + cbn [length]. change (Z.of_nat 1) with 1.
      apply bytes_at_mk; [lia | rewrite Hsk; lia |].
      intros j Hj. rewrite Hsk in Hj. apply VIS. apply Hsl. lia.
Qed.

Lemma fb_nonul : forall (W : world tfibsegs) mem x k,
  first_byte tfibsegs W mem x (k + 1) 0 k -> 0 <= k ->
  ~ In (Z_to_bv 8 0) (mk_slack (mrestrict (w_H W) mem) x (Z.to_nat k)).
Proof.
  intros W mem x k (_ & Hlt & _) Hk Hin. unfold mk_slack in Hin.
  apply in_map_iff in Hin as (j & Ej & Hj). apply in_seq in Hj.
  destruct (Hlt (Z.of_nat j) ltac:(lia)) as (b & Hb & Hb0).
  unfold aview in Hb. rewrite PSS.mbyte_mrd in Hb. unfold byte_at in Ej.
  revert Hb Ej. destruct (BM.mrd BI.asegs (mrestrict (w_H W) mem) (BM.wa (x + Z.of_nat j))) as [c|];
    intros Hb Ej; [|discriminate Hb].
  cbn in Hb. injection Hb as Hb. subst c. apply Hb0. rewrite <- Hb. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* ---- the fuzz_preset.asan runtime cells the interceptor walk reads ---- *)
(* FSstrlen.v:420-428 *)
Lemma keep_range : forall A n,
  forallb (fun i => negb (NM.cj_drop tfibsegs (Z_to_bv 64 (A + Z.of_nat i)))) (seq 0 n) = true ->
  forall z, A <= z < A + Z.of_nat n -> NM.cj_drop tfibsegs (Z_to_bv 64 z) = false.
Proof.
  intros A n Hb z Hz. rewrite forallb_forall in Hb.
  specialize (Hb (Z.to_nat (z - A)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in Hb by lia. replace (A + (z - A)) with z in Hb by lia.
  apply negb_true_iff in Hb. exact Hb.
Qed.

(* FSstrlen.v:430-441, without the user-poison window: the cells of the restricted memory survive normalization *)
Lemma agree_cells : forall (H : word -> bool) mem A n,
  forallb (fun i => negb (NM.cj_drop tfibsegs (Z_to_bv 64 (A + Z.of_nat i)))) (seq 0 n) = true ->
  BD.agree_on (fun z => A <= z < A + Z.of_nat n) (mrestrict H mem) (NM.normalize_cj tfibsegs (mrestrict H mem)).
Proof.
  intros H mem A n Hb a Ha.
  pose proof (keep_range A n Hb (bv_unsigned a) Ha) as K. rewrite Z_to_bv_bv_unsigned in K.
  unfold NM.normalize_cj. rewrite K. reflexivity.
Qed.

(* FSstrlen.v:444-449: an address above the image reads only what the memory holds *)
Lemma mrd_high : forall m (a : word), PS_IMG_TOP <= bv_unsigned a -> BM.mrd BI.asegs m a = m a.
Proof.
  intros m a Ha. unfold BM.mrd. destruct (m a); [reflexivity|].
  match goal with |- ?f _ _ = None => unfold f end. unfold memory_read.
  change (Z.of_N 1) with 1. change BI.asegs with tfibsegs. rewrite (find_segment_high (bv_unsigned a) Ha). reflexivity.
Qed.

(* FSstrlen.v:452-464: a byte the walk reads at a writable image address is writable *)
Lemma wview_of_mrd : forall m x b, BM.mrd BI.asegs m x = Some b -> LM.ro_addr tfibsegs x = false ->
  wview BI.asegs m x <> None.
Proof.
  intros m x b H R. unfold wview. destruct (m x) as [c|] eqn:E; [discriminate|].
  unfold BM.mrd in H. rewrite E in H.
  match type of H with ?f _ _ = _ => unfold f in H end. unfold memory_read in H.
  unfold LM.ro_addr in R. change (Z.of_N 1) with 1 in H. change BI.asegs with tfibsegs in *.
  destruct (find_segment tfibsegs (bv_unsigned x) 1) as [s|]; [|discriminate H].
  apply negb_false_iff in R. rewrite R.
  destruct (seg_readable s); [|discriminate H].
  destruct (segment_byte_at (seg_bytes s) (Z.to_N (bv_unsigned x - Z.of_N (seg_base s)))) eqn:Eb; [discriminate|].
  exfalso. simpl in H. rewrite Eb in H. discriminate H.
Qed.

(* FSstrlen.v:466-478 *)
Lemma rw_of_ro : forall m A cs, BSt.ro_cells BI.asegs m A cs ->
  forallb (fun i => negb (NM.cj_drop tfibsegs (Z_to_bv 64 (A + Z.of_nat i)))) (seq 0 (BC.cells_size cs)) = true ->
  length (BC.cells_bytes cs) = BC.cells_size cs ->
  BSt.rw_cells BI.asegs m A cs.
Proof.
  intros m A cs (Hwf & HB) Hk Hl. split; [split; [exact Hwf | exact HB]|].
  destruct HB as (H0 & H1 & HB). split; [exact H0|]. split; [rewrite <- Hl; exact H1|].
  intros i Hi. pose proof (HB (Z.to_nat i) ltac:(lia)) as Hr. rewrite Z2Nat.id in Hr by lia.
  destruct (nth_error (BC.cells_bytes cs) (Z.to_nat i)) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  apply (wview_of_mrd m _ b Hr).
  pose proof (keep_range A _ Hk (A + i) ltac:(lia)) as K. unfold NM.cj_drop in K.
  apply orb_false_iff in K as [K _]. exact K.
Qed.

(* FSstrlen.v:480-486 *)
Lemma nth_Z_to_le_bytes : forall n z i, (i < n)%nat ->
  nth_error (Z_to_le_bytes n z) i = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat i))).
Proof.
  induction n as [|n IH]; intros z i Hi; [lia|]. destruct i as [|i]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. do 3 f_equal. lia.
Qed.

(* FSstrlen.v:488-493 *)
Lemma le_byte_8 : forall v i, 0 <= v < 2 ^ 64 ->
  Z_to_bv 8 (le_byte v 8 i) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat i)).
Proof.
  intros v i Hv. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, le_byte. change (bv_modulus 8) with 256.
  change (8 * Z.of_nat 8) with 64. rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* FSstrlen.v:496-506: an 8-byte value the caller's view holds (val_mem) is a C8 cell of the kit *)
Lemma ro_c8_of_val_mem : forall m A v, 0 <= A -> A + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  val_mem tfibsegs m A 8 v -> BSt.ro_cells BI.asegs m A [BC.C8 (Z_to_bv 64 v)].
Proof.
  intros m A v HA HA8 Hv HV. split; [cbn; tauto|].
  cbn [BC.cells_bytes BC.cbytes]. rewrite app_nil_r.
  split; [exact HA|]. split; [exact HA8|].
  intros i Hi. assert (Hi8 : (i < 8)%nat) by exact Hi.
  rewrite <- PSS.mbyte_mrd. rewrite (HV i Hi8). rewrite le_byte_8 by exact Hv.
  unfold BM.le8, word_to_le_bytes. rewrite nth_Z_to_le_bytes by exact Hi8. rewrite BMS.unsigned_lit by lia.
  reflexivity.
Qed.

(* FSstrlen.v:508-515 *)
Lemma ro_cons8 : forall m A w cs, BSt.ro_cells BI.asegs m A [BC.C8 w] -> BSt.ro_cells BI.asegs m (A + 8) cs ->
  BSt.ro_cells BI.asegs m A (BC.C8 w :: cs).
Proof.
  intros m A w cs (_ & B1) (W2 & B2). split; [cbn; tauto|].
  cbn [BC.cells_bytes BC.cbytes] in B1 |- *. rewrite app_nil_r in B1.
  apply (proj2 (BM.bytes_at_app BI.asegs m A _ _)). split; [exact B1|].
  assert (L : length (BM.le8 w) = 8%nat) by reflexivity. rewrite L. exact B2.
Qed.

(* RE-DERIVED (FSstrlen.v:589-599 tl_cells took the shadow cell through rdword / YCbq.val_mem_of_rdword; here every
   cell is an ARcf const cell, `cell_holds ... (z8 (ANum a) v)`, so the 8 bytes are read off the cell directly) *)
Lemma val_mem_of_holds8 : forall B ly (H : word -> bool) mem a v,
  cell_holds B ly (aview tfibsegs H mem) (z8 (ANum a) v) -> val_mem tfibsegs (mrestrict H mem) a 8 v.
Proof.
  intros B ly H mem a v HC k Hk. unfold cell_holds in HC. cbn [z8 c8 c_at c_val c_w aeval] in HC.
  specialize (HC k Hk). unfold aview in HC. cbv beta in HC. revert HC.
  destruct (mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat k)) as [b|]; intros HC; [|discriminate HC].
  (* val_mem (YI04.v) states le_byte as YO0f.le_byte, cell_holds as YG0f.le_byte: the same body, so by conversion *)
  cbn [option_map] in HC. injection HC as HC. f_equal.
  transitivity (Z_to_bv 8 (bv_unsigned b)); [symmetry; apply Z_to_bv_bv_unsigned | f_equal; exact HC].
Qed.

(* an 8-byte const cell of the caller's view, as a kit cell of the walk's (normalized) memory *)
Lemma c8_norm : forall B ly (W : world tfibsegs) mem a v,
  cell_holds B ly (aview tfibsegs (w_H W) mem) (z8 (ANum a) v) ->
  ((0 <=? a) && (a + 8 <=? 2 ^ 64) && (0 <=? v) && (v <? 2 ^ 64))%bool = true ->
  forallb (fun i => negb (NM.cj_drop tfibsegs (Z_to_bv 64 (a + Z.of_nat i)))) (seq 0 8) = true ->
  BSt.ro_cells BI.asegs (NM.normalize_cj tfibsegs (mrestrict (w_H W) mem)) a [BC.C8 (Z_to_bv 64 v)].
Proof.
  intros B ly W mem a v HC Hb Hk.
  apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1, H2, H3. apply Z.ltb_lt in H4.
  apply (BD.ro_cells_agree BI.asegs (mrestrict (w_H W) mem)).
  - apply ro_c8_of_val_mem; [exact H1 | exact H2 | lia |]. exact (val_mem_of_holds8 B ly (w_H W) mem a v HC).
  - apply agree_cells. exact Hk.
Qed.

(* the same for a one-byte const cell *)
Lemma c1_norm : forall B ly (W : world tfibsegs) mem a v,
  cell_holds B ly (aview tfibsegs (w_H W) mem) (z1 (ANum a) v) ->
  ((0 <=? a) && (a + 1 <=? 2 ^ 64) && (0 <=? v) && (v <? 256))%bool = true ->
  forallb (fun i => negb (NM.cj_drop tfibsegs (Z_to_bv 64 (a + Z.of_nat i)))) (seq 0 1) = true ->
  BSt.ro_cells BI.asegs (NM.normalize_cj tfibsegs (mrestrict (w_H W) mem)) a [BC.C1 (Z_to_bv 8 v)].
Proof.
  intros B ly W mem a v HC Hb Hk.
  apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1, H2, H3. apply Z.ltb_lt in H4.
  apply (BD.ro_cells_agree BI.asegs (mrestrict (w_H W) mem)).
  - apply BQ.ro_C1_of_bytes.
    unfold cell_holds in HC. cbn [z1 c1 c_at c_val c_w aeval] in HC.
    specialize (HC 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in HC. rewrite Z.add_0_r in HC.
    pose proof (PSS.bytes_at1_of_view (w_H W) mem a _ ltac:(lia) HC) as Hb1.
    rewrite le_byte_1 in Hb1 by lia. exact Hb1.
  - apply agree_cells. exact Hk.
Qed.

(* MEMBERSHIP BY VALUE (Theorem Labs, 2026-10-29, PresetStrlenB, at the owner's request; the same three items as in
   lib/AU/PSstrlen.v): a cell `ACell (ANum a) w (AV (ANum v))` is in a list when a boolean search for exactly that
   address, width and value succeeds; vm_compute decides it. No proof in this file names a row index of AF0m.v. *)
Definition is_num_cell (a : Z) (w : nat) (v : Z) (c : acell) : bool :=
  match c with
  | ACell (ANum a') w' (AV (ANum v')) => (Z.eqb a' a && Nat.eqb w' w && Z.eqb v' v)%bool
  | _ => false
  end.

Lemma is_num_cell_eq : forall a w v c, is_num_cell a w v c = true -> c = ACell (ANum a) w (AV (ANum v)).
Proof.
  intros a w v [ca cw cv] H.
  destruct ca; try (cbn in H; discriminate H).
  destruct cv as [e|m x]; try (cbn in H; discriminate H).
  destruct e; try (cbn in H; discriminate H).
  cbn in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1, H3. apply Nat.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma In_of_num_cell : forall a w v l, existsb (is_num_cell a w v) l = true -> In (ACell (ANum a) w (AV (ANum v))) l.
Proof.
  intros a w v l H. apply existsb_exists in H as (c & Hin & Hc).
  rewrite <- (is_num_cell_eq a w v c Hc). exact Hin.
Qed.

(* `In c l` for a concrete numeric cell c (z8 / z4 / z2 / z1 of an ANum address) and a concrete list l *)
Ltac cell_in :=
  lazymatch goal with |- In ?c ?l =>
    let c' := eval cbv [YG0f.z8 YG0f.z4 YG0f.z2 YG0f.z1 YG0f.c8 YG0f.c4 YG0f.c2 YG0f.c1] in c in
    lazymatch c' with ACell (ANum ?a) ?w (AV (ANum ?v)) =>
      change (In (ACell (ANum a) w (AV (ANum v))) l); apply (In_of_num_cell a w v l); vm_compute; reflexivity
    end
  end.

(* a cell of Tfib_const_abs is an ARcf const cell under TfibSyms (ts_const, lib/A/AF0m.v) *)
Lemma const_cell : forall B ly rd c, TfibSyms B -> Forall (cell_holds B ly rd) (as_const B ly) ->
  In c Tfib_const_abs -> cell_holds B ly rd c.
Proof.
  intros B ly rd c TS F Hin. rewrite (ts_const B TS ly) in F. rewrite Forall_forall in F. apply F.
  unfold Tfib_const. apply in_app_iff. right. apply in_app_iff. left. exact Hin.
Qed.

Ltac cst TS CF := apply (const_cell _ _ _ _ TS CF); cell_in.
Ltac ro8 B ly TS CF := apply (c8_norm B ly); [cst TS CF | vm_compute; reflexivity | vm_compute; reflexivity].
Ltac ro1 B ly TS CF := apply (c1_norm B ly); [cst TS CF | vm_compute; reflexivity | vm_compute; reflexivity].
Ltac cell_rw := apply rw_of_ro; [| vm_compute; reflexivity | reflexivity].

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* NAMED PREMISE, the one the donor did not have in this form (its FsRtCells B, FSstrlen.v:580-581, cut to the one
   cell ARcf's const cells do not give): at every ARcf state, __interception::real_strlen (0xa3d28, .data) holds musl's
   strlen 0x9b904, the REAL(strlen) the interceptor jumps through (K/A/I_strlen.v icells_sl). The ELF's own .data bytes
   there are 0x9b904. AF0m.v's Tfib_const_abs carries this slot since 977bd48ee806 (tfibsyms_real_strlen, below). *)
Definition PsRealStrlen (B : asyms) : Prop :=
  forall ly S Hp (W : world tfibsegs) mem md, ARcf tfibsegs B ly S Hp W mem md ->
  cell_holds B ly (aview tfibsegs (w_H W) mem) (z8 (ANum 0xa3d28) 0x9b904).

(* image A's generated record gives it (Theorem Labs, 2026-10-29, PresetStrlenB): h-hpreset-7's 977bd48ee806 adds
   `z8 (ANum 0xa3d28) 0x9b904` to lib/A/AF0m.v Tfib_const_abs; found BY VALUE (cell_in), so amc_const under ts_const
   reads it. The image-B twin is lib/AU/PSstrlen.v tfibsyms_real_strlen_B. *)
Lemma tfibsyms_real_strlen : forall B, TfibSyms B -> PsRealStrlen B.
Proof.
  intros B TS ly S Hp W mem md HAR.
  pose proof (amc_const _ _ _ _ _ (proj1 HAR)) as CF.
  rewrite (ts_const B TS ly) in CF. rewrite Forall_forall in CF. apply CF.
  unfold Tfib_const. apply in_app_iff. right. apply in_app_iff. left.
  cell_in.
Qed.

(* FSstrlen.v:617-628 / 561-573 / 590-599: all the cells the walk reads, on its (normalized) memory, each found BY
   VALUE in lib/A/AF0m.v Tfib_const_abs: 0xaaeb8 (__asan_shadow_memory_dynamic_address) = 0x7fff8000;
   0xabb98 (asan_inited) = 1; 0xabba0.. = kHighMemEnd, 0, 0; 0xa3e38 (real_strnlen) = 0x9bb40;
   0xa3d50 (real_memchr) = 0x9b1b8; 0x13cae3 (a flag byte) = 1; the .got slots 0xa2000 .. 0xa2028. *)
Lemma walk_cells : forall B ly S Hp (W : world tfibsegs) mem md,
  TfibSyms B -> PsRealStrlen B -> ARcf tfibsegs B ly S Hp W mem md ->
  BR.m2s_cells (NM.normalize_cj tfibsegs (mrestrict (w_H W) mem)) /\
  BN.icells_sn (NM.normalize_cj tfibsegs (mrestrict (w_H W) mem)) /\
  BL.icells_sl (NM.normalize_cj tfibsegs (mrestrict (w_H W) mem)).
Proof.
  intros B ly S Hp W mem md TS RS HAR.
  pose proof (amc_const _ _ _ _ _ (proj1 HAR)) as CF.
  split; [|split].
  - unfold BR.m2s_cells. split; [|split].
    + cell_rw. apply ro_cons8; [ro8 B ly TS CF|]. apply ro_cons8; [ro8 B ly TS CF|].
      apply ro_cons8; [ro8 B ly TS CF|]. ro8 B ly TS CF.
    + cell_rw. ro8 B ly TS CF.
    + cell_rw. apply ro_cons8; [ro8 B ly TS CF|]. apply ro_cons8; [ro8 B ly TS CF|].
      ro8 B ly TS CF.
  - unfold BN.icells_sn. split; [|split; [|split; [|split; [|split; [|split]]]]].
    + apply ro_cons8; [ro8 B ly TS CF|]. ro8 B ly TS CF.
    + ro8 B ly TS CF.
    + ro8 B ly TS CF.
    + ro8 B ly TS CF.
    + ro8 B ly TS CF.
    + cell_rw. ro1 B ly TS CF.
    + ro1 B ly TS CF.
  - unfold BL.icells_sl. apply (c8_norm B ly); [exact (RS ly S Hp W mem md HAR) | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

(* NEW SHAPE (FSstrlen.v:632-639 cstr_off_frame derived the separation from cstr_ok's ceiling bound; the target
   carries the frame premise itself): the string lies wholly below the 2 * ESTACK window or wholly above sp *)
Lemma str_off_frame : forall sp x k, 0 <= k ->
  (forall a, x <= a <= x + k -> ~ (sp - 2 * ESTACK <= a < sp)) ->
  x + k + 1 <= sp - 2 * ESTACK \/ sp <= x.
Proof.
  intros sp x k Hk H.
  destruct (Z_lt_ge_dec x sp) as [L|L]; [|right; lia]. left.
  destruct (Z_le_gt_dec (x + k + 1) (sp - 2 * ESTACK)) as [E|E]; [exact E|]. exfalso.
  apply (H (Z.max x (sp - 2 * ESTACK))); unfold ESTACK in *; lia.
Qed.

(* the contract's post (YGcfStr.v astrlen_realizes_cfm at segs := tfibsegs: astrlen_realizes_cf's post with the
   memnorm keep LAST), named *)
Definition strlen_post (B : asyms) ly S Hp (W : world tfibsegs) regs mem md (k : Z) : world tfibsegs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
       ARcf tfibsegs B ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 k /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
       (YAkMemnorm.memnorm tfibsegs mem -> YAkMemnorm.memnorm tfibsegs mem').

(* FSstrlen.v:643-745, AR -> ARcf: the post of a walk that ends at the return address with a0 = r, the stack window
   [sp - D, sp) its only change, read back on the caller's memory *)
Lemma post_of_walk : forall B ly S Hp (W : world tfibsegs) regs mem md (r v D : Z) ms' model' c m'
    t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  ecall_pre_cf tfibsegs B ly S Hp W regs mem md ->
  NM.ro_agree tfibsegs (mrestrict (w_H W) mem) ->
  0 <= D <= ESTACK -> Z_to_bv 64 r = w64 v ->
  NM.ms_rel_cj tfibsegs c
    (BMS.MS (BF.mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) t0 t1 t2 (reg_get regs 8)
       (reg_get regs 9) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
       (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
       (reg_get regs 27) t3 t4 t5 t6) fp_regs (BMS.ret_pc (reg_get regs 1)) fp_csr None m' (YK11.seg_rom BI.asegs)) ->
  NM.cj_same tfibsegs (mrestrict (w_H W) mem) (ms_mem c) ->
  L6.ms_eqv c ms' ->
  BF.munch [(spZ regs - D, spZ regs)] (NM.normalize_cj tfibsegs (mrestrict (w_H W) mem)) m' ->
  BF.stk BI.asegs m' (spZ regs - D) (spZ regs) ->
  same_but_materialized md model' ->
  strlen_post B ly S Hp W regs mem md v W (mkCfg (unrestrict (w_H W) mem ms') model').
Proof.
  intros B ly S Hp W regs mem md r v D ms' model' c m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    Hpre RO HD Hv Hrel Hsame Heqv MU ST Hsbm.
  pose proof Hpre as (HAR & Hret & Hal & Hlo & Hhi & Hwin & _ & _).
  pose proof (amc_layout _ _ _ _ _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
  unfold YG0f.kHighMemBeg, YG0f.kHighMemEnd in Lbeg, Lhi.
  assert (HE : ESTACK = 4096) by reflexivity.
  pose proof (AR_laws_ok_cf tfibsegs B) as LAWS.
  destruct (same_but_materialized_frame md model' Hsbm)
    as (_ & V1 & V2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V3).
  set (H := w_H W) in *. set (mR := mrestrict H mem) in *. set (sp := spZ regs) in *.
  remember (munrestrict H mem (ms_mem ms')) as mem'' eqn:Emem''.
  destruct Hrel as (Rr & Rf & Rpc & Rsvc & Rresv & Rfc & Rrom & Rmem).
  cbn [BMS.MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem] in Rr, Rf, Rpc, Rsvc, Rresv, Rfc, Rrom, Rmem.
  destruct Heqv as (Er & Ef & Epc & Esvc & Eresv & Efc & Emem & Erom).
  rewrite Rr in Er.
  assert (MUc : BF.munch [(sp - D, sp)] mR (ms_mem c))
    by exact (NM.munch_rel_cj tfibsegs [(sp - D, sp)] mR _ (ms_mem c) m' (NM.mem_rel_cj_normalize tfibsegs mR RO) Rmem Hsame MU).
  (* outside the walk's window the caller's memory is unchanged *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - D <= a < sp) -> mem'' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hn. rewrite Emem''. unfold munrestrict. destruct (H (Z_to_bv 64 a)) eqn:Eh; [reflexivity|].
    rewrite <- Emem. rewrite (MUc (Z_to_bv 64 a)) by (rewrite BMS.unsigned_lit by lia; cbn; split; [lia | exact I]).
    unfold mR, mrestrict. rewrite Eh. reflexivity. }
  (* the whole walk window is present after the walk *)
  assert (WIN : forall a, sp - D <= a < sp -> exists b, ms_mem ms' (Z_to_bv 64 a) = Some b).
  { intros a Ha. destruct ST as (_ & _ & STa). destruct (STa a Ha) as (_ & b & Hb).
    assert (K : NM.cj_drop tfibsegs (Z_to_bv 64 a) = false) by (apply cj_keep_high; unfold PS_IMG_TOP, TASK_SIZE; lia).
    exists b. rewrite <- Emem. rewrite <- (NM.mem_rel_cj_keep tfibsegs _ _ _ Rmem K).
    rewrite mrd_high in Hb by (unfold BM.wa; rewrite BMS.unsigned_lit by lia; unfold PS_IMG_TOP; lia).
    exact Hb. }
  assert (WRAP : forall a, Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64) /\ 0 <= a mod 2 ^ 64 < 2 ^ 64).
  { intros a. split; [|apply Z.mod_pos_bound; lia]. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod. reflexivity. }
  (* a byte present before is present after *)
  assert (PRES : forall a, H (Z_to_bv 64 a) = false -> mem (Z_to_bv 64 a) <> None -> mem'' (Z_to_bv 64 a) <> None).
  { intros a Hh Hm. destruct (WRAP a) as (Ew & Hw). rewrite Ew in *. set (a' := a mod 2 ^ 64) in *.
    destruct (Z_le_gt_dec (sp - D) a') as [L1|L1]; [destruct (Z_lt_ge_dec a' sp) as [L2|L2]|].
    - destruct (WIN a' ltac:(lia)) as (b & Hb). rewrite Emem''. unfold munrestrict. rewrite Hh, Hb. discriminate.
    - rewrite KEEP by lia. exact Hm.
    - rewrite KEEP by lia. exact Hm. }
  unfold strlen_post. split; [reflexivity|]. exists (ms_regs ms'), mem'', model'.
  split.
  { (* the configuration at the return address *)
    assert (Fpc : ms_pc_val ms' = w64 (raZ regs)).
    { rewrite <- Epc, Rpc. unfold raZ, w64. rewrite getr_nz by reflexivity. rewrite Z_to_bv_bv_unsigned.
      rewrite getr_nz in Hret by reflexivity. apply ret_pc_ok. exact Hret. }
    assert (Ffr : ms_fregs ms' = fp_regs) by congruence.
    assert (Fsvc : ms_svc_pending ms' = None) by congruence.
    assert (Frv : ms_resv ms' = None) by congruence.
    assert (Ffc : ms_fcsr ms' = fp_csr) by congruence.
    assert (From : ms_rom ms' = YK11.seg_rom tfibsegs) by (rewrite <- Erom, Rrom; reflexivity).
    unfold cfg_at, YK11.mkst, unrestrict. rewrite Fpc, Ffr, Fsvc, Frv, Ffc, From, Emem''. reflexivity. }
  split.
  { (* ARcf, by the cf frame law (AR_laws_ok_cf) *)
    apply (alc_frame _ _ LAWS ly S Hp W mem md mem'' model' HAR).
    - intros a Ha Hown. destruct (Z_le_gt_dec (sp - D) a) as [L1|L1]; [destruct (Z_lt_ge_dec a sp) as [L2|L2]|].
      + exfalso. apply (alc_stack _ _ LAWS ly S Hp W mem md a HAR); [lia | exact Hown].
      + apply aview_at. rewrite KEEP by lia. reflexivity.
      + apply aview_at. rewrite KEEP by lia. reflexivity.
    - intros a Hv'. unfold aview, mbyte, mrestrict in Hv' |- *.
      destruct (w_H W (Z_to_bv 64 a)) eqn:Eh; [exact Hv'|].
      destruct (mem (Z_to_bv 64 a)) as [b|] eqn:Em.
      + destruct (mem'' (Z_to_bv 64 a)) as [b'|] eqn:Em''; [cbn; discriminate|].
        exfalso. apply (PRES a Eh); [rewrite Em; discriminate | exact Em''].
      + destruct (mem'' (Z_to_bv 64 a)); [cbn; discriminate | exact Hv'].
    - exact V1.
    - exact V2.
    - exact V3.
    - intros a _ Hh. rewrite Emem''. unfold munrestrict. fold H in Hh. rewrite Hh. reflexivity. }
  split; [exact (aregs_of_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Er)|].
  split; [exact Hsbm|].
  split.
  { rewrite (a0_of_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Er). exact Hv. }
  split.
  { intros a Ha Hn. apply aview_at. fold sp in Hn. apply KEEP; lia. }
  split.
  { intros a (Hh & b & Hb). split; [exact Hh|].
    destruct (mem'' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
    exfalso. apply (PRES a Hh); [rewrite Hb; discriminate | exact E]. }
  { (* the memnorm keep: the raw memory changes only in [sp - D, sp) (KEEP), which lies above the image
       (find_segment_high) and below TASK_SIZE; YAkMemnorm.memnorm_frame_off_segs *)
    intros MN0. apply (YAkMemnorm.memnorm_frame_off_segs tfibsegs mem mem'' (sp - D) sp MN0).
    - intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
      rewrite <- (Z_to_bv_bv_unsigned 64 x). apply KEEP; lia.
    - unfold TASK_SIZE. lia.
    - intros x Hx. apply find_segment_high. unfold PS_IMG_TOP. lia. }
Qed.

(* FSstrlen.v:749-825: the core, the strlen interceptor at its trampoline, from the contract's facts with the frame
   separation named *)
Lemma ps_strlen_core : forall B, TfibSyms B -> PsRealStrlen B ->
  forall ly S Hp (W : world tfibsegs) regs mem md x k,
  ecall_pre_cf tfibsegs B ly S Hp W regs mem md -> rom_view tfibsegs W mem ->
  YK11.getr regs 10 = w64 x -> 0 < x -> 0 <= k -> k + 1 < 2 ^ 32 ->
  first_byte tfibsegs W mem x (k + 1) 0 k ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x (k + 1) ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) x (k + 1) ->
  (forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview tfibsegs (w_H W) mem a <> None) ->
  amem_range8 x (k + 1) ->
  x + k + 1 <= spZ regs - 2 * ESTACK \/ spZ regs <= x ->
  SRr tfibsegs W (cfg_at tfibsegs 0x42d18 regs mem md) (strlen_post B ly S Hp W regs mem md k).
Proof.
  intros B TS RS ly S Hp W regs mem md x k Hpre Hrom Hx Hx0 Hk0 Hk32 Hfb Hra Hhull Hsl Hamr Hfr.
  pose proof Hpre as (HAR & Hret & Hal & Hlo & Hhi & Hwin & _ & _).
  pose proof (amc_layout _ _ _ _ _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
  unfold YG0f.kHighMemBeg, YG0f.kHighMemEnd in Lbeg, Lhi.
  assert (HE : ESTACK = 4096) by reflexivity.
  pose proof (ro_agree_of_rom_view W mem Hrom) as RO.
  pose proof (walk_cells B ly S Hp W mem md TS RS HAR) as (M2S & ICN & ICL).
  assert (Esp : bv_unsigned (reg_get regs 2) = spZ regs) by (unfold spZ; rewrite getr_nz by reflexivity; reflexivity).
  assert (Ha0 : reg_get regs 10 = Z_to_bv 64 x) by (rewrite <- getr_nz by reflexivity; exact Hx).
  assert (Hamr' : (0 <= x /\ x + (k + 1) + 8 <= 0x7fff7fff) \/
                  (0x10007fff800f <= x /\ x + (k + 1) + 8 <= 0x7fffffffffff))
    by (unfold amem_range8, YG0f.kLowMemEnd, YG0f.kHighMemBeg, YG0f.kHighMemEnd in Hamr; lia).
  set (H := w_H W) in *. set (mR := mrestrict H mem). set (sp := spZ regs) in *.
  set (lo := sp - 2224).
  set (str := mk_slack mR x (Z.to_nat k)).
  set (slack := mk_slack mR (x + k + 1) (slack_len (x + k + 1))).
  assert (Lstr : Z.of_nat (length str) = k) by (unfold str; rewrite length_mk_slack; lia).
  assert (Lsl : Z.of_nat (length slack) = (- (x + k + 1)) mod 8).
  { unfold slack, slack_len. rewrite length_mk_slack. rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). reflexivity. }
  assert (Lsl7 : 0 <= (- (x + k + 1)) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  apply (ESR.srr_of_evt tfibsegs Hwx_ps W 0x42d18 regs mem md
    (walk_at (BL.istrlen_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
       (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
       (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) fp_regs fp_csr
       (Z.of_nat (length str)) lo (NM.normalize_cj tfibsegs mR)) mR)).
  - refine (_ : BE.evt BI.asegs _ (st_at regs fp_regs (Z_to_bv 64 0x42d18) fp_csr mR)).
    apply bz_transport; [exact RO|].
    apply (bz_strlen regs fp_regs fp_csr _ x str slack lo).
    + exact Ha0.
    + rewrite Esp. apply stk_norm_high; [unfold lo, PS_IMG_TOP; lia | unfold TASK_SIZE; lia |].
      apply ESR.stk_of_apresent; [unfold lo; lia | lia |].
      intros a Ha. apply Hwin. unfold lo in Ha. lia.
    + rewrite Esp. unfold lo. lia.
    + unfold BR.kHighShadowEnd, lo. lia.
    + rewrite Esp. lia.
    + lia.
    + rewrite Lstr. lia.
    + rewrite Lstr. lia.
    + refine (NM.bytes_at_normalize_cj_low tfibsegs mR x (str ++ Z_to_bv 8 0 :: slack) RO _ _).
      * rewrite length_app. cbn [length]. unfold TASK_SIZE. lia.
      * exact (fb_bytes W mem x k Hfb ltac:(lia) ltac:(unfold TASK_SIZE; lia) Hsl).
    + exact (fb_nonul W mem x k Hfb Hk0).
    + rewrite Lstr, Lsl. lia.
    + rewrite Esp, Lstr, Lsl. unfold lo. lia.
    + rewrite Lstr. apply chk_norm; [lia | lia | lia | lia | | exact Hra | exact Hhull].
      unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd. lia.
    + exact M2S.
    + exact ICN.
    + exact ICL.
    + apply bz_mem_inv_normalize.
  - intros ms' model' (c & s0 & HQ & Hrel & Hsame & Heqv) Hsbm _.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Es0 & MU & _ & _ & ST').
    subst s0. rewrite Esp in MU, ST'.
    apply (post_of_walk B ly S Hp W regs mem md (Z.of_nat (length str)) k 2224 ms' model' c m'
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hpre RO); try assumption.
    + lia.
    + rewrite Lstr. reflexivity.
Qed.

(* ---- the contract ---- *)
(* FSstrlen.v:828-835 fs_strlen_realizesU, restated in cgif's call form over ARcf (YGcfStr.v), with the memnorm
   keep: astrlen_realizes_cfm *)
Theorem ps_strlen_realizes_cfm : forall B, TfibSyms B -> PsRealStrlen B ->
  astrlen_realizes_cfm tfibsegs B 0x42d18.
Proof.
  intros B TS RS ly S Hp W regs mem md x k Hpre H2lo H2win Hx Hx0 Hk0 Hk32 Hx63 Hfb Hsrc Hfr2 Hamr Hra Hhull Hsl Hrom.
  pose proof (str_off_frame (spZ regs) x k Hk0 Hfr2) as Hfr.
  exact (ps_strlen_core B TS RS ly S Hp W regs mem md x k Hpre Hrom Hx Hx0 Hk0 Hk32 Hfb Hra Hhull Hsl Hamr Hfr).
Qed.

(* astrlen_realizes_cf: the same row with the keep dropped *)
Theorem ps_strlen_realizes_cf : forall B, TfibSyms B -> PsRealStrlen B ->
  astrlen_realizes_cf tfibsegs B 0x42d18.
Proof.
  intros B TS RS ly S Hp W regs mem md x k Hpre H2lo H2win Hx Hx0 Hk0 Hk32 Hx63 Hfb Hsrc Hfr2 Hamr Hra Hhull Hsl Hrom.
  eapply SRr_mono; [exact (ps_strlen_realizes_cfm B TS RS ly S Hp W regs mem md x k Hpre H2lo H2win Hx Hx0 Hk0 Hk32
    Hx63 Hfb Hsrc Hfr2 Hamr Hra Hhull Hsl Hrom)|].
  cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & HAR & Hp' & Hs & Hv & Hf & Hap & _).
  split; [reflexivity|]. exists regs', mem', md'.
  exact (conj Hc (conj HAR (conj Hp' (conj Hs (conj Hv (conj Hf Hap)))))).
Qed.

(* CLOSED (Theorem Labs, 2026-10-29, PresetStrlenB): over image A's generated record alone; PsRealStrlen is
   discharged by tfibsyms_real_strlen *)
Theorem ps_strlen_realizes_cfm_closed : forall B, TfibSyms B -> astrlen_realizes_cfm tfibsegs B 0x42d18.
Proof. intros B TS. exact (ps_strlen_realizes_cfm B TS (tfibsyms_real_strlen B TS)). Qed.
Theorem ps_strlen_realizes_cf_closed : forall B, TfibSyms B -> astrlen_realizes_cf tfibsegs B 0x42d18.
Proof. intros B TS. exact (ps_strlen_realizes_cf B TS (tfibsyms_real_strlen B TS)). Qed.

End core.
