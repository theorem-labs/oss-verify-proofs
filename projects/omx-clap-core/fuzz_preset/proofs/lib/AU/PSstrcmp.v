(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-29 (PresetStrlenB, c-libc-stdio lane): fuzz_preset.asan-ubsan's (IMAGE B's) strcmp
   interceptor, called at its trampoline __wrap_strcmp 0x42e0c (`jal zero, 0x433c0` = ___interceptor_strcmp), in the
   contract of the second allocator instance:
   `ps_strcmp_realizes_cf_B : forall B, YF0m.TfibSyms B -> astrcmp_realizes_cf tfibsegs B 0x42e0c`
   (lib/Reusable/YGcfStr.v; `tfibsegs` is lib/Reusable/YB1v.v's, AsanUbsan.M.loaded_segments; YF0m.TfibSyms is image
   B's generated record), and its memnorm twin ps_strcmp_realizes_cfm_B (astrcmp_realizes_cfm; the keep comes from
   AU/PSstrlen.v's post_of_walk, PresetStrRo). Image B only. rule 24: the CONFIRM is the internal file strcmpB-CONFIRM.md
   (StrcmpBLookupCheck, 2026-10-29 13:18Z): no ref proves strcmp's interceptor at image B. This file is the IMAGE-B
   RESTATEMENT of an existing, proved composition.
   2026-10-29 (pstr102, #102 pin B' asan-ubsan d663f82d, twin c90d4fa5): presetstr-ro 45e489ec67c7's file (blob
   27b807515ae1) with every image-B numeral moved to B' by symbol + offset and the KEYING table re-keyed A' -> B',
   over the B' kit lib/K5/B10 (re-derived by tools/presetstr/presetstr_reloc.py), the B' YF0m.v f82202ebccdf and
   CfImgB 82495e01f675; pc_strcmp_B cites CfImgB's cf_pc_strcmp by field name.

   DONOR: lib/A/PSstrcmp.v at origin/cold/c-libc-stdio-presetstr 20751730fbc2 (`ps_strcmp_realizes_cf`, image A,
   Qed), itself the port of fuzz_state's FSstrcmp.v (origin/cold/port-state-rt-str 999a7102a6e). Every lemma below is
   the donor's, in the donor's order, under the donor's name, with the donor's proof script, unless listed here. Its
   inputs are the image-B halves of the same pieces, REUSED, not copied:
   - the walk: lib/K5/B10/I_strcmp_entry.v `istrcmp_wrap_closed` (= istrcmp_wrap_spec rip_proof: the trampoline step
     at 0x42e0c, then K5/B10/I_strcmp.v istrcmp_spec at 0x433c0 with K5/B10/R_isPoisoned.v rip_proof), Qed, no
     hypothesis; its cells K5/B10/R_m2s.v m2s_cells and K5/B10/I_strcmpw.v icells_scmp;
   - the image-B infrastructure: lib/AU/PSstrlen.v (post_of_walk, walk_at, st_at, bz_transport, mk_slack, byte_at,
     bytes_at_mk, agree_cells, str_off_frame, chk_norm, stk_norm_high, bz_mem_inv_normalize, ro_agree_of_rom_view,
     val_mem_of_holds8, getr_nz, strlen_post (the shared post, here with v := strcmp_res c1 c2), and the by-value cell
     search cell_in) and lib/AU/PSbz_str.v (bytes_at1_of_view, mbyte_mrd);
   - the evt -> SRr bridge lib/Reusable/YEvtSRr.v and the transports, segs-generic, through AU/PSstrlen.v.
   musl's strcmp (image B 0x9c11c) is NOT on the walked path: the interceptor reaches it through
   __interception::real_strcmp (0xa4570) only when TryAsanInitFromRtl returns 0, and the walk takes asan_inited = 1
   (icells_scmp's rw cell 0xac3d8 = 1). So there is no real_strcmp premise and 0xa4570 need not be a const cell.

   KEYING. Every image-B number below was re-derived from image B's OWN unstripped twin (fuzz_preset.asan-ubsan,
   sha256 c90d4fa54d43160b..c175, pin d663f82d) by SYMBOL + OFFSET from its .symtab (pyelftools), never by a delta
   from image A and never by reusing an A number. Old (image A', bff8519bbe3e) -> new (image B'):
     __wrap_strcmp                          0x42d20 -> 0x42e0c  (first insn 0x5b40006f = jal zero, ___interceptor_strcmp)
     ___interceptor_strcmp                  0x432d4 -> 0x433c0  (1328 bytes in both)
     strcmp (musl, NOT walked)              0x9b8cc -> 0x9c11c
     __interception::real_strcmp (.data)    0xa3d30 holds 0x9b8cc -> 0xa4570 holds 0x9c11c (not read)
     __sanitizer::common_flags_dont_use     0x13c9e8 -> 0x13d228 (.bss): +240 word 0x13cad8 -> 0x13d318 (byte 5 =
                                            +245, 0x13cadd -> 0x13d31d, is 0); +248 word 0x13cae0 -> 0x13d320 (byte 2 =
                                            +250, 0x13cae2 -> 0x13d322, is 1); the two words' run-time values
                                            0x101000100000000 / 0x101010101010101 are YF0m.v's cells
     __asan_shadow_memory_dynamic_address   0xaaeb8 -> 0xab6f8 (.bss; 0x7fff8000)
     __asan::asan_inited                    0xabb98 -> 0xac3d8 (.bss; 1)
     __asan::kHighMemEnd/kMidMemBeg/End     0xabba0.. -> 0xac3e0.. (.bss; 0x7fffffffffff, 0, 0)
     .got+0x50 / +0x60..+0x78               0xa2000 / 0xa2010..0xa2028 -> 0xa2840 / 0xa2850..0xa2868
     walk depth ISTRCMP_DEPTH               2272 -> 2272 (the image-B walk's own statement)
   The image-B kit (K5/B10) already states exactly these values, and lib/Reusable/YF0m.v (B' blob f82202ebccdf, on this
   base) carries every one of the cells as a Tfib_const_abs cell, so no generated table had to be taken from elsewhere.

   WHAT CHANGED against the donor (R = re-derived for image B; S = shape changed; everything else = image names only):
     module aliases QI QD QK QQ QR QS QW QL QEnt   -> lib/K5/B10; BI.asegs -> BI.bsegs; PSS / PSL -> lib/AU/PSbz_str /
                                                 lib/AU/PSstrlen
     pc_strcmp_A                            R -> pc_strcmp_B (CfImgB's cf_pc_strcmp, by field name, and the
                                                 kit's e_wrap_strcmp)
     const_cell_B                           S  A/PSstrlen.v's const_cell (In c Tfib_const_abs -> cell_holds) restated
                                                 over YF0m.TfibSyms: AU/PSstrlen.v's const_cell takes PsConstCellsB,
                                                 not the record, so it does not fit here
     qcst                                   S  uses const_cell_B and AU/PSstrlen.v's cell_in (cells found BY VALUE)
     bz_strcmp, ps_strcmp_core              R  entry 0x42d20 -> 0x42e0c, K5/B10 istrcmp_wrap_closed
     walk_cells_scmp                        R  the image-B cells (the flag words 0x13d318 / 0x13d320)
     ps_strcmp_realizes_cf                  -> ps_strcmp_realizes_cf_B (premise YF0m.TfibSyms B, the donor's shape) *)
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
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib.Exec.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib.Mem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib.Frame.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib.MState.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib.Cells.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib.Step.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.ImageA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.D_kit.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.I_consts.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.I_qck.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.R_m2s.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.I_strcmp_spec.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.I_strcmpw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.I_strcmp.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.I_strcmp_entry.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK14.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YEvtSRr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YP09 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI04 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0d2cf YG0lawscf YGcfStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB PSbz_str PSstrlen.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Module NM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.MemNorm.
Module L6 := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Regs6ss.
Module BE := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.Exec.
Module BM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.Mem.
Module BMS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.MState.
Module BI := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.ImageA.
Module BC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.Cells.
Module BSt := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib.Step.
Module QE := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib.Exec.
Module QM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib.Mem.
Module QF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib.Frame.
Module QMS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib.MState.
Module QC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib.Cells.
Module QSt := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib.Step.
Module QI := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.ImageA.
Module QD := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.D_kit.
Module QK := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.I_consts.
Module QQ := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.I_qck.
Module QR := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.R_m2s.
Module QS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.I_strcmp_spec.
Module QW := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.I_strcmpw.
Module QL := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.I_strcmp.
Module QEnt := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10.I_strcmp_entry.
Module PSS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSbz_str.
Module PSL := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSstrlen.
Module ESR := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YEvtSRr.

(* the segment lists are image B's: YB1v's tfibsegs, the K kit's bsegs and the K5/B10 kit's asegs, by conversion *)
Lemma tfibsegs_bsegs_q : tfibsegs = BI.bsegs /\ QI.asegs = BI.bsegs.
Proof. split; reflexivity. Qed.

(* the pc of the contract: __wrap_strcmp in fuzz_preset.asan-ubsan, the same number in CfImgB (generated from the
   ELF; cited by field name) and in the kit's entry walk *)
Lemma pc_strcmp_B : @cf_pc_strcmp CfImgB.CfImg_B = 0x42e0c /\ QEnt.e_wrap_strcmp = 0x42e0c.
Proof. split; reflexivity. Qed.

(* ---- the two kits' runs are the same run (each kit has its OWN inductive `msteps`) ---- *)
Lemma k5_msteps_bz : forall s s', QE.msteps QI.asegs s s' -> BE.msteps BI.bsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH].
  - apply BE.msteps_refl.
  - eapply BE.msteps_cons; [exact Hs | exact IH].
Qed.

Lemma k5_evt_bz : forall (Q : machine_state -> Prop) ms, QE.evt QI.asegs Q ms -> BE.evt BI.bsegs Q ms.
Proof. intros Q ms (ms' & H & HQ). exists ms'. split; [exact (k5_msteps_bz ms ms' H) | exact HQ]. Qed.

(* PSbz_str.v mbyte_mrd, in the K5 kit's names (both hold by reflexivity) *)
Lemma q_mbyte_mrd : forall (m : word -> option byte) a, mbyte tfibsegs m a = QM.mrd QI.asegs m (QM.wa a).
Proof. reflexivity. Qed.

(* ---- the compared prefixes, as the walk reads them ---- *)
(* the i-th byte of mk_slack *)
Lemma nth_mk_slack : forall m e n i, (i < n)%nat ->
  nth_error (PSL.mk_slack m e n) i = Some (PSL.byte_at m (e + Z.of_nat i)).
Proof.
  intros m e n i Hi. unfold PSL.mk_slack. rewrite nth_error_map, nth_error_seq.
  replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  cbn [option_map Nat.add]. reflexivity.
Qed.

(* a byte the caller's view holds is a byte the walk reads, with the same value *)
Lemma view_byte : forall (W : world tfibsegs) mem a v,
  aview tfibsegs (w_H W) mem a = Some v ->
  BM.mrd BI.bsegs (mrestrict (w_H W) mem) (BM.wa a) <> None /\
  bv_unsigned (PSL.byte_at (mrestrict (w_H W) mem) a) = v.
Proof.
  intros W mem a v Hv. unfold aview in Hv. rewrite PSS.mbyte_mrd in Hv. unfold PSL.byte_at.
  destruct (BM.mrd BI.bsegs (mrestrict (w_H W) mem) (BM.wa a)) as [b|] eqn:E.
  - cbn [option_map] in Hv. injection Hv as <-. split; [discriminate | reflexivity].
  - cbn [option_map] in Hv. discriminate Hv.
Qed.

(* the kit's result is the contract's CharCmpX *)
Lemma cmpx_res : forall c1 c2, QS.cmpx c1 c2 = strcmp_res c1 c2.
Proof.
  intros c1 c2. unfold QS.cmpx, strcmp_res.
  destruct (Z.eqb_spec c1 c2) as [->|NE].
  - rewrite Z.ltb_irrefl. reflexivity.
  - destruct (Z.ltb_spec c1 c2) as [L|L]; [reflexivity|].
    destruct (Z.ltb_spec c2 c1) as [L2|L2]; [reflexivity | lia].
Qed.

(* the two strings the walk compares are the k + 1 bytes it reads at x and at y, they stop at k, and the kit's
   result is the contract's *)
Lemma meet_strings : forall (W : world tfibsegs) mem x y k c1 c2,
  str_meet tfibsegs W mem x y k c1 c2 ->
  0 <= x -> 0 <= y -> x + (k + 1) <= TASK_SIZE -> y + (k + 1) <= TASK_SIZE ->
  QM.bytes_at QI.asegs (mrestrict (w_H W) mem) x (PSL.mk_slack (mrestrict (w_H W) mem) x (Z.to_nat (k + 1)))
  /\ QM.bytes_at QI.asegs (mrestrict (w_H W) mem) y (PSL.mk_slack (mrestrict (w_H W) mem) y (Z.to_nat (k + 1)))
  /\ Z.of_nat (length (PSL.mk_slack (mrestrict (w_H W) mem) x (Z.to_nat (k + 1)))) = k + 1
  /\ Z.of_nat (length (PSL.mk_slack (mrestrict (w_H W) mem) y (Z.to_nat (k + 1)))) = k + 1
  /\ QS.strcmp_ok (PSL.mk_slack (mrestrict (w_H W) mem) x (Z.to_nat (k + 1)))
                  (PSL.mk_slack (mrestrict (w_H W) mem) y (Z.to_nat (k + 1)))
  /\ QS.strcmp_sz (PSL.mk_slack (mrestrict (w_H W) mem) x (Z.to_nat (k + 1)))
                  (PSL.mk_slack (mrestrict (w_H W) mem) y (Z.to_nat (k + 1))) = k + 1
  /\ QS.strcmp_res (PSL.mk_slack (mrestrict (w_H W) mem) x (Z.to_nat (k + 1)))
                   (PSL.mk_slack (mrestrict (w_H W) mem) y (Z.to_nat (k + 1))) = strcmp_res c1 c2.
Proof.
  intros W mem x y k c1 c2 (Hk0 & Hbef & Hc1v & Hc2v & Hstop) Hx Hy Htx Hty.
  set (bx := PSL.mk_slack (mrestrict (w_H W) mem) x (Z.to_nat (k + 1))).
  set (b2 := PSL.mk_slack (mrestrict (w_H W) mem) y (Z.to_nat (k + 1))).
  assert (Lx : Z.of_nat (length bx) = k + 1).
  { unfold bx. rewrite PSL.length_mk_slack. rewrite Z2Nat.id by lia. reflexivity. }
  assert (Ly : Z.of_nat (length b2) = k + 1).
  { unfold b2. rewrite PSL.length_mk_slack. rewrite Z2Nat.id by lia. reflexivity. }
  assert (EX : forall i, (i < Z.to_nat (k + 1))%nat ->
               nth_error bx i = Some (PSL.byte_at (mrestrict (w_H W) mem) (x + Z.of_nat i)))
    by (intros i Hi; unfold bx; apply nth_mk_slack; exact Hi).
  assert (EY : forall i, (i < Z.to_nat (k + 1))%nat ->
               nth_error b2 i = Some (PSL.byte_at (mrestrict (w_H W) mem) (y + Z.of_nat i)))
    by (intros i Hi; unfold b2; apply nth_mk_slack; exact Hi).
  assert (BX : QM.bytes_at QI.asegs (mrestrict (w_H W) mem) x bx).
  { unfold bx. apply PSL.bytes_at_mk; [exact Hx | rewrite Z2Nat.id by lia; unfold TASK_SIZE in Htx; lia |].
    intros j Hj. rewrite Z2Nat.id in Hj by lia.
    destruct (Z.eq_dec j k) as [->|NE].
    - exact (proj1 (view_byte W mem (x + k) c1 Hc1v)).
    - destruct (Hbef j ltac:(lia)) as (b & Hb & _ & _). exact (proj1 (view_byte W mem (x + j) b Hb)). }
  assert (BY : QM.bytes_at QI.asegs (mrestrict (w_H W) mem) y b2).
  { unfold b2. apply PSL.bytes_at_mk; [exact Hy | rewrite Z2Nat.id by lia; unfold TASK_SIZE in Hty; lia |].
    intros j Hj. rewrite Z2Nat.id in Hj by lia.
    destruct (Z.eq_dec j k) as [->|NE].
    - exact (proj1 (view_byte W mem (y + k) c2 Hc2v)).
    - destruct (Hbef j ltac:(lia)) as (b & _ & Hb & _). exact (proj1 (view_byte W mem (y + j) b Hb)). }
  assert (HP : QS.sc_pre bx b2 (Z.to_nat k)).
  { intros j Hj. destruct (Hbef (Z.of_nat j) ltac:(lia)) as (b & Hbx1 & Hby1 & Hnz).
    destruct (view_byte W mem (x + Z.of_nat j) b Hbx1) as (_ & Ux).
    destruct (view_byte W mem (y + Z.of_nat j) b Hby1) as (_ & Uy).
    exists (PSL.byte_at (mrestrict (w_H W) mem) (x + Z.of_nat j)).
    split; [apply EX; lia|]. split.
    - rewrite (EY j ltac:(lia)). f_equal. apply bv_eq. rewrite Ux, Uy. reflexivity.
    - rewrite Ux. exact Hnz. }
  assert (CX : nth_error bx (Z.to_nat k) = Some (PSL.byte_at (mrestrict (w_H W) mem) (x + k))).
  { rewrite (EX (Z.to_nat k) ltac:(lia)). rewrite Z2Nat.id by lia. reflexivity. }
  assert (CY : nth_error b2 (Z.to_nat k) = Some (PSL.byte_at (mrestrict (w_H W) mem) (y + k))).
  { rewrite (EY (Z.to_nat k) ltac:(lia)). rewrite Z2Nat.id by lia. reflexivity. }
  destruct (view_byte W mem (x + k) c1 Hc1v) as (_ & U1).
  destruct (view_byte W mem (y + k) c2 Hc2v) as (_ & U2).
  assert (HB : bv_unsigned (PSL.byte_at (mrestrict (w_H W) mem) (x + k))
               <> bv_unsigned (PSL.byte_at (mrestrict (w_H W) mem) (y + k))
               \/ bv_unsigned (PSL.byte_at (mrestrict (w_H W) mem) (x + k)) = 0)
    by (rewrite U1, U2; exact Hstop).
  destruct (QS.res_break bx b2 (Z.to_nat k) _ _ HP CX CY HB) as (EI & ER).
  assert (SZ : QS.strcmp_sz bx b2 = k + 1).
  { unfold QS.strcmp_sz. rewrite EI. rewrite Z2Nat.id by lia. reflexivity. }
  split; [exact BX|]. split; [exact BY|]. split; [exact Lx|]. split; [exact Ly|].
  split; [unfold QS.strcmp_ok; rewrite SZ, Lx, Ly; lia|].
  split; [exact SZ|]. rewrite ER, U1, U2. apply cmpx_res.
Qed.

(* ---- the cells, in the K5 kit's `cell` type (a different inductive from the K kit's) ---- *)
Lemma q_rw_of_ro : forall m A cs, QSt.ro_cells QI.asegs m A cs ->
  forallb (fun i => negb (NM.cj_drop tfibsegs (Z_to_bv 64 (A + Z.of_nat i)))) (seq 0 (QC.cells_size cs)) = true ->
  length (QC.cells_bytes cs) = QC.cells_size cs ->
  QSt.rw_cells QI.asegs m A cs.
Proof.
  intros m A cs (Hwf & HB) Hk Hl. split; [split; [exact Hwf | exact HB]|].
  destruct HB as (H0 & H1 & HB). split; [exact H0|]. split; [rewrite <- Hl; exact H1|].
  intros i Hi. pose proof (HB (Z.to_nat i) ltac:(lia)) as Hr. rewrite Z2Nat.id in Hr by lia.
  destruct (nth_error (QC.cells_bytes cs) (Z.to_nat i)) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  apply (PSL.wview_of_mrd m _ b Hr).
  pose proof (PSL.keep_range A _ Hk (A + i) ltac:(lia)) as K. unfold NM.cj_drop in K.
  apply orb_false_iff in K as [K _]. exact K.
Qed.

Lemma q_ro_c8_of_val_mem : forall m A v, 0 <= A -> A + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  val_mem tfibsegs m A 8 v -> QSt.ro_cells QI.asegs m A [QC.C8 (Z_to_bv 64 v)].
Proof.
  intros m A v HA HA8 Hv HV. split; [cbn; tauto|].
  cbn [QC.cells_bytes QC.cbytes]. rewrite app_nil_r.
  split; [exact HA|]. split; [exact HA8|].
  intros i Hi. assert (Hi8 : (i < 8)%nat) by exact Hi.
  rewrite <- q_mbyte_mrd. rewrite (HV i Hi8). rewrite PSL.le_byte_8 by exact Hv.
  unfold QM.le8, word_to_le_bytes. rewrite PSL.nth_Z_to_le_bytes by exact Hi8.
  rewrite QMS.unsigned_lit by lia. reflexivity.
Qed.

Lemma q_ro_cons8 : forall m A w cs, QSt.ro_cells QI.asegs m A [QC.C8 w] -> QSt.ro_cells QI.asegs m (A + 8) cs ->
  QSt.ro_cells QI.asegs m A (QC.C8 w :: cs).
Proof.
  intros m A w cs (_ & B1) (W2 & B2). split; [cbn; tauto|].
  cbn [QC.cells_bytes QC.cbytes] in B1 |- *. rewrite app_nil_r in B1.
  apply (proj2 (QM.bytes_at_app QI.asegs m A _ _)). split; [exact B1|].
  assert (L : length (QM.le8 w) = 8%nat) by reflexivity. rewrite L. exact B2.
Qed.

Lemma q_c8_norm : forall B ly (W : world tfibsegs) mem a v,
  cell_holds B ly (aview tfibsegs (w_H W) mem) (z8 (ANum a) v) ->
  ((0 <=? a) && (a + 8 <=? 2 ^ 64) && (0 <=? v) && (v <? 2 ^ 64))%bool = true ->
  forallb (fun i => negb (NM.cj_drop tfibsegs (Z_to_bv 64 (a + Z.of_nat i)))) (seq 0 8) = true ->
  QSt.ro_cells QI.asegs (NM.normalize_cj tfibsegs (mrestrict (w_H W) mem)) a [QC.C8 (Z_to_bv 64 v)].
Proof.
  intros B ly W mem a v HC Hb Hk.
  apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1, H2, H3. apply Z.ltb_lt in H4.
  apply (QD.ro_cells_agree QI.asegs (mrestrict (w_H W) mem)).
  - apply q_ro_c8_of_val_mem; [exact H1 | exact H2 | lia |]. exact (PSL.val_mem_of_holds8 B ly (w_H W) mem a v HC).
  - apply PSL.agree_cells. exact Hk.
Qed.

Lemma q_c1_norm : forall B ly (W : world tfibsegs) mem a v,
  cell_holds B ly (aview tfibsegs (w_H W) mem) (z1 (ANum a) v) ->
  ((0 <=? a) && (a + 1 <=? 2 ^ 64) && (0 <=? v) && (v <? 256))%bool = true ->
  forallb (fun i => negb (NM.cj_drop tfibsegs (Z_to_bv 64 (a + Z.of_nat i)))) (seq 0 1) = true ->
  QSt.ro_cells QI.asegs (NM.normalize_cj tfibsegs (mrestrict (w_H W) mem)) a [QC.C1 (Z_to_bv 8 v)].
Proof.
  intros B ly W mem a v HC Hb Hk.
  apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1, H2, H3. apply Z.ltb_lt in H4.
  apply (QD.ro_cells_agree QI.asegs (mrestrict (w_H W) mem)).
  - apply QQ.ro_C1_of_bytes.
    unfold cell_holds in HC. cbn [z1 c1 c_at c_val c_w aeval] in HC.
    specialize (HC 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in HC. rewrite Z.add_0_r in HC.
    pose proof (PSS.bytes_at1_of_view (w_H W) mem a _ ltac:(lia) HC) as Hb1.
    rewrite PSL.le_byte_1 in Hb1 by lia. exact Hb1.
  - apply PSL.agree_cells. exact Hk.
Qed.

(* one byte of an 8-byte const cell: the K5/B10 walk reads 0x13d31d and 0x13d322, which YF0m's Tfib_const_abs pins
   as bytes 5 and 2 of the words at 0x13d318 and 0x13d320 *)
Lemma q_c1_of_z8 : forall B ly (W : world tfibsegs) mem a v (j : nat) (u w : Z),
  cell_holds B ly (aview tfibsegs (w_H W) mem) (z8 (ANum a) v) ->
  (j < 8)%nat -> a + Z.of_nat j = w -> 0 <= w < 2 ^ 64 -> YG0f.le_byte v 8 j = u ->
  forallb (fun i => negb (NM.cj_drop tfibsegs (Z_to_bv 64 (w + Z.of_nat i)))) (seq 0 1) = true ->
  QSt.ro_cells QI.asegs (NM.normalize_cj tfibsegs (mrestrict (w_H W) mem)) w [QC.C1 (Z_to_bv 8 u)].
Proof.
  intros B ly W mem a v j u w HC Hj Hw Hwr Hu Hk.
  apply (QD.ro_cells_agree QI.asegs (mrestrict (w_H W) mem)).
  - apply QQ.ro_C1_of_bytes.
    unfold cell_holds in HC. cbn [z8 c8 c_at c_val c_w aeval] in HC.
    specialize (HC j Hj). rewrite Hw, Hu in HC.
    exact (PSS.bytes_at1_of_view (w_H W) mem w u Hwr HC).
  - apply PSL.agree_cells. exact Hk.
Qed.

(* the K kit's 8-byte cell is the K5 kit's: the two `cell` inductives differ, their bytes do not *)
Lemma q_ro_c8_of_k : forall m A w, BSt.ro_cells BI.bsegs m A [BC.C8 w] -> QSt.ro_cells QI.asegs m A [QC.C8 w].
Proof. intros m A w (_ & HB). split; [cbn; tauto|]. exact HB. Qed.

(* AU/PSstrlen.v chk_norm, carried across the cell type *)
Lemma chk_norm_q : forall (H : word -> bool) mem x n,
  0 <= x -> 0 < n -> x + n <= 2 ^ 47 -> n <= 2 ^ 40 -> QK.region_in_mem x n ->
  range_addressable (aview tfibsegs H mem) SHADOW_OFF x n -> shadow_hull_vis (aview tfibsegs H mem) x n ->
  QQ.chk_ok (NM.normalize_cj tfibsegs (mrestrict H mem)) x n.
Proof.
  intros H mem x n Hx Hn Hxn H40 Hreg Hra Hhull.
  destruct (PSL.chk_norm H mem x n Hx Hn Hxn H40 Hreg Hra Hhull) as (AC & QW0 & RO).
  split; [exact AC|]. split; [|exact RO].
  intros Hb. destruct (QW0 Hb) as (w1 & w2 & Q1 & Q2).
  exists w1, w2. split; apply q_ro_c8_of_k; assumption.
Qed.

(* a cell of image B's Tfib_const_abs is an ARcf const cell under image B's TfibSyms (YF0m.ts_const): A/PSstrlen.v's
   const_cell over YF0m *)
Lemma const_cell_B : forall B ly rd c, YF0m.TfibSyms B -> Forall (cell_holds B ly rd) (as_const B ly) ->
  In c YF0m.Tfib_const_abs -> cell_holds B ly rd c.
Proof.
  intros B ly rd c TS F Hin. rewrite (YF0m.ts_const B TS ly) in F. rewrite Forall_forall in F. apply F.
  unfold YF0m.Tfib_const. apply in_app_iff. right. apply in_app_iff. left. exact Hin.
Qed.

(* each cell found BY VALUE in YF0m.v's Tfib_const_abs (AU/PSstrlen.v cell_in): no row index *)
Ltac qcst TS CF := apply (const_cell_B _ _ _ _ TS CF); PSL.cell_in.
Ltac qro8 B ly TS CF := apply (q_c8_norm B ly); [qcst TS CF | vm_compute; reflexivity | vm_compute; reflexivity].
Ltac qro1 B ly TS CF := apply (q_c1_norm B ly); [qcst TS CF | vm_compute; reflexivity | vm_compute; reflexivity].
Ltac qrw := apply q_rw_of_ro; [| vm_compute; reflexivity | reflexivity].

(* the trampoline and the interceptor in the kit's words, one lemma of the kit (K5/B10/I_strcmp_entry.v
   istrcmp_wrap_closed: `jal zero, 0x433c0` at 0x42e0c, then istrcmp_spec rip_proof). ISTRCMP_DEPTH = 2272. *)
Lemma bz_strcmp : forall regs F fc m0 (p1 p2 : Z) (b1 b2 : list byte) (lo : Z),
  reg_get regs 10 = Z_to_bv 64 p1 -> reg_get regs 11 = Z_to_bv 64 p2 ->
  QF.stk QI.asegs m0 lo (bv_unsigned (reg_get regs 2)) ->
  lo <= bv_unsigned (reg_get regs 2) - 2272 ->
  QR.kHighShadowEnd + 8 <= lo -> bv_unsigned (reg_get regs 2) < 2 ^ 63 ->
  Z.of_nat (length b1) < 2 ^ 40 -> Z.of_nat (length b2) < 2 ^ 40 ->
  QM.bytes_at QI.asegs m0 p1 b1 -> QM.bytes_at QI.asegs m0 p2 b2 -> QS.strcmp_ok b1 b2 ->
  p1 + QS.strcmp_sz b1 b2 <= 2 ^ 47 -> p2 + QS.strcmp_sz b1 b2 <= 2 ^ 47 ->
  (p1 + QS.strcmp_sz b1 b2 <= lo \/ bv_unsigned (reg_get regs 2) <= p1) ->
  (p2 + QS.strcmp_sz b1 b2 <= lo \/ bv_unsigned (reg_get regs 2) <= p2) ->
  QQ.chk_ok m0 p1 (QS.strcmp_sz b1 b2) -> QQ.chk_ok m0 p2 (QS.strcmp_sz b1 b2) ->
  QR.m2s_cells m0 -> QW.icells_scmp m0 -> QM.mem_inv QI.asegs m0 ->
  BE.evt BI.bsegs
    (QL.istrcmp_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
       (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
       (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) F fc
       (QS.strcmp_res b1 b2) lo m0)
    (BMS.MS (L6.mkR_of regs) F (Z_to_bv 64 0x42e0c) fc None m0 (YK11.seg_rom BI.bsegs)).
Proof.
  intros regs F fc m0 p1 p2 b1 b2 lo Ha0 Ha1 ST LO LOLO SPH L1 L2 B1 B2 OK R1 R2 SEP1 SEP2 CS1 CS2 M2S IC MI.
  apply k5_evt_bz.
  change (L6.mkR_of regs) with (QF.mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
    (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10)
    (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16)
    (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
    (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28)
    (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)).
  exact (QEnt.istrcmp_wrap_closed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F fc m0 p1 p2 b1 b2 lo Ha0 Ha1 ST LO LOLO SPH L1 L2 B1 B2 OK R1 R2 SEP1 SEP2 CS1 CS2 M2S IC MI).
Qed.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* every cell the K5/B10 strcmp walk reads, on its (normalized) memory, from ARcf's const cells under YF0m.TfibSyms B,
   each found BY VALUE in lib/Reusable/YF0m.v Tfib_const_abs: the word 0x13d318 (byte 5 = 0x13d31d is 0), the word
   0x13d320 (byte 2 = 0x13d322 is 1), 0xab6f8 (__asan_shadow_memory_dynamic_address) = 0x7fff8000, 0xac3d8
   (asan_inited) = 1, 0xac3e0.. = kHighMemEnd, 0, 0, and the .got slots 0xa2840, 0xa2850..0xa2868. *)
Lemma walk_cells_scmp : forall B ly S Hp (W : world tfibsegs) mem md,
  YF0m.TfibSyms B -> ARcf tfibsegs B ly S Hp W mem md ->
  QR.m2s_cells (NM.normalize_cj tfibsegs (mrestrict (w_H W) mem)) /\
  QW.icells_scmp (NM.normalize_cj tfibsegs (mrestrict (w_H W) mem)).
Proof.
  intros B ly S Hp W mem md TS HAR.
  pose proof (amc_const _ _ _ _ _ (proj1 HAR)) as CF.
  split.
  - unfold QR.m2s_cells. split; [|split].
    + qrw. apply q_ro_cons8; [qro8 B ly TS CF|]. apply q_ro_cons8; [qro8 B ly TS CF|].
      apply q_ro_cons8; [qro8 B ly TS CF|]. qro8 B ly TS CF.
    + qrw. qro8 B ly TS CF.
    + qrw. apply q_ro_cons8; [qro8 B ly TS CF|]. apply q_ro_cons8; [qro8 B ly TS CF|].
      qro8 B ly TS CF.
  - unfold QW.icells_scmp. split; [|split; [|split; [|split; [|split]]]].
    + qro8 B ly TS CF.
    + qro8 B ly TS CF.
    + qro8 B ly TS CF.
    + qrw. qro1 B ly TS CF.
    + apply (q_c1_of_z8 B ly W mem 0x13d318 0x101000100000000 5%nat 0 0x13d31d);
        [qcst TS CF | lia | vm_compute; reflexivity | lia | vm_compute; reflexivity
        | vm_compute; reflexivity].
    + apply (q_c1_of_z8 B ly W mem 0x13d320 0x101010101010101 2%nat 1 0x13d322);
        [qcst TS CF | lia | vm_compute; reflexivity | lia | vm_compute; reflexivity
        | vm_compute; reflexivity].
Qed.

(* the core, over ARcf and the target's str_meet, with the frame separation named *)
Lemma ps_strcmp_core_B : forall B, YF0m.TfibSyms B ->
  forall ly S Hp (W : world tfibsegs) regs mem md x y k c1 c2,
  ecall_pre_cf tfibsegs B ly S Hp W regs mem md -> rom_view tfibsegs W mem ->
  YK11.getr regs 10 = w64 x -> YK11.getr regs 11 = w64 y -> 0 < x -> 0 < y -> k + 1 < 2 ^ 32 ->
  str_meet tfibsegs W mem x y k c1 c2 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x (k + 1) ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) x (k + 1) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF y (k + 1) ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) y (k + 1) ->
  amem_range8 x (k + 1) -> amem_range8 y (k + 1) ->
  x + k + 1 <= spZ regs - 2 * ESTACK \/ spZ regs <= x ->
  y + k + 1 <= spZ regs - 2 * ESTACK \/ spZ regs <= y ->
  SRr tfibsegs W (cfg_at tfibsegs 0x42e0c regs mem md)
    (PSL.strlen_post B ly S Hp W regs mem md (strcmp_res c1 c2)).
Proof.
  intros B TS ly S Hp W regs mem md x y k c1 c2 Hpre Hrom Hx Hy Hx0 Hy0 Hk32 Hmeet
    Hrax Hhx Hray Hhy Hamx Hamy Hfrx Hfry.
  pose proof Hpre as (HAR & Hret & Hal & Hlo & Hhi & Hwin & _ & _).
  pose proof (amc_layout _ _ _ _ _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
  unfold YG0f.kHighMemBeg, YG0f.kHighMemEnd in Lbeg, Lhi.
  assert (HE : ESTACK = 4096) by reflexivity.
  pose proof Hmeet as (Hk0 & _ & _ & _ & _).
  assert (Hamx' : (0 <= x /\ x + (k + 1) + 8 <= 0x7fff7fff) \/
                  (0x10007fff800f <= x /\ x + (k + 1) + 8 <= 0x7fffffffffff))
    by (unfold amem_range8, YG0f.kLowMemEnd, YG0f.kHighMemBeg, YG0f.kHighMemEnd in Hamx; lia).
  assert (Hamy' : (0 <= y /\ y + (k + 1) + 8 <= 0x7fff7fff) \/
                  (0x10007fff800f <= y /\ y + (k + 1) + 8 <= 0x7fffffffffff))
    by (unfold amem_range8, YG0f.kLowMemEnd, YG0f.kHighMemBeg, YG0f.kHighMemEnd in Hamy; lia).
  pose proof (PSL.ro_agree_of_rom_view W mem Hrom) as RO.
  pose proof (walk_cells_scmp B ly S Hp W mem md TS HAR) as (M2S & ICS).
  assert (Esp : bv_unsigned (reg_get regs 2) = spZ regs)
    by (unfold spZ; rewrite PSL.getr_nz by reflexivity; reflexivity).
  assert (Ha0 : reg_get regs 10 = Z_to_bv 64 x) by (rewrite <- PSL.getr_nz by reflexivity; exact Hx).
  assert (Ha1 : reg_get regs 11 = Z_to_bv 64 y) by (rewrite <- PSL.getr_nz by reflexivity; exact Hy).
  destruct (meet_strings W mem x y k c1 c2 Hmeet ltac:(lia) ltac:(lia)
              ltac:(unfold TASK_SIZE; lia) ltac:(unfold TASK_SIZE; lia))
    as (BX & BY & LX & LY & OK & SZ & RES).
  set (H := w_H W) in *. set (mR := mrestrict H mem) in *. set (sp := spZ regs) in *.
  set (bx := PSL.mk_slack mR x (Z.to_nat (k + 1))) in *.
  set (b2 := PSL.mk_slack mR y (Z.to_nat (k + 1))) in *.
  set (lo := sp - 2272).
  apply (ESR.srr_of_evt tfibsegs PSL.Hwx_ps W 0x42e0c regs mem md
    (PSL.walk_at (QL.istrcmp_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
       (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21)
       (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
       fp_regs fp_csr (QS.strcmp_res bx b2) lo (NM.normalize_cj tfibsegs mR)) mR)).
  - refine (_ : BE.evt BI.bsegs _ (PSL.st_at regs fp_regs (Z_to_bv 64 0x42e0c) fp_csr mR)).
    apply PSL.bz_transport; [exact RO|].
    apply (bz_strcmp regs fp_regs fp_csr _ x y bx b2 lo).
    + exact Ha0.
    + exact Ha1.
    + rewrite Esp. apply PSL.stk_norm_high; [unfold lo, PSL.PS_IMG_TOP; lia | unfold TASK_SIZE; lia |].
      apply ESR.stk_of_apresent; [unfold lo; lia | lia |].
      intros a Ha. apply Hwin. unfold lo in Ha. lia.
    + rewrite Esp. unfold lo. lia.
    + unfold QR.kHighShadowEnd, lo. lia.
    + rewrite Esp. lia.
    + rewrite LX. lia.
    + rewrite LY. lia.
    + refine (NM.bytes_at_normalize_cj_low tfibsegs mR x bx RO _ BX).
      rewrite LX. unfold TASK_SIZE. lia.
    + refine (NM.bytes_at_normalize_cj_low tfibsegs mR y b2 RO _ BY).
      rewrite LY. unfold TASK_SIZE. lia.
    + exact OK.
    + rewrite SZ. lia.
    + rewrite SZ. lia.
    + rewrite Esp, SZ. unfold lo. lia.
    + rewrite Esp, SZ. unfold lo. lia.
    + rewrite SZ. apply chk_norm_q; [lia | lia | lia | lia | | exact Hrax | exact Hhx].
      unfold QK.region_in_mem, QR.kLowMemEnd, QR.kHighShadowEnd, QR.kHighMemEnd. lia.
    + rewrite SZ. apply chk_norm_q; [lia | lia | lia | lia | | exact Hray | exact Hhy].
      unfold QK.region_in_mem, QR.kLowMemEnd, QR.kHighShadowEnd, QR.kHighMemEnd. lia.
    + exact M2S.
    + exact ICS.
    + apply PSL.bz_mem_inv_normalize.
  - intros ms' model' (c & s0 & HQ & Hrel & Hsame & Heqv) Hsbm _.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Es0 & MU & _ & _ & ST').
    subst s0. rewrite Esp in MU, ST'.
    apply (PSL.post_of_walk B ly S Hp W regs mem md (QS.strcmp_res bx b2) (strcmp_res c1 c2) 2272 ms' model' c m'
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hpre RO); try assumption.
    + lia.
    + rewrite RES. reflexivity.
Qed.

(* ---- the contract ---- *)
(* the image-B twin of lib/A/PSstrcmp.v ps_strcmp_realizes_cfm: with the memnorm keep (astrcmp_realizes_cfm), which
   PSL.strlen_post carries and PSL.post_of_walk proves *)
Theorem ps_strcmp_realizes_cfm_B : forall B, YF0m.TfibSyms B -> astrcmp_realizes_cfm tfibsegs B 0x42e0c.
Proof.
  intros B TS ly S Hp W regs mem md x y k c1 c2 Hpre H2lo H2win Hx Hy Hx0 Hy0 Hk32 Hxk Hyk Hmeet
    Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy Hrom.
  pose proof Hmeet as (Hk0 & _ & _ & _ & _).
  pose proof (PSL.str_off_frame (spZ regs) x k Hk0 Hbx) as Hfrx.
  pose proof (PSL.str_off_frame (spZ regs) y k Hk0 Hby) as Hfry.
  exact (ps_strcmp_core_B B TS ly S Hp W regs mem md x y k c1 c2 Hpre Hrom Hx Hy Hx0 Hy0 Hk32 Hmeet
           Hrax Hhx Hray Hhy Hamx Hamy Hfrx Hfry).
Qed.

(* the image-B twin of lib/A/PSstrcmp.v ps_strcmp_realizes_cf: the same row with the keep dropped *)
Theorem ps_strcmp_realizes_cf_B : forall B, YF0m.TfibSyms B -> astrcmp_realizes_cf tfibsegs B 0x42e0c.
Proof.
  intros B TS ly S Hp W regs mem md x y k c1 c2 Hpre H2lo H2win Hx Hy Hx0 Hy0 Hk32 Hxk Hyk Hmeet
    Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy Hrom.
  eapply SRr_mono; [exact (ps_strcmp_realizes_cfm_B B TS ly S Hp W regs mem md x y k c1 c2 Hpre H2lo H2win Hx Hy Hx0
    Hy0 Hk32 Hxk Hyk Hmeet Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy Hrom)|].
  cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & HAR & Hp' & Hs & Hv & Hf & Hap & _).
  split; [reflexivity|]. exists regs', mem', md'.
  exact (conj Hc (conj HAR (conj Hp' (conj Hs (conj Hv (conj Hf Hap)))))).
Qed.

End core.
