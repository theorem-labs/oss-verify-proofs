(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-29 (PresetStrcmpA, c-libc-stdio lane): fuzz_preset.asan's strcmp interceptor, called at its
   trampoline __wrap_strcmp 0x42d20, in the contract of the second allocator instance:
   `ps_strcmp_realizes_cf : forall B, TfibSyms B -> astrcmp_realizes_cf tfibsegs B 0x42d20`
   (lib/Reusable/YGcfStr.v). Image A (fuzz_preset.asan) only.
   2026-10-29 (pstr102, #102 pin A' asan 1be0f53d, twin bff8519b): presetstr-ro 45e489ec67c7's file (blob 59361db7ca8a)
   with every image numeral moved from the old twin f0d2e8d4 to A' by symbol + offset (table in the commit),
   over the A' kit lib/K5/A10 (re-derived by tools/presetstr/presetstr_reloc.py); pc_strcmp_A cites CfImgA's
   cf_pc_strcmp by field name, as YGcfStr.v holds no pc any more.
   rule 24: no function proved. This file is a PORT of an existing composition; it composes:

   WHICH PC. 0x42d20 is __wrap_strcmp, the one-instruction trampoline (`jal zero, 0x432d4`), NOT the interceptor
   body ___interceptor_strcmp 0x432d4. The same choice PSstrlen.v made for strlen (0x42d18, not 0x42da8), and for
   the same reason: fuzz_preset's 19 strcmp call sites are all `jal ra, __wrap_strcmp` (YGcfStr.v's header records
   that objdump count, taken on the two rebuilt unstripped twins; I did not re-run it), so the contract must hold
   at the pc the program actually calls, and lib/A/CfImgA.v's `cf_pc_strcmp` (the API field that feeds AsanAPI_cf) is
   0x42d20. The kit walk used here, K5/A10/I_strcmp_entry.v `istrcmp_wrap_closed`, starts at the trampoline and
   steps once into the body, so no separate statement at 0x432d4 is needed.

   DONORS
   - the composition: origin/cold/port-state-rt-str 999a7102a6e (17818dd9abc an ancestor; the file is unchanged
     between them except its header), proofs/omx-clap-core/fuzz_state/lib/A/FSstrcmp.v, `fs_strcmp_realizesU`, Qed.
     Every lemma below names its donor lines FSstrcmp.v:N-M;
   - the infrastructure it composes, here taken from lib/A/PSstrlen.v (this tree's port of the donor's FSstrlen.v,
     which FSstrcmp.v also composes): `post_of_walk`, `walk_at`, `st_at`, `bz_transport`, `mk_slack`, `byte_at`,
     `bytes_at_mk`, `agree_cells`, `const_cell`, `str_off_frame`, `chk_norm`, `stk_norm_high`,
     `bz_mem_inv_normalize`, `ro_agree_of_rom_view`, `val_mem_of_holds8`, `getr_nz`, and the post `strlen_post`,
     which is the SHARED post of both contracts (`a0 = w64 v` with ARcf kept, the callee-saved registers kept and
     memory outside [sp - 2 * ESTACK, sp) unchanged): here v := strcmp_res c1 c2;
   - the shadow half: lib/A/PSbz_str.v, REUSED, not copied (`chk_ok_of_view`, `bytes_at1_of_view`, `mbyte_mrd`);
   - the walk: this tree's lib/K5, leptonica/fhmtgen_fuzzer's kit relocated to preset:
     K5/A10/I_strcmp_entry.v `istrcmp_wrap_closed` (= istrcmp_wrap_spec rip_proof: the trampoline step, then
     I_strcmp.v istrcmp_spec with K5/A10/R_isPoisoned.v rip_proof). musl's strcmp 0x9b8cc is NOT on the walked
     path: the interceptor reaches it through __interception::real_strcmp (0xa3d30) only when TryAsanInitFromRtl
     returns 0, and the walk takes asan_inited = 1 (icells_scmp's rw cell 0xabb98 = 1). So there is NO
     `PsRealStrcmp` premise, and the 8-byte word 0xa3d30 is NOT needed in AF0m's Tfib_const_abs (checked by word
     address, not by name: 0xa3d30 does not occur in lib/A/AF0m.v; it does not have to);
   - the evt -> SRr bridge: lib/Reusable/YEvtSRr.v (srr_of_evt, stk_of_apresent);
   - the transports: lib/MemNorm.v, lib/Lib/RegisterBridge.v, lib/Lib/Regs6ss.v, through PSstrlen's bz_transport.

   THE ONE STATEMENT CHANGE (the parent's decision, 2026-10-29): astrcmp_realizes_cf now takes the per-call
   `rom_view segs W mem`, in the place astrlen_realizes_cf has it. AStrcmpDef's own proof (fuzz_grant's symbolic
   walk) tracks each read, so it never needs rom_view; this route is the kit composition, whose normalisation
   MemNorm.evt_normalize_cj needs `ro_agree` of the whole store (lib/MemNorm.v:861-862), because the kit's mem_inv
   forbids stored bytes at read-only addresses (lib/K5/Lib/Mem.v:106, :127-130) while data loads read the store
   first (Mem.v:57); and ARcf has no read-only value clause. See YGcfStr.v's header.

   WHAT CHANGED, lemma by lemma (P = ported with paths changed; R = re-derived for preset A; S = swapped AR -> ARcf;
   N = new shape, forced by the target text; K = the K5 kit's copy of a K-kit lemma, needed because each kit has its
   OWN inductive `msteps` and its OWN inductive `cell` type, so those two are the only things in this file that
   cannot cross kits by conversion):
     k5_msteps_bz, k5_evt_bz                        K  (no donor: PSstrlen.v:234-257's bz_msteps_l / bz_evt_l, between
                                                       this tree's two kits instead of kit and lib/Lib)
     q_mbyte_mrd                                    K  PSbz_str.v mbyte_mrd in K5 names (both by reflexivity)
     nth_mk_slack, view_byte                        N  FSstrcmp.v:195-229 str_prefix_facts read the string out of
                                                       `cstr`; the target gives `str_meet` over `aview`, so the
                                                       strings here are the bytes the walk reads (mk_slack)
     cmpx_res                                       N  FSstrcmp.v:118-124 cmpx_sgn + :91-116 strcmp_facts's result
                                                       clause -> the target's strcmp_res (CharCmpX) directly
     meet_strings                                   N  FSstrcmp.v:91-116 strcmp_facts + :127-144 map_bv8_inj /
                                                       cstr_range: from str_meet, the two byte lists, their
                                                       bytes_at, the kit's strcmp_ok / strcmp_sz / strcmp_res
     q_rw_of_ro, q_ro_c8_of_val_mem, q_ro_cons8,    K  PSstrlen.v:551-563, :583-603, :619-650 in K5 names
       q_c8_norm, q_c1_norm
     q_c1_of_z8                                     N  one byte of an 8-byte const cell: the K5 walk reads
                                                       0x13cadd and 0x13cae2, which AF0m pins inside the words at
                                                       0x13cad8 and 0x13cae0 (PSstrlen needed only whole cells)
     q_ro_c8_of_k, chk_norm_q                       K  PSstrlen.v:417-427 chk_norm carried across the cell type
     bz_strcmp                                      R  FSstrcmp.v:160-190 -> over istrcmp_wrap_closed (entry
                                                       0x42d20, depth 2272 = ISTRCMP_DEPTH); the kit's premises are
                                                       leptonica's: `kHighShadowEnd + 8 <= lo`
     walk_cells_scmp                                S  FSstrcmp.v's FSL.walk_cells use -> the 6 cells of K5's
                                                       icells_scmp and the 3 of its m2s_cells, all from ARcf's
                                                       const cells (amc_const) under TfibSyms B
     str_prefix_facts                               dropped (its content is meet_strings + PSstrlen's chk_norm)
     fs_strcmp_realizesU                            S  FSstrcmp.v:231-322 -> ps_strcmp_core + ps_strcmp_realizes_cf
     fs_strcmp_realizes, strcmp_k, nth_error_firstn_lt, nonzero_head, map_bv8_inj, cstr_range,
       range_addressable_sub, hull_sub                 dropped: the donor needed them to cut whole C strings down to
                                                       the compared prefix and to weaken its shadow facts to it; the
                                                       target's str_meet / src_ok_cf are already stated at k + 1

   PREMISES. The donor's theorem took AR_laws tfibsegs B, TfibSyms B, FsShadowSyms B and FSL.FsRtCells B. Here:
   AR_laws_cf is proved (AR_laws_ok_cf, through PSstrlen's post_of_walk), not a premise; TfibSyms B is kept; the
   other two are gone - every cell the walk reads is in AF0m's Tfib_const_abs (found BY VALUE, PSL.cell_in; no proof
   names a row index), so unlike strlen there is NO cell premise and NO generated cell to add. *)
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
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.ImageA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.D_kit.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.I_consts.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.I_qck.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.R_m2s.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.I_strcmp_spec.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.I_strcmpw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.I_strcmp.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.I_strcmp_entry.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK14.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YEvtSRr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YP09 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI04 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0d2cf YG0lawscf YGcfStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfImgA PSbz_str PSstrlen.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
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
Module QI := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.ImageA.
Module QD := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.D_kit.
Module QK := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.I_consts.
Module QQ := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.I_qck.
Module QR := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.R_m2s.
Module QS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.I_strcmp_spec.
Module QW := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.I_strcmpw.
Module QL := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.I_strcmp.
Module QEnt := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10.I_strcmp_entry.
Module PSS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSbz_str.
Module PSL := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSstrlen.
Module ESR := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YEvtSRr.

(* the pc of the contract: __wrap_strcmp in fuzz_preset.asan, the same number in CfImgA (generated from the ELF; cited
   by field name) and in the kit's entry walk *)
Lemma pc_strcmp_A : @cf_pc_strcmp CfImgA.CfImg_A = 0x42d20 /\ QEnt.e_wrap_strcmp = 0x42d20.
Proof. split; reflexivity. Qed.

(* ---- the two kits' runs are the same run (each kit has its OWN inductive `msteps`) ---- *)
(* PSstrlen.v:234-239 between lib/K and lib/Lib; here between lib/K5 and lib/K *)
Lemma k5_msteps_bz : forall s s', QE.msteps QI.asegs s s' -> BE.msteps BI.asegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH].
  - apply BE.msteps_refl.
  - eapply BE.msteps_cons; [exact Hs | exact IH].
Qed.

(* PSstrlen.v:242-243 *)
Lemma k5_evt_bz : forall (Q : machine_state -> Prop) ms, QE.evt QI.asegs Q ms -> BE.evt BI.asegs Q ms.
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
  BM.mrd BI.asegs (mrestrict (w_H W) mem) (BM.wa a) <> None /\
  bv_unsigned (PSL.byte_at (mrestrict (w_H W) mem) a) = v.
Proof.
  intros W mem a v Hv. unfold aview in Hv. rewrite PSS.mbyte_mrd in Hv. unfold PSL.byte_at.
  destruct (BM.mrd BI.asegs (mrestrict (w_H W) mem) (BM.wa a)) as [b|] eqn:E.
  - cbn [option_map] in Hv. injection Hv as <-. split; [discriminate | reflexivity].
  - cbn [option_map] in Hv. discriminate Hv.
Qed.

(* FSstrcmp.v:118-124 cmpx_sgn: the kit's result is the contract's CharCmpX *)
Lemma cmpx_res : forall c1 c2, QS.cmpx c1 c2 = strcmp_res c1 c2.
Proof.
  intros c1 c2. unfold QS.cmpx, strcmp_res.
  destruct (Z.eqb_spec c1 c2) as [->|NE].
  - rewrite Z.ltb_irrefl. reflexivity.
  - destruct (Z.ltb_spec c1 c2) as [L|L]; [reflexivity|].
    destruct (Z.ltb_spec c2 c1) as [L2|L2]; [reflexivity | lia].
Qed.

(* FSstrcmp.v:91-116 strcmp_facts, restated for the target's str_meet: the two strings the walk compares are the
   k + 1 bytes it reads at x and at y, they stop at k, and the kit's result is the contract's *)
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
(* PSstrlen.v:551-563 *)
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

(* PSstrlen.v:583-593 *)
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

(* PSstrlen.v:596-603 *)
Lemma q_ro_cons8 : forall m A w cs, QSt.ro_cells QI.asegs m A [QC.C8 w] -> QSt.ro_cells QI.asegs m (A + 8) cs ->
  QSt.ro_cells QI.asegs m A (QC.C8 w :: cs).
Proof.
  intros m A w cs (_ & B1) (W2 & B2). split; [cbn; tauto|].
  cbn [QC.cells_bytes QC.cbytes] in B1 |- *. rewrite app_nil_r in B1.
  apply (proj2 (QM.bytes_at_app QI.asegs m A _ _)). split; [exact B1|].
  assert (L : length (QM.le8 w) = 8%nat) by reflexivity. rewrite L. exact B2.
Qed.

(* PSstrlen.v:619-631 *)
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

(* PSstrlen.v:634-650 *)
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

(* NEW: one byte of an 8-byte const cell. The K5 walk reads 0x13cadd and 0x13cae2, which AF0m's Tfib_const_abs pins
   as bytes 5 and 2 of the words at 0x13cad8 and 0x13cae0; PSstrlen needed only whole cells. *)
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
Lemma q_ro_c8_of_k : forall m A w, BSt.ro_cells BI.asegs m A [BC.C8 w] -> QSt.ro_cells QI.asegs m A [QC.C8 w].
Proof. intros m A w (_ & HB). split; [cbn; tauto|]. exact HB. Qed.

(* PSstrlen.v:417-427 chk_norm, carried across the cell type *)
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

(* each cell found BY VALUE in AF0m.v's Tfib_const_abs (A/PSstrlen.v cell_in; 2026-10-29, PresetStrlenB, the one
   writer of this change): no row index, so a regenerated table that moves rows breaks nothing here *)
Ltac qcst TS CF := apply (PSL.const_cell _ _ _ _ TS CF); PSL.cell_in.
Ltac qro8 B ly TS CF := apply (q_c8_norm B ly); [qcst TS CF | vm_compute; reflexivity | vm_compute; reflexivity].
Ltac qro1 B ly TS CF := apply (q_c1_norm B ly); [qcst TS CF | vm_compute; reflexivity | vm_compute; reflexivity].
Ltac qrw := apply q_rw_of_ro; [| vm_compute; reflexivity | reflexivity].

(* FSstrcmp.v:160-190, over this tree's K5 walk: the trampoline and the interceptor in the kit's words, one lemma of
   the kit (K5/A10/I_strcmp_entry.v istrcmp_wrap_closed: `jal zero, 0x432d4` at 0x42d20, then istrcmp_spec
   rip_proof). ISTRCMP_DEPTH = 2272. *)
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
  BE.evt BI.asegs
    (QL.istrcmp_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
       (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
       (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) F fc
       (QS.strcmp_res b1 b2) lo m0)
    (BMS.MS (L6.mkR_of regs) F (Z_to_bv 64 0x42d20) fc None m0 (YK11.seg_rom BI.asegs)).
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

(* every cell the K5 strcmp walk reads, on its (normalized) memory, from ARcf's const cells under TfibSyms B, each
   found BY VALUE in lib/A/AF0m.v Tfib_const_abs: the word 0x13cad8 (byte 5 = 0x13cadd is 0), the word 0x13cae0
   (byte 2 = 0x13cae2 is 1), 0xaaeb8 (__asan_shadow_memory_dynamic_address) = 0x7fff8000, 0xabb98 (asan_inited) = 1,
   0xabba0.. = kHighMemEnd, 0, 0, and the .got slots 0xa2000, 0xa2010..0xa2028. __interception::real_strcmp
   (0xa3d30) is NOT among them and is not read: the walk takes asan_inited = 1, so the interceptor never reaches the
   REAL(strcmp) tail call. *)
Lemma walk_cells_scmp : forall B ly S Hp (W : world tfibsegs) mem md,
  TfibSyms B -> ARcf tfibsegs B ly S Hp W mem md ->
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
    + apply (q_c1_of_z8 B ly W mem 0x13cad8 0x101000100000000 5%nat 0 0x13cadd);
        [qcst TS CF | lia | vm_compute; reflexivity | lia | vm_compute; reflexivity
        | vm_compute; reflexivity].
    + apply (q_c1_of_z8 B ly W mem 0x13cae0 0x101010101010101 2%nat 1 0x13cae2);
        [qcst TS CF | lia | vm_compute; reflexivity | lia | vm_compute; reflexivity
        | vm_compute; reflexivity].
Qed.

(* FSstrcmp.v:231-322 fs_strcmp_realizesU, over ARcf and the target's str_meet, with the frame separation named *)
Lemma ps_strcmp_core : forall B, TfibSyms B ->
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
  SRr tfibsegs W (cfg_at tfibsegs 0x42d20 regs mem md)
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
  apply (ESR.srr_of_evt tfibsegs PSL.Hwx_ps W 0x42d20 regs mem md
    (PSL.walk_at (QL.istrcmp_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
       (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21)
       (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
       fp_regs fp_csr (QS.strcmp_res bx b2) lo (NM.normalize_cj tfibsegs mR)) mR)).
  - refine (_ : BE.evt BI.asegs _ (PSL.st_at regs fp_regs (Z_to_bv 64 0x42d20) fp_csr mR)).
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
(* with the memnorm keep (astrcmp_realizes_cfm): PSL.strlen_post carries it, proved by PSL.post_of_walk *)
Theorem ps_strcmp_realizes_cfm : forall B, TfibSyms B -> astrcmp_realizes_cfm tfibsegs B 0x42d20.
Proof.
  intros B TS ly S Hp W regs mem md x y k c1 c2 Hpre H2lo H2win Hx Hy Hx0 Hy0 Hk32 Hxk Hyk Hmeet
    Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy Hrom.
  pose proof Hmeet as (Hk0 & _ & _ & _ & _).
  pose proof (PSL.str_off_frame (spZ regs) x k Hk0 Hbx) as Hfrx.
  pose proof (PSL.str_off_frame (spZ regs) y k Hk0 Hby) as Hfry.
  exact (ps_strcmp_core B TS ly S Hp W regs mem md x y k c1 c2 Hpre Hrom Hx Hy Hx0 Hy0 Hk32 Hmeet
           Hrax Hhx Hray Hhy Hamx Hamy Hfrx Hfry).
Qed.

(* astrcmp_realizes_cf: the same row with the keep dropped *)
Theorem ps_strcmp_realizes_cf : forall B, TfibSyms B -> astrcmp_realizes_cf tfibsegs B 0x42d20.
Proof.
  intros B TS ly S Hp W regs mem md x y k c1 c2 Hpre H2lo H2win Hx Hy Hx0 Hy0 Hk32 Hxk Hyk Hmeet
    Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy Hrom.
  eapply SRr_mono; [exact (ps_strcmp_realizes_cfm B TS ly S Hp W regs mem md x y k c1 c2 Hpre H2lo H2win Hx Hy Hx0
    Hy0 Hk32 Hxk Hyk Hmeet Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy Hrom)|].
  cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & HAR & Hp' & Hs & Hv & Hf & Hap & _).
  split; [reflexivity|]. exists regs', mem', md'.
  exact (conj Hc (conj HAR (conj Hp' (conj Hs (conj Hv (conj Hf Hap)))))).
Qed.

End core.
