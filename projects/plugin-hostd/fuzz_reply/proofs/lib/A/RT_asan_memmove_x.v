(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: fuzz_reply.asan's __asan_memmove (0x52e04), its site contract
   W_sites.v amemmove_realizes, as an instance of the Bz walk Bz/A/I_amemmovew.v amemmove_spec.
   The pieces composed:
   - the walk: lib/A/Bz/A/I_amemmovew.v (pcap's walk, a working branch eabce720039, relocated to
     fuzz_reply.asan: the 220 words differ only in auipc/ld/jal) with its section hypothesis RIP =
     Bz/A/R_isPoisoned.v rip_proof, and the internal memmove lib/A/Bz/A/I_imemmove.v it calls;
   - the transport and the post: lib/A/RT_post.v (aentry_post_of_walk, bz_transport, chk_norm, stk_norm_high,
     ro_agree_of_rom_view, the cell lemmas), lib/A/FRbz_bridge.v (srr_of_evt, stk_of_apresent) and FRbz_str.v;
   - the runtime cells: the relocated core's Tfib_const (AF0x.tfib_const_lookup from TfibSyms), so this file takes
     no cell premise of its own.
   The program calls __asan_memmove directly (jal 0x52e04), so there is no trampoline.
   No refusal exit: the walk proves both range checks pass (the quick check, or __asan_region_is_poisoned returning
   0), so it never reaches an error branch, the fatal stack trace or libunwind. *)
(* Modified by Theorem Labs, 2026-10-29: from lib/A/RT_asan_memmove.v, as the module RT_asan_memmove_x: cut to the proof of rt_amemmove and its cell lemmas (the other helper lemmas are used by Import) and restated over a generic allocator invariant ARx under lib/Rt/RTx.v's rt_laws (tfib_const_lookup_x, cell_val_x, ro8_x and walk_cells_memmove_x read the cells through the const-cells law; rt_amemmove_x); the corollaries rt_amemmove_of_x (rt_amemmove's statement, unchanged) and rt_amemmove_cf added. *)
(* lib/A/RT_asan_memmove.v's runtime contract rt_amemmove restated over a generic
   allocator invariant ARx (ghost head set Hp threaded) under the five-law record rt_laws of lib/Rt/RTx.v
   (a Theorem Labs lane's, the one record for both images: rtl_frame, rtl_stack, rtl_const, rtl_layout, rtl_const_cells).
   RT_asan_memmove.v is not edited; its helper lemmas are used by Import. The statement is W_sites_x.v's
   amemmove_realizes_x; the proof of rt_amemmove_x is RT_asan_memmove.v's with AR -> ARx (am_layout of proj1 HAR ->
   rtl_layout, al_frame / al_stack -> rtl_frame / rtl_stack, RT_kit / RT_post's AR lemmas -> their _x forms there).
   Measured (lines at a working branch 9b1367c7fe1): the original reads AR through
   al_frame / al_stack (through RT_post.aentry_post_of_walk, :379), the ARm field am_layout (:278 and RT_post.v:249),
   the layout law here, and the ARm field am_const (:128 in walk_cells_memmove, through AF0x.tfib_const_lookup), the
   const-cells law here (walk_cells_memmove_x below); the three-law note (RESUME.md:116-122 sha256 704eb9d3afa6; internal record) did not count
   the ARm fields, hence the record's rtl_layout and rtl_const_cells.
   At the end: rt_amemmove_of_x, whose statement is byte for byte RT_asan_memmove.v's rt_amemmove, from the twin at
   cgif's AR (ARx := FCiface.AR_nohp, laws RTx.rt_laws_AR); and rt_amemmove_cf, the twin at ARx := ARcf with the laws
   from AR_laws_cf (RTx.rt_laws_cf). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Img0.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.MState.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.ImageA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Step.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.D_kit.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_consts.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_qck.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_amemmovew.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FRbz_bridge.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FRbz_str.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
AB1v AB1w AE2k AE2y AF0l AF0m AF0x ACfn W_syms W_listing W_tbl W_place W_pl W_img W_kit W_sites RT_post.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.FCiface.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YGcfNames.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0ncf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0dcf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.W_sites_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RT_asan_memmove.
Open Scope Z_scope.
(* the libraries Required above (FCiface -> YF0v; the cf files) set Zify's euclidean-division flag to false
   globally (e.g. Reusable/Q/YW06_cf.v:26); the original's lia steps need it on, as in the original's own build *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Module FCI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.FCiface.
Module CFN := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YGcfNames.
Module NCF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0ncf.
Module DCF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0dcf.
Module RTX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Module WSX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.W_sites_x.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- the runtime cells the walk reads, from TfibSyms' constant table, over the const-cells law ----
   AF0x.v:207-216 tfib_const_lookup and RT_asan_memmove.v:111-121 cell_val / ro8 read the cells from AR's ARm part
   (am_const); these copies read them from the list `Forall (cell_holds B ly ..) (as_const B ly)` itself, which is
   the conclusion of RTx.v's rtl_const_cells (YCbqG.v:153 ARx_const_cells_law's text).  The proofs are the originals' with `am_const B ly S _ M` -> M. *)
Lemma tfib_const_lookup_x : forall B, TfibSyms B -> forall ly H mem a (w : nat) v,
  Forall (cell_holds B ly (aview tfibsegs H mem)) (as_const B ly) ->
  cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
  val_mem tfibsegs (mrestrict H mem) a w v.
Proof.
  intros B TB ly H mem a w v M E.
  apply (cell_holds_val_mem B ly H mem (ANum a) w (ANum v)).
  apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs H mem)) (as_const B ly)) M).
  rewrite (ts_const B TB ly). exact (cell_lookup_In _ _ _ E).
Qed.

Lemma cell_val_x : forall B, TfibSyms B -> forall ly (H : word -> bool) mem a (w : N) v,
  Forall (cell_holds B ly (aview frsegs H mem)) (as_const B ly) -> AE2y.const_chk ly a w v = true ->
  val_mem frsegs (mrestrict H mem) a (N.to_nat w) v.
Proof.
  intros B TB ly H mem a w v HM Hc.
  exact (tfib_const_lookup_x B TB ly H mem a (N.to_nat w) v HM (AE2y.const_chk_sound ly a w v Hc)).
Qed.

Ltac ro8_x B TB HM a v :=
  apply ro_c8_of_val_mem; [lia | lia | lia |
    exact (cell_val_x B TB _ _ _ a 8%N v HM ltac:(vm_compute; reflexivity))].

Lemma walk_cells_memmove_x : forall B
  (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop),
  TfibSyms B -> RTX.rt_laws frsegs B ARx -> forall ly S Hp (W : world frsegs) mem md,
  ARx ly S Hp W mem md ->
  BR2.m2s_cells (NM.normalize_cj I0.rsegs (mrestrict (w_H W) mem)) /\
  BMM.amm_cells (NM.normalize_cj I0.rsegs (mrestrict (w_H W) mem)).
Proof.
  intros B ARx TB LAWS ly S Hp W mem md HAR. pose proof (RTX.rtl_const_cells _ _ _ LAWS ly S Hp W mem md HAR) as HM.
  set (H := w_H W) in *. set (mR := mrestrict H mem) in *.
  (* the single cells on the restricted memory *)
  assert (C0 : BSt.ro_cells BI.asegs mR 0x9d9d0 [BC.C8 (Z_to_bv 64 0xa60b8)]) by ro8_x B TB HM 0x9d9d0 0xa60b8.
  assert (C1 : BSt.ro_cells BI.asegs mR 0x9d9d8 [BC.C8 (Z_to_bv 64 0xa6da8)]) by ro8_x B TB HM 0x9d9d8 0xa6da8.
  assert (C2 : BSt.ro_cells BI.asegs mR 0x9d9e0 [BC.C8 (Z_to_bv 64 0xa6db0)]) by ro8_x B TB HM 0x9d9e0 0xa6db0.
  assert (C3 : BSt.ro_cells BI.asegs mR 0x9d9e8 [BC.C8 (Z_to_bv 64 0xa6da0)]) by ro8_x B TB HM 0x9d9e8 0xa6da0.
  assert (C4 : BSt.ro_cells BI.asegs mR 0xa60b8 [BC.C8 (Z_to_bv 64 0x7fff8000)]) by ro8_x B TB HM 0xa60b8 0x7fff8000.
  assert (C5 : BSt.ro_cells BI.asegs mR 0xa6da0 [BC.C8 (Z_to_bv 64 0x7fffffffffff)]) by ro8_x B TB HM 0xa6da0 0x7fffffffffff.
  assert (C6 : BSt.ro_cells BI.asegs mR 0xa6da8 [BC.C8 (Z_to_bv 64 0)]) by ro8_x B TB HM 0xa6da8 0.
  assert (C7 : BSt.ro_cells BI.asegs mR 0xa6db0 [BC.C8 (Z_to_bv 64 0)]) by ro8_x B TB HM 0xa6db0 0.
  assert (C8 : BSt.ro_cells BI.asegs mR 0x9e538 [BC.C8 (Z_to_bv 64 0xa6d99)]) by ro8_x B TB HM 0x9e538 0xa6d99.
  assert (C9 : BSt.ro_cells BI.asegs mR 0xa6d99 [BC.C1 (Z_to_bv 8 1)]).
  { apply ro_c1_one_of_val_mem; [lia | lia |].
    exact (cell_val_x B TB ly H mem 0xa6d99 1%N 1 HM ltac:(vm_compute; reflexivity)). }
  (* the chains the walks ask for *)
  assert (G0 : BSt.ro_cells BI.asegs mR 0x9d9d0
     [BC.C8 (Z_to_bv 64 0xa60b8); BC.C8 (Z_to_bv 64 0xa6da8); BC.C8 (Z_to_bv 64 0xa6db0); BC.C8 (Z_to_bv 64 0xa6da0)]).
  { apply ro_cons8; [exact C0|]. apply ro_cons8; [exact C1|]. apply ro_cons8; [exact C2|]. exact C3. }
  assert (G1 : BSt.ro_cells BI.asegs mR 0xa6da0
     [BC.C8 (Z_to_bv 64 0x7fffffffffff); BC.C8 (Z_to_bv 64 0); BC.C8 (Z_to_bv 64 0)]).
  { apply ro_cons8; [exact C5|]. apply ro_cons8; [exact C6|]. exact C7. }
  (* move each to the normalized memory and, where the walk asks for it, to rw_cells *)
  assert (NRM : forall A k cs, BSt.ro_cells BI.asegs mR A cs -> BC.cells_size cs = k ->
     forallb (fun i => negb (NM.cj_drop I0.rsegs (Z_to_bv 64 (A + Z.of_nat i)))) (seq 0 k) = true ->
     BSt.ro_cells BI.asegs (NM.normalize_cj I0.rsegs mR) A cs).
  { intros A k cs Hc Hk Hb. eapply BD.ro_cells_agree; [exact Hc|]. rewrite Hk. apply agree_cells. exact Hb. }
  split.
  - split; [|split].
    + apply rw_of_ro; [apply (NRM _ 32%nat); [exact G0 | reflexivity | vm_compute; reflexivity]
                      | vm_compute; reflexivity | reflexivity].
    + apply rw_of_ro; [apply (NRM _ 8%nat); [exact C4 | reflexivity | vm_compute; reflexivity]
                      | vm_compute; reflexivity | reflexivity].
    + apply rw_of_ro; [apply (NRM _ 24%nat); [exact G1 | reflexivity | vm_compute; reflexivity]
                      | vm_compute; reflexivity | reflexivity].
  - split; [apply (NRM _ 8%nat); [exact C0 | reflexivity | vm_compute; reflexivity]|].
    split; [apply (NRM _ 8%nat); [exact C8 | reflexivity | vm_compute; reflexivity]|].
    split; [apply (NRM _ 8%nat); [exact C4 | reflexivity | vm_compute; reflexivity]|].
    apply (NRM _ 1%nat); [exact C9 | reflexivity | vm_compute; reflexivity].
Qed.

(* ---- THE SITE CONTRACT over ARx ---- *)
Theorem rt_amemmove_x : forall B
  (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop),
  RTX.rt_laws frsegs B ARx -> TfibSyms B ->
  WSX.amemmove_realizes_x (PI := PB_fr) B ARx PC_asan_memmove.
Proof.
  intros B ARx LAWS TB ly S hps W regs mem md d x n HPRE G10 G11 G12 Hn Hd0 Hdn HDST HAMd HRAd HHULLd
    Hx0 Hxn HSRC HAMx HRAx HHULLx Hrom H8 HnIMG.
  pose proof HPRE as (HAR & Hret & Hal & Hlo & Hhi & Hwin & Hgp & Htp).
  pose proof (RTX.rtl_layout _ _ _ LAWS ly S hps W mem md HAR) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
  unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
  assert (HE : ESTACK = 4096) by reflexivity.
  pose proof (ro_agree_of_rom_view W mem Hrom) as RO.
  destruct (walk_cells_memmove_x B ARx TB LAWS ly S hps W mem md HAR) as (M2S & IC).
  set (H := w_H W) in *. set (mR := mrestrict H mem) in *. set (sp := spZ regs) in *.
  set (m0 := NM.normalize_cj I0.rsegs mR) in *.
  set (lo0 := sp - ESTACK).
  assert (Esp : bv_unsigned (reg_get regs 2) = sp)
    by (unfold sp, spZ; rewrite getr_nz by reflexivity; reflexivity).
  (* the stack window *)
  assert (ST : BF.stk BI.asegs m0 lo0 sp).
  { apply stk_norm_high; [unfold lo0, FR_IMG_TOP; lia | unfold TASK_SIZE; lia|].
    apply FRB.stk_of_apresent; [unfold lo0; lia | lia | exact Hwin]. }
  (* the bytes the walk reads and writes *)
  set (src := bytes_of mR x n).
  set (junk := bytes_of m0 d n).
  assert (Lsrc : Z.of_nat (length src) = n) by (unfold src; rewrite length_bytes_of, Z2Nat.id by lia; reflexivity).
  assert (Ljunk : length junk = length src) by (unfold junk, src; rewrite !length_bytes_of; reflexivity).
  assert (SRCB : BM.bytes_at BI.asegs m0 x src).
  { apply (NM.bytes_at_normalize_cj_low I0.rsegs mR x src RO);
      [rewrite Lsrc; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, TASK_SIZE in HAMx |- *; lia|].
    apply bytes_of_at; [lia | lia | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMx; lia|].
    intros i Hi. destruct (HSRC (x + i) ltac:(lia)) as (Hv & _).
    intros Hc. apply Hv. exact (f_equal (option_map (fun b : byte => bv_unsigned b)) Hc). }
  (* every destination byte: off the image, not hidden, kept by the normalization *)
  assert (DB : forall a, d <= a < d + n ->
     H (Z_to_bv 64 a) = false /\ mR (Z_to_bv 64 a) <> None /\
     NM.cj_drop I0.rsegs (Z_to_bv 64 a) = false /\ BM.mrd BI.asegs m0 (BM.wa a) = mR (Z_to_bv 64 a)).
  { intros a Ha. apply dest_byte; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMd;
      unfold TASK_SIZE; lia | exact (HnIMG a Ha) | exact (proj1 (HDST a Ha)) ]. }
  assert (DSTB : BM.bytes_at BI.asegs m0 d junk).
  { apply bytes_of_at; [lia | lia | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMd; lia|].
    intros i Hi. destruct (DB (d + i) ltac:(lia)) as (_ & Hm & _ & Hr). rewrite Hr. exact Hm. }
  assert (DSTW : BM.wr_at BI.asegs m0 d n).
  { split; [lia|]. split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMd; lia|].
    intros i Hi. destruct (DB (d + i) ltac:(lia)) as (_ & Hm & Hcj & _).
    intros Hc. apply Hm.
    assert (E0 : m0 (Z_to_bv 64 (d + i)) = mR (Z_to_bv 64 (d + i)))
      by (unfold m0, NM.normalize_cj; rewrite Hcj; reflexivity).
    rewrite <- E0. unfold wview in Hc.
    destruct (m0 (BM.wa (d + i))) eqn:E; [discriminate Hc | exact E]. }
  assert (DST : BSt.rw_cells BI.asegs m0 d [BC.CB (length src) junk]).
  { split.
    - split; [cbn [BC.cells_wf BC.cell_wf]; split; [exact Ljunk | exact I]|].
      cbn [BC.cells_bytes BC.cbytes]. rewrite app_nil_r. exact DSTB.
    - cbn [BC.cells_size BC.csize]. rewrite Nat.add_0_r, Lsrc. exact DSTW. }
  (* the two range checks *)
  assert (CS : BQ.chk_ok m0 x n).
  { destruct (Z.eq_dec n 0) as [->|NE]; [apply chk_ok0|].
    apply chk_norm; [lia | lia | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMx; lia | lia
                    | apply region_of_amem_range; [lia | lia | exact HAMx | exact (proj2 (H8 ltac:(lia)))]
                    | exact HRAx | exact (HHULLx ltac:(lia))]. }
  assert (CD : BQ.chk_ok m0 d n).
  { destruct (Z.eq_dec n 0) as [->|NE]; [apply chk_ok0|].
    apply chk_norm; [lia | lia | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMd; lia | lia
                    | apply region_of_amem_range; [lia | lia | exact HAMd | exact (proj1 (H8 ltac:(lia)))]
                    | exact HRAd | exact (HHULLd ltac:(lia))]. }
  (* the two separation facts *)
  assert (SEPS : n = 0 \/ x + n <= sp - 2224 \/ sp <= x).
  { destruct (Z.eq_dec n 0) as [->|NE]; [left; reflexivity|]. right.
    destruct (range_off_scratch sp ESTACK x n ltac:(lia) ltac:(lia)
      ltac:(intros a Ha; exact (proj2 (HSRC a Ha)))) as [L|L]; [left; lia | right; exact L]. }
  assert (SEPD : n = 0 \/ d + n <= sp - 2224 \/ sp <= d).
  { destruct (Z.eq_dec n 0) as [->|NE]; [left; reflexivity|]. right.
    destruct (range_off_scratch sp ESTACK d n ltac:(lia) ltac:(lia)
      ltac:(intros a Ha; exact (proj2 (proj2 (HDST a Ha))))) as [L|L]; [left; lia | right; exact L]. }
  (* run the walk and read its post back *)
  unfold PC_asan_memmove.
  apply (FRB.srr_of_evt fr_wx W 0x52e04 regs mem md
    (walk_at (BMM.amemmove_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
       (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21)
       (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
       fp_regs fp_csr d src lo0 m0) mR)).
  - refine (_ : BE.evt BI.asegs _ (st_at regs fp_regs (w64 0x52e04) fp_csr mR)).
    apply bz_transport; [exact RO|].
    apply (bz_amemmove regs fp_regs fp_csr m0 d x src junk lo0).
    + rewrite <- getr_nz by reflexivity. exact G10.
    + rewrite <- getr_nz by reflexivity. exact G11.
    + rewrite <- getr_nz by reflexivity. rewrite Lsrc. exact G12.
    + rewrite Esp. exact ST.
    + rewrite Esp. unfold lo0. lia.
    + unfold BR2.kHighShadowEnd, lo0. lia.
    + rewrite Esp. lia.
    + lia.
    + lia.
    + rewrite Lsrc. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMd. lia.
    + rewrite Lsrc. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMx. lia.
    + rewrite Esp, Lsrc. exact SEPS.
    + rewrite Esp, Lsrc. exact SEPD.
    + exact SRCB.
    + exact DST.
    + rewrite Lsrc. exact CS.
    + rewrite Lsrc. exact CD.
    + exact M2S.
    + exact IC.
    + apply bz_mem_inv_normalize.
  - intros ms' model' (c & s0 & HQ & Hrel & Hsame & Heqv) Hsbm _.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Es0 & MU & _ & _ & ST' & RWD).
    subst s0. rewrite Esp in MU, ST'.
    apply (aentry_post_of_walk_x B ARx LAWS ESTACK 2224 [(d, d + n)] (fun a => d <= a < d + n)
      (fun regs' mem' => getr regs' 10 = w64 d /\
         forall i, 0 <= i < n -> aview frsegs (w_H W) mem' (d + i) = aview frsegs (w_H W) mem (x + i))
      d ly S hps W regs mem md ms' model' c m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HPRE ltac:(lia) RO
      ltac:(lia)).
    + intros a Ha. inversion Ha as [iv l0 Hiv|iv l0 Hiv]; [cbn in Hiv; exact Hiv | inversion Hiv].
    + intros a Ha. exact (proj1 (proj2 (HDST a Ha))).
    + intros a Ha _. destruct (DB a Ha) as (_ & _ & Hcj & _). split; [exact Hcj|].
      destruct RWD as (_ & HW). cbn [BC.cells_size BC.csize] in HW. rewrite Nat.add_0_r in HW.
      destruct HW as (_ & _ & HW). pose proof (HW (a - d) ltac:(rewrite Lsrc; lia)) as Hv.
      replace (d + (a - d)) with a in Hv by lia.
      exact (wview_off_img m' a
        ltac:(unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMd; lia) (HnIMG a Ha) Hv).
    + exact Hrel.
    + exact Hsame.
    + exact Heqv.
    + eapply BF.munch_weaken; [|exact MU]. unfold BF.sub_fp. cbn [BF.outside]. cbn [fst snd].
      intros a (Ha1 & Ha2 & _). rewrite Lsrc. split; [exact Ha2|]. split; [exact Ha1 | exact I].
    + exact ST'.
    + exact Hsbm.
    + intros regs'' mem'' Ha0 Hagree. split; [exact Ha0|].
      intros i Hi. destruct (DB (d + i) ltac:(lia)) as (Hh & _ & Hcj & _).
      assert (Hdi : 0 <= d + i < 2 ^ 64)
        by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMd; lia).
      assert (Hxi : 0 <= x + i < 2 ^ 64)
        by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMx; lia).
      assert (Em : mem'' (BM.wa (d + i)) = m' (BM.wa (d + i))) by exact (Hagree _ Hh Hcj).
      (* the walk left the source bytes at the destination *)
      destruct RWD as (HC & _). destruct HC as (_ & HB). cbn [BC.cells_bytes BC.cbytes] in HB.
      rewrite app_nil_r in HB. destruct HB as (_ & _ & HB).
      pose proof (HB (Z.to_nat i) ltac:(rewrite <- Lsrc in Hi; lia)) as Hnth.
      rewrite Z2Nat.id in Hnth by lia.
      unfold src, bytes_of in Hnth. rewrite nth_error_map, nth_error_seq in Hnth.
      replace (Z.to_nat i <? Z.to_nat n)%nat with true in Hnth by (symmetry; apply Nat.ltb_lt; lia).
      cbn [option_map] in Hnth. rewrite Nat.add_0_l, Z2Nat.id in Hnth by lia.
      rewrite (mrd_off_img m' (d + i) Hdi (HnIMG (d + i) ltac:(lia))) in Hnth.
      (* read both sides as the Bz tree's byte reads *)
      rewrite !aview_mrd. fold H. fold mR.
      rewrite (mrd_off_img (mrestrict H mem'') (d + i) Hdi (HnIMG (d + i) ltac:(lia))).
      rewrite (mrestrict_false H mem'' (BM.wa (d + i)) Hh), Em, Hnth.
      unfold byte_or0.
      destruct (BM.mrd BI.asegs mR (BM.wa (x + i))) as [b2|] eqn:E2; [reflexivity|].
      exfalso. destruct (HSRC (x + i) ltac:(lia)) as (Hvis & _). apply Hvis.
      rewrite aview_mrd. fold H. fold mR. rewrite E2. reflexivity.
Qed.

(* ---- the instance at cgif's AR (Hp ignored): the statement is RT_asan_memmove.v's rt_amemmove, byte for byte ---- *)
Corollary rt_amemmove_of_x : forall B, AR_laws frsegs B -> TfibSyms B ->
  amemmove_realizes (PI := PB_fr) B PC_asan_memmove.
Proof.
  intros B LAWS TB ly S W regs mem md.
  exact (rt_amemmove_x B (FCI.AR_nohp frsegs B) (RTX.rt_laws_AR frsegs B LAWS) TB ly S [] W regs mem md).
Qed.

(* ---- the instance at ARcf, the laws from AR_laws_cf ---- *)
Section cf. Context {ci : CFN.CfImg} {cp : CFN.CfParams}.
Corollary rt_amemmove_cf : forall B, DCF.AR_laws_cf frsegs B -> TfibSyms B ->
  WSX.amemmove_realizes_x (PI := PB_fr) B (NCF.ARcf frsegs B) PC_asan_memmove.
Proof.
  intros B L TB.
  exact (rt_amemmove_x B (NCF.ARcf frsegs B) (RTX.rt_laws_cf frsegs B L) TB).
Qed.
End cf.

End core.
