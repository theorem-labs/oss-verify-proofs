(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names and addresses changed; 1348 of its 1450 lines of code are new or changed and 1100 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/A1.v, with its module paths and module names changed; 631 of its 720 lines of code are new or changed and 1361 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSstrlen.v, with its module paths, module names, addresses and numbers changed; 123 of its 239 lines of code are new or changed and 604 lines of the source are left out. *)
(* fs.asan's memchr interceptor (PC_memchr 0x4266c), its runtime contract in S0's ARU form: amemchr_realizesU.
   rule 24: no function proved. This file composes existing pieces:
   - the Bz body walk: a working branch 840c4afa7e2 lib/A/Bz/A/I_memchrw.v imemchr_spec (from
     __interceptor_memchr 0x43e30 to the return), with its section hypotheses RIP = R_isPoisoned.rip_proof and
     MCH = FSsl.mch_proof (the plain memchr 0x98924 through REAL(memchr));
   - the bridge and the transport: lib/A/FSstrlen.v (a Theorem Labs lane's FMbz_bridge.v / FMbz_str.v, a Theorem Labs lane MemNorm /
     RegisterBridge; post_of_walk, walk_cells, chk_norm, stk_norm_high);
   - the statements: S0 a working branch 71efad42f00 lib/A/FSH_Gen.v amemchr_realizesU (with
     `amem_range x (n + 8)`) / amemchr_realizes_of_U.
   The trampoline __wrap_memchr 0x4266c is one `j 0x43e30` (one step, tramp_memchr).
   The window lies below the walk's stack frame by one lemma, zbuf_off_frame (the statement's `x + n <= alloc_ceiling`
   and layout_ok's ASAN_CEIL <= ly_stk_lo).
   Named premises beyond AR_laws / TfibSyms: FSH_Base.FsShadowSyms B and FSstrlen.FsRtCells B (see FSstrlen.v).
   Theorem Labs TEXTS (a Theorem Labs lane 2026-10-29 00:19Z): memchr has TWO runtime-contract texts, kept on purpose. This file proves fs's
   U form (poisoned heads allowed, U <> []). The image-neutral M form is disco's: a working branch 67a52884e5d
   proofs/libreac/fuzz_disco/lib/Rt/MemchrDef.v:37 amemchr_realizesM lo hi pc (U = [] only; read-only bytes by consts_view lo hi; the whole window
   [x, x + n) addressable, where fs states the prefix up to the first match).
   The free bridge from fs's U form to the U = [] case: S0 a working branch 77f52bf41b8 lib/A/FSupoison.v:37
   unpoison_nil, :39 ARU_nil, lib/A/FSH_Gen.v:258 ecall_preU_k_nil, :419 rt_post_ro_of_U, giving amemchr_realizes_of_U (FSH_Gen.v:491).
   The two texts are not derived from each other; revisit only if a third unit needs the poisoned form. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.MemNorm.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Img0.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSsl.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Exec.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Frame.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.MState.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.ImageA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Tac.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Step.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.StoreFast.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.P.Str_tac.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Spec.StrFun.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_consts.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_qck.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_memchrw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSstrlen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YP09 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AF0m FSupoison FSH_Gen FSH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSbz_bridge FSbz_str.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module NM := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.MemNorm.
Module L6 := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Regs6ss.
Module I0 := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Img0.
Module SL := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSsl.
Module BE := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Exec.
Module BM := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Mem.
Module BF := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Frame.
Module BMS := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.MState.
Module BI := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.ImageA.
Module BSF := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Spec.StrFun.
Module BK := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_consts.
Module BQ := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_qck.
Module BR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.R_m2s.
Module BP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.R_isPoisoned.
Module BMC := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_memchrw.
Module FSL := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSstrlen.
Module FSB := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSbz_bridge.
Module FSS := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSbz_str.

(* ---- the trampoline and the interceptor walk, in the Bz tree's words ---- *)
Module W.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Tac.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.ImageA.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Exec.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.MState.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Step.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.StoreFast.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.P.Str_tac.

(* __wrap_memchr 0x4266c: `j 0x43e30` *)
Lemma tramp_memchr : forall (Q : machine_state -> Prop) R F fc m,
  evt asegs Q (MS R F (Z_to_bv 64 0x43e30) fc None m (YK11.seg_rom asegs)) ->
  evt asegs Q (MS R F (Z_to_bv 64 0x4266c) fc None m (YK11.seg_rom asegs)).
Proof. intros Q R F fc m H. lstep. exact H. Qed.
End W.

Lemma bz_memchr : forall regs F fc m0 (s cz n : Z) (buf : list byte) (lo : Z),
  reg_get regs 10 = Z_to_bv 64 s -> reg_get regs 11 = Z_to_bv 64 cz -> reg_get regs 12 = Z_to_bv 64 n ->
  BF.stk BI.asegs m0 lo (bv_unsigned (reg_get regs 2)) -> lo <= bv_unsigned (reg_get regs 2) - 2208 ->
  BR.kHighShadowEnd < lo -> bv_unsigned (reg_get regs 2) < 2 ^ 63 ->
  0 <= s <= 2 ^ 47 -> 0 <= cz < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> s + BMC.memchr_len s (cz mod 256) n buf <= 2 ^ 47 ->
  BM.bytes_at BI.asegs m0 s buf -> BSF.memchr_ok s (cz mod 256) n buf ->
  (s + Z.of_nat (length buf) <= bv_unsigned (reg_get regs 2) - 2208 \/ bv_unsigned (reg_get regs 2) <= s) ->
  BQ.chk_ok m0 s (BMC.memchr_len s (cz mod 256) n buf) -> BR.m2s_cells m0 -> BMC.icells_mc m0 ->
  BM.mem_inv BI.asegs m0 ->
  BE.evt BI.asegs
    (BMC.imemchr_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
       (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
       (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) F fc
       (BSF.memchr_res s (cz mod 256) n buf) lo m0)
    (BMS.MS (L6.mkR_of regs) F (Z_to_bv 64 0x4266c) fc None m0 (YK11.seg_rom BI.asegs)).
Proof.
  intros regs F fc m0 s cz n buf lo H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18.
  apply W.tramp_memchr.
  change (L6.mkR_of regs) with (BF.mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
    (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10)
    (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16)
    (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
    (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28)
    (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)).
  exact (BMC.imemchr_spec BP.rip_proof SL.mch_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F fc m0 s cz n buf lo H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18).
Qed.

(* ---- the byte window and the musl model ---- *)
Lemma find_byte_zfind : forall c l, Forall (fun b => 0 <= b < 256) l ->
  BSF.find_byte c (map (Z_to_bv 8) l) = zfind c l.
Proof.
  intros c l F. induction F as [|a l Ra F IH]; [reflexivity|]. cbn [map BSF.find_byte zfind].
  assert (Ea : bv_unsigned (Z_to_bv 8 a) = a).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia. }
  rewrite Ea, IH. destruct (a =? c); [reflexivity|]. destruct (zfind c l); reflexivity.
Qed.

Lemma zfind_lt : forall c l k, zfind c l = Some k -> (k < length l)%nat.
Proof.
  intros c l. induction l as [|a l IH]; intros k H; cbn in H; [discriminate H|].
  destruct (a =? c); [injection H as <-; cbn; lia|].
  destruct (zfind c l) as [k'|] eqn:E; cbn in H; [injection H as <-; cbn; specialize (IH k' eq_refl); lia | discriminate H].
Qed.

Lemma zbytes_bytes : forall (W : world tfibsegs) mem x l,
  zbytes_at tfibsegs W mem x l -> 0 <= x -> x + Z.of_nat (length l) <= 2 ^ 64 ->
  BM.bytes_at BI.asegs (mrestrict (w_H W) mem) x (map (Z_to_bv 8) l).
Proof.
  intros W mem x l HG Hx Htop. split; [exact Hx|]. split; [rewrite length_map; exact Htop|].
  intros i Hi. rewrite length_map in Hi.
  pose proof (HG i Hi) as (V & R).
  specialize (V 0%nat ltac:(lia)). rewrite Nat2Z.inj_0, Z.add_0_r in V.
  rewrite FSS.mbyte_mrd, FSL.le_byte_1 in V by exact R. rewrite V.
  rewrite nth_error_map. rewrite (nth_error_nth' l 0) by exact Hi. reflexivity.
Qed.

Lemma zbytes_range : forall (W : world tfibsegs) mem x l, zbytes_at tfibsegs W mem x l -> Forall (fun c => 0 <= c < 256) l.
Proof.
  intros W mem x l HG. apply Forall_forall. intros c Hc.
  apply (In_nth l c 0) in Hc as (j & Hj & Ej).
  destruct (HG j Hj) as (_ & R). rewrite Ej in R. exact R.
Qed.

Lemma chk_ok_0 : forall m p, BQ.chk_ok m p 0.
Proof.
  intros m p. split; [intros i Hi; lia|]. split; [intros H; lia|]. intros H; lia.
Qed.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* FRAME for a byte window: below the walk's stack window (the window's alloc_ceiling bound and layout_ok's
   ASAN_CEIL <= ly_stk_lo) *)
Lemma zbuf_off_frame : forall B ly St U (W : world tfibsegs) regs mem md x n,
  ecall_preU_k tfibsegs B STK_RT_STR ly St U W regs mem md -> x + n <= alloc_ceiling ->
  x + n <= spZ regs - STK_RT_STR.
Proof.
  intros B ly St U W regs mem md x n (((HAR & _) & _) & Hlo & _) Hceil.
  pose proof (am_layout B ly St _ (proj1 HAR)) as HLY. pose proof (lo_stk_ceil ly HLY) as Hst.
  unfold ASAN_CEIL in Hst. lia.
Qed.

(* the core: the memchr interceptor at PC_memchr, from the statement's facts with the +8 range named *)
Lemma fs_memchr_core : forall B, AR_laws tfibsegs B -> FsShadowSyms B -> FSL.FsRtCells B ->
  forall ly St U (W : world tfibsegs) regs mem md x c n (l : list Z),
  ecall_preU_k tfibsegs B STK_RT_STR ly St U W regs mem md -> rom_view tfibsegs W mem ->
  YK11.getr regs 10 = w64 x -> YK11.getr regs 11 = w64 c -> 0 <= c < 256 -> YK11.getr regs 12 = w64 n ->
  0 <= n < 2 ^ 32 ->
  zbytes_at tfibsegs W mem x l -> Z.of_nat (length l) = n -> 4096 <= x -> x + n <= alloc_ceiling ->
  amem_range x (n + 8) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x (mchr_len c l) ->
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x (mchr_len c l)) ->
  SRr tfibsegs W (cfg_at tfibsegs PC_memchr regs mem md)
    (rt_post_roU tfibsegs B STK_RT_STR ly St U W regs mem md
      (fun v => match zfind c l with None => v = 0 | Some k => v = x + Z.of_nat k end)).
Proof.
  intros B LAWS TL CELLS ly St U W regs mem md x c n l Hpre Hrom Hx Hc Hc8 Hn Hn32 Hb Hl Hx0 Hceil Hamr Hra Hhull.
  pose proof Hpre as (((HAR & Hret & Hal & Hlo1 & Hhi & _ & _ & _) & Hupok & Hupd) & Hlo & Hwin).
  pose proof (am_layout B ly St _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
  assert (HK : STK_RT_STR = 8192) by reflexivity.
  unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
  pose proof (zbuf_off_frame B ly St U W regs mem md x n Hpre Hceil) as Hfr.
  pose proof alloc_ceiling_lt as Hclt.
  pose proof (FSL.ro_agree_of_rom_view W mem Hrom) as RO.
  pose proof (FSL.walk_cells B LAWS TL CELLS ly St U W mem md HAR Hupok) as (M2S & _ & _ & _ & _ & ICM).
  assert (Esp : bv_unsigned (reg_get regs 2) = spZ regs)
    by (unfold spZ; rewrite FSL.getr_nz by reflexivity; reflexivity).
  assert (Ha0 : reg_get regs 10 = Z_to_bv 64 x) by (rewrite <- FSL.getr_nz by reflexivity; exact Hx).
  assert (Ha1 : reg_get regs 11 = Z_to_bv 64 c) by (rewrite <- FSL.getr_nz by reflexivity; exact Hc).
  assert (Ha2 : reg_get regs 12 = Z_to_bv 64 n) by (rewrite <- FSL.getr_nz by reflexivity; exact Hn).
  assert (Hamr' : (0 <= x /\ x + n + 8 <= 0x7fff7fff) \/ (0x10007fff8000 <= x /\ x + n + 8 <= 0x7fffffffffff))
    by (unfold amem_range, YG0f.kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
  pose proof (zbytes_range W mem x l Hb) as Rg.
  set (buf := map (Z_to_bv 8) l).
  assert (Lbuf : Z.of_nat (length buf) = n) by (unfold buf; rewrite length_map; exact Hl).
  assert (Ec : c mod 256 = c) by (apply Z.mod_small; lia).
  assert (Efirst : firstn (Z.to_nat n) buf = buf) by (apply firstn_all2; lia).
  assert (Efind : BSF.find_byte c buf = zfind c l) by (exact (find_byte_zfind c l Rg)).
  (* the musl model at this window: its result and its range are the statement's *)
  assert (Eres : BSF.memchr_res x c n buf = match zfind c l with Some k => x + Z.of_nat k | None => 0 end).
  { unfold BSF.memchr_res. rewrite Efirst, Efind. reflexivity. }
  assert (Elen : BMC.memchr_len x c n buf = mchr_len c l).
  { unfold BMC.memchr_len, mchr_len. rewrite Eres. destruct (zfind c l) as [k|] eqn:Ez.
    - replace (x + Z.of_nat k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). lia.
    - cbn. lia. }
  assert (Hmlen : 0 <= mchr_len c l <= n).
  { unfold mchr_len. destruct (zfind c l) as [k|] eqn:Ez; [pose proof (zfind_lt c l k Ez); lia | lia]. }
  assert (Hok : BSF.memchr_ok x c n buf).
  { unfold BSF.memchr_ok. rewrite Efirst. destruct (BSF.find_byte c buf); [left|]; lia. }
  set (r := BSF.memchr_res x c n buf).
  assert (Hr : 0 <= r < 2 ^ 64).
  { unfold r. rewrite Eres. destruct (zfind c l) as [k|] eqn:Ez; [pose proof (zfind_lt c l k Ez); lia | lia]. }
  set (H := w_H W) in *. set (mR := mrestrict H mem) in *. set (sp := spZ regs) in *.
  set (lo := sp - STK_RT_STR).
  unfold PC_memchr.
  apply (FSB.srr_of_evt FSL.Hwx_fs W 0x4266c regs mem md
    (FSL.walk_at (BMC.imemchr_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
       (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
       (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) fp_regs fp_csr
       (BSF.memchr_res x (c mod 256) n buf) lo (NM.normalize_cj I0.rsegs mR)) mR)).
  - refine (_ : BE.evt BI.asegs _ (FSL.st_at regs fp_regs (Z_to_bv 64 0x4266c) fp_csr mR)).
    apply FSL.bz_transport; [exact RO|].
    apply (bz_memchr regs fp_regs fp_csr _ x c n buf lo).
    + exact Ha0.
    + exact Ha1.
    + exact Ha2.
    + rewrite Esp. apply FSL.stk_norm_high; [unfold lo, FSL.FS_IMG_TOP; lia | unfold TASK_SIZE; lia |].
      apply FSB.stk_of_apresent; [unfold lo; lia | lia | exact Hwin].
    + rewrite Esp. unfold lo. lia.
    + unfold BR.kHighShadowEnd, lo. lia.
    + rewrite Esp. lia.
    + lia.
    + lia.
    + lia.
    + rewrite Ec, Elen. lia.
    + apply (NM.bytes_at_normalize_cj_low I0.rsegs mR x buf RO); [unfold TASK_SIZE; lia|].
      exact (zbytes_bytes W mem x l Hb ltac:(lia) ltac:(lia)).
    + rewrite Ec. exact Hok.
    + rewrite Esp, Lbuf. lia.
    + rewrite Ec, Elen. destruct (Z.eq_dec (mchr_len c l) 0) as [E0|E0]; [rewrite E0; apply chk_ok_0|].
      apply FSL.chk_norm; [lia | lia | lia | lia | | exact Hra | apply Hhull; lia].
      unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd. lia.
    + exact M2S.
    + exact ICM.
    + apply FSL.bz_mem_inv_normalize.
  - intros ms' model' (cc & s0 & HQ & Hrel & Hsame & Heqv) Hsbm _.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Es0 & MU & _ & _ & ST').
    subst s0. rewrite Esp in MU, ST'. rewrite Ec in *.
    apply (FSL.post_of_walk B LAWS ly St U W regs mem md _ r r 2208 ms' model' cc m'
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hpre RO); try assumption.
    + rewrite HK. lia.
    + reflexivity.
    + unfold r. rewrite Eres. destruct (zfind c l); reflexivity.
Qed.

(* ---- the contract ---- *)
Theorem fs_memchr_realizesU : forall B, AR_laws tfibsegs B -> TfibSyms B -> FsShadowSyms B -> FSL.FsRtCells B ->
  amemchr_realizesU tfibsegs B PC_memchr.
Proof.
  intros B LAWS _ TL CELLS ly St U W regs mem md x c n l Hpre Hrom Hx Hc Hc8 Hn Hn32 Hb Hl Hx0 Hceil Hamr Hra Hhull.
  exact (fs_memchr_core B LAWS TL CELLS ly St U W regs mem md x c n l Hpre Hrom Hx Hc Hc8 Hn Hn32 Hb Hl Hx0 Hceil
    Hamr Hra Hhull).
Qed.

Corollary fs_memchr_realizes : forall B, AR_laws tfibsegs B -> TfibSyms B -> FsShadowSyms B -> FSL.FsRtCells B ->
  amemchr_realizes tfibsegs B PC_memchr.
Proof.
  intros B LAWS TB TL CELLS. apply amemchr_realizes_of_U. exact (fs_memchr_realizesU B LAWS TB TL CELLS).
Qed.

End core.
