(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names and addresses changed; 1348 of its 1450 lines of code are new or changed and 1100 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/A1.v, with its module paths and module names changed; 631 of its 720 lines of code are new or changed and 1361 lines of the source are left out. *)
(* fs.asan's strlen interceptor (PC_strlen 0x42654), its runtime contract in S0's ARU form: astrlen_realizesU.
   rule 24: no function proved. This file composes existing pieces:
   - the Bz body walk: a working branch 840c4afa7e2 lib/A/Bz/A/I_strlen.v istrlen_spec (from
     __interceptor_strlen 0x426e4 to the return), with its section hypotheses RIP = R_isPoisoned.rip_proof and
     SL = FSsl.sl_proof (the plain strlen 0x99070 through REAL(strlen));
   - the bridge: a working branch cedf3d02589 FMbz_bridge.v / FMbz_str.v (here FSbz_bridge.srr_of_evt,
     stk_of_apresent; FSbz_str.chk_ok_of_view, aview_eq, hull_of_shadow_hull_vis, mbyte_mrd);
   - a Theorem Labs lane's own transport of a Bz walk to the machine (840c4afa7e2 lib/MemNorm.v evt_normalize_cj: the walk runs on
     the memory with the read-only and above-TASK_SIZE bytes dropped; lib/Lib/RegisterBridge.v evt_register_transport:
     the walk's register tree mkR_of regs); the image lemmas of a Theorem Labs lane's lib/A/BzBridge.v:22-79 (wx_apart, seg tops,
     bz_mem_inv_normalize, wview_of_mrd) restated here without its AsanRT import;
   - the statements: S0 a working branch cbc42a13380 lib/A/FSH_Gen.v astrlen_realizesU / astrlen_realizes_of_U.
   The trampoline __wrap_strlen 0x42654 is one `j 0x426e4` (one step, tramp_strlen).
   Named premises beyond AR_laws / TfibSyms: FsShadowSyms B (the shadow-offset cell's two symbols in AB1w's names, the
   walk kit's premise text and the relocated core's ACeg.TfibLib fields; ACeg.v cannot be Required yet) and FsRtCells B (the other fs.asan runtime cells
   the interceptor walks read; lib/A/AF0m.v's Tfib_const is cgif's; RELOC's relocated cells discharge it).
   The core's names (YK11.getr / mkst / seg_rom) are written qualified; lib/Lib and the Bz tree are Required, not
   Imported, outside Module W.
   Theorem Labs TEXTS (a Theorem Labs lane 2026-10-29 00:19Z): strlen has TWO runtime-contract texts, kept on purpose. This file proves fs's
   U form (poisoned heads allowed, U <> []). The image-neutral M form is disco's: a working branch 67a52884e5d
   proofs/libreac/fuzz_disco/lib/Rt/StrlenDef.v:40 astrlen_realizesM lo hi pc (U = [] only; read-only bytes by consts_view lo hi plus presence of the
   tail word strlen reads past the NUL).
   The free bridge from fs's U form to the U = [] case: S0 a working branch 77f52bf41b8 lib/A/FSupoison.v:37
   unpoison_nil, :39 ARU_nil, lib/A/FSH_Gen.v:258 ecall_preU_k_nil, :419 rt_post_ro_of_U, giving astrlen_realizes_of_U (FSH_Gen.v:425).
   The two texts are not derived from each other; revisit only if a third unit needs the poisoned form. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.MemNorm.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Exec.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.RegisterBridge.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Img0.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSsl.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Exec.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Frame.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.MState.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.ImageA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Cells.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Step.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Tac.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.StoreFast.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.P.Str_tac.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.D_kit.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_consts.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_qck.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_strnlenw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_strcmpw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_strlen.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_memchrw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YCbq.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YK14.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.AB1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YP09 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AF0m FSupoison FSH_Gen FSH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSbz_str FSbz_bridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module NM := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.MemNorm.
Module LE := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Exec.
Module LM := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.
Module L6 := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Regs6ss.
Module LR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.RegisterBridge.
Module I0 := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Img0.
Module SL := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSsl.
Module BE := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Exec.
Module BM := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Mem.
Module BF := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Frame.
Module BMS := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.MState.
Module BI := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.ImageA.
Module BC := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Cells.
Module BSt := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Step.
Module BD := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.D_kit.
Module BK := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_consts.
Module BQ := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_qck.
Module BR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.R_m2s.
Module BP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.R_isPoisoned.
Module BN := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_strnlenw.
Module BS := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_strcmpw.
Module BL := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_strlen.
Module BMC := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_memchrw.
Module YCbq := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YCbq.
Module AB1w := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.AB1w.
Module FSS := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSbz_str.
Module FSB := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSbz_bridge.

(* ---- the image (fs.asan; Img0.rsegs, ImageA.asegs and AB1v.tfibsegs name the same segments) ---- *)
Lemma Hwx_fs : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Lemma wx_apart_fs : NM.wx_apart I0.rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Definition seg_tops_below (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

(* every loaded segment of fs.asan ends below 0x600000 *)
Definition FS_IMG_TOP : Z := 0x600000.
Lemma rsegs_below : seg_tops_below I0.rsegs FS_IMG_TOP = true.
Proof. vm_compute. reflexivity. Qed.

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

Lemma find_segment_spec : forall segs x n s, find_segment segs x n = Some s ->
  In s segs /\ Z.of_N (seg_base s) <= x /\ x + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  induction segs as [|s0 r IH]; intros x n s H; cbn in H; [discriminate H|].
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1, E2.
    split; [left; reflexivity | lia].
  - destruct (IH x n s H) as (Hi & H1 & H2). split; [right; exact Hi | lia].
Qed.

Lemma find_segment_high : forall x, FS_IMG_TOP <= x -> find_segment I0.rsegs x 1 = None.
Proof.
  intros x Hx. destruct (find_segment I0.rsegs x 1) as [s|] eqn:E; [|reflexivity].
  destruct (find_segment_below I0.rsegs FS_IMG_TOP x 1 s rsegs_below E ltac:(lia)) as [L|L]; lia.
Qed.

(* an address above the image and below TASK_SIZE keeps its byte in the normalized memory *)
Lemma cj_keep_high : forall x, FS_IMG_TOP <= x < TASK_SIZE -> NM.cj_drop I0.rsegs (Z_to_bv 64 x) = false.
Proof.
  intros x Hx. unfold TASK_SIZE, FS_IMG_TOP in Hx.
  assert (Ex : bv_unsigned (Z_to_bv 64 x) = x) by (apply BMS.unsigned_lit; lia).
  apply NM.cj_drop_false_intro.
  - unfold LM.ro_addr. rewrite Ex, (find_segment_high x ltac:(unfold FS_IMG_TOP; lia)). reflexivity.
  - right. rewrite Ex. unfold TASK_SIZE. lia.
Qed.

Lemma seg_addr_below : forall a, BM.seg_addr I0.rsegs a = true -> bv_unsigned a < BM.UTOP.
Proof.
  intros a H. unfold BM.seg_addr in H.
  destruct (find_segment I0.rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  destruct (find_segment_below I0.rsegs FS_IMG_TOP (bv_unsigned a) 1 s rsegs_below E ltac:(lia)) as [L|L];
    [unfold BM.UTOP, FS_IMG_TOP in *; lia | discriminate L].
Qed.

(* the Bz walks' memory invariant holds of every normalized memory (a Theorem Labs lane's BzBridge.v bz_mem_inv_normalize) *)
Lemma bz_mem_inv_normalize : forall m, BM.mem_inv BI.asegs (NM.normalize_cj I0.rsegs m).
Proof.
  intros m. apply BM.mem_inv_intro.
  - exact seg_addr_below.
  - intros a b H. destruct (NM.mem_inv_cj_normalize I0.rsegs m a b H) as [R [S|T]]; split.
    + exact R.
    + destruct (find_segment I0.rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|congruence].
      apply seg_addr_below. unfold BM.seg_addr. rewrite E. reflexivity.
    + exact R.
    + unfold BM.UTOP, TASK_SIZE in *. lia.
Qed.

(* ---- a Bz walk from the canonical register tree on the normalized memory, read on the machine ---- *)
Lemma bz_msteps_l : forall s s', BE.msteps BI.asegs s s' -> LE.msteps I0.rsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH].
  - apply LE.msteps_refl.
  - eapply LE.msteps_cons; [exact Hs | exact IH].
Qed.

Lemma bz_evt_l : forall (Q : machine_state -> Prop) ms, BE.evt BI.asegs Q ms -> LE.evt I0.rsegs Q ms.
Proof. intros Q ms (ms' & H & HQ). exists ms'. split; [exact (bz_msteps_l ms ms' H) | exact HQ]. Qed.

Definition st_at (regs F : bvmap 5 word) (pc : word) (fc : bv 32) (m : word -> option byte) : machine_state :=
  {| ms_regs := regs; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := None; ms_resv := None; ms_fcsr := fc;
     ms_mem := m; ms_rom := YK11.seg_rom tfibsegs |}.

Definition walk_at (Q : machine_state -> Prop) (m : word -> option byte) (a : machine_state) : Prop :=
  exists c s0, Q s0 /\ NM.ms_rel_cj I0.rsegs c s0 /\ NM.cj_same I0.rsegs m (ms_mem c) /\ L6.ms_eqv c a.

Lemma bz_transport : forall (Q : machine_state -> Prop) regs F pc fc m,
  NM.ro_agree I0.rsegs m ->
  BE.evt BI.asegs Q (BMS.MS (L6.mkR_of regs) F pc fc None (NM.normalize_cj I0.rsegs m) (YK11.seg_rom BI.asegs)) ->
  BE.evt BI.asegs (walk_at Q m) (st_at regs F pc fc m).
Proof.
  intros Q regs F pc fc m RO H.
  apply SL.evt_to_bz.
  pose proof (NM.evt_normalize_cj I0.rsegs Q (L6.mkR_of regs) F pc fc None m (YK11.seg_rom I0.rsegs) wx_apart_fs RO
    (bz_evt_l Q _ H)) as H2.
  assert (EQV : L6.ms_eqv (BMS.MS (L6.mkR_of regs) F pc fc None m (YK11.seg_rom I0.rsegs)) (st_at regs F pc fc m)).
  { unfold L6.ms_eqv, st_at, BMS.MS. cbn. split; [apply L6.xregs_eqv_sym, L6.mkR_of_eqv|].
    repeat split; reflexivity. }
  pose proof (LR.evt_register_transport I0.rsegs _ _ _ EQV H2) as H3.
  eapply LE.evt_mono; [exact H3|]. intros a (c & (s0 & HQ & Hrel & Hsame) & Heqv). exists c, s0. auto.
Qed.

(* ---- the trampoline and the interceptor walk, in the Bz tree's words ---- *)
Module W.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Tac.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.ImageA.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Exec.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.MState.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Step.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.StoreFast.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.P.Str_tac.

(* __wrap_strlen 0x42654: `j 0x426e4` *)
Lemma tramp_strlen : forall (Q : machine_state -> Prop) R F fc m,
  evt asegs Q (MS R F (Z_to_bv 64 0x426e4) fc None m (YK11.seg_rom asegs)) ->
  evt asegs Q (MS R F (Z_to_bv 64 0x42654) fc None m (YK11.seg_rom asegs)).
Proof. intros Q R F fc m H. lstep. exact H. Qed.
End W.

(* the interceptor walk from the trampoline, at the canonical register tree (I_strlen.v istrlen_spec, RIP / SL met) *)
Lemma bz_strlen : forall regs F fc m0 (s : Z) (str slack : list byte) (lo : Z),
  reg_get regs 10 = Z_to_bv 64 s ->
  BF.stk BI.asegs m0 lo (bv_unsigned (reg_get regs 2)) -> lo <= bv_unsigned (reg_get regs 2) - 2224 ->
  BR.kHighShadowEnd < lo -> bv_unsigned (reg_get regs 2) < 2 ^ 63 ->
  0 <= s <= 2 ^ 47 -> Z.of_nat (length str) < 2 ^ 40 -> s + Z.of_nat (length str) + 1 <= 2 ^ 47 ->
  BM.bytes_at BI.asegs m0 s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned (reg_get regs 2) - 2224 + 7 \/
   bv_unsigned (reg_get regs 2) <= s) ->
  BQ.chk_ok m0 s (Z.of_nat (length str) + 1) -> BR.m2s_cells m0 -> BN.icells_sn m0 -> BL.icells_sl m0 ->
  BM.mem_inv BI.asegs m0 ->
  BE.evt BI.asegs
    (BL.istrlen_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
       (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
       (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) F fc
       (Z.of_nat (length str)) lo m0)
    (BMS.MS (L6.mkR_of regs) F (Z_to_bv 64 0x42654) fc None m0 (YK11.seg_rom BI.asegs)).
Proof.
  intros regs F fc m0 s str slack lo Ha0 ST LO LOLO SPH S0 L40 SH BUF NZ PAD SEPS CS M2S IC ICL MI.
  apply W.tramp_strlen.
  change (L6.mkR_of regs) with (BF.mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
    (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10)
    (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16)
    (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
    (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28)
    (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)).
  exact (BL.istrlen_spec BP.rip_proof SL.sl_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F fc m0 s str slack lo Ha0 ST LO LOLO SPH S0 L40 SH BUF NZ PAD SEPS CS M2S IC ICL MI).
Qed.

(* ---- registers ---- *)
Lemma getr_nz : forall regs (r : bv 5), bv_eqb r 0 = false -> YK11.getr regs r = reg_get regs r.
Proof. intros regs r H. unfold YK11.getr. rewrite H. reflexivity. Qed.

(* lib/Prog/CF/WriterCall.v:19-35, unchanged but for the Bz tree's ret_pc *)
Lemma land_m2_mod : forall u, Z.land u (-2) mod 2 = 0.
Proof.
  intros u. replace (Z.land u (-2)) with (Z.shiftl (Z.shiftr u 1) 1).
  - rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. apply Z.mod_mul. lia.
  - rewrite <- (Z.ldiff_ones_r u 1) by lia. rewrite Z.ldiff_land. reflexivity.
Qed.

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

(* the callee-saved registers of a walk's final register tree are the caller's *)
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
Lemma option_map_unsigned_inj : forall (o1 o2 : option byte),
  option_map (fun b : byte => bv_unsigned b) o1 = option_map (fun b : byte => bv_unsigned b) o2 -> o1 = o2.
Proof.
  intros [b1|] [b2|] H; cbn in H; try discriminate; [|reflexivity].
  injection H as H. f_equal. apply bv_eq. exact H.
Qed.

(* rom_view: the bytes the restricted memory holds at read-only image addresses are the image's *)
Lemma ro_agree_of_rom_view : forall (W : world tfibsegs) mem,
  rom_view tfibsegs W mem -> NM.ro_agree I0.rsegs (mrestrict (w_H W) mem).
Proof.
  intros W mem HR a Ha. unfold LM.ro_addr in Ha.
  destruct (find_segment I0.rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate Ha].
  destruct (find_segment_spec _ _ _ _ E) as (Hin & H1 & H2).
  assert (Hro : in_rom tfibsegs (bv_unsigned a)).
  { exists s. split; [exact Hin|]. split; [apply negb_true_iff in Ha; exact Ha | lia]. }
  pose proof (HR _ Hro) as V. unfold aview, mbyte in V. rewrite !Z_to_bv_bv_unsigned in V.
  apply option_map_unsigned_inj. exact V.
Qed.

Lemma norm_keep_high : forall m (a : word), FS_IMG_TOP <= bv_unsigned a < TASK_SIZE ->
  NM.normalize_cj I0.rsegs m a = m a.
Proof.
  intros m a Ha. pose proof (cj_keep_high (bv_unsigned a) Ha) as K. rewrite Z_to_bv_bv_unsigned in K.
  unfold NM.normalize_cj. rewrite K. reflexivity.
Qed.

(* a stack window above the image keeps its bytes in the normalized memory *)
Lemma stk_norm_high : forall m lo hi, FS_IMG_TOP <= lo -> hi <= TASK_SIZE ->
  BF.stk BI.asegs m lo hi -> BF.stk BI.asegs (NM.normalize_cj I0.rsegs m) lo hi.
Proof.
  intros m lo hi Hlo Hhi (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb).
  assert (K : NM.normalize_cj I0.rsegs m (BM.wa a) = m (BM.wa a)).
  { apply norm_keep_high. rewrite BM.wa_unsigned by (unfold TASK_SIZE in Hhi; lia). lia. }
  split.
  - unfold wview. rewrite K. exact Hw.
  - exists b. unfold BM.mrd. rewrite K. exact Hb.
Qed.

(* the ASan range check of [x, x + n) on the normalized memory, from the donor's shadow facts (FSbz_str.chk_ok_of_view) *)
Lemma chk_norm : forall (H : word -> bool) mem x n,
  0 <= x -> 0 < n -> x + n <= 2 ^ 47 -> n <= 2 ^ 40 -> BK.region_in_mem x n ->
  range_addressable (aview tfibsegs H mem) SHADOW_OFF x n -> shadow_hull_vis (aview tfibsegs H mem) x n ->
  BQ.chk_ok (NM.normalize_cj I0.rsegs (mrestrict H mem)) x n.
Proof.
  intros H mem x n Hx Hn Hxn H40 Hreg Hra Hhull.
  apply (BQ.chk_ok_agree (mrestrict H mem)); [| lia | lia |].
  - apply FSS.chk_ok_of_view; [lia | lia | lia | lia | exact Hreg | exact Hra |].
    apply FSS.hull_of_shadow_hull_vis. exact Hhull.
  - intros a Ha. apply norm_keep_high. unfold FS_IMG_TOP, TASK_SIZE. lia.
Qed.

(* the string's bytes, its NUL and the rest of the NUL's 8-byte word *)
Definition byte_at (m : word -> option byte) (a : Z) : byte :=
  match BM.mrd BI.asegs m (BM.wa a) with Some b => b | None => Z_to_bv 8 0 end.
Definition mk_slack (m : word -> option byte) (e : Z) (k : nat) : list byte :=
  map (fun j => byte_at m (e + Z.of_nat j)) (seq 0 k).
Definition slack_len (e : Z) : nat := Z.to_nat ((- e) mod 8).

Lemma length_mk_slack : forall m e k, length (mk_slack m e k) = k.
Proof. intros. unfold mk_slack. rewrite length_map, length_seq. reflexivity. Qed.

Lemma le_byte_1 : forall v, 0 <= v < 256 -> Z_to_bv 8 (le_byte v 1 0) = Z_to_bv 8 v.
Proof.
  intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small v 256) by lia. reflexivity.
Qed.

Lemma cstr_bytes : forall (W : world tfibsegs) mem x l,
  cstr tfibsegs W mem x l -> 0 <= x -> x + Z.of_nat (length l) + 8 <= TASK_SIZE ->
  (forall a, x + Z.of_nat (length l) < a < x + Z.of_nat (length l) - (x + Z.of_nat (length l)) mod 8 + 8 ->
     aview tfibsegs (w_H W) mem a <> None) ->
  BM.bytes_at BI.asegs (mrestrict (w_H W) mem) x
    (map (Z_to_bv 8) l ++ Z_to_bv 8 0 ::
       mk_slack (mrestrict (w_H W) mem) (x + Z.of_nat (length l) + 1) (slack_len (x + Z.of_nat (length l) + 1))).
Proof.
  intros W mem x l (HG & _) Hx Htop Hsl.
  set (len := Z.of_nat (length l)) in *. set (m := mrestrict (w_H W) mem).
  set (k := slack_len (x + len + 1)).
  assert (Hk : Z.of_nat k = 7 - (x + len) mod 8).
  { unfold k, slack_len. rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). Z.div_mod_to_equations. lia. }
  assert (Ek : map (Z_to_bv 8) l ++ Z_to_bv 8 0 :: mk_slack m (x + len + 1) k
               = map (Z_to_bv 8) (l ++ [0]) ++ mk_slack m (x + len + 1) k).
  { rewrite map_app. cbn [map]. rewrite <- app_assoc. reflexivity. }
  rewrite Ek. clear Ek.
  assert (Hl1 : length (map (Z_to_bv 8) (l ++ [0])) = S (length l)).
  { rewrite length_map, length_app. cbn. lia. }
  split; [exact Hx|]. split.
  { rewrite length_app, Hl1, length_mk_slack. unfold TASK_SIZE in Htop. lia. }
  intros i Hi. rewrite length_app, Hl1, length_mk_slack in Hi.
  destruct (Nat.lt_ge_cases i (S (length l))) as [H1|H1].
  - rewrite nth_error_app1 by (rewrite Hl1; exact H1).
    pose proof (HG i ltac:(rewrite length_app; cbn; lia)) as (V & R).
    specialize (V 0%nat ltac:(lia)). rewrite Nat2Z.inj_0, Z.add_0_r in V.
    rewrite FSS.mbyte_mrd, le_byte_1 in V by exact R. fold m in V.
    rewrite V. rewrite nth_error_map.
    rewrite (nth_error_nth' (l ++ [0]) 0) by (rewrite length_app; cbn; lia). reflexivity.
  - rewrite nth_error_app2 by (rewrite Hl1; exact H1). rewrite Hl1.
    set (j := (i - S (length l))%nat).
    unfold mk_slack. rewrite nth_error_map, nth_error_seq.
    replace (j <? k)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn [option_map Nat.add].
    assert (Ea : x + len + 1 + Z.of_nat j = x + Z.of_nat i) by (unfold j, len; lia).
    rewrite Ea. unfold byte_at.
    assert (Hv : aview tfibsegs (w_H W) mem (x + Z.of_nat i) <> None) by (apply Hsl; unfold j in *; lia).
    unfold aview in Hv. rewrite FSS.mbyte_mrd in Hv. fold m in Hv.
    destruct (BM.mrd BI.asegs m (BM.wa (x + Z.of_nat i))) as [b|]; [reflexivity | exfalso; apply Hv; reflexivity].
Qed.

Lemma cstr_nonul : forall (W : world tfibsegs) mem x l,
  cstr tfibsegs W mem x l -> ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) l).
Proof.
  intros W mem x l (HG & HF) Hin. apply in_map_iff in Hin as (c & Ec & Hc).
  pose proof (proj1 (Forall_forall _ _) HF c Hc) as Hc0.
  apply (In_nth l c 0) in Hc as (j & Hj & Ej).
  destruct (HG j ltac:(rewrite length_app; cbn; lia)) as (_ & R).
  rewrite app_nth1 in R by exact Hj. rewrite Ej in R.
  apply (f_equal bv_unsigned) in Ec. rewrite !Z_to_bv_unsigned in Ec. unfold bv_wrap in Ec.
  change (bv_modulus 8) with 256 in Ec. rewrite (Z.mod_small c 256), Z.mod_0_l in Ec by lia.
  cbv beta in Hc0. exact (Hc0 Ec).
Qed.

(* ---- the fs.asan runtime cells the interceptor walks read ---- *)
Lemma keep_range : forall A n,
  forallb (fun i => negb (NM.cj_drop I0.rsegs (Z_to_bv 64 (A + Z.of_nat i)))) (seq 0 n) = true ->
  forall z, A <= z < A + Z.of_nat n -> NM.cj_drop I0.rsegs (Z_to_bv 64 z) = false.
Proof.
  intros A n Hb z Hz. rewrite forallb_forall in Hb.
  specialize (Hb (Z.to_nat (z - A)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in Hb by lia. replace (A + (z - A)) with z in Hb by lia.
  apply negb_true_iff in Hb. exact Hb.
Qed.

Lemma agree_cells : forall (H : word -> bool) U mem A n,
  forallb (fun i => negb (NM.cj_drop I0.rsegs (Z_to_bv 64 (A + Z.of_nat i)))) (seq 0 n) = true ->
  A + Z.of_nat n <= 0x7fff8000 -> (forall s, in_ush U s = true -> 0x7fff8000 <= s) ->
  BD.agree_on (fun z => A <= z < A + Z.of_nat n) (mrestrict H (unpoison U mem))
    (NM.normalize_cj I0.rsegs (mrestrict H mem)).
Proof.
  intros H U mem A n Hb HAn HU a Ha.
  pose proof (keep_range A n Hb (bv_unsigned a) Ha) as K. rewrite Z_to_bv_bv_unsigned in K.
  unfold NM.normalize_cj. rewrite K. unfold mrestrict. destruct (H a); [reflexivity|].
  unfold unpoison. destruct (in_ush U (bv_unsigned a)) eqn:E; [|reflexivity].
  apply HU in E. lia.
Qed.

(* an address above the image reads only what the memory holds *)
Lemma mrd_high : forall m (a : word), FS_IMG_TOP <= bv_unsigned a -> BM.mrd BI.asegs m a = m a.
Proof.
  intros m a Ha. unfold BM.mrd. destruct (m a); [reflexivity|].
  match goal with |- ?f _ _ = None => unfold f end. unfold memory_read.
  change (Z.of_N 1) with 1. change BI.asegs with I0.rsegs. rewrite (find_segment_high (bv_unsigned a) Ha). reflexivity.
Qed.

(* a byte the walk reads at a writable image address is writable (a Theorem Labs lane's BzBridge.v wview_of_mrd) *)
Lemma wview_of_mrd : forall m x b, BM.mrd BI.asegs m x = Some b -> LM.ro_addr I0.rsegs x = false ->
  wview BI.asegs m x <> None.
Proof.
  intros m x b H R. unfold wview. destruct (m x) as [c|] eqn:E; [discriminate|].
  unfold BM.mrd in H. rewrite E in H.
  match type of H with ?f _ _ = _ => unfold f in H end. unfold memory_read in H.
  unfold LM.ro_addr in R. change (Z.of_N 1) with 1 in H. change BI.asegs with I0.rsegs in *.
  destruct (find_segment I0.rsegs (bv_unsigned x) 1) as [s|]; [|discriminate H].
  apply negb_false_iff in R. rewrite R.
  destruct (seg_readable s); [|discriminate H].
  destruct (segment_byte_at (seg_bytes s) (Z.to_N (bv_unsigned x - Z.of_N (seg_base s)))) eqn:Eb; [discriminate|].
  exfalso. simpl in H. rewrite Eb in H. discriminate H.
Qed.

Lemma rw_of_ro : forall m A cs, BSt.ro_cells BI.asegs m A cs ->
  forallb (fun i => negb (NM.cj_drop I0.rsegs (Z_to_bv 64 (A + Z.of_nat i)))) (seq 0 (BC.cells_size cs)) = true ->
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

Lemma nth_Z_to_le_bytes : forall n z i, (i < n)%nat ->
  nth_error (Z_to_le_bytes n z) i = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat i))).
Proof.
  induction n as [|n IH]; intros z i Hi; [lia|]. destruct i as [|i]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. do 3 f_equal. lia.
Qed.

Lemma le_byte_8 : forall v i, 0 <= v < 2 ^ 64 ->
  Z_to_bv 8 (le_byte v 8 i) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat i)).
Proof.
  intros v i Hv. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, le_byte. change (bv_modulus 8) with 256.
  change (8 * Z.of_nat 8) with 64. rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* an 8-byte value the donor reads (val_mem) is a C8 cell of the Bz tree *)
Lemma ro_c8_of_val_mem : forall m A v, 0 <= A -> A + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  val_mem tfibsegs m A 8 v -> BSt.ro_cells BI.asegs m A [BC.C8 (Z_to_bv 64 v)].
Proof.
  intros m A v HA HA8 Hv HV. split; [cbn; tauto|].
  cbn [BC.cells_bytes BC.cbytes]. rewrite app_nil_r.
  split; [exact HA|]. split; [exact HA8|].
  intros i Hi. assert (Hi8 : (i < 8)%nat) by exact Hi.
  rewrite <- FSS.mbyte_mrd. rewrite (HV i Hi8). rewrite le_byte_8 by exact Hv.
  unfold BM.le8, word_to_le_bytes. rewrite nth_Z_to_le_bytes by exact Hi8. rewrite BMS.unsigned_lit by lia.
  reflexivity.
Qed.

Lemma ro_cons8 : forall m A w cs, BSt.ro_cells BI.asegs m A [BC.C8 w] -> BSt.ro_cells BI.asegs m (A + 8) cs ->
  BSt.ro_cells BI.asegs m A (BC.C8 w :: cs).
Proof.
  intros m A w cs (_ & B1) (W2 & B2). split; [cbn; tauto|].
  cbn [BC.cells_bytes BC.cbytes] in B1 |- *. rewrite app_nil_r in B1.
  apply (proj2 (BM.bytes_at_app BI.asegs m A _ _)). split; [exact B1|].
  assert (L : length (BM.le8 w) = 8%nat) by reflexivity. rewrite L. exact B2.
Qed.

(* the cells FsShadowSyms gives at every ASan state (AR_const_law: the shadow-offset cell and its GOT slot) *)
Definition fs_tl_cells (m : word -> option byte) : Prop :=
  BSt.ro_cells BI.asegs m 0x9f6f0 [BC.C8 (Z_to_bv 64 0xa7f38)] /\
  BSt.ro_cells BI.asegs m 0xa7f38 [BC.C8 (Z_to_bv 64 0x7fff8000)].

(* the rest, fs.asan's measured numbers (the named premise FsRtCells): the GOT slots 0x9f6e0 (the flags struct
   0x139a68) and 0x9f6f8.. (kMidMemBeg / kMidMemEnd / kHighMemEnd cells), REAL(strlen) 0xa1408 = 0x99070 and REAL(memchr)
   0xa1430 = 0x98924, asan_inited 0xa8c18 = 1, kHighMemEnd / kMidMem* at 0xa8c20, the flag bytes 0x139b5d = 0,
   0x139b62 = 1, 0x139b63 = 1 *)
Definition fs_rt_rest (m : word -> option byte) : Prop :=
  BSt.ro_cells BI.asegs m 0x9f6e0 [BC.C8 (Z_to_bv 64 0x139a68)] /\
  BSt.ro_cells BI.asegs m 0x9f6f8 [BC.C8 (Z_to_bv 64 0xa8c28); BC.C8 (Z_to_bv 64 0xa8c30); BC.C8 (Z_to_bv 64 0xa8c20)] /\
  BSt.ro_cells BI.asegs m 0xa1408 [BC.C8 (Z_to_bv 64 0x99070)] /\
  BSt.ro_cells BI.asegs m 0xa1430 [BC.C8 (Z_to_bv 64 0x98924)] /\
  BSt.ro_cells BI.asegs m 0xa8c18 [BC.C1 (Z_to_bv 8 1)] /\
  BSt.ro_cells BI.asegs m 0xa8c20 [BC.C8 (Z_to_bv 64 BR.kHighMemEnd); BC.C8 (Z_to_bv 64 0); BC.C8 (Z_to_bv 64 0)] /\
  BSt.ro_cells BI.asegs m 0x139b5d [BC.C1 (Z_to_bv 8 0)] /\
  BSt.ro_cells BI.asegs m 0x139b62 [BC.C1 (Z_to_bv 8 1)] /\
  BSt.ro_cells BI.asegs m 0x139b63 [BC.C1 (Z_to_bv 8 1)].

(* what the three interceptor walks ask *)
Definition fs_walk_cells (m : word -> option byte) : Prop :=
  BR.m2s_cells m /\ BN.icells_sn m /\ BL.icells_sl m /\ BS.icells_sc m /\
  BSt.ro_cells BI.asegs m 0x139b62 [BC.C1 (Z_to_bv 8 1)] /\ BMC.icells_mc m.

Ltac cell_ro C HU :=
  eapply BD.ro_cells_agree; [exact C|];
  apply agree_cells; [vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | exact HU].

Lemma fs_tl_norm : forall (H : word -> bool) U mem, (forall s, in_ush U s = true -> 0x7fff8000 <= s) ->
  fs_tl_cells (mrestrict H (unpoison U mem)) -> fs_tl_cells (NM.normalize_cj I0.rsegs (mrestrict H mem)).
Proof. intros H U mem HU (C1 & C2). split; [cell_ro C1 HU | cell_ro C2 HU]. Qed.

Lemma fs_rest_norm : forall (H : word -> bool) U mem, (forall s, in_ush U s = true -> 0x7fff8000 <= s) ->
  fs_rt_rest (mrestrict H (unpoison U mem)) -> fs_rt_rest (NM.normalize_cj I0.rsegs (mrestrict H mem)).
Proof.
  intros H U mem HU (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
  split; [cell_ro C1 HU|]. split; [cell_ro C2 HU|]. split; [cell_ro C3 HU|]. split; [cell_ro C4 HU|].
  split; [cell_ro C5 HU|]. split; [cell_ro C6 HU|]. split; [cell_ro C7 HU|]. split; [cell_ro C8 HU|].
  cell_ro C9 HU.
Qed.

Ltac cell_rw C := apply rw_of_ro; [exact C | vm_compute; reflexivity | reflexivity].

Lemma fs_walk_cells_of : forall m, fs_tl_cells m -> fs_rt_rest m -> fs_walk_cells m.
Proof.
  intros m (T1 & T2) (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
  assert (G : BSt.ro_cells BI.asegs m 0x9f6f0
    [BC.C8 (Z_to_bv 64 0xa7f38); BC.C8 (Z_to_bv 64 0xa8c28); BC.C8 (Z_to_bv 64 0xa8c30); BC.C8 (Z_to_bv 64 0xa8c20)])
    by (apply ro_cons8; [exact T1 | exact R2]).
  split; [split; [cell_rw G | split; [cell_rw T2 | cell_rw R6]]|].
  split; [split; [exact R1 | split; [exact T1 | split; [exact T2 | split; [cell_rw R5 | exact R9]]]]|].
  split; [exact R3|].
  split; [split; [exact R1 | split; [exact T1 | split; [exact T2 | split; [cell_rw R5 | exact R7]]]]|].
  split; [exact R8|].
  split; [exact T1 | split; [exact R4 | split; [exact T2 | cell_rw R5]]].
Qed.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* NAMED PREMISE: at every ASan state the restricted memory holds the fs.asan runtime cells fs_rt_rest (the cells the
   interceptor walks read beyond FsShadowSyms'). A fact about B's constant cells (as_const), which this
   tree's TfibSyms (lib/A/AF0m.v, cgif's numerals) does not carry yet; RELOC's relocated cells discharge it. *)
Definition FsRtCells (B : asyms) : Prop :=
  forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md -> fs_rt_rest (mrestrict (w_H W) mem).

(* FsShadowSyms B (the shadow-offset cell's two symbols) is S0's, lib/A/FSH_Base.v:116-118. *)

Lemma tfib_D_shadow_vals : AB1w.tfib_D_GOT_asan_shadow_memory_dynamic_address = 0x9f6f0 /\
  AB1w.tfib_D_asan_shadow_memory_dynamic_address = 0xa7f38.
Proof. split; reflexivity. Qed.

(* the shadow-offset cell and its GOT slot, by AR_const_law *)
Lemma tl_cells : forall B, FsShadowSyms B -> AR_laws tfibsegs B -> forall ly S (W : world tfibsegs) mem md,
  AR tfibsegs B ly S W mem md -> fs_tl_cells (mrestrict (w_H W) mem).
Proof.
  intros B (Egot & Ecell) LAWS ly S W mem md HAR. destruct tfib_D_shadow_vals as (V1 & V2). rewrite V1 in Egot. rewrite V2 in Ecell.
  destruct (al_const _ _ LAWS ly S W mem md HAR) as (C1 & _ & C3 & _).
  rewrite Ecell in C1, C3. rewrite Egot in C3.
  split; apply ro_c8_of_val_mem; try lia.
  - exact (YCbq.val_mem_of_rdword tfibsegs _ _ _ _ C3).
  - exact (YCbq.val_mem_of_rdword tfibsegs _ _ _ _ C1).
Qed.

(* the shadow bytes a user-poisoned range covers lie between the shadow offset and the high memory *)
Lemma ush_bounds : forall B, AR_laws tfibsegs B -> forall ly S (W : world tfibsegs) mem md U,
  AR tfibsegs B ly S W mem md -> upoison_ok B ly S U ->
  forall s, in_ush U s = true -> 0x7fff8000 <= s < kHighMemBeg.
Proof.
  intros B LAWS ly S W mem md U HAR OK s Hs.
  apply in_ush_spec in Hs as (r & Hr & Hs).
  destruct OK as [F _]. rewrite Forall_forall in F.
  destruct (F r Hr) as (A8 & L8 & M8 & p & n & Hb & P1 & P2).
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hb) as (_ & Hp & Hpn & _).
  pose proof alloc_ceiling_lt as Hc. pose proof YK06.alloc_ceiling_val as Hc6.
  assert (Hrq : 8 * (req_size n / 8) <= req_size n) by (apply Z.mul_div_le; lia).
  unfold shadow_addr, SHADOW_OFF, kHighMemBeg in *. Z.div_mod_to_equations. lia.
Qed.

(* all the cells, on the walk's (normalized) memory *)
Lemma walk_cells : forall B, AR_laws tfibsegs B -> FsShadowSyms B -> FsRtCells B ->
  forall ly S U (W : world tfibsegs) mem md,
  AR tfibsegs B ly S W (unpoison U mem) md -> upoison_ok B ly S U ->
  fs_walk_cells (NM.normalize_cj I0.rsegs (mrestrict (w_H W) mem)).
Proof.
  intros B LAWS TL CELLS ly S U W mem md HAR OK.
  pose proof (ush_bounds B LAWS ly S W (unpoison U mem) md U HAR OK) as USH.
  assert (HU : forall s, in_ush U s = true -> 0x7fff8000 <= s) by (intros s Hs; exact (proj1 (USH s Hs))).
  apply fs_walk_cells_of.
  - exact (fs_tl_norm (w_H W) U mem HU (tl_cells B TL LAWS ly S W (unpoison U mem) md HAR)).
  - exact (fs_rest_norm (w_H W) U mem HU (CELLS ly S W (unpoison U mem) md HAR)).
Qed.

(* FRAME: the string lies below the walk's stack window (cstr_ok's alloc_ceiling bound and layout_ok's
   ASAN_CEIL <= ly_stk_lo). The one place the frame separation is derived; a later premise swap changes only this lemma. *)
Lemma cstr_off_frame : forall B ly S U (W : world tfibsegs) regs mem md x l,
  ecall_preU_k tfibsegs B STK_RT_STR ly S U W regs mem md -> cstr_ok tfibsegs W mem x l ->
  x + Z.of_nat (length l) + 1 <= spZ regs - STK_RT_STR \/ spZ regs <= x.
Proof.
  intros B ly S U W regs mem md x l (((HAR & _) & _) & Hlo & _) (_ & _ & Hceil & _).
  pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_stk_ceil ly HLY) as Hst.
  unfold ASAN_CEIL in Hst. left. lia.
Qed.

(* the post of a walk that ends at the return address with a0 = r, the stack window [sp - D, sp) its only change,
   read back on the caller's memory *)
Lemma post_of_walk : forall B, AR_laws tfibsegs B ->
  forall ly S U (W : world tfibsegs) regs mem md (R : Z -> Prop) (r v D : Z) ms' model' c m'
    t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  ecall_preU_k tfibsegs B STK_RT_STR ly S U W regs mem md ->
  NM.ro_agree I0.rsegs (mrestrict (w_H W) mem) ->
  0 <= D <= STK_RT_STR -> Z_to_bv 64 r = w64 v -> 0 <= v < 2 ^ 64 -> R v ->
  NM.ms_rel_cj I0.rsegs c
    (BMS.MS (BF.mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) t0 t1 t2 (reg_get regs 8)
       (reg_get regs 9) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
       (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
       (reg_get regs 27) t3 t4 t5 t6) fp_regs (BMS.ret_pc (reg_get regs 1)) fp_csr None m' (YK11.seg_rom BI.asegs)) ->
  NM.cj_same I0.rsegs (mrestrict (w_H W) mem) (ms_mem c) ->
  L6.ms_eqv c ms' ->
  BF.munch [(spZ regs - D, spZ regs)] (NM.normalize_cj I0.rsegs (mrestrict (w_H W) mem)) m' ->
  BF.stk BI.asegs m' (spZ regs - STK_RT_STR) (spZ regs) ->
  same_but_materialized md model' ->
  rt_post_roU tfibsegs B STK_RT_STR ly S U W regs mem md R W (mkCfg (unrestrict (w_H W) mem ms') model').
Proof.
  intros B LAWS ly S U W regs mem md R r v D ms' model' c m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    Hpre RO HD Hv Hv64 HR Hrel Hsame Heqv MU ST Hsbm.
  pose proof Hpre as (((HAR & Hret & Hal & Hlo1 & Hhi & _ & _ & _) & Hupok & Hupd) & Hlo & Hwin).
  pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
  assert (HK : STK_RT_STR = 8192) by reflexivity.
  unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
  pose proof (ush_bounds B LAWS ly S W (unpoison U mem) md U HAR Hupok) as USH.
  destruct (same_but_materialized_frame md model' Hsbm)
    as (_ & V1 & V2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V3).
  set (H := w_H W) in *. set (mR := mrestrict H mem) in *. set (sp := spZ regs) in *.
  remember (munrestrict H mem (ms_mem ms')) as mem'' eqn:Emem''.
  destruct Hrel as (Rr & Rf & Rpc & Rsvc & Rresv & Rfc & Rrom & Rmem).
  cbn [BMS.MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem] in Rr, Rf, Rpc, Rsvc, Rresv, Rfc, Rrom, Rmem.
  destruct Heqv as (Er & Ef & Epc & Esvc & Eresv & Efc & Emem & Erom).
  rewrite Rr in Er.
  assert (MUc : BF.munch [(sp - D, sp)] mR (ms_mem c))
    by exact (NM.munch_rel_cj I0.rsegs [(sp - D, sp)] mR _ (ms_mem c) m' (NM.mem_rel_cj_normalize I0.rsegs mR RO) Rmem Hsame MU).
  (* outside the walk's window the caller's memory is unchanged *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - D <= a < sp) -> mem'' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hn. rewrite Emem''. unfold munrestrict. destruct (H (Z_to_bv 64 a)) eqn:Eh; [reflexivity|].
    rewrite <- Emem. rewrite (MUc (Z_to_bv 64 a)) by (rewrite BMS.unsigned_lit by lia; cbn; split; [lia | exact I]).
    unfold mR, mrestrict. rewrite Eh. reflexivity. }
  (* the whole STK window is present after the walk *)
  assert (WIN : forall a, sp - STK_RT_STR <= a < sp -> exists b, ms_mem ms' (Z_to_bv 64 a) = Some b).
  { intros a Ha. destruct ST as (_ & _ & STa). destruct (STa a Ha) as (_ & b & Hb).
    assert (K : NM.cj_drop I0.rsegs (Z_to_bv 64 a) = false) by (apply cj_keep_high; unfold FS_IMG_TOP, TASK_SIZE; lia).
    exists b. rewrite <- Emem. rewrite <- (NM.mem_rel_cj_keep I0.rsegs _ _ _ Rmem K).
    rewrite mrd_high in Hb by (unfold BM.wa; rewrite BMS.unsigned_lit by lia; unfold FS_IMG_TOP; lia).
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
  unfold rt_post_roU. split; [reflexivity|]. exists (ms_regs ms'), mem'', model', v.
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
  { (* AR, by the frame law *)
    apply (al_frame _ _ LAWS ly S W (unpoison U mem) md (unpoison U mem'') model' HAR).
    - intros a Ha Hown. destruct (Z_le_gt_dec (sp - D) a) as [L1|L1]; [destruct (Z_lt_ge_dec a sp) as [L2|L2]|].
      + exfalso. apply (al_stack _ _ LAWS ly S W (unpoison U mem) md a HAR); [lia | exact Hown].
      + apply aview_at. unfold unpoison. rewrite KEEP by lia. reflexivity.
      + apply aview_at. unfold unpoison. rewrite KEEP by lia. reflexivity.
    - intros a Hv'. unfold aview, mbyte, mrestrict in Hv' |- *.
      destruct (w_H W (Z_to_bv 64 a)) eqn:Eh; [exact Hv'|].
      unfold unpoison in Hv' |- *. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))); [cbn; discriminate|].
      destruct (mem (Z_to_bv 64 a)) as [b|] eqn:Em.
      + destruct (mem'' (Z_to_bv 64 a)) as [b'|] eqn:Em''; [cbn; discriminate|].
        exfalso. apply (PRES a Eh); [rewrite Em; discriminate | exact Em''].
      + destruct (mem'' (Z_to_bv 64 a)); [cbn; discriminate | exact Hv'].
    - exact V1.
    - exact V2.
    - exact V3.
    - intros a _ Hh. rewrite Emem''. unfold unpoison, munrestrict. fold H in Hh. rewrite Hh. reflexivity. }
  split.
  { (* the user-poisoned shadow keeps its magic *)
    intros s Hs. destruct (USH s Hs) as (S1 & S2). unfold kHighMemBeg in S2.
    rewrite (aview_at tfibsegs (w_H W) mem'' mem s); [exact (Hupd s Hs)|]. apply KEEP; lia. }
  split; [exact (aregs_of_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Er)|].
  split; [exact Hsbm|].
  split.
  { rewrite (a0_of_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Er). exact Hv. }
  split; [exact Hv64|]. split; [exact HR|].
  split.
  { intros a Ha Hn. apply aview_at. apply KEEP; lia. }
  { intros a (Hh & b & Hb). split; [exact Hh|].
    destruct (mem'' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
    exfalso. apply (PRES a Hh); [rewrite Hb; discriminate | exact E]. }
Qed.

(* the core: the strlen interceptor at PC_strlen, from the facts cstr_ok gives (the length bound, the +8 range and the
   frame separation named) *)
Lemma fs_strlen_core : forall B, AR_laws tfibsegs B -> FsShadowSyms B -> FsRtCells B ->
  forall ly S U (W : world tfibsegs) regs mem md x (l : list Z),
  ecall_preU_k tfibsegs B STK_RT_STR ly S U W regs mem md -> rom_view tfibsegs W mem ->
  YK11.getr regs 10 = w64 x ->
  cstr tfibsegs W mem x l -> 4096 <= x ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length l) + 1) ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) x (Z.of_nat (length l) + 1) ->
  (forall a, x + Z.of_nat (length l) < a < x + Z.of_nat (length l) - (x + Z.of_nat (length l)) mod 8 + 8 ->
     aview tfibsegs (w_H W) mem a <> None) ->
  Z.of_nat (length l) < 2 ^ 40 ->
  amem_range x (Z.of_nat (length l) + 8) ->
  x + Z.of_nat (length l) + 1 <= spZ regs - STK_RT_STR \/ spZ regs <= x ->
  SRr tfibsegs W (cfg_at tfibsegs PC_strlen regs mem md)
    (rt_post_roU tfibsegs B STK_RT_STR ly S U W regs mem md (fun v => v = Z.of_nat (length l))).
Proof.
  intros B LAWS TL CELLS ly S U W regs mem md x l Hpre Hrom Hx Hcs Hx0 Hra Hhull Hsl Hlen Hamr Hfr.
  pose proof Hpre as (((HAR & Hret & Hal & Hlo1 & Hhi & _ & _ & _) & Hupok & Hupd) & Hlo & Hwin).
  pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
  assert (HK : STK_RT_STR = 8192) by reflexivity.
  unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
  pose proof (ro_agree_of_rom_view W mem Hrom) as RO.
  pose proof (walk_cells B LAWS TL CELLS ly S U W mem md HAR Hupok) as (M2S & ICN & ICL & _ & _ & _).
  assert (Esp : bv_unsigned (reg_get regs 2) = spZ regs) by (unfold spZ; rewrite getr_nz by reflexivity; reflexivity).
  assert (Ha0 : reg_get regs 10 = Z_to_bv 64 x) by (rewrite <- getr_nz by reflexivity; exact Hx).
  assert (Hamr' : (0 <= x /\ x + Z.of_nat (length l) + 8 <= 0x7fff7fff) \/
                  (0x10007fff8000 <= x /\ x + Z.of_nat (length l) + 8 <= 0x7fffffffffff))
    by (unfold amem_range, YG0f.kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
  set (H := w_H W) in *. set (mR := mrestrict H mem). set (sp := spZ regs) in *.
  set (len := Z.of_nat (length l)) in *.
  set (lo := sp - STK_RT_STR).
  set (str := map (Z_to_bv 8) l).
  set (slack := mk_slack mR (x + len + 1) (slack_len (x + len + 1))).
  assert (Lstr : Z.of_nat (length str) = len) by (unfold str, len; rewrite length_map; reflexivity).
  assert (Lsl : Z.of_nat (length slack) = (- (x + len + 1)) mod 8).
  { unfold slack, slack_len. rewrite length_mk_slack. rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). reflexivity. }
  assert (Lsl7 : 0 <= (- (x + len + 1)) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  unfold PC_strlen.
  apply (FSB.srr_of_evt Hwx_fs W 0x42654 regs mem md
    (walk_at (BL.istrlen_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
       (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
       (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) fp_regs fp_csr
       (Z.of_nat (length str)) lo (NM.normalize_cj I0.rsegs mR)) mR)).
  - refine (_ : BE.evt BI.asegs _ (st_at regs fp_regs (Z_to_bv 64 0x42654) fp_csr mR)).
    apply bz_transport; [exact RO|].
    apply (bz_strlen regs fp_regs fp_csr _ x str slack lo).
    + exact Ha0.
    + rewrite Esp. apply stk_norm_high; [unfold lo, FS_IMG_TOP; lia | unfold TASK_SIZE; lia |].
      apply FSB.stk_of_apresent; [unfold lo; lia | lia | exact Hwin].
    + rewrite Esp. unfold lo. lia.
    + unfold BR.kHighShadowEnd, lo. lia.
    + rewrite Esp. lia.
    + lia.
    + rewrite Lstr. lia.
    + rewrite Lstr. lia.
    + refine (NM.bytes_at_normalize_cj_low I0.rsegs mR x (str ++ Z_to_bv 8 0 :: slack) RO _ _).
      * rewrite length_app. cbn [length]. unfold TASK_SIZE. lia.
      * exact (cstr_bytes W mem x l Hcs ltac:(lia) ltac:(unfold TASK_SIZE; lia) Hsl).
    + exact (cstr_nonul W mem x l Hcs).
    + rewrite Lstr, Lsl. lia.
    + rewrite Esp, Lstr, Lsl. lia.
    + rewrite Lstr. apply chk_norm; [lia | lia | lia | lia | | exact Hra | exact Hhull].
      unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd. lia.
    + exact M2S.
    + exact ICN.
    + exact ICL.
    + apply bz_mem_inv_normalize.
  - intros ms' model' (c & s0 & HQ & Hrel & Hsame & Heqv) Hsbm _.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Es0 & MU & _ & _ & ST').
    subst s0. rewrite Esp in MU, ST'.
    apply (post_of_walk B LAWS ly S U W regs mem md _ (Z.of_nat (length str)) len 2224 ms' model' c m'
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hpre RO); try assumption.
    + rewrite HK. lia.
    + rewrite Lstr. reflexivity.
    + lia.
    + reflexivity.
Qed.

(* ---- the contract ---- *)
Theorem fs_strlen_realizesU : forall B, AR_laws tfibsegs B -> TfibSyms B -> FsShadowSyms B -> FsRtCells B ->
  astrlen_realizesU tfibsegs B PC_strlen.
Proof.
  intros B LAWS _ TL CELLS ly S U W regs mem md x l Hpre Hrom Hx Hok.
  pose proof (cstr_off_frame B ly S U W regs mem md x l Hpre Hok) as Hfr.
  destruct Hok as (Hcs & Hx0 & _ & H32 & Hamr & Hra & Hhull & Hsl).
  exact (fs_strlen_core B LAWS TL CELLS ly S U W regs mem md x l Hpre Hrom Hx Hcs Hx0 Hra Hhull Hsl ltac:(lia) Hamr Hfr).
Qed.

Corollary fs_strlen_realizes : forall B, AR_laws tfibsegs B -> TfibSyms B -> FsShadowSyms B -> FsRtCells B ->
  astrlen_realizes tfibsegs B PC_strlen.
Proof.
  intros B LAWS TB TL CELLS. apply astrlen_realizes_of_U. exact (fs_strlen_realizesU B LAWS TB TL CELLS).
Qed.

End core.

(* the image end the Bz walk takes (Bz/A/I_ikit.v try_init_spec, 0x5fd000; fuzz_manifest's 0x5f7000 before the port fix)
   is fs's FS_IMG_END *)
Lemma ikit_img_end : (0x5fd000 = FS_IMG_END)%Z.
Proof. reflexivity. Qed.
