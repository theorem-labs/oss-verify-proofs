(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import Vdso.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require PropExec StdModel ShapeAlg ShapeLaws AgentLib ModelAmb Spec S0ReadBase S0ReadStage S0World
  S0StdioDefs S0ExitBase S0TargetPre.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Tac Image ZBridge Walk Arr SysStep ITree Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KInv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KLink. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM12. Import MM12. Import MM12.Malloc_iface. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM02. Import MM02. Import MM02.Malloc_ifaceP.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Plain Require Import PImg RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Mr Require Import MrRulesS0.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.MrP0 Require Import S0HeapPre S0HBase S0HConv S0SoDefs S0TrTail S0SoOk S0RdLib S0RdInv S0RdRules S0RdLoop S0RdEnd S0RdTop
  S0RdLeaf S0LfHdr S0LfJoin.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Module OSp := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec.
Module OTP := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.S0TargetPre.
Module OAL := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.AgentLib.
Module OSL := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.ShapeLaws.

Lemma rz_kept_hd {RCa1 : RunCtx}  : forall (R R' : bvmap 5 word) pc M mo T,
  (forall r : reg, In r hd_kept -> OP.getr R' r = OP.getr R r) ->
  (let g := fun k : Z => reg_get R (Z_to_bv 5 k) in let g' := fun k : Z => reg_get R' (Z_to_bv 5 k) in
   realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR (g' 1) (g 2) (g 3) (g 4) (g' 5) (g' 6) (g' 7) (g 8) (g 9) (g' 10) (g' 11) (g' 12) (g' 13) (g' 14) (g' 15)
                                   (g' 16) (g' 17) (g' 18) (g' 19) (g' 20) (g' 21) (g' 22) (g' 23) (g' 24) (g' 25) (g' 26) (g' 27)
                                   (g' 28) (g' 29) (g' 30) (g' 31))
                              bvmap_empty pc fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R' pc M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros R R' pc M mo T KEPT H. apply rz_mkR. unfold mkR_of. cbv zeta in H.
  assert (IN : forall k : Z, In k [2; 3; 4; 8; 9] -> In (Z_to_bv 5 k : reg) hd_kept).
  { intros k Hk. unfold hd_kept. cbn [In] in Hk |- *.
    destruct Hk as [<-|[<-|[<-|[<-|[<-|[]]]]]]; repeat (first [left; apply bv_eq; reflexivity | right]). }
  rewrite (KEPT _ (IN 2 ltac:(clear; cbn; tauto)) : reg_get R' (Z_to_bv 5 2) = _),
          (KEPT _ (IN 3 ltac:(clear; cbn; tauto)) : reg_get R' (Z_to_bv 5 3) = _),
          (KEPT _ (IN 4 ltac:(clear; cbn; tauto)) : reg_get R' (Z_to_bv 5 4) = _),
          (KEPT _ (IN 8 ltac:(clear; cbn; tauto)) : reg_get R' (Z_to_bv 5 8) = _),
          (KEPT _ (IN 9 ltac:(clear; cbn; tauto)) : reg_get R' (Z_to_bv 5 9) = _).
  exact H.
Qed.

Section LEAFHDR.
Context {RCa1 : RunCtx}.
Context {rc : runConstT}.
Variable sp0 : word.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis HATOP : ATOP = bv_unsigned sp0 - 8388608.
(* port727 (): over the launch input, as RdTop: RdTop's hdr_cont is stated over
   inp / rdraw (its GPOST's AmbIn and file system are the launch's), so the leaves are too. *)
Variables (inp : ProcInput) (rdraw : EntryDraw) (tid : word) (content : list byte).
Local Notation stdin0 := (ModelAmb.amb_of inp (vdso_run_init (ed_vdso rdraw))) (only parsing).
Local Notation fs0 := (in_fs inp) (only parsing).
Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.

Let SP : Z := bv_unsigned sp0.
Let L : Z := Z.of_nat (length content).
Abbreviation GPOST := (G_post stdin0 fs0 tid).

Lemma SPr : 0x7fff80000000 <= SP <= 0x800000000000.
Proof. destruct Hvsp as (A & B & _). unfold sp_window_lo, sp_window_hi in *. unfold SP. lia. Qed.
Lemma SP16 : SP mod 16 = 0.
Proof. destruct Hvsp as (_ & _ & C). exact C. Qed.

Definition WHD : list (Z * Z) := [(SP - 512, SP - 128); (0x1f7c0, 0x1f8a8)].

Lemma fm_ivs_hd : fm_ivs (hd_regions SP) = WHD.
Proof.
  pose proof SPr as SPR. unfold fm_ivs, hd_regions, WHD. cbn [map fst snd].
  rewrite !unsigned_lit by lia. repeat f_equal; lia.
Qed.

Lemma whd_disjoint : forall A n, 0 <= n ->
  (SP - 128 <= A \/ (A + n <= SP - 512 /\ (A + n <= 0x1f7c0 \/ 0x1f8a8 <= A))) -> disjoint_from WHD A n.
Proof. intros A n Hn H. pose proof SPr as SPR. unfold WHD. cbn [disjoint_from]. lia. Qed.

Lemma whd_write_ok : forall LB, Forall (rclient_write_ok LB) WHD.
Proof.
  intros LB. pose proof SPr as SPR. unfold WHD.
  repeat (apply Forall_cons; [|try apply Forall_nil]); unfold rclient_write_ok; cbn [fst snd].
  - left. lia.
  - right; left. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
Qed.

Lemma hd_transport : forall M M', rd_base SP tid M -> munch WHD M M' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) M M' ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) M' (SP - 6144513) (SP - 128)
  /\ (exists junk, rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' (SP - 128) (main_cells SP junk))
  /\ (exists errv : word, rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' RERRNO [C4 errv])
  /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M' /\ rauxv_ok M' SP
  /\ pristine_in exit_ivs2 M'
  /\ OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M' (Z_to_bv 64 0x2fa58) 4 = Some (word_to_le_bytes 4 tid)
  /\ so_pristine M'.
Proof.
  intros M M' [ST UP (junk & FRM) (errv & ERR) MI AUX IMG TIDC] MU WM.
  pose proof SPr as SPR.
  pose proof (same_on_munch _ _ _ MU WM) as SO.
  assert (OUT : forall a, (SP - 128 <= a \/ (a < SP - 512 /\ (a < 0x1f7c0 \/ 0x1f8a8 <= a))) -> outside WHD a).
  { intros a Ha. apply (disjoint_outside WHD a 1); [|lia]. apply whd_disjoint; lia. }
  assert (NONE : forall lo hi a, In (lo, hi) rd_ivs -> lo <= a < hi -> (a < 0x1f7c0 \/ 0x1f8a8 <= a) -> M' (Z_to_bv 64 a) = None).
  { intros lo hi a IN Ha Hf.
    assert (R : 0 <= a < 2 ^ 64 /\ a < SP - 512).
    { unfold rd_ivs in IN. cbn [In] in IN. repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]). destruct IN. }
    destruct (SO a (proj1 R) (OUT a ltac:(lia))) as [E _]. unfold wa in E. rewrite E. exact (IMG lo hi a IN Ha). }
  split; [apply (stk_wmono M M'); [exact ST | lia | exact WM]|].
  split; [exists junk; eapply rw_cells_transport; [exact FRM | exact MU | exact WM |]; apply whd_disjoint; [cbn; lia | left; lia]|].
  split; [exists errv; eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]; apply whd_disjoint; [cbn; lia |];
          right; unfold RERRNO; cbn; lia|].
  split; [eapply mem_inv_munch; [exact MI | exact MU | intros a Ha; apply OUT; lia |];
          (* route (A): WHD's stack interval is in rd_base's window; the other is the image *)
          unfold WHD; constructor; [|constructor; [|constructor]]; intros a Ha Hout; cbn [fst snd] in Ha;
          [pose proof ST as (_ & _ & STK); exact (proj1 (STK a ltac:(lia))) | lia]|].
  split.
  { destruct AUX as (av & auxvs & auxr & rnd & C1 & A1 & A2 & H).
    exists av, auxvs, auxr, rnd. split; [|split; [|split; [|exact H]]].
    + eapply rw_cells_transport; [exact C1 | exact MU | exact WM |]. apply whd_disjoint; [cbn; lia |]. right. unfold RAUXV_CELL. cbn. lia.
    + eapply bytes_at_transport; [exact A1 | exact MU |]. apply whd_disjoint; [lia | left; lia].
    + eapply bytes_at_transport; [exact A2 | exact MU |]. apply whd_disjoint; [lia | left; lia]. }
  split.
  { intros lo hi a IN Ha. unfold exit_ivs2 in IN. cbn [In] in IN.
    destruct IN as [IN|[IN|[IN|[IN|[IN|[IN|[IN|[]]]]]]]]; injection IN as <- <-.
    - apply (NONE 0x1e000 0x1e780); [clear; cbn; tauto | lia | lia].
    - apply (NONE 0x1e788 0x1f9b0); [clear; cbn; tauto | lia | lia].
    - apply (NONE 0x1e788 0x1f9b0); [clear; cbn; tauto | lia | lia].
    - apply (NONE 0x1e788 0x1f9b0); [clear; cbn; tauto | lia | lia].
    - apply (NONE 0x1f9b1 0x1f9f9); [clear; cbn; tauto | lia | lia].
    - apply (NONE 0x4fb40 0x4fd70); [clear; cbn; tauto | lia | lia].
    - apply (NONE 0x501b0 0x51000); [clear; cbn; tauto | lia | lia]. }
  split.
  { rewrite <- TIDC. apply (rdn_same_on (outside WHD)); [exact SO | | lia | lia].
    intros x Hx. apply OUT. cbn in Hx. lia. }
  intros i [Hi|Hi].
  - apply (NONE 0x1e788 0x1f9b0); [clear; cbn; tauto | lia | lia].
  - apply (NONE 0x501b0 0x51000); [clear; cbn; tauto | lia | lia].
Qed.

Lemma hd_img_of_base : forall M, rd_base SP tid M ->
  forall i, 0x10000 <= i < 0x1e780 \/ 0x1e788 <= i < 0x1f9b0 -> M (Z_to_bv 64 i) = None.
Proof.
  intros M BASE i Hi. pose proof (rb_img _ _ _ BASE) as IMG. pose proof (rb_mi _ _ _ BASE) as MI.
  destruct Hi as [Hi|Hi].
  - destruct (Z_lt_le_dec i 0x1e000) as [A|A]; [apply mem_inv_none; [exact MI | lia]|].
    apply (IMG 0x1e000 0x1e780 i); [clear; cbn; tauto | lia].
  - apply (IMG 0x1e788 0x1f9b0 i); [clear; cbn; tauto | lia].
Qed.

Lemma hdr_leaf : forall (P : list byte -> Prop) (msg : list byte),
  hdr_diag_stmt P msg -> P content ->
  forall (pb : bptr) (buf cap : Z) (M : word -> option byte) (s : PState) (mo : Model)
         (x18 x24 x25 x26 x27 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
    rd_inv SP tid content GPOST pb buf cap L M s mo -> 65536 <= cap <= 2 ^ 26 -> L < cap ->
    realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (SP - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 2) (Z_to_bv 64 buf)
                                   y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 L) (Z_to_bv 64 3) (Z_to_bv 64 cap)
                                   (Z_to_bv 64 0x1f9f9) (Z_to_bv 64 0) x24 x25 x26 x27 y28 y29 y30 y31)
                              bvmap_empty (Z_to_bv 64 0x13e4c) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) (OSp.t_die msg fs0).
Proof.
  intros P msg HD HP pb buf cap M s mo x18 x24 x25 x26 x27 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RI HCAP HL.
  pose proof SPr as SPR. pose proof SP16 as SPA.
  pose proof (rd_blk_range _ _ _ _ _ _ _ _ _ _ _ RI) as (BR1 & BR2 & BR3 & BR4).
  pose proof RI as [HH HOWN (bs & BLK & PRE) [LEN1 LEN2] BASE].
  pose proof HOWN as [(Ld & _ & HKL & _) [_ HG]]. unfold G_post in HG.
  pose proof (kl_halt _ _ _ HKL) as Hh.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo (kl_minv _ _ _ HKL)) as Hl.
  assert (FD2 : fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite HG; reflexivity).
  assert (CONT : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 buf) (length content) = Some content).
  { pose proof (rw_cells_bytes_at _ _ _ _ BLK) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    assert (LBS : length bs = Z.to_nat cap) by (destruct BLK as [[[W _] _] _]; exact W).
    pose proof (bytes_at_rdn (run_segments psegs rc_inp rc_sp rc_mb) M buf bs 0 (length content) B ltac:(unfold L in *; lia)) as X.
    rewrite Z.add_0_r in X. cbn [skipn] in X. unfold L in PRE. rewrite Nat2Z.id in PRE. rewrite PRE in X.
    rewrite firstn_all in X. exact X. }
  eapply ShapeAlg.rz_conseq.
  2:{ unfold OSp.t_die. apply OAL.t_emit_congr. apply (OSL.t_emit_W_nil 1). apply OSL.t_exit_has_nil. }
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    eapply (HD SP buf content (bv_unsigned CAN) RR M mo) end.
  - constructor.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + split; [exact SPR | exact SPA].
    + fold L. lia.
    + fold L. lia.
    + exact (stack_writable_of_base SP SPR tid content M BASE).   (* port727: window, no ATOP *)
    + exact (hd_img_of_base M BASE).
    + exact (lf_got _ _ _ HH).
    + exact (lf_guard _ _ _ HH).
    + pose proof (bv_unsigned_in_range _ CAN) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X.
    + exact CONT.
  - exact HP.
  - exact FD2.
  - exact (minv_reader _ (kl_minv _ _ _ HKL)).   (* port727: the far-end reader *)
  - exact Hh.
  - exact Hl.
  - apply OSL.t_emit_has_nil.
  -
    intros R' M' KEPT FM (wp & rp & FC).
    destruct (munch_of_frame_mod _ _ _ FM) as [MU WM]. rewrite fm_ivs_hd in MU.
    destruct (hd_transport M M' BASE MU WM) as (ST' & (junk & FRM') & (errv & ERR') & MI' & AUX' & PR' & TIDC' & SOP').
    assert (HH' : RHEAP s [(pb, buf, cap)] M') by (eapply RHEAP_frame_proof; [exact HH | exact MU | exact WM | apply whd_write_ok]).
    eapply (rz_kept_hd _ _ _ _ _ _ KEPT). cbv beta zeta. simp_regs.
    lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ => forget_regs R' end.
    unfold main_cells in FRM'.
    eapply (main_join_rz_g SP SPR so_ok so_ok_exit so_ok_frame
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              M' mo s pb buf cap fs0 0%nat 2 (bv_unsigned tid) (SP - 6144513) junk _ _ _ _ _ _ _ _ errv wp rp);
      [ reflexivity | reflexivity | reflexivity | reflexivity | right; reflexivity | exact HH'
      | eapply OWN_weaken; [exact HOWN|]; split; rewrite HG; reflexivity
      | exact AUX' | exact ST' | lia | lia | exact ERR' | exact MI' | exact FRM' | exact PR' | exact FC | lia
      | rewrite Z_to_bv_bv_unsigned; exact TIDC' | left; split; [reflexivity | exact SOP'] ].
Qed.

Variable AI : nat -> list bptr -> PState -> Model -> Prop.

Theorem leaf_short : hdr_cont sp0 inp rdraw tid content AI (L < 6) (OSp.t_die OSp.msg_short fs0).
Proof.
  intros j pb buf cap M s mo x18 x24 x25 x26 x27 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RI _ HCAP HL HP.
  eapply (hdr_leaf _ _ hdr_diag_short); [unfold L in HP; lia | exact RI | exact HCAP | exact HL].
Qed.

Theorem leaf_overrun :
  hdr_cont sp0 inp rdraw tid content AI (6 <= L < 6 + OTP.hdr_cfglen content) (OSp.t_die OSp.msg_overrun fs0).
Proof.
  intros j pb buf cap M s mo x18 x24 x25 x26 x27 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RI _ HCAP HL HP.
  eapply (hdr_leaf _ _ hdr_diag_overrun); [unfold L in HP; split; lia | exact RI | exact HCAP | exact HL].
Qed.
End LEAFHDR.
