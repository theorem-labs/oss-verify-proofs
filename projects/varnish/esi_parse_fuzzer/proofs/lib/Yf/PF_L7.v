(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr SysStep RzBridge MState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec RelSpec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct Lazyiq4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcpnnp AIcpya4 AIcp3q7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpwpz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpwpz AIcpw0i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg AIcp1qh.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpwpz.AIcpdm8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpwpz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpw0i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcp8qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp1qh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World A_Img.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require DA_Eg3i DA_Cells DA_Ldix DA_Se7o DA_Tcfe DA_Fh3h.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Exec.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Se7o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tcfe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Fh3h.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_seql.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_sjs3 PF_low PF_file PF_pc1 PF_pc2d PF_vf PF_vpsh.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_sjs3.RA_pdfk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.PF_low OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.PF_file OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.PF_pc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.PF_pc2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.PF_vf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.PF_vpsh.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Local Ltac cbn_mf_in H ::=
  cbv beta iota delta [mf_set_w mf_set_rp mf_set_mode mf_set_flags mf_set_buf mf_set_write_lbf stdout_buffered stdout0 stderr0
       mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize
       mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148] in H.
Ltac icall_consts_in H ::= unfold vp_pre_post, vp_frames, vf_pre_post, vf_frame, vf_file1, pfd_mid, pfd_ret, vf_post_post, vp_post_post,
  fwritex_fit_post, VP_DEPTH, VFB_DEPTH, PC2_DEPTH, FWRITEX_STACK, VP_VF_RET, VF_PC2_RET, FWX5_RET, PRINTF_CORE in H; cbn_mf_in H;
  unfold STDOUT_BUF, STDOUT_F in H; rewrite ?unsigned_lit in H by lia; cbn [length app Z.of_nat] in H; rewrite ?length_app in H; cbn [length] in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LO; @CV; @CEIL; @SPVA; @VAHI; @JL; @PLEN; @PL; @JL'; @H2; @SPR; @H; @JL1; @Ha; @W; @CQ; @JL''; @H1; @H0; @H3; @L; @Hn; @VALO; @CM; @S0; @S1; @Hi])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)

(* [comment removed for export] *)
Section Cells.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variable v : word -> option byte.
  Hypothesis CH : consts_hold LPA v.
  #[using="CH"] Lemma vpicpt_cells_of_consts : vpicpt_cells v.
  Proof.
    split; [apply asan_inited_cell_of_bytes; apply (consts_lookup v _ _ CH); vm_compute; reflexivity|].
    split; [apply ro_C8_of_bytes; apply (consts_lookup v _ _ CH); vm_compute; reflexivity|].
    split. { replace 0x146f3c with (0x146ee8 + Z.of_nat 84)%Z by reflexivity.
             eapply (ro_C1_of_nth v 0x146ee8 pa_common_flags_bytes 84); [apply (consts_lookup v _ _ CH); vm_compute; reflexivity| reflexivity]. }
    split; [apply ro_C8_of_bytes; apply (consts_lookup v _ _ CH); vm_compute; reflexivity|].
    split; [apply ro_C8_of_bytes; apply (consts_lookup v _ _ CH); vm_compute; reflexivity|].
    exact (map_cells_of_consts v CH).
  Qed.
End Cells.

(* [comment removed for export] *)
Lemma u64s_le8_1 : forall w : word, u64s [w] = le8 w.
Proof. intros w. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma stack_zsh_bounds : forall zlo zhi,
  alloc_ceiling + 64 <= zlo -> zlo <= zhi -> zhi + 80 <= 2^47 ->
  zsh_bounds (sh alloc_ceiling) (Z.to_nat ((2^47 - alloc_ceiling) / 8)) zlo zhi
  /\ 2147446784 <= sh alloc_ceiling.   (* [comment removed for export] *)
Proof.
  (* [comment removed for export] *)
  intros zlo zhi H1 H2 H3. pose proof alloc_ceiling_val as CV. pose proof alloc_ceiling_mod16 as CM.
  set (q := alloc_ceiling / 16) in *.
  assert (CQ : alloc_ceiling = 16 * q) by (pose proof (Z_div_mod_eq_full alloc_ceiling 16); lia).
  assert (D8 : alloc_ceiling / 8 = 2 * q) by (rewrite CQ; replace (16 * q) with ((2 * q) * 8) by lia; apply Z.div_mul; lia).
  assert (DK : (2^47 - alloc_ceiling) / 8 = 17592186044416 - 2 * q)
    by (rewrite CQ; replace (2^47 - 16 * q) with ((17592186044416 - 2 * q) * 8) by lia; apply Z.div_mul; lia).
  unfold zsh_bounds, sh, sha, shadow_off, kHighShadowEnd_z, kHighMemBeg_z, SBUF_HI, kShadowOffset.
  rewrite D8, DK. rewrite Z2Nat.id by lia. change (2^47)%Z with 140737488355328%Z in *.
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; Z.div_mod_to_equations; lia.
Qed.

End CEIL.

(* [comment removed for export] *)
Lemma fmtd_cells : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x149a5 PF_pc1.FMT_D.
Proof.
  intros m MI. pose proof (ro_cells_image rsegs m 0x149a5 [Z_to_bv 8 37; Z_to_bv 8 100; Z_to_bv 8 10; Z_to_bv 8 0] MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as [_ B].
  split; [cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; exact I| cbn [cells_bytes cbytes] in *; exact B].
Qed.

(* [comment removed for export] *)
Lemma fmtd_nl : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x149a7 [Z_to_bv 8 10].
Proof.
  intros m MI. pose proof (proj2 (fmtd_cells m MI)) as B. cbn [cells_bytes cbytes app] in B.
  apply (bytes_at_app_l m 0x149a7 [Z_to_bv 8 10] [Z_to_bv 8 0]).
  exact (bytes_at_app_r m 0x149a5 [Z_to_bv 8 37; Z_to_bv 8 100] [Z_to_bv 8 10; Z_to_bv 8 0] B).
Qed.

(* [comment removed for export] *)
Lemma cb2_merge : forall segs m a n1 n2 (l1 l2 : list byte),
  rw_cells segs m a [CB n1 l1; CB n2 l2] -> rw_cells segs m a [CB (n1 + n2) (l1 ++ l2)].
Proof.
  intros. eapply rw_cells_recast_pf; [exact H| |].
  - destruct H as [[W _] _]. cbn [cells_wf cell_wf] in W |- *. split; [rewrite length_app; lia| exact I].
  - cbn [cells_bytes cbytes]. rewrite <- app_assoc, !app_nil_r. reflexivity.
Qed.
Lemma cb2_split : forall segs m a n1 n2 (l1 l2 : list byte),
  rw_cells segs m a [CB (n1 + n2) (l1 ++ l2)] -> length l1 = n1 -> rw_cells segs m a [CB n1 l1; CB n2 l2].
Proof.
  intros segs m a n1 n2 l1 l2 H L. eapply rw_cells_recast_pf; [exact H| |].
  - destruct H as [[W _] _]. cbn [cells_wf cell_wf] in W |- *. rewrite length_app in W. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
  - cbn [cells_bytes cbytes]. rewrite <- app_assoc, !app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_rebuild2 : forall (m m' : word -> option byte) A n (j bs1 bs2 : list byte),
  rw_cells rsegs m A [CB n j] -> wmono rsegs m m' ->
  bytes_at rsegs m' A bs1 -> rw_cells rsegs m' (A + Z.of_nat (length bs1)) [CB (length bs2) bs2] ->
  (length bs1 + length bs2 = n)%nat ->
  rw_cells rsegs m' A [CB (length bs1) bs1; CB (length bs2) bs2].
Proof.
  intros m m' A n j bs1 bs2 [[W B] WR] WM B1 [[W2 B2] _] L. split; [split|].
  - cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. cbn [cells_bytes cbytes] in B2. rewrite app_nil_r in B2.
    apply (proj2 (bytes_at_app rsegs m' A bs1 bs2)). split; [exact B1| exact B2].
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, L. cbn [cells_size csize Nat.add] in WR. rewrite Nat.add_0_r in WR.
    exact (wr_at_transport rsegs m m' A _ WR WM).
Qed.

(* [comment removed for export] *)
Lemma stk_wr_at : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> a + n <= hi -> wr_at rsegs m a n.
Proof.
  intros m lo hi a n (S0 & S1 & S) Ha Hn. split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (S (a + i) ltac:(lia))).
Qed.

Definition keepP (P : Prop) : Prop := P.   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac post_pcall :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  (let T := type of PO in let h := atac_head_of T in try unfold h in PO);
  icall_consts_in PO; rewrite ?unsigned_lit in PO by lia;
  destruct_exs PO;
  let E := fresh "E" in destruct PO as [E PO]; subst ms'; try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).
Tactic Notation "pcall" uconstr(SPEC) "by" tactic3(side) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC; side | post_pcall ]
  end.

Section Leaves.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)

  Lemma vprintf_next_ok : vprintf_next_stmt.
  Proof.
    unfold vprintf_next_stmt. intros until K. cbv zeta.
    intros AINV MI TP A0 A1 VAB VALO VAHI SPVA RNGC ZSH SOUT PLEN [g CAN] GOT ST LO CEIL SP16 HKONT.
    destruct SOUT as (mo & junk & FILE & BUFS & PL).
    unfold VPRINTF_ICPT_STACK, FMT_D in *. subst a0 a1.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof alloc_ceiling_val as CV.
    pose proof (consts_hold_ainv LPA A m md AINV) as CH.
    pose proof (vpicpt_cells_of_consts _ CH) as VC. pose proof (asan_memcpy_cells_of_consts _ CH) as CMC. pose proof (asan_memset_cells_of_consts _ CH) as CMS.
    destruct (RNGC _ CH) as [RNGA RNGB].
    unfold DA_Ldix.FMT_D, STDOUT_F, STDOUT_BUF, DA_Eg3i.SSP_GUARD, SSP_GOT in *.
    pose proof (fmtd_cells _ MI) as HF.
    (* [comment removed for export] *)
    pose proof BUFS as BUFS0. lazymatch type of BUFS0 with ?T => change T with (keepP T) in BUFS0 end.
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in BUFS. destruct BUFS as [RWP RST]. cbn [cells_size csize Nat.add] in RST.
    assert (BUF : bytes_at rsegs (aview A m) 0x608ae8 p).
    { pose proof (proj2 (proj1 RWP)) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X. }
    (* [comment removed for export] *)
    destruct (stack_zsh_bounds (Clg:=Clg) (bv_unsigned sp - 464 - 4928) (bv_unsigned sp - 464 + 96) ltac:(lia) ltac:(lia) ltac:(lia)) as [ZB SBL].
    assert (SF : sfF 0x149a5 4 0x608ae8 1024 (sh alloc_ceiling) (Z.to_nat ((2^47 - alloc_ceiling) / 8))
                     (bv_unsigned sp + -96 + -368 - PC2_DEPTH) (bv_unsigned sp + -96 + -368 + 96) (aview A m)).
    { unfold sfF, PC2_DEPTH. replace (bv_unsigned sp + -96 + -368 - 4928) with (bv_unsigned sp - 464 - 4928) by lia.
      replace (bv_unsigned sp + -96 + -368 + 96) with (bv_unsigned sp - 464 + 96) by lia.
      refine (conj CMC (conj CMS (conj RNGA (conj RNGB (conj ZSH (conj ZB SBL)))))). }
    assert (VL : vpsh_low 0x149a5 (aview A m)) by (split; [exact VC| exact RNGA]).
    assert (VAA : bytes_at rsegs (aview A m) va (u64s [Z_to_bv 64 0])) by (rewrite u64s_le8_1; exact VAB).
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0xada18, 0xada18 + 152); (0x608ae8, 0x608ae8 + 1024)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(bv_unsigned sp - 8192, bv_unsigned sp); (0xada18, 0xada18 + 152); (0x608ae8, 0x608ae8 + 1024)]).
    { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|]. eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
      split. { right. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
      split; [| exact I]. right. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
    assert (HW : wfok [(bv_unsigned sp - 8192, bv_unsigned sp); (0xada18, 0xada18 + 152); (0x608ae8, 0x608ae8 + 1024)]) by solve_wfok.
    unfold file_at, file_cells in FILE. cbn_mf_in FILE.
    assert (LA4 : 0 <= 4) by lia. assert (LN : 0 <= 1024) by lia.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    assert (H1 : lo <= bv_unsigned sp - VP_DEPTH) by (unfold VP_DEPTH; lia).
    assert (H2 : alloc_ceiling <= lo) by exact CEIL.   (* [comment removed for export] *)
    assert (H3 : va + 8 * Z.of_nat (length [Z_to_bv 64 0]) <= 2^63) by (cbn [length]; lia).
    assert (H4 : IMG_LO <= 0x149a5) by (unfold IMG_LO; lia).
    assert (H5 : 0x149a5 + 4 <= RO_TOP) by (unfold RO_TOP; lia).
    icall (vp_pre ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 0x149a5 va [Z_to_bv 64 0] H1 H2 SPVA H3 H5
             t0 t1 t2 _ _ a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (aview A m) eq_refl eq_refl ST HF VAA VL MI)
      by (first [eassumption | reflexivity | lia]).
    lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST1;
      pose proof (fok_sfF _ _ _ _ _ _ _ _ LA4 LN _ _ _ MU HW SF) as SF1;
      pose proof (fok_vpsh_low _ _ _ _ MU HW VL) as VL1;
      destruct PC0 as [VFR1 VFR2]; rename MI0 into MI1 end.
    (* [comment removed for export] *)
    assert (H6 : lo <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) - VFB_DEPTH) by (rewrite unsigned_lit by lia; unfold VFB_DEPTH; lia).
    assert (H7 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) <= 2^47) by (rewrite unsigned_lit by lia; lia).
    assert (H8 : 0x149a5 + 4 <= RO_TOP) by (unfold RO_TOP; lia).
    assert (F1 : mf_flags (stdout_buffered mo p) = 5) by reflexivity.
    assert (F2 : mf_lock (stdout_buffered mo p) = -1) by reflexivity.
    assert (F3 : 0 < mf_buf (stdout_buffered mo p)) by (cbn_mf; unfold STDOUT_BUF; lia).
    assert (F4 : mf_buf (stdout_buffered mo p) + mf_bufsize (stdout_buffered mo p) < 2^47) by (cbn_mf; unfold STDOUT_BUF; lia).
    assert (F5 : 0 < mf_bufsize (stdout_buffered mo p) < 2^31) by (cbn_mf; lia).
    assert (F6 : FILE_LO <= 0xada18 /\ 0xada18 + 152 <= FILE_HI) by (unfold FILE_LO, FILE_HI; lia).
    assert (F7 : if false then mf_wend (stdout_buffered mo p) = w0 /\ (0 <= mf_mode (stdout_buffered mo p) < 2^32)%Z
                 else mf_wend (stdout_buffered mo p) = Z_to_bv 64 (mf_buf (stdout_buffered mo p) + mf_bufsize (stdout_buffered mo p))) by (cbn_mf; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    icall (vf_pre_buf PF_pc1.FMT_D 4 eq_refl pc1_d towrite_ok
             (Z_to_bv 64 VP_VF_RET) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 0x149a5) (Z_to_bv 64 0xada18) (Z_to_bv 64 va) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
             lo 0x149a5 0xada18 va g (stdout_buffered mo p) false
             H6 H7 H2 H8 F1 F2 F3 F4 F5 F6 F7
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx eq_refl eq_refl eq_refl)
      by (first [ rewrite ?unsigned_lit by lia; eassumption | split; eassumption | apply fmtd_cells; assumption
                | unfold file_at, file_cells; cbn_mf; eassumption | reflexivity | lia ]
          || match goal with |- ?G => idtac "VFSIDE-FAIL" G end)
    end.
    clear SF1 VL1 POST.
    lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST2;
      pose proof (fok_sfF _ _ _ _ _ _ _ _ LA4 LN _ _ _ MU HW SF) as SF2;
      destruct PC0 as [APC2 VFR3]; rename MI into MI2; rename POST0 into FILE2 end.
    (* [comment removed for export] *)
    assert (Q1 : lo <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96 + -368)) - PC2_DEPTH) by (rewrite unsigned_lit by lia; unfold PC2_DEPTH; lia).
    assert (Q3 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96 + -368)) + 368 <= va) by (rewrite unsigned_lit by lia; lia).
    assert (G1 : mf_wbase (stdout_buffered mo p) = Z_to_bv 64 (mf_buf (stdout_buffered mo p))) by reflexivity.
    assert (G2 : mf_wpos (stdout_buffered mo p) = Z_to_bv 64 (mf_buf (stdout_buffered mo p) + Z.of_nat (length p))) by reflexivity.
    assert (G3 : mf_wend (stdout_buffered mo p) = Z_to_bv 64 (mf_buf (stdout_buffered mo p) + mf_bufsize (stdout_buffered mo p))) by reflexivity.
    assert (G4 : 0 <= mf_bufsize (stdout_buffered mo p) < 2^31) by (cbn_mf; lia).
    assert (G5 : -2^31 <= mf_lbf (stdout_buffered mo p) < 2^31) by (cbn_mf; lia).
    assert (G6 : Z.of_nat (length p) + 2 <= mf_bufsize (stdout_buffered mo p)) by (cbn_mf; lia).
    pose proof (rw_CB_length _ _ _ _ _ (proj2 (proj1 (rw_cells_app rsegs _ _ [_] _) (BUFS0 : rw_cells _ _ _ _)))) as JL.
    assert (G7 : Z.of_nat (length p) + Z.of_nat (length junk) = mf_bufsize (stdout_buffered mo p)).
    { cbn_mf. pose proof BUFS0 as BUFS1. unfold keepP in BUFS1. destruct BUFS1 as [[W _] _]. cbn in W. lia. }
    replace (1024 - length p)%nat with (length junk) in RST by lia.
    replace (6327016 + Z.of_nat (length p + 0)) with (6327016 + Z.of_nat (length p)) in RST by lia.
    assert (G8 : 0xada18 + 152 <= mf_buf (stdout_buffered mo p) \/ mf_buf (stdout_buffered mo p) + mf_bufsize (stdout_buffered mo p) <= 0xada18) by (cbn_mf; unfold STDOUT_BUF; lia).
    assert (G9 : mf_buf (stdout_buffered mo p) + mf_bufsize (stdout_buffered mo p) <= lo \/ bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96 + -368)) + 16 <= mf_buf (stdout_buffered mo p)) by (cbn_mf; unfold STDOUT_BUF; lia).
    assert (G10 : (SBUF_LO <= mf_buf (stdout_buffered mo p) /\ mf_buf (stdout_buffered mo p) + mf_bufsize (stdout_buffered mo p) <= SBUF_HI) \/ kHighMemBeg_z <= mf_buf (stdout_buffered mo p)) by (cbn_mf; unfold STDOUT_BUF, SBUF_LO, SBUF_HI; lia).
    assert (G11 : mf_buf (stdout_buffered mo p) + mf_bufsize (stdout_buffered mo p) <= va) by (cbn_mf; unfold STDOUT_BUF; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    icall (pf_pc2d_head (Z_to_bv 64 VF_PC2_RET) (Z_to_bv 64 (bv_unsigned sp + -96 + -368)) gp tp (Z_to_bv 64 0xada18) (Z_to_bv 64 0x149a5) (Z_to_bv 64 DA_Eg3i.SSP_GUARD) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 5) s6 s7 s8 s9 s10 s11 F fc
             lo 0x149a5 0xada18 va g (stdout_buffered mo p) p junk (sh alloc_ceiling) (Z.to_nat ((2^47 - alloc_ceiling) / 8))
             fwritex_fit_ok Q1 H2 Q3 H4 H5 F1 G1 G2 G3 F3 F4 G4 G5 G6 G7 F6 G8 G9 G10 G11
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx (Z_to_bv 64 0) eq_refl eq_refl _ _ _)
      by (cbn_mf; first [ rewrite ?unsigned_lit by lia; eassumption | split; eassumption | apply fmtd_cells; assumption
                | rewrite ?unsigned_lit by lia; eapply rwc_eq; [eassumption| unfold STDOUT_BUF; lia]
                | unfold va_area; eassumption | apply sx32_zero | reflexivity
                | rewrite ?unsigned_lit by lia; f_equal; lia | lia ]
          || match goal with |- ?G => idtac "PCSIDE-FAIL" G end)
    end.
    clear SF2.
    lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST3;
      pose proof (fok_sfF _ _ _ _ _ _ _ _ LA4 LN _ _ _ MU HW SF) as SF3;
      lazymatch goal with H : file_at mx _ _ |- _ => rename H into FILE3 end;
      lazymatch goal with H : bytes_at rsegs mx 0x608ae8 _ |- _ => rename H into BUF3 end;
      lazymatch goal with H : mem_inv rsegs mx |- _ => rename H into MI3 end end.
    (* [comment removed for export] *)
    assert (JL' : (length (skipn 1 junk) = length junk - 1)%nat) by apply length_skipn.
    lazymatch goal with H : rw_cells rsegs _ _ [CB (length junk - 1)%nat (skipn 1 junk)] |- _ =>
      replace (length junk - 1)%nat with (length (skipn 1 junk)) in H by exact JL' end.
    set (junk' := skipn 1 junk) in *; clearbody junk'.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    icall (fwritex_fit_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx 0xada18
             (mf_set_w (stdout_buffered mo p) (Z_to_bv 64 (0x608ae8 + Z.of_nat (length p) + 1)) (Z_to_bv 64 0x608ae8) (Z_to_bv 64 (0x608ae8 + 1024)))
             (p ++ [Z_to_bv 8 48]) [Z_to_bv 8 10] junk' 0x149a7 lo)
      by (cbn_mf; unfold FWRITEX_STACK, STDOUT_BUF; rewrite ?length_app; cbn [length Z.of_nat];
          first [ reflexivity
                | rewrite ?unsigned_lit by lia; eassumption
                | left; lia
                | apply fmtd_nl; assumption
                | lazymatch goal with |- memcpy_icpt_cells _ => exact (proj1 SF3) end
                | lazymatch goal with |- (_ = 0 \/ _)%type => right; split;
                    [ eapply (sfF_fmt_range _ _ _ _ _ _ _ _ _ _ _ SF3); lia | eapply (sfF_buf_range _ _ _ _ _ _ _ _ _ _ _ SF3); lia ] end
                | eapply rwc_eq; [eassumption| lia]
                | eapply bytes_at_eqa; [eassumption| lia]
                | f_equal; lia
                | lia
                | rewrite ?unsigned_lit by lia; lia ]
          || match goal with |- ?G => idtac "W2CSIDE-FAIL" G end)
    end.
    lazymatch goal with H : bytes_at rsegs ?mx 0x608ae8 _ |- _ => rename H into BUF4;
      lazymatch goal with H : rw_cells rsegs mx (0x608ae8 + _ + _) _ |- _ => rename H into RST4 end;
      lazymatch goal with H : file_at mx _ _ |- _ => rename H into FILE4 end end.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (bv_unsigned sp + -96 + -368 + -544)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96 + -368)) + -544))
      by (rewrite unsigned_lit by lia; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pcall (pf_pc2d_tail (Z_to_bv 64 VF_PC2_RET) (Z_to_bv 64 (bv_unsigned sp + -96 + -368)) gp tp (Z_to_bv 64 0xada18) (Z_to_bv 64 0x149a5) (Z_to_bv 64 DA_Eg3i.SSP_GUARD) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 5) s6 s7 s8 s9 s10 s11 F fc
             lo 0x149a5 0xada18 g (p ++ [Z_to_bv 8 48]) junk' Q1 F6
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx _ _ _ _)
      by (first [ rewrite ?unsigned_lit by lia; eassumption | split; eassumption | apply fmtd_cells; assumption ]
          || match goal with |- ?G => idtac "TAILSIDE-FAIL" G end)
    end.
    lazymatch goal with H : stk rsegs ?mx lo (bv_unsigned sp + -96 + -368) |- _ => rename H into ST5 end.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (bv_unsigned sp + -96 + -368)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) + -368))
      by (rewrite unsigned_lit by lia; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    icall (vf_post_buf PF_pc1.FMT_D (Z_to_bv 64 VP_VF_RET) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 0x149a5) (Z_to_bv 64 0xada18) (Z_to_bv 64 va) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
             lo 0x149a5 0xada18 va g H6 H2 F6
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx _ _ _)
      by (first [ rewrite ?unsigned_lit by lia; eassumption | split; eassumption | reflexivity ]
          || match goal with |- ?G => idtac "VFPOSTSIDE-FAIL" G end)
    end.
    lazymatch goal with H : stk rsegs ?mx lo (bv_unsigned sp + -96) |- _ => rename H into ST6;
      lazymatch goal with H : file_at mx _ _ |- _ => rename H into FILE6 end;
      lazymatch goal with H : mem_inv rsegs mx |- _ => rename H into MI6 end end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pcall (vp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 0x149a5 va [Z_to_bv 64 0] H1
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx _)
      by (first [ rewrite ?unsigned_lit by lia; eassumption | split; eassumption ]
          || match goal with |- ?G => idtac "VPPOSTSIDE-FAIL" G end)
    end.
    lazymatch goal with H : stk rsegs ?mx lo (bv_unsigned sp) |- _ => rename H into ST7 end.
    (* [comment removed for export] *)
    astopx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    pose proof (as_minv LPA A m1 md1 AINV1) as [_ HH1].
    pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _).
    eapply (HKONT m1 md1 _ AINV1).
    { split; [| split; [| exact HH1]]. rewrite FS1; reflexivity. rewrite FDS1; reflexivity. }
    { exists mo, (skipn 1 junk'). split; [| split].
      - lazymatch type of FILE6 with file_at _ _ ?fr => replace (stdout_buffered mo (p ++ [Z_to_bv 8 48; Z_to_bv 8 10])) with fr; [exact FILE6|] end.
        unfold stdout_buffered. cbn_mf. rewrite length_app. cbn [length]. f_equal. f_equal. unfold STDOUT_BUF. lia.
      - assert (JL'' : (length (skipn 1 junk') = length junk' - 1)%nat) by apply length_skipn.
        replace (1024 - length (p ++ [Z_to_bv 8 48; Z_to_bv 8 10]))%nat with (length (skipn 1 junk')) by (rewrite length_app; cbn [length]; lia).
        unfold keepP in BUFS0. pose proof (cb2_merge _ _ _ _ _ _ _ BUFS0) as W0.
        eapply (rw_cells_rebuild2 (aview A m) (aview A m1) 0x608ae8 _ (p ++ junk)); [exact W0| exact WM| | | rewrite length_app, JL''; cbn [length]; lia].
        + rewrite <- app_assoc in BUF4. exact BUF4.
        + lazymatch goal with H : rw_cells rsegs _ (0x608ae8 + _ + _) [CB (length junk' - 1)%nat _] |- _ =>
            rewrite <- JL'' in H; eapply rwc_eq; [exact H| rewrite length_app; cbn [length]; lia] end.
      - rewrite length_app. cbn [length]. lia. }
    hot_eexists_all. split; [reflexivity|].
    split. { exact MU. }
    split. { exact WM. }
    split; [exact MI6| exact ST7].
    Unshelve. all: try exact 0%Z; try exact w0; try exact []; try reflexivity; try (rewrite ?unsigned_lit by lia; f_equal; lia).
  Qed.

  Lemma vprintf_first_ok : vprintf_first_stmt.
  Proof.
    unfold vprintf_first_stmt. intros until K. cbv zeta.
    intros AINV MI TP A0 A1 VAB VALO VAHI SPVA RNGC ZSH SOUT FDL [g CAN] GOT ST LO CEIL SP16 HK HKONT.
    destruct SOUT as [FILE [junk BUFS]].
    unfold VPRINTF_ICPT_STACK, FMT_D in *. subst a0 a1.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof alloc_ceiling_val as CV.
    pose proof (consts_hold_ainv LPA A m md AINV) as CH.
    pose proof (vpicpt_cells_of_consts _ CH) as VC. pose proof (asan_memcpy_cells_of_consts _ CH) as CMC. pose proof (asan_memset_cells_of_consts _ CH) as CMS.
    destruct (RNGC _ CH) as [RNGA RNGB].
    unfold DA_Ldix.FMT_D, STDOUT_F, STDOUT_BUF, DA_Eg3i.SSP_GUARD, SSP_GOT in *.
    pose proof (fmtd_cells _ MI) as HF.
    (* [comment removed for export] *)
    pose proof BUFS as BUFS0. lazymatch type of BUFS0 with ?T => change T with (keepP T) in BUFS0 end.
    pose proof (rw_CB_length _ _ _ _ _ BUFS) as JL.
    pose proof BUFS as RST. rewrite <- JL in RST.
    pose proof (bytes_at_nil rsegs (aview A m) 0x608ae8 ltac:(lia)) as BUF.
    pose proof (stk_wr_at _ _ _ (bv_unsigned sp - 8192) 8192 ST ltac:(lia) ltac:(lia)) as WRS.
    (* [comment removed for export] *)
    destruct (stack_zsh_bounds (Clg:=Clg) (bv_unsigned sp - 464 - 4928) (bv_unsigned sp - 464 + 96) ltac:(lia) ltac:(lia) ltac:(lia)) as [ZB SBL].
    assert (SF : sfF 0x149a5 4 0x608ae8 1024 (sh alloc_ceiling) (Z.to_nat ((2^47 - alloc_ceiling) / 8))
                     (bv_unsigned sp + -96 + -368 - PC2_DEPTH) (bv_unsigned sp + -96 + -368 + 96) (aview A m)).
    { unfold sfF, PC2_DEPTH. replace (bv_unsigned sp + -96 + -368 - 4928) with (bv_unsigned sp - 464 - 4928) by lia.
      replace (bv_unsigned sp + -96 + -368 + 96) with (bv_unsigned sp - 464 + 96) by lia.
      refine (conj CMC (conj CMS (conj RNGA (conj RNGB (conj ZSH (conj ZB SBL)))))). }
    assert (VL : vpsh_low 0x149a5 (aview A m)) by (split; [exact VC| exact RNGA]).
    assert (VAA : bytes_at rsegs (aview A m) va (u64s [Z_to_bv 64 0])) by (rewrite u64s_le8_1; exact VAB).
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0xada18, 0xada18 + 152); (0x608ae8, 0x608ae8 + 1024)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(bv_unsigned sp - 8192, bv_unsigned sp); (0xada18, 0xada18 + 152); (0x608ae8, 0x608ae8 + 1024)]).
    { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|]. eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
      split. { right. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
      split; [| exact I]. right. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
    assert (HW : wfok [(bv_unsigned sp - 8192, bv_unsigned sp); (0xada18, 0xada18 + 152); (0x608ae8, 0x608ae8 + 1024)]) by solve_wfok.
    assert (LA4 : 0 <= 4) by lia. assert (LN : 0 <= 1024) by lia.
    unfold file_at, file_cells in FILE. cbn_mf_in FILE.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    assert (H1 : lo <= bv_unsigned sp - VP_DEPTH) by (unfold VP_DEPTH; lia).
    assert (H2 : alloc_ceiling <= lo) by exact CEIL.   (* [comment removed for export] *)
    assert (H3 : va + 8 * Z.of_nat (length [Z_to_bv 64 0]) <= 2^63) by (cbn [length]; lia).
    assert (H4 : IMG_LO <= 0x149a5) by (unfold IMG_LO; lia).
    assert (H5 : 0x149a5 + 4 <= RO_TOP) by (unfold RO_TOP; lia).
    icall (vp_pre ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 0x149a5 va [Z_to_bv 64 0] H1 H2 SPVA H3 H5
             t0 t1 t2 _ _ a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (aview A m) eq_refl eq_refl ST HF VAA VL MI)
      by (first [eassumption | reflexivity | lia]).
    lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST1;
      pose proof (fok_sfF _ _ _ _ _ _ _ _ LA4 LN _ _ _ MU HW SF) as SF1;
      pose proof (fok_vpsh_low _ _ _ _ MU HW VL) as VL1;
      destruct PC0 as [VFR1 VFR2]; rename MI0 into MI1 end.
    (* [comment removed for export] *)
    assert (H6 : lo <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) - VFB_DEPTH) by (rewrite unsigned_lit by lia; unfold VFB_DEPTH; lia).
    assert (H7 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) <= 2^47) by (rewrite unsigned_lit by lia; lia).
    assert (H8 : 0x149a5 + 4 <= RO_TOP) by (unfold RO_TOP; lia).
    assert (F1 : mf_flags stdout0 = 5) by reflexivity.
    assert (F2 : mf_lock stdout0 = -1) by reflexivity.
    assert (F3 : 0 < mf_buf stdout0) by (cbn_mf; unfold STDOUT_BUF; lia).
    assert (F4 : mf_buf stdout0 + mf_bufsize stdout0 < 2^47) by (cbn_mf; unfold STDOUT_BUF; lia).
    assert (F5 : 0 < mf_bufsize stdout0 < 2^31) by (cbn_mf; lia).
    assert (F6 : FILE_LO <= 0xada18 /\ 0xada18 + 152 <= FILE_HI) by (unfold FILE_LO, FILE_HI; lia).
    assert (F7 : if true then mf_wend stdout0 = w0 /\ (0 <= mf_mode stdout0 < 2^32)%Z
                 else mf_wend stdout0 = Z_to_bv 64 (mf_buf stdout0 + mf_bufsize stdout0)) by (split; [reflexivity| cbn_mf; lia]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    icall (vf_pre_buf PF_pc1.FMT_D 4 eq_refl pc1_d towrite_ok
             (Z_to_bv 64 VP_VF_RET) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 0x149a5) (Z_to_bv 64 0xada18) (Z_to_bv 64 va) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
             lo 0x149a5 0xada18 va g stdout0 true
             H6 H7 H2 H8 F1 F2 F3 F4 F5 F6 F7
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx eq_refl eq_refl eq_refl)
      by (first [ rewrite ?unsigned_lit by lia; eassumption | split; eassumption | apply fmtd_cells; assumption
                | unfold file_at, file_cells; cbn_mf; eassumption | reflexivity | lia ]
          || match goal with |- ?G => idtac "VFSIDE-FAIL" G end)
    end.
    clear SF1 VL1 POST.
    lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST2;
      pose proof (fok_sfF _ _ _ _ _ _ _ _ LA4 LN _ _ _ MU HW SF) as SF2;
      destruct PC0 as [APC2 VFR3]; rename MI into MI2; rename POST0 into FILE2 end.
    lazymatch type of FILE2 with file_at _ _ ?fx => set (f1 := fx) in FILE2 end.
    (* [comment removed for export] *)
    assert (Q1 : lo <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96 + -368)) - PC2_DEPTH) by (rewrite unsigned_lit by lia; unfold PC2_DEPTH; lia).
    assert (Q3 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96 + -368)) + 368 <= va) by (rewrite unsigned_lit by lia; lia).
    assert (G1 : mf_wbase f1 = Z_to_bv 64 (mf_buf f1)) by reflexivity.
    assert (G2 : mf_wpos f1 = Z_to_bv 64 (mf_buf f1 + Z.of_nat (@length byte []))) by (subst f1; cbn_mf; cbn [length Z.of_nat]; f_equal; lia).
    assert (G3 : mf_wend f1 = Z_to_bv 64 (mf_buf f1 + mf_bufsize f1)) by reflexivity.
    assert (G0 : mf_flags f1 = 5) by reflexivity.
    assert (G4 : 0 <= mf_bufsize f1 < 2^31) by (subst f1; cbn_mf; lia).
    assert (G5 : -2^31 <= mf_lbf f1 < 2^31) by (subst f1; cbn_mf; lia).
    assert (G6 : Z.of_nat (@length byte []) + 2 <= mf_bufsize f1) by (subst f1; cbn_mf; cbn; lia).
    assert (G7 : Z.of_nat (@length byte []) + Z.of_nat (length junk) = mf_bufsize f1) by (subst f1; cbn_mf; cbn [length Z.of_nat]; lia).
    assert (G8 : 0xada18 + 152 <= mf_buf f1 \/ mf_buf f1 + mf_bufsize f1 <= 0xada18) by (subst f1; cbn_mf; unfold STDOUT_BUF; lia).
    assert (G9 : mf_buf f1 + mf_bufsize f1 <= lo \/ bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96 + -368)) + 16 <= mf_buf f1) by (subst f1; cbn_mf; unfold STDOUT_BUF; lia).
    assert (G10 : (SBUF_LO <= mf_buf f1 /\ mf_buf f1 + mf_bufsize f1 <= SBUF_HI) \/ kHighMemBeg_z <= mf_buf f1) by (subst f1; cbn_mf; unfold STDOUT_BUF, SBUF_LO, SBUF_HI; lia).
    assert (G11 : mf_buf f1 + mf_bufsize f1 <= va) by (subst f1; cbn_mf; unfold STDOUT_BUF; lia).
    assert (B0 : 0 < mf_buf f1) by (subst f1; cbn_mf; unfold STDOUT_BUF; lia).
    assert (BHI : mf_buf f1 + mf_bufsize f1 < 2^47) by (subst f1; cbn_mf; unfold STDOUT_BUF; lia).
    subst f1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    icall (pf_pc2d_head (Z_to_bv 64 VF_PC2_RET) (Z_to_bv 64 (bv_unsigned sp + -96 + -368)) gp tp (Z_to_bv 64 0xada18) (Z_to_bv 64 0x149a5) (Z_to_bv 64 DA_Eg3i.SSP_GUARD) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 5) s6 s7 s8 s9 s10 s11 F fc
             lo 0x149a5 0xada18 va g _ [] junk (sh alloc_ceiling) (Z.to_nat ((2^47 - alloc_ceiling) / 8))
             fwritex_fit_ok Q1 H2 Q3 H4 H5 G0 G1 G2 G3 B0 BHI G4 G5 G6 G7 F6 G8 G9 G10 G11
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx (Z_to_bv 64 0) eq_refl eq_refl _ _ _)
      by (cbn_mf; first [ rewrite ?unsigned_lit by lia; eassumption | split; eassumption | apply fmtd_cells; assumption
                | rewrite ?unsigned_lit by lia; eapply rwc_eq; [eassumption| unfold STDOUT_BUF; cbn [length Z.of_nat]; lia]
                | rewrite ?unsigned_lit by lia; eapply bytes_at_eqa; [eassumption| unfold STDOUT_BUF; lia]
                | unfold va_area; eassumption | apply sx32_zero | reflexivity
                | rewrite ?unsigned_lit by lia; f_equal; lia | lia ]
          || match goal with |- ?G => idtac "PCSIDE-FAIL" G end)
    end.
    clear SF2.
    lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST3;
      pose proof (fok_sfF _ _ _ _ _ _ _ _ LA4 LN _ _ _ MU HW SF) as SF3;
      lazymatch goal with H : file_at mx _ _ |- _ => rename H into FILE3 end;
      lazymatch goal with H : bytes_at rsegs mx 0x608ae8 _ |- _ => rename H into BUF3 end;
      lazymatch goal with H : rw_cells rsegs mx (0x608ae8 + _ + _) _ |- _ => rename H into RST3 end;
      lazymatch goal with H : mem_inv rsegs mx |- _ => rename H into MI3 end end.
    clear G0 G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 B0 BHI.
    (* [comment removed for export] *)
    assert (JL1 : (length (skipn 1 junk) = length junk - 1)%nat) by apply length_skipn.
    rewrite <- JL1 in RST3.
    replace (6327016 + Z.of_nat 0 + 1) with (6327016 + Z.of_nat (length [Z_to_bv 8 48])) in RST3 by (cbn; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof BUFS0 as W0; unfold keepP in W0;
      pose proof (cb2_merge _ _ _ _ _ _ _ (rw_cells_rebuild2 (aview A m) mx 0x608ae8 1024%nat junk [Z_to_bv 8 48] (skipn 1 junk) W0 WM BUF3 RST3 ltac:(cbn [length]; lia))) as BJ2;
      assert (BJ : rw_cells rsegs mx 0x608ae8 [CB 1024%nat (Z_to_bv 8 48 :: skipn 1 junk)])
        by (eapply rw_cells_recast_pf; [exact BJ2| cbn [cells_wf cell_wf length]; split; [cbn [length] in JL1; lia| exact I] | reflexivity]);
      clear BJ2 W0
    end.
    (* [comment removed for export] *)
    astopx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    pose proof (as_minv LPA A m1 md1 AINV1) as [_ HH1].
    pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _).
    (* [comment removed for export] *)
    eapply (fwritex_nl_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 md1 A
              _ [Z_to_bv 8 48] (Z_to_bv 8 48 :: skipn 1 junk) 0x149a7 lo K AINV1 MI3).
    all: lazymatch goal with
         | |- forall m' md', ainv _ _ _ -> _ => idtac
         | |- ?G => first [ reflexivity
                          | rewrite ?unsigned_lit by lia; eassumption
                          | exact BJ
                          | unfold STDOUT_BUF, STDOUT_F; cbn_mf; cbn [length Z.of_nat]; first [ reflexivity | f_equal; lia | lia ]
                          | rewrite FDS1; exact FDL
                          | apply fmtd_nl; assumption
                          | eexists; eassumption
                          | lazymatch goal with |- memcpy_icpt_cells _ => exact (proj1 SF3) end
                          | unfold STDOUT_F; left; lia
                          | exact HK
                          | unfold FWRITEX_STACK; rewrite ?unsigned_lit by lia; lia ]
                    || idtac "NLSIDE-FAIL" G
         end.
    intros m2 md2 AINV2 IO2 FILE5 [bj2 BUF5] ms' PO2.
    destruct_exs PO2. destruct PO2 as [E [MU2 [WM2 [MI5 ST5]]]]. subst ms'.
    unfold FWRITEX_STACK, STDOUT_F, STDOUT_BUF in MU2, ST5, FILE5, BUF5. rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in ST5 by lia.
    cbn_mf_in FILE5.
    transport_after_call rsegs (aview A m1) (aview A m2) MU2 WM2. clear MI3 MU2 WM2.
    destruct IO2 as (FS2 & FDS2 & _).
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0xada18, 0xada18 + 152)] (aview A m2)) as MU3.
    pose proof (wmono_refl rsegs (aview A m2)) as WM3.
    assert (CF3 : client_fpx (L:=LPA) A (aview A m2) [(bv_unsigned sp - 8192, bv_unsigned sp); (0xada18, 0xada18 + 152)]).
    { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|].
        lazymatch goal with H : wr_at rsegs (aview A m2) (bv_unsigned sp - 8192) 8192 |- _ =>
          replace (bv_unsigned sp - (bv_unsigned sp - 8192)) with 8192 by lia; eapply (wr_at_mapped LPA); [exact H| apply (off_image_stack LPA); lia] end. }
      split; [| exact I]. right. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
    assert (HW3 : wfok [(bv_unsigned sp - 8192, bv_unsigned sp); (0xada18, 0xada18 + 152)]) by solve_wfok.
    ago AINV2. fold_cl_segs.
    replace (ret_pc (Z_to_bv 64 650488)) with (Z_to_bv 64 650488) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (bv_unsigned sp + -96 + -368 + -544)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96 + -368)) + -544))
      by (rewrite unsigned_lit by lia; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pcall (pf_pc2d_tail (Z_to_bv 64 VF_PC2_RET) (Z_to_bv 64 (bv_unsigned sp + -96 + -368)) gp tp (Z_to_bv 64 0xada18) (Z_to_bv 64 0x149a5) (Z_to_bv 64 DA_Eg3i.SSP_GUARD) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 5) s6 s7 s8 s9 s10 s11 F fc
             lo 0x149a5 0xada18 g [Z_to_bv 8 48] (skipn 1 junk) Q1 F6
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx _ _ _ _)
      by (first [ rewrite ?unsigned_lit by lia; eassumption | split; eassumption | apply fmtd_cells; assumption ]
          || match goal with |- ?G => idtac "TAILSIDE-FAIL" G end)
    end.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (bv_unsigned sp + -96 + -368)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) + -368))
      by (rewrite unsigned_lit by lia; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    icall (vf_post_buf PF_pc1.FMT_D (Z_to_bv 64 VP_VF_RET) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 0x149a5) (Z_to_bv 64 0xada18) (Z_to_bv 64 va) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
             lo 0x149a5 0xada18 va g H6 H2 F6
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx _ _ _)
      by (first [ rewrite ?unsigned_lit by lia; eassumption | split; eassumption | unfold file_at, file_cells; cbn_mf; eassumption | reflexivity ]
          || match goal with |- ?G => idtac "VFPOSTSIDE-FAIL" G end)
    end.
    lazymatch goal with H : stk rsegs ?mx lo (bv_unsigned sp + -96) |- _ => rename H into ST6;
      lazymatch goal with H : file_at mx _ _ |- _ => rename H into FILE6 end;
      lazymatch goal with H : mem_inv rsegs mx |- _ => rename H into MI6 end end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pcall (vp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 0x149a5 va [Z_to_bv 64 0] H1
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx _)
      by (first [ rewrite ?unsigned_lit by lia; eassumption | split; eassumption ]
          || match goal with |- ?G => idtac "VPPOSTSIDE-FAIL" G end)
    end.
    lazymatch goal with H : stk rsegs ?mx lo (bv_unsigned sp) |- _ => rename H into ST7 end.
    (* [comment removed for export] *)
    astopx AINV2 MU3 WM3 CF3. rename m0 into m3. rename md0 into md3. rename AINV0 into AINV3.
    pose proof (as_minv LPA A m3 md3 AINV3) as [_ HH3].
    pose proof (sbm_io md2 md3 SBM0) as (FS3 & FDS3 & _).
    eapply (HKONT m3 md3 _ AINV3).
    { split; [| split; [| exact HH3]]. rewrite FS3, FS2, FS1; reflexivity. rewrite FDS3, FDS2, FDS1; reflexivity. }
    { lazymatch type of FILE6 with file_at _ _ ?fr => exists (mf_mode fr) end.
      lazymatch goal with H : rw_cells rsegs (aview A m3) 0x608ae8 [CB 1024%nat ?bj] |- _ => exists bj end.
      split; [| split].
      - lazymatch type of FILE6 with file_at _ _ ?fr => replace (stdout_buffered (mf_mode fr) []) with fr; [exact FILE6|] end.
        unfold stdout_buffered. cbn_mf. cbn [length Z.of_nat]. unfold STDOUT_BUF. f_equal; f_equal; lia.
      - cbn [length Nat.sub]. lazymatch goal with H : rw_cells rsegs (aview A m3) 0x608ae8 [CB 1024%nat ?bj] |- _ =>
          apply (cb2_split _ _ _ 0 1024 [] bj); [exact H| reflexivity] end.
      - cbn. lia. }
    hot_eexists_all. split; [reflexivity|].
    split. { first [ exact MU | eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU3]; unfold sub_fp; cbn [outside]; intros; lia ]. }
    split. { first [ exact WM | eapply wmono_trans; [exact WM| exact WM3] ]. }
    split; [exact MI6| exact ST7].
    Unshelve. all: try exact 0%Z; try exact w0; try exact []; try reflexivity; try (rewrite ?unsigned_lit by lia; f_equal; lia).
  Qed.
End Leaves.
